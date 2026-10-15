import Proof.MachineModel.Run
import Proof.CaseAnalysis.RowsSourceDigits
import Proof.CaseAnalysis.RowsBankPolynomial
import Proof.CaseAnalysis.RowsFamilyLoop
import Proof.CaseAnalysis.RowsSourceMeaning

namespace NearCubicWires.ExtIncidence
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution SupplierPrinter
open RepairOrdinary.CloseoutRowsSourceDigits
open RepairOrdinary.CloseoutRowsCacheInput RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem maskOf_map_val {B : ℕ} (m : List (Fin B)) :
    maskOf B (m.map Fin.val) = List.ofFn (fun i : Fin B => decide (i ∈ m)) := by
  unfold maskOf
  congr 1
  funext i
  apply decide_eq_decide.mpr
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := List.mem_map.mp h
    exact (Fin.ext hji) ▸ hj
  · intro h
    exact List.mem_map.mpr ⟨i, h, rfl⟩

def rawIndices {B : ℕ} (ms : List (List (Fin B))) := ms.map (List.map Fin.val)
def rawRows {B : ℕ} (ms : List (List (Fin B))) :=
  ms.map (fun m=>List.ofFn (fun i : Fin B=>decide (i∈m)))

theorem raw_table_eq_rows {B : ℕ} (ms : List (List (Fin B))) :
    ExtIncidence.table B (rawIndices ms)=(rawRows ms).flatten := by
  simp only [ExtIncidence.table,rawIndices,rawRows,List.map_map,Function.comp_def,
    ExtIncidence.maskOf_map_val]

theorem raw_rows_run {B : ℕ} (ms : List (List (Fin B))) (pre tail out : List Bool) (c : ℕ) :
    ∃ r : ExecutionReceipt 5 7,
      runFrom ExtIncidence.machine (ExtIncidence.cost B (rawIndices ms))
        (ExtIncidence.cfg 0 (pre++ExtIncidence.stream (rawIndices ms)++tail) pre.length B 1
          (List.replicate B false) 0 out c)=some r ∧
      r.final=ExtIncidence.cfg 6 (pre++ExtIncidence.stream (rawIndices ms)++tail)
        (pre.length+(ExtIncidence.stream (rawIndices ms)).length) B 1 (List.replicate B false) 0
        (out++(rawRows ms).flatten) (c+ms.length) ∧
      r.steps=ExtIncidence.cost B (rawIndices ms) := by
  have valid : ∀ m∈rawIndices ms,∀ d∈m,d<B := by
    intro m hm d hd
    obtain ⟨m',_,rfl⟩:=List.mem_map.mp hm
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hd
    exact i.isLt
  obtain ⟨r,hr,hf,hs⟩:=ExtIncidence.stream_run pre tail B (rawIndices ms) valid out c
  refine ⟨r,hr,?_,hs⟩
  rw [raw_table_eq_rows] at hf
  simpa only [rawIndices,List.length_map] using hf

theorem raw_polynomial_value {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    {R C : Type} (holds : Equation l r→R→C→Bool)
    (ms : List (List (Fin gs.length))) (row : R) (column : C) :
    exactPolynomialValue holds (polynomial gs (rawRows ms)) row column=
      exactPolynomialValue (fun i=>holds (coordinates (RowCachedEquation.equation gs[i.val]))) ms row column := by
  unfold exactPolynomialValue polynomialOccurrenceCount
  congr 2
  simp only [polynomial,rawRows,List.map_map,Function.comp_def,CloseoutRowsSourceMeaning.monomial_value]

/-- The canonical monomial occurrence list of `P`, as child indices. Repeated
variables inside one monomial stay repeated here and collapse in the row. -/
noncomputable def occurrences {B : ℕ} (P : MvPolynomial (Fin B) (ZMod 2)) : List (List ℕ) :=
  (polynomialMonomialOccurrences P).map (List.map Fin.val)

theorem occurrences_bound {B : ℕ} (P : MvPolynomial (Fin B) (ZMod 2)) :
    ∀ m ∈ occurrences P, ∀ d ∈ m, d < B := by
  intro m hm d hd
  obtain ⟨m', _, rfl⟩ := List.mem_map.mp hm
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
  exact i.isLt

theorem table_eq_rows {B : ℕ} (P : MvPolynomial (Fin B) (ZMod 2)) :
    table B (occurrences P) = (rows P).flatten := by
  simp only [table, occurrences, rows, List.map_map, Function.comp_def, maskOf_map_val]

theorem occurrences_length {B : ℕ} (P : MvPolynomial (Fin B) (ZMod 2)) :
    (occurrences P).length = (rows P).length := by
  simp [occurrences, rows]

/-- The producer on the canonical occurrence stream of `P`: it appends exactly
the bank's `rows.flatten`, counts `P.support.card` rows in unary, returns the
template head to 1 and the scratch row to all-zero. -/
theorem rows_run {B : ℕ} (P : MvPolynomial (Fin B) (ZMod 2)) (pre tail out : List Bool) (c : ℕ) :
    ∃ r : ExecutionReceipt 5 7,
      runFrom machine (cost B (occurrences P))
        (cfg 0 (pre ++ stream (occurrences P) ++ tail) pre.length B 1 (List.replicate B false) 0 out c) =
          some r ∧
      r.final.tapes 3 = out ++ (rows P).flatten ∧
      r.final.heads 3 = (out ++ (rows P).flatten).length ∧
      r.final.tapes 4 = List.replicate (c + P.support.card) true ∧
      r.final.heads 4 = c + P.support.card ∧
      r.final.tapes 2 = List.replicate B false ∧ r.final.heads 2 = 0 ∧
      r.final.tapes 1 = UnaryTemplate.tape B ∧ r.final.heads 1 = 1 ∧
      r.final.tapes 0 = pre ++ stream (occurrences P) ++ tail ∧
      r.final.heads 0 = pre.length + (stream (occurrences P)).length ∧
      r.steps = cost B (occurrences P) := by
  obtain ⟨r, hr, _, t0, h0, t1, hh1, t2, hh2, t3, hh3, t4, hh4, hs⟩ :=
    stream_run_tapes pre tail B (occurrences P) (occurrences_bound P) out c
  have hcount : c + (occurrences P).length = c + P.support.card := by
    rw [occurrences_length, rows_length]
  refine ⟨r, hr, ?_, ?_, ?_, ?_, t2, hh2, t1, hh1, t0, h0, hs⟩
  · rw [t3, table_eq_rows]
  · rw [hh3, table_eq_rows]
  · rw [t4, hcount]
  · rw [hh4, hcount]

/-- Prepared-input specialization only: this does not compose the incidence producer with the bank. -/
theorem bank_application {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (P : MvPolynomial (Fin gs.length) (ZMod 2)) (p F Q w : ℕ) (bankOut : List Bool)
    (hM : 0 < P.support.card) (hw : P.support.card < 2^w) (hQp : Q ≤ p)
    (hp : RowTupleFixedCapacity.width gs Q ≤ p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    let C := CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    ∃ actual, runFrom CloseoutRowsBankPolynomial.machine (CloseoutRowsBankPolynomial.budget Q C)
        (CloseoutRowsBankPolynomial.entry gs p F Q w C (rows P) bankOut) = some actual ∧
      actual.final.tapes 31 =
        bankOut ++ (CloseoutRowsSharedDigits.cuts gs Q w (rows P)).flatMap (MatrixScoreBatch.cutWord p) ∧
      actual.steps ≤ CloseoutRowsBankPolynomial.budget Q C := by
  intro C
  obtain ⟨actual, ha, _, ht, _, hs⟩ := CloseoutRowsBankPolynomial.polynomial_run gs p F Q w (rows P) bankOut
    (fun row hr => row_length P row hr) (by rw [rows_length]; exact hM) (by rw [rows_length]; exact hw)
    hQp hp hF
  exact ⟨actual, ha, ht, hs⟩

/-- Prepared-input specialization of the existing packet family loop. The adopted
direct-bank route has a separate physical producer/docking obligation. -/
theorem family_application {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (ps : List (MvPolynomial (Fin gs.length) (ZMod 2))) (p F Q : ℕ) (out pre tail : List Bool)
    (hQp : Q ≤ p) (hp : RowTupleFixedCapacity.width gs Q ≤ p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    let w := width ps
    let C := CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let result := out ++ ((bank ps).flatMap (CloseoutRowsSharedDigits.cuts gs Q w)).flatMap
      (MatrixScoreBatch.cutWord p)
    ∃ actual, runFrom CloseoutRowsFamilyLoop.machine (CloseoutRowsFamilyLoop.budget (bank ps).length Q C)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0
          (CloseoutRowsFamilyLoop.entry gs p F Q w C (bank ps) pre tail 0 out) (bank ps).length 1) =
          some actual ∧
      actual.final = RepairSource.VerifierDecoding.RepeatMachine.cfg 3
        (CloseoutRowsFamilyLoop.entry gs p F Q w C (bank ps) pre tail (bank ps).length result)
        (bank ps).length 1 ∧
      actual.steps ≤ CloseoutRowsFamilyLoop.budget (bank ps).length Q C := by
  intro w C result
  exact CloseoutRowsFamilyLoop.family_run gs p F Q w (bank ps) out pre tail
    (fun rs hrs row hrow => by
      obtain ⟨P, _, rfl⟩ := List.mem_map.mp hrs
      exact row_length P row hrow)
    (bank_width ps) hQp hp hF

end NearCubicWires.ExtIncidence
