import Proof.CaseAnalysis.RowsCommonInput
import Proof.Supplier.EquationRowProducer

/-! The raw signed row is physically printed into the matrix request before
the existing count-table and six-field record caller runs. The initial
metadata contains only Q, parity, the selection mask and scalar fields.
The row-printing budget is added once to the complete table budget. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawRecord
open LocalBitMultitape MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
open RepairRepresentation
open CompetitorCrossScheduler (producer)
open CompetitorMonomialStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program) := 130+CompetitorCountTableRecord.tapes p
def receive (p : Program) (i : Fin (CompetitorCountTableRecord.tapes p)) : Fin (tapes p) :=
  if i.val=0 then ⟨128,by unfold tapes; omega⟩ else i.natAdd 130
def extra (p : Program) (row : EquationRow.Input) (Q : ℕ) (q : ℚ)
    (denominator : ℕ) (xs : List (Bool × ℕ)) (i : Fin (CompetitorCountTableRecord.tapes p)) :=
  if i.val=0 then [] else CompetitorCountTableRecord.input p (EquationRow.request row)
    Q row.odd q denominator xs i
def input (p : Program) (row : EquationRow.Input) (Q : ℕ) (q : ℚ)
    (denominator : ℕ) (xs : List (Bool × ℕ)) :=
  Fin.addCases (m := 130) (n := CompetitorCountTableRecord.tapes p) (motive := fun _ => List Bool)
    (EquationRowFramed.input row) (extra p row Q q denominator xs)
noncomputable def first (p : Program) :=
  TapeEmbedding.machine (CompetitorCountTableRecord.tapes p) EquationRowFramed.machine
noncomputable def last {s : ℕ} (p : Program) (callee : Machine (CompetitorCountTableRecord.tapes p) s) :=
  RecoveryFocus.machine (receive p) callee
noncomputable def machine {s : ℕ} (p : Program) (callee : Machine (CompetitorCountTableRecord.tapes p) s) :=
  Composition.machine (first p) (last p callee)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (Q : ℕ) :=
  EquationRowFramed.uniformBudget row+1+CompetitorCountTableRecord.budget a (EquationRow.request row) Q
noncomputable def envelope (a : WilliamsAlgorithm) (row : EquationRow.Input) :=
  EquationRowFramed.uniformBudget row+1+CompetitorCountTableRecord.envelope a (EquationRow.request row)

theorem receive_injective (p : Program) : Function.Injective (receive p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [receive] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv <;> omega

theorem input_zero (p : Program) (row : EquationRow.Input) (Q : ℕ) (q : ℚ)
    (denominator : ℕ) (xs : List (Bool × ℕ))
    (i : Fin (CompetitorCountTableRecord.tapes p)) (hi : i.val=0) :
    CompetitorCountTableRecord.input p (EquationRow.request row) Q row.odd q denominator xs i=
      physicalInput (EquationRow.request row) := by
  let z : Fin (CompetitorCrossScheduler.tapes p) := ⟨0,by unfold CompetitorCrossScheduler.tapes; omega⟩
  have he : i=(((z.castAdd 511).castAdd 124).castAdd 92).castAdd 27 := Fin.ext hi
  rw [he]
  simp [CompetitorCountTableRecord.input,
    CompetitorSelectedTable.extend,CompetitorSelectedTable.tapes,CompetitorCountTable.input,
    CompetitorCountTable.extend,CompetitorCountTable.tapes,CompetitorCountBanks.input,
    CompetitorCountBanks.extend,CompetitorCountBanks.tapes,CompetitorCrossScheduler.input,
    CompetitorCrossScheduler.tapes,Fin.addCases,z]

theorem prefix_run {s : ℕ} (p : Program) (callee : Machine (CompetitorCountTableRecord.tapes p) s)
    (row : EquationRow.Input) (Q : ℕ) (q : ℚ) (denominator : ℕ) (xs : List (Bool × ℕ))
    (fuel : ℕ) (child : ExecutionReceipt (CompetitorCountTableRecord.tapes p) s)
    (ch : run callee fuel (CompetitorCountTableRecord.input p (EquationRow.request row)
      Q row.odd q denominator xs)=some child) :
    ∃ actual,run (machine p callee) (EquationRowFramed.uniformBudget row+1+fuel)
      (input p row Q q denominator xs)=some actual ∧
      actual.steps≤EquationRowFramed.uniformBudget row+1+child.steps ∧
      (∀ i,actual.final.heads (receive p i)=child.final.heads i) ∧
      (∀ i,actual.final.tapes (receive p i)=child.final.tapes i) := by
  let ext := extra p row Q q denominator xs
  obtain ⟨base,hbase,bt,bh,bs⟩ := EquationRowFramed.producer_run row
  let before : ExecutionReceipt (tapes p) _ := TapeEmbedding.receipt
    (fun _ : Fin (CompetitorCountTableRecord.tapes p) => 0) ext base
  have hfirst := TapeEmbedding.run_embed EquationRowFramed.machine
    (fun _ : Fin (CompetitorCountTableRecord.tapes p) => 0) ext _ _ base hbase
  have hheads : ∀ i,before.final.heads (receive p i)=0 := by
    intro i
    by_cases hz : i.val=0
    · simp only [receive,hz,↓reduceIte]
      change before.final.heads ((128 : Fin 130).castAdd (CompetitorCountTableRecord.tapes p))=0
      rw [TapeEmbedding.receipt_heads_old]
      exact bh 128
    · simp only [receive,hz,↓reduceIte]
      exact TapeEmbedding.receipt_heads_new _ ext base i
  have htapes : ∀ i,before.final.tapes (receive p i)=
      CompetitorCountTableRecord.input p (EquationRow.request row) Q row.odd q denominator xs i := by
    intro i
    by_cases hz : i.val=0
    · simp only [receive,hz,↓reduceIte]
      change before.final.tapes ((128 : Fin 130).castAdd (CompetitorCountTableRecord.tapes p))=_
      rw [TapeEmbedding.receipt_tapes_old,bt]
      exact (input_zero p row Q q denominator xs i hz).symm
    · simp only [receive,hz,↓reduceIte]
      rw [TapeEmbedding.receipt_tapes_new]
      simp only [ext,extra,hz,↓reduceIte]
  obtain ⟨tail,th,_,ts,hh,tt,_⟩ := RecoveryFocus.dock (receive p) (receive_injective p)
    callee fuel before.final.heads before.final.tapes _ hheads htapes child ch
  have htail : runFrom (last p callee) fuel
      (Composition.restart before.final (last p callee).start)=some tail := th
  have hj := Composition.run_join (first p) (last p callee) _ _ _ before tail hfirst htail
  have hi : Composition.leftConfig _ (TapeEmbedding.config
      (fun _ : Fin (CompetitorCountTableRecord.tapes p) => 0) ext
      (initialConfiguration EquationRowFramed.machine (EquationRowFramed.input row)))=
      initialConfiguration (machine p callee) (input p row Q q denominator xs) := by
    apply configuration_ext
    · rfl
    · funext i
      change Fin.addCases (m := 130) (n := CompetitorCountTableRecord.tapes p)
        (motive := fun _ => ℕ) (fun _ => 0) (fun _ => 0) i=0
      refine Fin.addCases (m := 130) (n := CompetitorCountTableRecord.tapes p) ?_ ?_ i <;>
        intro j <;> simp only [Fin.addCases_left,Fin.addCases_right]
    · rfl
  rw [hi] at hj
  refine ⟨Composition.joinedReceipt before tail,hj,?_,hh,tt⟩
  change base.steps+1+tail.steps≤_
  rw [ts]
  omega

theorem raw_record_run (a : WilliamsAlgorithm) (row : EquationRow.Input) (Q : ℕ)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (q : ℚ) (denominator : ℕ) (hQ : Q≤(EquationRow.request row).p)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : ℤ)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat)) :
    ∃ actual,run (machine (producer a) (CompetitorCountTableRecord.machine a)) (budget a row Q)
      (input (producer a) row Q q denominator (CompetitorSelectedCells.cells row.odd f select))=some actual ∧
      actual.steps≤envelope a row ∧
      actual.final.tapes (receive (producer a) (CompetitorCountTableRecord.slots (producer a) 117))=
        recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator ∧
      actual.final.heads (receive (producer a) (CompetitorCountTableRecord.slots (producer a) 117))=
        (recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator).length ∧
      actual.final.tapes (receive (producer a) (CompetitorCountTableRecord.slots (producer a) 0))=
        physicalInput (EquationRow.request row) := by
  have hwidth : Q≤CompetitorSameBucketColdDense.width (EquationRow.request row) := by
    rw [CompetitorSameBucketColdDense.width_eq]
    exact hQ.trans (by omega)
  obtain ⟨child,ch,cs,ct,co,c0⟩ := CompetitorCountTableRecord.record_run a (EquationRow.request row)
    Q row.odd f select q denominator hwidth (CompetitorRowCountMeaning.odd_even_size row) hf hc
  obtain ⟨actual,ha,hs,hh,ht⟩ := prefix_run (producer a) (CompetitorCountTableRecord.machine a)
    row Q q denominator _ _ child ch
  have cb := cs.trans (CompetitorCountTableRecord.budget_bound a (EquationRow.request row) Q hQ)
  refine ⟨actual,ha,?_,(ht _).trans ct,(hh _).trans co,(ht _).trans c0⟩
  unfold envelope
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsRawRecord
