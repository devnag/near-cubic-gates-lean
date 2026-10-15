import Proof.MachineModel.NativeRowInput
import Proof.MachineModel.Bridge
import Proof.CaseAnalysis.RowsUniversalLowering
import Proof.CaseAnalysis.RawRowsLoad
import Proof.CaseAnalysis.FinalPrinterBridge

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.ThresholdCompiler
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open scoped BigOperators

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput

noncomputable section

/-! ## 1. The residual reindexer (H2) — the only new mathematics -/

section Hardwire
variable {q : ℕ}

/-- A.2's reassembly at general arity. Definitionally `C10PrinterBridge.inputOf` once
`live := normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale`. -/
def joinInput (live : Finset (Fin q)) (y : BitInput live.card) (z : BitInput liveᶜ.card) :
    BitInput q := (normalizedLiveExternalInputEquiv live).symm (y, z)

theorem joinInput_coord (live : Finset (Fin q)) (y : BitInput live.card) (z : BitInput liveᶜ.card)
    (c : Fin live.card ⊕ Fin liveᶜ.card) :
    joinInput live y z (normalizedLiveExternalCoordinateEquiv live c) = Sum.elim y z c := by
  unfold joinInput normalizedLiveExternalInputEquiv bitInputSumEquiv
  simp [Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

/-- **The `q → q-K` hardwiring of one live assignment `y`** (paper.tex:2870). The live block's
partial score is subtracted from the exact target; the residual coordinates keep their weights. -/
def hardwire (live : Finset (Fin q)) (g : ExactThresholdGate q) (y : BitInput live.card) :
    ExactThresholdGate liveᶜ.card where
  weight := fun i => g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inr i))
  target := g.target -
    ∑ j : Fin live.card,
      g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inl j)) * (if y j then 1 else 0)

theorem hardwire_eval (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (z : BitInput liveᶜ.card) :
    (hardwire live g y).eval z = g.eval (joinInput live y z) := by
  have hsum : (∑ k : Fin q, g.weight k * (if joinInput live y z k then 1 else 0)) =
      (∑ j : Fin live.card,
        g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inl j)) * (if y j then 1 else 0)) +
      (∑ i : Fin liveᶜ.card,
        g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inr i)) *
          (if z i then 1 else 0)) := by
    rw [← Equiv.sum_comp (normalizedLiveExternalCoordinateEquiv live)
      (fun k => g.weight k * (if joinInput live y z k then 1 else 0)), Fintype.sum_sum_type]
    congr 1
    · exact Finset.sum_congr rfl (fun j _ => by rw [joinInput_coord]; rfl)
    · exact Finset.sum_congr rfl (fun i _ => by rw [joinInput_coord]; rfl)
  unfold ExactThresholdGate.eval
  apply decide_eq_decide.mpr
  rw [hsum]
  show (∑ i : Fin liveᶜ.card,
      g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inr i)) *
        (if z i then 1 else 0)) =
      g.target - (∑ j : Fin live.card,
        g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inl j)) *
          (if y j then 1 else 0)) ↔ _
  omega

/-- The arity cast `liveᶜ.card = (s+1)/2 + s/2` demanded by `CloseoutRowsSharedInput.input`. -/
def castGate {m n : ℕ} (h : m = n) (g : ExactThresholdGate n) : ExactThresholdGate m where
  weight := fun i => g.weight (Fin.cast h i)
  target := g.target

theorem castGate_eval {m n : ℕ} (h : m = n) (g : ExactThresholdGate n) (x : BitInput m) :
    (castGate h g).eval x = g.eval (fun i => x (Fin.cast h.symm i)) := by
  unfold ExactThresholdGate.eval castGate
  congr 1
  apply propext
  constructor <;> intro hx <;> rw [← hx]
  · exact (Fintype.sum_equiv (finCongr h) _ _ (fun i => by simp)).symm
  · exact Fintype.sum_equiv (finCongr h) _ _ (fun i => by simp)

/-- The pool coordinate a malformed occurrence code is sent to: never satisfied, matching
`encodedFiniteBooleanAssignment`'s "invalid codes are false". -/
def falseGate (n : ℕ) : ExactThresholdGate n := ⟨fun _ => 0, 1⟩

@[simp] theorem falseGate_eval (n : ℕ) (x : BitInput n) : (falseGate n).eval x = false := by
  unfold ExactThresholdGate.eval falseGate
  simp

/-- The printer's matrix point `(i,j)` as a point of the residual cube: A.12's two half-cubes
(`RowBinLift.assignment`, `Proof/Supplier/RowBinLiftCuts.lean`). -/
def halfPoint (l r rowN colN : ℕ) : BitInput (l+r) :=
  fun k => Fin.addCases (fun i : Fin l => rowN.testBit i.val)
    (fun i : Fin r => colN.testBit i.val) k

/-- The cached equation of an exact gate holds at `(i,j)` exactly when the gate accepts the
half-cube point. -/
theorem coordinates_holds {l r : ℕ} (g : ExactThresholdGate (l+r)) (rowN colN : ℕ) :
    decide ((CloseoutRowsCacheInput.coordinates (RowCachedEquation.equation g)).Holds
        (RowBinLift.assignment rowN colN)) = g.eval (halfPoint l r rowN colN) := by
  have hscore : (CloseoutRowsCacheInput.coordinates (RowCachedEquation.equation g)).score
        (RowBinLift.assignment rowN colN) =
      ∑ k : Fin (l+r), g.weight k * (if halfPoint l r rowN colN k then 1 else 0) := by
    unfold LabelledEquation.score CloseoutRowsCacheInput.coordinates
      RowCachedEquation.equation RowBinLift.assignment halfPoint
    rw [Fintype.sum_sum_type, Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, Sum.elim_inl, Sum.elim_inr, bitInt]
    rfl
  have htarget : (CloseoutRowsCacheInput.coordinates (RowCachedEquation.equation g)).target =
      g.target := rfl
  unfold ExactThresholdGate.eval LabelledEquation.Holds LabelledEquation.difference
  apply decide_eq_decide.mpr
  rw [hscore, htarget]
  omega

end Hardwire

/-! ## 2. The pool: one gate per (pooled exact child, live assignment) -/

section Pool
variable {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : ℕ)

/-- The `2^K` live assignments, in the canonical `Fintype` order. -/
def liveList : List (BitInput live.card) := (Finset.univ : Finset (BitInput live.card)).toList

theorem liveList_length : (liveList live).length = 2 ^ live.card := by
  rw [liveList, Finset.length_toList, Finset.card_univ, card_bitInput]

/-- The pooled exact-child cache of A.2's `X`/`C` pool (S3a), at arity `q`. -/
def childList : List (ExactThresholdGate q) :=
  ExtDecompositionBatch.GS a (CloseoutRowsUniversal.pool live occ)

/-- The arity-`q` never-satisfied gate, the `getD` default of `childList`. -/
def falseChild : ExactThresholdGate q := falseGate q

/-- `pool` entry number `k+1`: child `k % B` hardwired at live assignment `k / B`. -/
def poolFn (harity : (s+1)/2+s/2 = liveᶜ.card) (k : ℕ) :
    ExactThresholdGate ((s+1)/2+s/2) :=
  castGate harity (hardwire live
    ((childList a live occ).getD (k % (childList a live occ).length) (falseChild))
    ((liveList live).getD (k / (childList a live occ).length) (fun _ => false)))

/-- **The pool** (paper.tex:2870): the sentinel coordinate, then one exact-threshold coordinate over
the residual variables for every (pooled child, live assignment) pair. -/
def pool (harity : (s+1)/2+s/2 = liveᶜ.card) : List (ExactThresholdGate ((s+1)/2+s/2)) :=
  falseGate ((s+1)/2+s/2) ::
    List.ofFn (fun k : Fin ((liveList live).length * (childList a live occ).length) =>
      poolFn a live occ s harity k.val)

theorem pool_length (harity : (s+1)/2+s/2 = liveᶜ.card) :
    (pool a live occ s harity).length =
      (liveList live).length * (childList a live occ).length + 1 := by
  rw [pool, List.length_cons, List.length_ofFn]

/-- The residual point underlying a matrix coordinate of the printed table. -/
def residualPoint (harity : (s+1)/2+s/2 = liveᶜ.card) (x : BitInput ((s+1)/2+s/2)) :
    BitInput liveᶜ.card := fun i => x (Fin.cast harity.symm i)

/-- The pool index of occurrence-child code `c` at live assignment number `yi`. -/
def poolIndex (harity : (s+1)/2+s/2 = liveᶜ.card) (yi : Fin (liveList live).length) (c : ℕ) :
    Fin (pool a live occ s harity).length :=
  if h : c < (childList a live occ).length then
    ⟨(childList a live occ).length * yi.val + c + 1, by
      rw [pool_length]
      have h1 : (childList a live occ).length * (yi.val + 1) ≤
          (childList a live occ).length * (liveList live).length :=
        Nat.mul_le_mul_left _ yi.isLt
      rw [Nat.mul_succ] at h1
      have h2 : (liveList live).length * (childList a live occ).length =
          (childList a live occ).length * (liveList live).length := Nat.mul_comm _ _
      omega⟩
  else ⟨0, by rw [pool_length]; omega⟩

/-- Body lookup: pool coordinate `k+1` is the `k`-th (child, live assignment) pair. -/
theorem pool_getElem (harity : (s+1)/2+s/2 = liveᶜ.card) (k : ℕ)
    (hk : k + 1 < (pool a live occ s harity).length) :
    (pool a live occ s harity)[k + 1]'hk = poolFn a live occ s harity k := by
  simp only [pool, List.getElem_cons_succ, List.getElem_ofFn]

/-- Sentinel lookup: pool coordinate `0` is never satisfied. -/
theorem pool_getElem_zero (harity : (s+1)/2+s/2 = liveᶜ.card)
    (hk : 0 < (pool a live occ s harity).length) :
    (pool a live occ s harity)[0]'hk = falseGate ((s+1)/2+s/2) := by
  simp only [pool, List.getElem_cons_zero]

/-- **The pool lookup is exactly `CloseoutRowsUniversal.assignment`**: the coordinate the printer
reads at the matrix point is the S3a pooled-child value at the reassembled `q`-bit input. -/
theorem pool_index_eval (harity : (s+1)/2+s/2 = liveᶜ.card)
    (yi : Fin (liveList live).length) (c : ℕ) (x : BitInput ((s+1)/2+s/2)) :
    ((pool a live occ s harity).get (poolIndex a live occ s harity yi c)).eval x =
      CloseoutRowsUniversal.assignment a live occ
        (joinInput live ((liveList live).get yi) (residualPoint live s harity x)) c := by
  rw [List.get_eq_getElem]
  by_cases h : c < (childList a live occ).length
  · have hpos : 0 < (childList a live occ).length := Nat.lt_of_le_of_lt (Nat.zero_le c) h
    have hval : (poolIndex a live occ s harity yi c).val =
        (childList a live occ).length * yi.val + c + 1 := by
      unfold poolIndex
      rw [dif_pos h]
    have hlt : (childList a live occ).length * yi.val + c + 1 <
        (pool a live occ s harity).length := hval ▸ (poolIndex a live occ s harity yi c).isLt
    have hcell : (pool a live occ s harity)[(poolIndex a live occ s harity yi c).val]'
        (poolIndex a live occ s harity yi c).isLt =
        poolFn a live occ s harity ((childList a live occ).length * yi.val + c) := by
      simp only [hval]
      exact pool_getElem a live occ s harity _ hlt
    have hmod : ((childList a live occ).length * yi.val + c) %
        (childList a live occ).length = c := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h]
    have hdiv : ((childList a live occ).length * yi.val + c) /
        (childList a live occ).length = yi.val := by
      rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt h]
      omega
    have h' : c < (ExtDecompositionBatch.GS a (CloseoutRowsUniversal.pool live occ)).length := h
    rw [hcell, poolFn, hmod, hdiv,
      List.getD_eq_getElem (childList a live occ) falseChild h,
      List.getD_eq_getElem (liveList live) (fun _ => false) yi.isLt,
      castGate_eval, hardwire_eval]
    unfold CloseoutRowsUniversal.assignment encodedFiniteBooleanAssignment residualPoint
    rw [dif_pos h']
    simp only [List.get_eq_getElem]
    rfl
  · have hval : (poolIndex a live occ s harity yi c).val = 0 := by
      unfold poolIndex
      rw [dif_neg h]
    have hcell : (pool a live occ s harity)[(poolIndex a live occ s harity yi c).val]'
        (poolIndex a live occ s harity yi c).isLt = falseGate ((s+1)/2+s/2) := by
      simp only [hval]
      exact pool_getElem_zero a live occ s harity _
    have h' : ¬ c < (ExtDecompositionBatch.GS a (CloseoutRowsUniversal.pool live occ)).length := h
    rw [hcell, falseGate_eval]
    unfold CloseoutRowsUniversal.assignment encodedFiniteBooleanAssignment
    rw [dif_neg h']

end Pool

/-! ## 3. The bank, its size gates, and `rowInput` -/

section Bank
variable {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : ℕ)

/-- The monomials of one bank row, as pool indices: the S3a lowering of `P` with every occurrence
code sent to its coordinate at live assignment `yi`. -/
def indexRow (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial)
    (yi : Fin (liveList live).length) : List (List (Fin (pool a live occ s harity).length)) :=
  (CloseoutRowsUniversal.lower a live occ P).map
    (fun m => m.map (poolIndex a live occ s harity yi))

/-- The occurrence-index bank `ExtIncidence.NativeRowInput.input` consumes, one row per live
assignment (paper.tex:2870). -/
def ps (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) :
    List (List (List (Fin (pool a live occ s harity).length))) :=
  List.ofFn (indexRow a live occ s harity P)

/-- **The bank**: `ExtIncidence.NativeRowInput.bank` turns the index lists into the monomial masks
`CloseoutRowsCacheInput.family` expects. -/
def bank (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) :
    List (List (List Bool)) :=
  ExtIncidence.NativeRowInput.bank (ps a live occ s harity P)

theorem bank_eq_nativeBank (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) :
    bank a live occ s harity P = ExtIncidence.NativeRowInput.bank (ps a live occ s harity P) := rfl

/-- **`2^K` hardwired live assignments** — paper.tex:2870. -/
theorem bank_length (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) :
    (bank a live occ s harity P).length = 2 ^ live.card := by
  rw [bank, ExtIncidence.NativeRowInput.bank, List.length_map, ps, List.length_ofFn,
    liveList_length]

/-- Every bank row has `N_mon` monomials, so `hw` of `NativeRowInput.input` is the lowering bound. -/
theorem ps_rows_lt (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w) :
    ∀ ms ∈ ps a live occ s harity P, ms.length < 2 ^ w := by
  intro ms hms
  obtain ⟨yi, rfl⟩ := List.mem_ofFn.mp hms
  simpa only [indexRow, List.length_map] using hmon

/-- `bank_rows_le` of P2R §1.5, free from `ExtIncidence.NativeRowInput.bank_width`. -/
theorem bank_rows_le (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w) :
    ∀ rows ∈ bank a live occ s harity P, rows.length ≤ 2 ^ w :=
  ExtIncidence.NativeRowInput.bank_width (ps a live occ s harity P) w
    (ps_rows_lt a live occ s harity P w hmon)

/-- Every bank row is a list of `pool`-length characteristic vectors — `rawRows` is `List.ofFn`. -/
theorem bank_row_length (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) :
    ∀ rows ∈ bank a live occ s harity P, ∀ row ∈ rows,
      row.length = (pool a live occ s harity).length := by
  intro rows hrows row hrow
  obtain ⟨ms, _, rfl⟩ := List.mem_map.mp hrows
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hrow
  exact List.length_ofFn

/-- The BinLift batch length `CloseoutRowsCacheInput.input` measures is the emitted cut count
`raw_cuts_gate` bounds (`CloseoutRowsSharedDigits.batch_perm` + `RowPowerBinLift.batch_length`). -/
theorem batch_length_eq {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (Q w : ℕ)
    (bk : List (List (List Bool))) (hw : ∀ rows ∈ bk, rows.length ≤ 2 ^ w) :
    (RowBinLift.batch Q (CloseoutRowsCacheInput.family gs bk)).length =
      (bk.flatMap (CloseoutRowsSharedDigits.cuts gs Q w)).length := by
  rw [(CloseoutRowsSharedDigits.batch_perm gs Q w bk hw).length_eq, RowPowerBinLift.batch_length]

/-- **The size gate** (`hg` of `NativeRowInput.input`), `Q := K+1` verbatim as in `raw_cuts_gate`. -/
theorem gate (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w) (hpos : 1 ≤ w)
    (hload : 200 * (live.card + w * (live.card + 2)) ≤ s) :
    (RowBinLift.batch (live.card + 1)
      (CloseoutRowsCacheInput.family (pool a live occ s harity)
        (bank a live occ s harity P))).length ^ 100 ≤ 2 ^ s := by
  have hw := bank_rows_le a live occ s harity P w hmon
  rw [batch_length_eq (pool a live occ s harity) (live.card + 1) w
    (bank a live occ s harity P) hw]
  exact CloseoutRawRows.raw_cuts_gate (pool a live occ s harity) live.card w s
    (bank a live occ s harity P) (le_of_eq (bank_length a live occ s harity P)) hw hpos hload

def rowInput (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
    (hpos : 1 ≤ w) (hload : 200 * (live.card + w * (live.card + 2)) ≤ s) : EquationRow.Input :=
  ExtIncidence.NativeRowInput.input s (live.card + 1) w (pool a live occ s harity)
    (ps a live occ s harity P) hs (gate a live occ s harity P w hmon hpos hload)
    (ps_rows_lt a live occ s harity P w hmon)

/-- `Q ≤ p` — `CloseoutRowsSharedInput.common_width`, at `rfl` level. -/
theorem rowInput_p (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
    (hpos : 1 ≤ w) (hload : 200 * (live.card + w * (live.card + 2)) ≤ s) :
    live.card + 1 ≤
      (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).p := by
  have h : (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).p =
      ((exactListWord (pool a live occ s harity)).length + 1) *
        ((pool a live occ s harity).length * (live.card + 1)) + (live.card + 1) + 1 := rfl
  omega

/-- The cuts of `rowInput` are the emitted per-row cut stream (needed by S3c-3's writer). -/
theorem rowInput_cuts (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
    (hpos : 1 ≤ w) (hload : 200 * (live.card + w * (live.card + 2)) ≤ s) :
    (rowInput a live occ s harity P w hs hmon hpos hload).cuts =
      (bank a live occ s harity P).flatMap
        (CloseoutRowsSharedDigits.cuts (pool a live occ s harity) (live.card + 1) w) := rfl

end Bank

/-! ## 4. `bank_eval` — the one semantic identity -/

section Eval
variable {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : ℕ)

theorem exactPolynomialValue_map {Row Column E F : Type} (holds : F → Row → Column → Bool)
    (f : E → F) (mons : List (List E)) (row : Row) (col : Column) :
    exactPolynomialValue holds (mons.map (fun m => m.map f)) row col =
      exactPolynomialValue (fun e => holds (f e)) mons row col := by
  unfold exactPolynomialValue polynomialOccurrenceCount exactMonomialValue
  simp only [List.map_map, Function.comp_def, List.all_map]

theorem bank_eval (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial)
    (yi : Fin (liveList live).length) (rowN colN : ℕ) :
    CompetitorRowCountMeaning.occurrence
        (CloseoutRowsCacheInput.polynomial (pool a live occ s harity)
          (ExtIncidence.rawRows (indexRow a live occ s harity P yi))) rowN colN % 2 =
      (exactPolynomialValue
        (fun (code : ℕ) (y : BitInput live.card) (z : BitInput liveᶜ.card) =>
          encodedFiniteBooleanAssignment
            (fun i : Fin occ.length =>
              residualVariable (occ.get i).gate live (joinInput live y z)) code)
        P ((liveList live).get yi)
        (residualPoint live s harity (halfPoint ((s+1)/2) (s/2) rowN colN))).toNat := by
  set x : BitInput ((s+1)/2+s/2) := halfPoint ((s+1)/2) (s/2) rowN colN with hx
  set z : BitInput liveᶜ.card := residualPoint live s harity x with hz
  set y : BitInput live.card := (liveList live).get yi with hy
  have hstep :
      CompetitorRowCountMeaning.occurrence
          (CloseoutRowsCacheInput.polynomial (pool a live occ s harity)
            (ExtIncidence.rawRows (indexRow a live occ s harity P yi))) rowN colN % 2 =
        (exactPolynomialValue
          (fun (e : RowBinLift.Equation ((s+1)/2) (s/2)) (_ : Unit) (_ : Unit) =>
            decide (e.Holds (RowBinLift.assignment rowN colN)))
          (CloseoutRowsCacheInput.polynomial (pool a live occ s harity)
            (ExtIncidence.rawRows (indexRow a live occ s harity P yi))) () ()).toNat :=
    (exactPolynomialValue_toNat _ _ () ()).symm
  rw [hstep, ExtIncidence.raw_polynomial_value]
  congr 1
  rw [indexRow, exactPolynomialValue_map]
  have hcoord : (fun (c : ℕ) =>
      (fun (i : Fin (pool a live occ s harity).length) (_ : Unit) (_ : Unit) =>
        decide ((CloseoutRowsCacheInput.coordinates
          (RowCachedEquation.equation (pool a live occ s harity)[i.val])).Holds
            (RowBinLift.assignment rowN colN)))
        (poolIndex a live occ s harity yi c)) =
      (fun (c : ℕ) (_ : Unit) (_ : Unit) =>
        CloseoutRowsUniversal.assignment a live occ (joinInput live y z) c) := by
    funext c _ _
    dsimp only
    rw [coordinates_holds, hy, hz, hx, ← List.get_eq_getElem]
    exact pool_index_eval a live occ s harity yi c _
  rw [hcoord]
  have hlower := CloseoutRowsUniversal.lower_value a live occ P (joinInput live y z)
  exact hlower

end Eval

/-! ## 5. The C10 instantiation consumed by S3c-2 / S4 / S1 -/

section C10
variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- The C10 live set `I` of A.2 (`Proof/Supplier/SupplierEstimator.lean`). -/
def liveSet : Finset (Fin request.q) :=
  normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale

/-- The residual arity `s = q − K` (`C10PrinterBridge.residualArity_eq`). -/
theorem residualArity (liveScale' : ℕ) :
    (liveSet request liveScale')ᶜ.card =
      request.q - normalizedLiveCount request.q liveScale' :=
  C10PrinterBridge.residualArity_eq request liveScale'

/-- The half-cube arity cast at the C10 request: `(s+1)/2 + s/2 = liveᶜ.card`. -/
theorem c10_arity (liveScale' : ℕ) :
    (request.q - normalizedLiveCount request.q liveScale' + 1) / 2 +
        (request.q - normalizedLiveCount request.q liveScale') / 2 =
      (liveSet request liveScale')ᶜ.card := by
  rw [residualArity]
  omega

theorem joinInput_eq_inputOf
    (y : BitInput (liveSet request liveScale).card)
    (z : BitInput (liveSet request liveScale)ᶜ.card) :
    joinInput (liveSet request liveScale) y z =
      C10PrinterBridge.inputOf request liveScale y z := rfl

theorem bank_eval_residualHolds (a : DecompositionAlgorithm) (s : ℕ)
    (harity : (s+1)/2+s/2 = (liveSet request liveScale)ᶜ.card)
    (P : StructuralGF2Polynomial)
    (yi : Fin (liveList (liveSet request liveScale)).length) (rowN colN : ℕ) :
    CompetitorRowCountMeaning.occurrence
        (CloseoutRowsCacheInput.polynomial
          (pool a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity)
          (ExtIncidence.rawRows
            (indexRow a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity
              P yi))) rowN colN % 2 =
      (exactPolynomialValue (C10PrinterBridge.residualHolds request liveScale) P
        ((liveList (liveSet request liveScale)).get yi)
        (residualPoint (liveSet request liveScale) s harity
          (halfPoint ((s+1)/2) (s/2) rowN colN))).toNat :=
  bank_eval a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity P yi
    rowN colN

end C10

end

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput
