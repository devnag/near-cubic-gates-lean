import Proof.CaseAnalysis.RowsPermutedRecord
import Proof.Supplier.RowTupleTerms

/-! A single width covers the actual positional-subset cut family, including
its signed coefficient and empty child lists. Its equation request applies
the existing successor widening once. Family size is the actual occurrence
count; no duplicate monomial is removed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRows
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope MatrixScoreBatch EquationRow RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def commonWidth (w D Q : ℕ) := w*(D*Q)+Q
def orderedCuts {l r : ℕ} (w Q : ℕ) (ms : List (List (Equation l r))) :=
  (RowTupleTerms.terms Q ms).map fun t => split t.1 (RowPowerBinLift.stack w t.2)
def orderedBatch {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r)))) :=
  rows.flatMap (orderedCuts w Q)

theorem ordered_cuts_perm {l r : ℕ} (w Q : ℕ) (ms : List (List (Equation l r))) :
    (orderedCuts w Q ms).Perm (RowPowerBinLift.cuts w Q ms) :=
  (RowTupleTerms.terms_perm Q ms).map _
theorem ordered_batch_perm {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r)))) :
    (orderedBatch w Q rows).Perm (RowPowerBinLift.batch w Q rows) := by
  apply List.Perm.flatMap_left
  intro ms _
  exact ordered_cuts_perm w Q ms
theorem ordered_batch_length {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r)))) :
    (orderedBatch w Q rows).length=(RowBinLift.batch Q rows).length :=
  (ordered_batch_perm w Q rows).length_eq.trans (RowPowerBinLift.batch_length w Q rows)

theorem term_length {α : Type} (D Q : ℕ) (ms : List (List α))
    (hD : ∀ m∈ms, m.length≤D) (t : ℤ × List α) (ht : t∈RowBinLift.terms Q ms) :
    t.2.length≤D*Q := by
  obtain ⟨j,hj,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨selected,hs,rfl⟩ := List.mem_map.mp ht
  obtain ⟨hsub,hlen⟩ := List.mem_sublistsLen.mp hs
  have hsum := RowBinLift.sum_le_length_mul (selected.map List.length) D (by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hn
    exact hD m (hsub.subset hm))
  have hjQ : j+1≤Q := (Nat.succ_le_of_lt (List.mem_range.mp hj)).trans (Nat.min_le_left _ _)
  rw [List.length_map,hlen] at hsum
  simpa only [List.length_flatten,Nat.mul_comm] using
    hsum.trans (Nat.mul_le_mul_right D hjQ)

theorem split_fits {l r : ℕ} (p : ℕ) (c : ℤ) (e : Equation l r)
    (he : equationMagnitudeBound e<2^p) (hc : c.natAbs<2^p) : Fits p (split c e) := by
  have hweight (i : Fin l ⊕ Fin r) : (e.weights i).natAbs<2^p := by
    have hs := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le (e.weights j).natAbs)
      (Finset.mem_univ i)
    apply (hs.trans (Nat.le_add_right _ e.target.natAbs)).trans_lt
    exact he
  refine ⟨?_,?_,hc⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact hweight (.inl i)
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact hweight (.inr i)
  · exact (Nat.le_add_left _ _).trans_lt he

theorem ordered_cuts_fit {l r : ℕ} (w D Q : ℕ) (ms : List (List (Equation l r)))
    (hD : ∀ m∈ms, m.length≤D)
    (hw : ∀ e∈ms.flatten, equationMagnitudeBound e<2^w)
    (c : Cut) (hc : c∈orderedCuts w Q ms) : Fits (commonWidth w D Q) c := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
  have hterm : t∈RowBinLift.terms Q ms := (RowTupleTerms.terms_perm Q ms).mem_iff.mp ht
  have hlen := term_length D Q ms hD t hterm
  have hbase := RowPowerBinLift.stack_width w t.2
    (fun e he => hw e (RowPowerBinLift.term_members Q ms t hterm e he))
  have he : equationMagnitudeBound (RowPowerBinLift.stack w t.2)<2^commonWidth w D Q :=
    hbase.trans_le (Nat.pow_le_pow_right (by decide) (by
      unfold commonWidth
      exact (Nat.mul_le_mul_left w hlen).trans (Nat.le_add_right _ _)))
  have coeff := (RowBinLift.term_bounds Q D w ms hD (fun e he => (hw e he).le) t hterm).1
  exact split_fits _ _ _ he
    (coeff.trans_le (Nat.pow_le_pow_right (by decide) (by unfold commonWidth; omega)))

def commonInput (s w D Q : ℕ) (rows : List (List (List (Equation ((s+1)/2) (s/2)))))
    (hs : 67 ≤ s) (hg : (RowBinLift.batch Q rows).length^100≤2^s)
    (hD : ∀ ms∈rows, ∀ m∈ms, m.length≤D)
    (hw : ∀ ms∈rows, ∀ e∈ms.flatten, equationMagnitudeBound e<2^w) : EquationRow.Input where
  d := (s+1)/2
  p := commonWidth w D Q
  odd := decide (s%2=1)
  cuts := orderedBatch w Q rows
  lengths := by
    intro c hc
    obtain ⟨ms,_,hm⟩ := List.mem_flatMap.mp hc
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hm
    simp only [split,List.length_ofFn]
    constructor
    · trivial
    · by_cases hp : s%2=1 <;> simp [hp] <;> omega
  fits := by
    intro c hc
    obtain ⟨ms,hm,hc⟩ := List.mem_flatMap.mp hc
    exact ordered_cuts_fit w D Q ms (hD ms hm) (hw ms hm) c hc
  oddPositive := by intro _; omega
  gateSquare := by
    apply doubled_gateSquare hs
    simpa only [ordered_batch_length] using hg

theorem common_input_width (s w D Q : ℕ) (rows : List (List (List (Equation ((s+1)/2) (s/2)))))
    (hs : 67 ≤ s) (hg : (RowBinLift.batch Q rows).length^100≤2^s)
    (hD : ∀ ms∈rows, ∀ m∈ms, m.length≤D)
    (hw : ∀ ms∈rows, ∀ e∈ms.flatten, equationMagnitudeBound e<2^w) :
    (request (commonInput s w D Q rows hs hg hD hw)).p=w*(D*Q)+Q+1 := rfl

end NearCubicWires.RepairOrdinary.CloseoutRows
