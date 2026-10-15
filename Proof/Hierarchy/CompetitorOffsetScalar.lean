import Proof.Supplier.RowExternalSelectionInput
import Proof.Hierarchy.CompetitorRecordScalarBounds

/-! Residual-offset counts feed the exact scalar format. All offsets are
summed once, in the actual scan order; neither offset cardinality nor child
cardinality divides the original normalization denominator. -/
namespace NearCubicWires.RepairOrdinary.CompetitorOffsetScalar
open LocalBitMultitape MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
open CompetitorMonomialStream CompetitorRationalDecision CompetitorMonomialProducts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def entry {u : ℕ} (odd : Bool) (f : Fin u → Fin u → ℕ)
    (select : Fin u → Fin u → Bool) (q : ℚ) (denominator : ℕ) : Entry :=
  ⟨q,(selected (CompetitorSelectedCells.cells odd f select)).sum,denominator⟩
def entries {α : Type} [DecidableEq α] {u : ℕ} (order : List α) (odd : Bool)
    (offset : Fin u → Fin u → α) (f : α → Fin u → Fin u → ℕ) (q : ℚ) (denominator : ℕ) :=
  order.map (fun wanted => entry odd (f wanted) (RowExternalSelection.select offset wanted) q denominator)

theorem entry_valid (r : Request) (Q : ℕ) (odd : Bool)
    (f : Fin r.U → Fin r.U → ℕ) (select : Fin r.U → Fin r.U → Bool)
    (q : ℚ) (denominator : ℕ) (hf : ∀ i j,f i j<2^Q)
    (hp : positive q<2^(scalarWidth r Q)) (hn : negative q<2^(scalarWidth r Q))
    (hq : q.den<2^(scalarWidth r Q)) (hd : denominator<2^(scalarWidth r Q)) (hpos : 0<denominator) :
    (entry odd f select q denominator).Valid (scalarWidth r Q) := by
  refine ⟨hp,hn,hq,?_,hd,hpos⟩
  exact scalar_fit r Q _ (CompetitorSelectedCells.cells_length odd f select)
    (CompetitorSelectedCells.cells_fit Q odd f select hf)

theorem estimate_sum {α : Type} [Fintype α] [DecidableEq α] {u : ℕ}
    (order : List α) (horder : order.Perm (Finset.univ.toList)) (odd : Bool)
    (offset : Fin u → Fin u → α) (f : α → Fin u → Fin u → ℕ) (q : ℚ) (denominator : ℕ) :
    ((contributions (entries order odd offset f q denominator)).map CompetitorValidity.Estimate.value).sum=
      q*((RowExternalSelection.total odd (fun i j => f (offset i j) i j) : ℚ)/denominator) := by
  simp only [contributions,entries,List.map_map,Function.comp_def,Entry.estimate_value,entry]
  rw [(horder.map (fun wanted => q*((((selected (CompetitorSelectedCells.cells odd (f wanted)
    (RowExternalSelection.select offset wanted))).sum : ℕ) : ℚ)/denominator))).sum_eq]
  rw [Finset.sum_map_toList,←Finset.mul_sum,←Finset.sum_div,←Nat.cast_sum,RowExternalSelection.offset_sum]

theorem scalar_run {α : Type} [Fintype α] [DecidableEq α]
    (r : Request) (Q l : ℕ) (order : List α) (horder : order.Perm (Finset.univ.toList)) (odd : Bool)
    (offset : Fin r.U → Fin r.U → α) (f : α → Fin r.U → Fin r.U → ℕ)
    (q threshold : ℚ) (denominator : ℕ)
    (hf : ∀ wanted i j,f wanted i j<2^Q)
    (hp : positive q<2^(scalarWidth r Q)) (hn : negative q<2^(scalarWidth r Q))
    (hq : q.den<2^(scalarWidth r Q)) (hd : denominator<2^(scalarWidth r Q)) (hpos : 0<denominator)
    (ht : 0≤threshold) (htp : CompetitorThresholdDecision.numerator threshold<2^l)
    (htd : threshold.den<2^l) :
    ∃ actual,run (CompetitorRecordScalar.machine true l threshold)
      (CompetitorRecordScalar.budget (scalarWidth r Q) l order.length)
      (CompetitorRecordScalar.input (scalarWidth r Q) (entries order odd offset f q denominator))=some actual ∧
      actual.steps≤3536000*(order.length+1)^3*(scalarWidth r Q+l+1)^2 ∧
      actual.final.heads 205=0 ∧
      (readTapeBit (actual.final.tapes 205) 0=true ↔
        threshold≤q*((RowExternalSelection.total odd (fun i j => f (offset i j) i j) : ℚ)/denominator)) := by
  have hv : ∀ a∈entries order odd offset f q denominator,a.Valid (scalarWidth r Q) := by
    intro a ha
    obtain ⟨wanted,_,rfl⟩ := List.mem_map.mp ha
    exact entry_valid r Q odd (f wanted) _ q denominator (hf wanted) hp hn hq hd hpos
  obtain ⟨actual,ha,hs,hh,hflag⟩ := CompetitorRecordScalar.runtime_run true l threshold (scalarWidth r Q)
    (entries order odd offset f q denominator) hv ht htp htd
  have hlen : (entries order odd offset f q denominator).length=order.length := List.length_map _
  rw [hlen] at ha hs
  have hvsum := estimate_sum order horder odd offset f q denominator
  change (readTapeBit (actual.final.tapes 205) 0=true ↔
    threshold≤((contributions (entries order odd offset f q denominator)).map CompetitorValidity.Estimate.value).sum) at hflag
  rw [hvsum] at hflag
  exact ⟨actual,ha,hs.trans (CompetitorRecordScalar.polynomial_bound (scalarWidth r Q) l order.length),hh,hflag⟩

end NearCubicWires.RepairOrdinary.CompetitorOffsetScalar
