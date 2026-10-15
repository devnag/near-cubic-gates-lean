import Proof.Supplier.RowCachedCoordinateReusable

/-! Uniform scratch capacities for the actual cached-coordinate call. Bounds
come from its native source bytes, so every selected child uses one bank. -/
namespace NearCubicWires.RepairOrdinary.RowCachedCoordinateBounds
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def size {n : ℕ} (gs : List (ExactThresholdGate n)) (w : ℕ) :=
  (exactListWord gs).length+(n+1)*(gs.length+1)+w+1
def inner (w : ℕ) := 32*(w+1)
def outer {n : ℕ} (gs : List (ExactThresholdGate n)) (w : ℕ) := 256*size gs w
def width {n : ℕ} (gs : List (ExactThresholdGate n)) := (exactListWord gs).length+1

theorem child_bytes {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length) :
    (exactWord gs[i]).length≤(exactListWord gs).length := by
  have h := congrArg List.length (DecompositionCachedChild.selected_word gs i hi)
  simp only [List.length_append] at h
  omega

theorem coordinate_bytes {n : ℕ} (g : ExactThresholdGate n) (j : ℕ) (hj : j≤n) :
    (RowNativeCoordinate.prior g j).length≤(exactWord g).length ∧
    natBitLength (RowNativeCoordinate.value g j hj).natAbs≤(exactWord g).length := by
  have h := congrArg List.length (RowNativeCoordinate.selected_word g j hj)
  simp only [List.length_append,DecompositionSource.intWord_length,intBitLength,natBitLength] at h ⊢
  constructor <;> omega

theorem value_width {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) : natBitLength (RowCachedCoordinateAppend.value gs i hi j hj).natAbs≤width gs := by
  exact ((coordinate_bytes gs[i] j hj).2.trans (child_bytes gs i hi)).trans (Nat.le_succ _)

theorem inner_fits (z : ℤ) (w : ℕ) (hw : natBitLength z.natAbs≤w) :
    RowPowerNativeReset.rawTime z w+1 ≤ inner w := by
  unfold RowPowerNativeReset.rawTime inner
  omega

theorem field_budget (z : ℤ) (w : ℕ) (hw : natBitLength z.natAbs≤w) :
    RowPowerNativeReusable.budget z w (inner w)≤112*(w+1) := by
  unfold RowPowerNativeReusable.budget inner
  omega

theorem raw_budget {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (w : ℕ)
    (hw : natBitLength (RowCachedCoordinateAppend.value gs i hi j hj).natAbs≤w) :
    RowCachedCoordinateAppend.budget gs i hi j hj w (inner w)≤128*size gs w := by
  have hposition := DecompositionCachedChild.budget_bound gs i hi.le
  have hprior := (coordinate_bytes gs[i] j hj).1.trans (child_bytes gs i hi)
  have hfield := field_budget (RowCachedCoordinateAppend.value gs i hi j hj) w hw
  unfold RowCachedCoordinateAppend.budget RowNativeCoordinateAppend.budget RowNativeCoordinate.budget
  change RowPowerNativeReusable.budget (RowNativeCoordinate.value gs[i] j hj) w (inner w)≤112*(w+1) at hfield
  unfold size
  nlinarith

theorem outer_fits {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (w : ℕ)
    (hw : natBitLength (RowCachedCoordinateAppend.value gs i hi j hj).natAbs≤w) :
    RowCachedCoordinateAppend.budget gs i hi j hj w (inner w)+1≤outer gs w := by
  have h := raw_budget gs i hi j hj w hw
  have hs : 1 ≤ size gs w := by unfold size; omega
  unfold outer
  omega

theorem reusable_budget {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (w : ℕ)
    (hw : natBitLength (RowCachedCoordinateAppend.value gs i hi j hj).natAbs≤w) :
    RowCachedCoordinateReusable.budget gs i hi j hj w (inner w) (outer gs w)≤1024*size gs w := by
  have h := raw_budget gs i hi j hj w hw
  have hs : 1 ≤ size gs w := by unfold size; omega
  unfold RowCachedCoordinateReusable.budget outer
  omega

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (positive negative : List Bool) :
    let w := width gs
    let P := positive++Streaming.marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) false)
    let N := negative++Streaming.marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) true)
    ∃ r,runFrom RowCachedCoordinateReusable.machine
      (RowCachedCoordinateReusable.budget gs i hi j hj w (inner w) (outer gs w))
      (RowCachedCoordinateReusable.entry gs i j w (inner w) (outer gs w) positive negative)=some r ∧
      r.final.heads=(RowCachedCoordinateReusable.entry gs i j w (inner w) (outer gs w) P N).heads ∧
      r.final.tapes=(RowCachedCoordinateReusable.entry gs i j w (inner w) (outer gs w) P N).tapes ∧
      r.steps≤1024*size gs w := by
  dsimp only
  have hw := value_width gs i hi j hj
  obtain ⟨r,hr,rh,rt,rs⟩ := RowCachedCoordinateReusable.reusable_run gs i hi j hj positive negative
    (width gs) (inner (width gs)) (outer gs (width gs))
    (inner_fits _ _ hw) (outer_fits gs i hi j hj _ hw)
  exact ⟨r,hr,rh,rt,rs.le.trans (reusable_budget gs i hi j hj _ hw)⟩

end NearCubicWires.RepairOrdinary.RowCachedCoordinateBounds
