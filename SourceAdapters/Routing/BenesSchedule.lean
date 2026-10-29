import SourceAdapters.Routing.BenesRecursive
import SourceAdapters.Joins.AffineRouting

/-! Exact first, middle, and final dimensions of the Beneš schedule. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.BenesRecursive

@[simp] theorem switchCount_step (k : ℕ) :
    switchCount (k + 2) = switchCount (k + 1) + 2 := by
  unfold switchCount
  omega

@[simp] theorem dimension_first (k : ℕ) : dimension k 0 = 0 := by
  simp [dimension]

@[simp] theorem dimension_last (k : ℕ) :
    dimension (k + 2) (switchCount (k + 1) + 1) = 0 := by
  unfold dimension switchCount
  omega

theorem dimension_inner (k j : ℕ) (hj : j < switchCount (k + 1)) :
    dimension (k + 2) (j + 1) = dimension (k + 1) j + 1 := by
  unfold dimension switchCount at *
  omega

theorem dimension_lt {k j : ℕ} (hk : 1 ≤ k) :
    dimension k j < k := by
  unfold dimension
  omega

/-- A dimension-zero stage is precisely one switch per higher-bit lane. -/
theorem split_pair_stage {k : ℕ} (s : Settings (k + 1)) (j : ℕ)
    (b : BitVec k → Bool) (hd : dimension (k + 1) j = 0)
    (hs : ∀ x, s j x = b (LanePair.split x).1) (x : BitVec (k + 1)) :
    LanePair.split (stageMap (k + 1) s j x) = pairSwitch b (LanePair.split x) := by
  unfold stageMap
  rw [hs, hd]
  change LanePair.split (if b (LanePair.split x).1 then
    x ^^^ BitVec.ofNat (k + 1) 1 else x) =
      ((LanePair.split x).1, Bool.xor (LanePair.split x).2 (b (LanePair.split x).1))
  cases b (LanePair.split x).1 <;>
    simp only [ Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_true]
  exact LanePair.split_flip_zero x

end NearCubicGates.Adapters.Routing.BenesRecursive
