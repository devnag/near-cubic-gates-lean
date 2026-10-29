import NineInputs
import Mathlib.Algebra.Field.ZMod

/-!
# Vacuity checks for the BCGT13 leaves

- `tuple_valid`: the explicit tuple `(η, κ0, γ, μ) = (2, 4, 0, 1)` satisfies every condition of Eq. (6) of
  Theorem 11.1 (the paper's proof of `thm:short-pcp-ours` uses "fixed constants of that theorem"; this is an
  explicit valid tuple).
- `tuple_positive_exponents`: the same tuple has `e1 > 0 ∧ e2 > 0`, meeting the soundness constant's domain.
- `tuple_valid_6`: a second valid tuple with a smaller exponent (`log₂ c ≈ 22.2`).
- `not_valid_eta_one`: Eq. (6) is not vacuous: `η = 1` violates it.
- `basis_zmod2`: the hypotheses `IsBasis B O` of `BCGT13_Theorem11_1` are satisfiable (`F = ZMod 2`, `B = [1]`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Vacuity.BCGT13

open NearCubicGates.Published.BCGT13

/-- The tuple used throughout input 6. -/
def tuple : Tuple := ⟨2, 4, 0, 1⟩

theorem tuple_valid : tuple.Valid := by
  show Equation6 2 4 0 1; decide

/-- The tuple used throughout input 6 meets the additional domain hypothesis. -/
theorem tuple_positive_exponents : tuple.PositiveExponents := by
  have hthree : sThree 4 = 2 := by decide
  have hone : sOne 4 = 1 := by decide
  have hfloor : floorHalf 6 = 3 := by decide
  have hceil : ceilHalf 5 = 3 := by decide
  have h1 : 0 < Real.logb 2 (6 / 5 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  have h2 : 0 < Real.logb 2 (5 / 3 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  convert And.intro h1 h2 using 1
  norm_num [Tuple.PositiveExponents, tuple, hthree, hone, hfloor, hceil]

theorem tuple_valid_6 : (⟨2, 6, 0, 1⟩ : Tuple).Valid := by
  show Equation6 2 6 0 1; decide

theorem not_valid_eta_one : ¬ (⟨1, 4, 0, 0⟩ : Tuple).Valid := by
  show ¬ Equation6 1 4 0 0; decide

theorem basis_zmod2 : IsBasis ([1] : List (ZMod 2)) 0 := by
  unfold IsBasis; decide

end NearCubicGates.Adapters.Vacuity.BCGT13
