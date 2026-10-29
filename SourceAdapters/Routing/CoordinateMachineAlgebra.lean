import SourceAdapters.Routing.CoordinatesFinite
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD

/-!
# Pointwise compact-array updates for coordinate generation

The compact coordinate construction for `lem:generator` retains
one annihilator array and one coordinate row. These lemmas expose the
existing `annihilatorCoefficients` and `coordinateCoefficients` recurrences
as zero-default list reads. Padding and reads beyond the new array are
included in the statements; no second recurrence is introduced.

-/

set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.CoordinateMachineAlgebra

open Coordinates
variable {F : Type*} [Field F]

theorem getD_ofFn {k : ℕ} (c : Fin k → F) (r : ℕ) :
    (List.ofFn c).getD r 0 = if h : r < k then c ⟨r, h⟩ else 0 := by
  by_cases h : r < k
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
    simp [h]

theorem getD_add {k : ℕ} (a b : Fin k → F) (r : ℕ) :
    (List.ofFn (coefficientAdd a b)).getD r 0 =
      (List.ofFn a).getD r 0 + (List.ofFn b).getD r 0 := by
  simp only [getD_ofFn, coefficientAdd]
  split_ifs <;> simp

theorem getD_scale {k : ℕ} (a : F) (c : Fin k → F) (r : ℕ) :
    (List.ofFn (coefficientScale a c)).getD r 0 = a * (List.ofFn c).getD r 0 := by
  simp only [getD_ofFn, coefficientScale]
  split_ifs <;> simp

theorem pad_list {k : ℕ} (c : Fin k → F) :
    List.ofFn (coefficientPad c) = List.ofFn c ++ [0] := by
  rw [List.ofFn_succ']
  simp [coefficientPad]

theorem getD_pad {k : ℕ} (c : Fin k → F) (r : ℕ) :
    (List.ofFn (coefficientPad c)).getD r 0 = (List.ofFn c).getD r 0 := by
  rw [pad_list]
  by_cases h : r < (List.ofFn c).length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h),
      List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    simp [List.getD_eq_getElem?_getD]

theorem squareShift_list {k : ℕ} (c : Fin k → F) :
    List.ofFn (coefficientSquareShift c) = 0 :: (List.ofFn c).map (fun x => x ^ 2) := by
  rw [List.ofFn_succ]
  simp only [coefficientSquareShift, Fin.cases_zero, Fin.cases_succ]
  exact congrArg (List.cons (0 : F)) (List.ofFn_comp' c (fun x : F => x ^ 2))

theorem getD_squareShift {k : ℕ} (c : Fin k → F) (r : ℕ) :
    (List.ofFn (coefficientSquareShift c)).getD r 0 =
      if r = 0 then 0 else ((List.ofFn c).getD (r - 1) 0) ^ 2 := by
  rw [squareShift_list]
  cases r with
  | zero => simp
  | succ r =>
    have hm := List.getD_map (List.ofFn c) (0 : F) (fun x : F => x ^ 2) (n := r)
    change (List.map (fun x : F => x ^ 2) (List.ofFn c)).getD r ((0 : F) ^ 2) =
      ((List.ofFn c).getD r 0) ^ 2 at hm
    rw [zero_pow (by decide : (2 : ℕ) ≠ 0)] at hm
    simpa only [List.getD_cons_succ, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false] using hm

theorem annihilator_base (e : ℕ → F) :
    List.ofFn (annihilatorCoefficients e 0) = [1] := by
  simp [annihilatorCoefficients]

theorem coordinate_base (e : ℕ → F) (j : ℕ) :
    List.ofFn (coordinateCoefficients e 0 j) = [] := by
  simp

theorem annihilator_length (e : ℕ → F) (n : ℕ) :
    (List.ofFn (annihilatorCoefficients e n)).length = n + 1 := List.length_ofFn

theorem coordinate_length (e : ℕ → F) (n j : ℕ) :
    (List.ofFn (coordinateCoefficients e n j)).length = n := List.length_ofFn

/-- The annihilator update, including both padding boundaries and all later reads. -/
theorem annihilator_step_getD (e : ℕ → F) (n r : ℕ) :
    (List.ofFn (annihilatorCoefficients e (n + 1))).getD r 0 =
      (if r = 0 then 0 else ((List.ofFn (annihilatorCoefficients e n)).getD (r - 1) 0)^2) +
      linearizedValue (annihilatorCoefficients e n) (e n) *
        (List.ofFn (annihilatorCoefficients e n)).getD r 0 := by
  rw [annihilatorCoefficients, getD_add, getD_squareShift, getD_scale, getD_pad]

/-- The single-row update, valid also before the selected row is introduced. -/
theorem coordinate_step_getD (e : ℕ → F) (n j r : ℕ) :
    (List.ofFn (coordinateCoefficients e (n + 1) j)).getD r 0 =
      if j = n then
        (linearizedValue (annihilatorCoefficients e n) (e n))⁻¹ *
          (List.ofFn (annihilatorCoefficients e n)).getD r 0
      else
        (List.ofFn (coordinateCoefficients e n j)).getD r 0 +
          linearizedValue (coordinateCoefficients e n j) (e n) *
            ((linearizedValue (annihilatorCoefficients e n) (e n))⁻¹ *
              (List.ofFn (annihilatorCoefficients e n)).getD r 0) := by
  rw [coordinateCoefficients]
  split_ifs
  · exact getD_scale _ _ _
  · rw [getD_add, getD_pad, getD_scale, unitCoefficients, getD_scale]

/-- The final row is the exact coefficient row used by the explicit coordinate supplier. -/
theorem final_row {m : ℕ} (e : Fin m → F) (j : Fin m) :
    List.ofFn (coordinateCoefficients (extendBasis e) m j.val) =
      List.ofFn (finiteCoefficients e j) := rfl

end NearCubicGates.Adapters.Routing.CoordinateMachineAlgebra
