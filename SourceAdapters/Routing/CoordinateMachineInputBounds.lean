import SourceAdapters.Joins.CoordinateArray
import SourceAdapters.ShortPCP.Machines.FLang

/-!
# The coordinate request's actual modulus mask

The construction in `lem:generator`: the irreducible modulus has degree f. Its mask
therefore has exactly the leading bit and range required by the ordinary
field-word operations. No second modulus-validity premise is used.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicWires.WireExponent3_5
open NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters.ShortPCP.Machines.FL

theorem coordOk_modulusOk (p : CoordReq) (h : CoordOk p) : GF.ModulusOk p.irr p.f := by
  constructor
  · have hn : (GF.toPoly p.irr).coeff (GF.toPoly p.irr).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr h.1.ne_zero
    rw [h.2.1, GF.coeff_toPoly] at hn
    cases hb : p.irr.testBit p.f
    · simp [GF.bitF, hb] at hn
    · rfl
  · apply Nat.lt_pow_two_of_testBit
    intro i hi
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt
      (p := GF.toPoly p.irr) (show (GF.toPoly p.irr).natDegree < i by rw [h.2.1]; omega)
    rw [GF.coeff_toPoly] at hz
    cases hb : p.irr.testBit i
    · rfl
    · simp [GF.bitF, hb] at hz

theorem coordOk_mask_bounds (p : CoordReq) (h : CoordOk p) :
    2 ^ p.f ≤ p.irr ∧ p.irr < 2 * 2 ^ p.f := by
  have hm := coordOk_modulusOk p h
  exact ⟨Nat.ge_two_pow_of_testBit hm.1, by simpa [pow_succ, Nat.mul_comm] using hm.2⟩

theorem coordOk_fieldOk (G : Glob) (p : CoordReq) (h : CoordOk p) (hK : p.f + 2 ≤ G.K) :
    fieldOk G p.f p.irr = true := by
  have hb := coordOk_mask_bounds p h
  simp only [fieldOk, decide_eq_true_eq]
  exact ⟨by have := h.2.2; omega, hK, hb⟩

end NearCubicGates.Adapters.Routing.CoordinateMachine
