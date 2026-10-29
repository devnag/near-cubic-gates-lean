import SourceAdapters.Routing.CoordinateMachineAlgebra
import SourceAdapters.Routing.CoordinateMachineInputBounds
import SourceAdapters.ShortPCP.Machines.FLangLag

/-!
# Nonzero pivots and exact reduced coordinate masks

The construction in `lem:generator`: the compact solver divides only by the
annihilator pivot of an independent basis and emits the reduced masks of
its exact coefficient rows. These identities connect the existing
recurrence and reduced-word arithmetic to `Joins.coordMask`.

-/

set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.CoordinateMachineAlgebra

open Coordinates Polynomial
open NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.RAMACSP
open NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicWires.WireExponent3_5

variable {F : Type} [Field F]

/-- The compact evaluator has the same nonzero pivot as the proved polynomial recurrence. -/
theorem pivot_ne_zero [CharP F 2] (e : ℕ → F) (m : ℕ)
    (hi : Function.Injective (cube e m)) (n : ℕ) (hn : n < m) :
    linearizedValue (annihilatorCoefficients e n) (e n) ≠ 0 := by
  rw [← linearizedPolynomial_eval, annihilatorCoefficients_correct]
  exact pivot_ne_zero_of_cube_injective e m hi n hn

theorem finite_pivot_ne_zero [CharP F 2] {m : ℕ} (e : Fin m → F)
    (hi : Independent m e) (n : ℕ) (hn : n < m) :
    linearizedValue (annihilatorCoefficients (extendBasis e) n) (e ⟨n, hn⟩) ≠ 0 := by
  have hc : Function.Injective (cube (extendBasis e) m) := by
    intro v w hvw
    apply hi
    simpa only [cube_extendBasis, cubeEval] using hvw
  simpa only [extendBasis, dif_pos hn] using pivot_ne_zero (extendBasis e) m hc n hn

/-- The exact monomial-basis pivot needed for each valid request. -/
theorem request_pivot_ne_zero (p : CoordReq) (h : CoordOk p) (n : ℕ) (hn : n < p.m) :
    letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
    linearizedValue
      (annihilatorCoefficients (extendBasis (monoBasis (GF.toPoly p.irr) p.m)) n)
      (GF.rep p.irr (2 ^ n)) ≠ 0 := by
  letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
  have hm : p.m ≤ (GF.toPoly p.irr).natDegree := by
    rw [h.2.1]
    have := h.2.2.2
    omega
  simpa only [monoBasis, GF.rep_two_pow, GF.xRoot] using
    finite_pivot_ne_zero (monoBasis (GF.toPoly p.irr) p.m)
      (monoBasis_independent _ p.m hm) n hn

/-- A nonzero represented field value forces its input word to be nonzero. -/
theorem word_ne_zero_of_rep {p a : ℕ} (ha : GF.rep p a ≠ 0) : a ≠ 0 := by
  intro hz
  apply ha
  rw [hz, GF.rep_zero]

/-- Specialize the checked inverse-word operation to the actual quotient field. -/
theorem request_inverse (p : CoordReq) (h : CoordOk p) (a : ℕ)
    (ha : a < 2 ^ p.f) (ha0 : GF.rep p.irr a ≠ 0) :
    letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
    GF.rep p.irr (powW p.irr p.f a (2 ^ p.f - 2)) = (GF.rep p.irr a)⁻¹ := by
  letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
  have hf : 1 ≤ p.f := by have := h.2.2; omega
  simpa only [ev, RingHom.id_apply] using
    ev_inv (RingHom.id (AdjoinRoot (GF.toPoly p.irr))) p.f a
      (CoordinateMachine.coordOk_modulusOk p h) hf h.1 ha (word_ne_zero_of_rep ha0)

/-- Reducing a canonical quotient representative to f bits preserves its field value. -/
theorem rep_ofPoly_representative (p f : ℕ) (hm : (GF.toPoly p).Monic)
    (hf : (GF.toPoly p).natDegree = f) (x : AdjoinRoot (GF.toPoly p)) :
    GF.rep p (GF.ofPoly (AdjoinRoot.modByMonicHom hm x) f) = x := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  unfold GF.rep
  rw [AdjoinRoot.modByMonicHom_mk, GF.toPoly_ofPoly]
  · have hx := AdjoinRoot.mk_leftInverse hm (AdjoinRoot.mk (GF.toPoly p) q)
    rwa [AdjoinRoot.modByMonicHom_mk] at hx
  · have hd := Polynomial.degree_modByMonic_lt q hm
    rwa [Polynomial.degree_eq_natDegree hm.ne_zero, hf] at hd

theorem coordMask_lt (p : CoordReq) (h : CoordOk p) (a r : Fin p.m) :
    coordMask p h a r < 2 ^ p.f := GF.ofPoly_lt _ _

/-- The requested serialized mask represents precisely the final compact coefficient. -/
theorem coordMask_rep (p : CoordReq) (h : CoordOk p) (a r : Fin p.m) :
    letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
    GF.rep p.irr (coordMask p h a r) =
      finiteCoefficients (monoBasis (GF.toPoly p.irr) p.m) a r := by
  letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
  exact rep_ofPoly_representative p.irr p.f (modulus_monic h.1) h.2.1 _

/-- Equality of represented coefficients identifies the exact output mask, not just its class. -/
theorem eq_coordMask (p : CoordReq) (h : CoordOk p) (a r : Fin p.m) (w : ℕ)
    (hw : w < 2 ^ p.f)
    (hrep : letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
      GF.rep p.irr w = finiteCoefficients (monoBasis (GF.toPoly p.irr) p.m) a r) :
    w = coordMask p h a r := by
  apply GF.rep_injOn p.irr p.f w (coordMask p h a r)
    (CoordinateMachine.coordOk_modulusOk p h) hw (coordMask_lt p h a r)
  exact hrep.trans (coordMask_rep p h a r).symm

end NearCubicGates.Adapters.Routing.CoordinateMachineAlgebra
