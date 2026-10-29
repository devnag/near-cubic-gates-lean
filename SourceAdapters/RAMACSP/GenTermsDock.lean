import SourceAdapters.Joins.TermsCircuit

/-!
# Consumer dock of the join `TermsCircuit` (the generator's stage G5)

Paper: `lem:generator`. The ordinary term compiler prints exactly the
constraint circuit, with each field constant written as a reduced mask.-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP NearCubicWires
open NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.Joins
open Polynomial

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])

/-- The coordinate rows `λ_j` of the instance (as in `ownCircuit`). -/
def termsLam (r : Joins.ClockRequest) (h : ModulusGood V irrPoly r) :
    ℕ → Routing.Expr (Field2 (baseIrr V irrPoly r)) :=
  haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨h.1⟩
  let l := ownLayout V r.2
  let e : Fin l.m → Field2 (baseIrr V irrPoly r) := monoBasis (baseIrr V irrPoly r) l.m
  let hi : Routing.Independent l.m e := monoBasis_independent _ _ (by
    rw [h.2, ownLayout_m]; have := domExp_add_two_le_fieldExp V r.2; omega)
  let coords := Routing.explicitCoordinates e hi
  fun j => if hj : j < l.m then lamExpr (coords.coeff ⟨j, hj⟩) else .const 0

/-- The generator's request of the join at the clock request `r`. -/
def termsRequest (r : Joins.ClockRequest) (h : ModulusGood V irrPoly r) : Joins.TermsReq :=
  haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨h.1⟩
  ⟨fieldExp V r.2, baseIrr V irrPoly r, ownLayout V r.2, ownItems V r (termsLam V irrPoly r h)⟩

attribute [local irreducible] ownLayout baseIrr in
theorem termsRequest_ok (r : Joins.ClockRequest) (h : ModulusGood V irrPoly r) :
    Joins.TermsOk (termsRequest V irrPoly r h) := by
  have hl : (termsRequest V irrPoly r h).l = ownLayout V r.2 := rfl
  have hf : (termsRequest V irrPoly r h).f = fieldExp V r.2 := rfl
  have hi : (termsRequest V irrPoly r h).irr = baseIrr V irrPoly r := rfl
  have h2 := domExp_add_two_le_fieldExp V r.2
  have h1 : 1 ≤ domExp V r.2 := by unfold domExp; omega
  unfold Joins.TermsOk
  rw [hl, hf, hi, ownLayout_m]
  exact ⟨h.1, h.2, h1, h2⟩

attribute [local irreducible] ownLayout baseIrr in
/-- **The instance's constraint circuit is the join's serialized circuit.** -/
theorem ownConsOf_eq_terms (r : Joins.ClockRequest) (h : ModulusGood V irrPoly r) :
    ownConsOf V irrPoly r h = Joins.termsCircuit (termsRequest V irrPoly r h) (termsRequest_ok V irrPoly r h) := by
  rfl

end NearCubicGates.Adapters.RAMACSP.Gen
