import SourceAdapters.Joins.CoordinateArray

/-!
# Consumer dock of the join `CoordinateArray` (the generator's stage G5)

Paper: `lem:generator` computes the coordinate coefficient array with
O(mH³) field operations. The coordinate-machine request uses
`f = fieldExp V t`, `irr = modMask (irrPoly f) f` and `m = domExp V t`.
`request_ok` proves `CoordOk` from the irreducible choice and
`1 ≤ mH`, `mH + 2 ≤ f`; `coordWF` specializes the word function to clock requests.

-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicWires NearCubicWires.RepairOrdinary
open Polynomial

/-- The generator's coordinate request at the clock request `r`. -/
def coordRequest (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (r : Joins.ClockRequest) : Joins.CoordReq :=
  ⟨fieldExp V r.2, modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2), domExp V r.2⟩

/-- The modulus of the coordinate request is the instance's (`baseIrr`), when `irrPoly f` has degree `f`. -/
theorem coordRequest_toPoly (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (r : Joins.ClockRequest)
    (hd : (irrPoly (fieldExp V r.2)).natDegree = fieldExp V r.2) :
    WireExponent3_5.GF.toPoly (coordRequest V irrPoly r).irr = irrPoly (fieldExp V r.2) := by
  have he : WireExponent3_5.GF.toPoly (modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2)) =
      irrPoly (fieldExp V r.2) := by
    unfold modMask
    apply WireExponent3_5.GF.toPoly_ofPoly
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by rw [hd]; exact_mod_cast Nat.lt_succ_self _)
  simp only [coordRequest]
  exact he

/-- `CoordOk` at the generator's requests (`request_ok`). -/
theorem coordRequest_ok (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])
    (hI : NearCubicGates.Published.Shoup.IrreducibleChoice irrPoly) (r : Joins.ClockRequest) :
    Joins.CoordOk (coordRequest V irrPoly r) := by
  have hf := domExp_add_two_le_fieldExp V r.2
  obtain ⟨hi, hd⟩ := hI (fieldExp V r.2) (by omega)
  have hm : 1 ≤ domExp V r.2 := by unfold domExp laneExp; omega
  refine ⟨?_, ?_, hm, hf⟩
  · rw [coordRequest_toPoly V irrPoly r hd]; exact hi
  · rw [coordRequest_toPoly V irrPoly r hd]; exact hd

/-- The valid request. -/
def coordValid (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])
    (hI : NearCubicGates.Published.Shoup.IrreducibleChoice irrPoly) (r : Joins.ClockRequest) :
    {p : Joins.CoordReq // Joins.CoordOk p} := ⟨coordRequest V irrPoly r, coordRequest_ok V irrPoly hI r⟩

/-- **The dock** (`consumer`): from `CoordArrayWF`, the coordinate machine on the generator's requests. -/
theorem coordWF (h : Joins.CoordArrayWF) (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])
    (hI : NearCubicGates.Published.Shoup.IrreducibleChoice irrPoly) :
    ∃ K e : ℕ, Nonempty (WordFunction Joins.ClockRequest
      (fun r => Joins.coordInput (coordRequest V irrPoly r))
      (fun r => Joins.coordWord (coordRequest V irrPoly r) (coordRequest_ok V irrPoly hI r))
      (fun r => K * ((Joins.coordInput (coordRequest V irrPoly r)).length + 1) ^ e)) := by
  obtain ⟨K, e, ⟨W⟩⟩ := h
  exact ⟨K, e, ⟨⟨W.program, fun r => W.realizes (coordValid V irrPoly hI r)⟩⟩⟩

end NearCubicGates.Adapters.RAMACSP.Gen
