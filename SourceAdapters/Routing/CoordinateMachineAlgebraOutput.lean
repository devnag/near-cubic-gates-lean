import SourceAdapters.Routing.CoordinateMachineAlgebraField
import Mathlib.Data.List.FinRange

/-!
# Exact reduced rows and their emitted bits

The construction in `lem:generator`: each completed compact row is emitted as its exact
sequence of f-bit reduced coefficient masks. The representation equality
and reducedness invariant identify every numeric entry with the
coordinate output; no alternate row or serialization is introduced.

-/

set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.CoordinateMachineAlgebra

open Coordinates
open NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.WireExponent3_5

/-- The represented completed row has precisely m entries. -/
theorem completed_row_length (p : CoordReq) (h : CoordOk p) (a : Fin p.m) (R : List ℕ)
    (hmap : letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
      R.map (GF.rep p.irr) =
        List.ofFn (coordinateCoefficients (extendBasis (monoBasis (GF.toPoly p.irr) p.m)) p.m a.val)) :
    R.length = p.m := by
  have hn := congrArg List.length hmap
  simpa only [List.length_map, List.length_ofFn] using hn

/-- Reduced representatives determine the exact requested natural masks entry by entry. -/
theorem completed_row_masks (p : CoordReq) (h : CoordOk p) (a : Fin p.m) (R : List ℕ)
    (hR : ∀ w ∈ R, w < 2 ^ p.f)
    (hmap : letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
      R.map (GF.rep p.irr) =
        List.ofFn (coordinateCoefficients (extendBasis (monoBasis (GF.toPoly p.irr) p.m)) p.m a.val)) :
    R = List.ofFn (fun r : Fin p.m => coordMask p h a r) := by
  letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
  have hlen := completed_row_length p h a R hmap
  rw [final_row] at hmap
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlen
  · intro i hi hj
    have him : i < p.m := by simpa only [List.length_ofFn] using hj
    simp only [List.getElem_ofFn]
    apply eq_coordMask p h a ⟨i, him⟩ R[i] (hR _ (List.getElem_mem hi))
    have hv := congrArg (fun xs => xs.getD i 0) hmap
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),
      List.getElem_map, getD_ofFn, dif_pos him] at hv
    exact hv

/-- The row emitter's raw bits are exactly the row-major block required by coordWord. -/
theorem completed_row_bits (p : CoordReq) (h : CoordOk p) (a : Fin p.m) (R : List ℕ)
    (hR : ∀ w ∈ R, w < 2 ^ p.f)
    (hmap : letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
      R.map (GF.rep p.irr) =
        List.ofFn (coordinateCoefficients (extendBasis (monoBasis (GF.toPoly p.irr) p.m)) p.m a.val)) :
    R.flatMap (WilliamsLoaderForms.fixedWidthNatBits p.f) =
      (List.finRange p.m).flatMap (fun r => WilliamsLoaderForms.fixedWidthNatBits p.f (coordMask p h a r)) := by
  rw [completed_row_masks p h a R hR hmap, List.ofFn_eq_map, List.flatMap_map]

end NearCubicGates.Adapters.Routing.CoordinateMachineAlgebra
