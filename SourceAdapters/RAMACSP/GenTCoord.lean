import SourceAdapters.Joins.TermsCircuit

/-!
# The coordinate word of `Joins/CoordinateArray` is the coordinate part of `Joins/TermsCircuit`'s input

Paper: `lem:generator` and the coordinate description in
`app:affine-embedding`, "Selectors". The coordinate machine prints the reduced
coefficient masks in row order, for use in the emitted constraint circuit.-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Adapters

theorem coordWord_terms (p : Joins.TermsReq) (h : Joins.TermsOk p) (q : Joins.CoordReq) (hq : Joins.CoordOk q)
    (hf : q.f = p.f) (hm : q.m = p.l.m) (hirr : NearCubicWires.WireExponent3_5.GF.toPoly q.irr = p.irr) :
    Joins.coordWord q hq = Joins.termsCoordWord p h := by
  obtain ⟨f, P, l, items⟩ := p
  obtain ⟨f', I, m'⟩ := q
  simp only at hf hm hirr
  subst hf hm hirr
  rfl

end NearCubicGates.Adapters.RAMACSP.Gen
