import SourceAdapters.Routing.TermsMachineMatrix
import SourceAdapters.Routing.TermsMachinePrefix
import SourceAdapters.Routing.TermsMachineBoundsRequest

/-! The construction in `lem:generator`: the exact coordinate prefix at the actual request allocation. -/
set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.TermsMachine

open Joins ACSP RAMACSP ShortPCP.Machines.FL CoordinateMachine

theorem prepared_prefix_bounds (p : TermsReq) (h : TermsOk p) :
    Prefix.Bounds (globOf (preparedInput (termsInput p h))) p.f p.l.m 0 := by
  let G := globOf (preparedInput (termsInput p h))
  let M := Bounds.arithmeticBound (termsInput p h).length
  have hn := Bounds.prepared_numeric_bounds p h
  have ha := Bounds.request_arithmetic p h
  have hs := Bounds.request_size p h
  have hk := Bounds.prepared_large (termsInput p h)
  have hm : p.l.m ≤ G.N := by
    have hr := Bounds.raw_le_arithmetic (termsInput p h).length
    dsimp [G] at *
    omega
  have hcount : 0 + 3 * p.l.m * p.l.m + 2 * p.l.m ≤ M := by
    have hh := ha.2.2.2.2.2.2.2.1
    dsimp [M]
    nlinarith
  refine ⟨by have := h.2.2.2; omega, h.2.2.1, hm, hn.2.2.2,
    ?_, ?_, hcount.trans hn.1, ?_⟩
  · exact ha.2.2.2.1.trans hn.1
  · exact hn.2.2.1 _ (Nat.le_max_right _ _)
  · apply hn.2.1
    exact max_le_max hcount le_rfl

/-- The prefix printer's actual input pack and capacities come from the request. -/
theorem prefixRequest_spec (p : TermsReq) (h : TermsOk p) (s : FS)
    (h20 : s.env 20 = p.f) (h21 : s.env 21 = p.l.m)
    (h22 : s.env 22 = NearCubicWires.CanonicalBinary.bitsValue (termsCoordWord p h))
    (h24 : s.env 24 = 0) :
    let G := globOf (preparedInput (termsInput p h))
    Appends Prefix.writes s (evalS G Prefix.program s)
      (Prefix.words (s.env 31) (Prefix.gates p.l.m 0 (coordMasks p h))) ∧
      (evalS G Prefix.program s).env 24 = 3 * p.l.m * p.l.m + 2 * p.l.m := by
  have hh := Prefix.program_spec (globOf (preparedInput (termsInput p h))) s p.f p.l.m
    (coordMasks p h) (by simpa only [h24] using prepared_prefix_bounds p h)
    (coordMasks_lt p h) h20 h21 (h22.trans (packed_coordinates p h))
  simpa only [h24, Nat.zero_add] using And.intro hh.1 hh.2.1

/-- The numerical prefix is the mapped literal field-circuit prefix. -/
theorem prefixRequest_gates (p : TermsReq) (h : TermsOk p) :
    letI : Fact (Irreducible p.irr) := ⟨h.1⟩
    (Circuit.PrefixFormula.prefixGates p.l
      (explicitCoordinates (monoBasis p.irr p.l.m) (termsIndependent p h)) 0).map
        (codeGate (termsMask p h)) = Prefix.gates p.l.m 0 (coordMasks p h) := by
  letI : Fact (Irreducible p.irr) := ⟨h.1⟩
  exact Prefix.gates_code p.l _ (termsMask p h) (termsMask_zero p h) 0
    (coordMasks p h) (coordMasks_get p h)

end NearCubicGates.Adapters.Routing.TermsMachine
