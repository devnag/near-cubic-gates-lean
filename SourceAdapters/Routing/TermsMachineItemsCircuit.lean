import SourceAdapters.Routing.TermsMachineItemsRequest
import SourceAdapters.Routing.TermsMachinePrefixRequest

/-! # Exact concatenation of the numeric prefix and ordered item suffix -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Items

open Joins ACSP RAMACSP Circuit Circuit.PrefixFormula

/-- The actual requested code-gate list, with no omitted or merged item gates. -/
theorem request_gates (p : TermsReq) (h : TermsOk p) :
    letI : Fact (Irreducible p.irr) := ⟨h.1⟩
    termsCircuit p h = Prefix.gates p.l.m 0 (coordMasks p h) ++ [CodeGate.const 0] ++
      (itemsGates p.l (rowIds p.l.m p.l.m p.l.m) p.items
        (3 * p.l.m ^ 2 + 2 * p.l.m) (3 * p.l.m ^ 2 + 2 * p.l.m + 1)).map
          (codeGate (termsMask p h)) := by
  letI : Fact (Irreducible p.irr) := ⟨h.1⟩
  have hm : codeGate (termsMask p h) = gateMask p.irr (modulus_monic h.1) p.f :=
    funext (codeGate_termsMask p h)
  unfold termsCircuit
  rw [← hm, compileTerms_codes, prefixRequest_gates, termsMask_zero]

end NearCubicGates.Adapters.Routing.TermsMachine.Items
