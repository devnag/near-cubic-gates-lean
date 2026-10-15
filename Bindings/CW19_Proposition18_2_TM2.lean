import Bindings.TuringBridge.Budget
import Bindings.CW19_Proposition18_2
import StatementSupport

/-!
# Tier 2 binding: CW19 Proposition 18(2), the construction in Mathlib's standard model

Source PDF: `CW19_Chen_Williams_Stronger_Connections_via_PCPP.pdf`, PDF page 14
(printed 19:14), §2.1, verbatim (re-extracted for this module):

  "I Proposition 18. The following hold: … 2. THR ⊆ DOR ◦ ETHR [24]. (also see Appendix B) …
  Moreover, all the above have corresponding polynomial-time, deterministic constructions."

## What changes against the Tier 1 literal (`Bindings/CW19_Proposition18_2.lean`)

ONLY the algorithmic clause "polynomial-time, deterministic constructions". Tier 1 states it as
`PolynomialTimeConstruction dor`, one repo `OrdinaryWordFunction` within `C · (|gateWord G| + 1)^d`
steps. Here it is a Mathlib `Turing.TM2ComputableInPolyTime` machine (a finite, hence
deterministic, multi-stack Turing machine, `Mathlib/Computability/TuringMachine/Computable.lean`)
computing `G ↦ dor G` with
* input encoding `gateWord` (`n`, then `w_1, …, w_n`, then `T`), the SAME word as Tier 1;
* output encoding the identity on `List Bool`, applied to `circuitWord (dor G)` (`m`, then each
  ETHR gate), the SAME word as Tier 1;
* polynomial time in Mathlib's sense: a polynomial in the input length `|gateWord G|`, which is
  the Tier 1 reading "polynomial in the length of the gate's description".
The construction `dor` and the correctness clause `(dor n G).Computes G` are copied verbatim.

`tier1_of_tier2 : CW19_Proposition18_2_TM2 → CW19_Proposition18_2` is proved through
`tm2Poly_ordinary` (`Bindings/TuringBridge/Budget.lean`), and composed with the Tier 1 adapter it gives
`cw19_tm2_to_import : CW19_Proposition18_2_TM2 → DecompositionSource`.
-/

namespace NearCubicWires.Bindings.CW19TM2

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairSource
open NearCubicWires.Bindings.CW19 NearCubicWires.Bindings.Sim

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-- The Tier 1 algorithmic clause from the Tier 2 one. -/
theorem PolynomialTimeConstructionTM2.toTier1 {dor : (n : ℕ) → THRGate n → DORofETHR n}
    (h : PolynomialTimeConstructionTM2 dor) : Nonempty (PolynomialTimeConstruction dor) := by
  obtain ⟨H⟩ := h
  obtain ⟨K, e, ⟨W⟩⟩ := tm2Poly_ordinary H (fun G => (gateWord G.2).length) 1 1
    (fun G => by simp)
  exact ⟨⟨K, e, W⟩⟩

/-- **Tier 2 → Tier 1.** -/
theorem tier1_of_tier2 : CW19_Proposition18_2_TM2 → CW19_Proposition18_2 := by
  rintro ⟨dor, hcomp, h⟩
  exact ⟨dor, hcomp, h.toTier1⟩

/-- **Tier 2 → import**, through the Tier 1 adapter (`Bindings/CW19_Proposition18_2.lean`). -/
theorem cw19_tm2_to_import : CW19_Proposition18_2_TM2 → DecompositionSource :=
  fun h => cw19_to_import (tier1_of_tier2 h)

end NearCubicWires.Bindings.CW19TM2
