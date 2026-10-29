import SourceAdapters.Proximity.TrimHonestLayout

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": final actual restriction emits exactly the specified
prepared honest output, with no extra framing or omitted false bits. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

def finishCost {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ) (p : AcceptedSourceInput) : ℕ :=
  (trimSortedAddresses (clauseTrimRequest V p.1)).length +
    (6 * proofSize p.1 + 16 * (2 ^ (V p.1).randomBits * blockVariableBound q) + 38) *
      (trimSortedAddresses (clauseTrimRequest V p.1)).length + 6

theorem finish_run {q : ℕ} {C : Ctx} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (p : AcceptedSourceInput) (a : DS VV MM) (hc : Cst a)
    (ready : Ready C (V p.1) p.2.val (honest p) a)
    (hm : a.ram scheduleStore = trimSortedAddresses (clauseTrimRequest V p.1))
    (hlen : a.env scheduleLength = (trimSortedAddresses (clauseTrimRequest V p.1)).length)
    (hcursor : a.rc scheduleStore = (trimSortedAddresses (clauseTrimRequest V p.1)).length)
    (hout : a.out = [])
    (hvalues : ∀ x ∈ trimSortedAddresses (clauseTrimRequest V p.1), x < 2 ^ C.Wd)
    (hwidth : (trimSortedAddresses (clauseTrimRequest V p.1)).length < 2 ^ C.Wd) :
    Hs C outputProgram a (finishCost V proofSize p) (fun b => b.out = preparedHonestOutput V proofSize honest p) := by
  have run := output_program (V p.1) p.2.val (honest p) a hc ready
    (trimSortedAddresses (clauseTrimRequest V p.1)) hm hlen hvalues hwidth
  refine run.mono (by rw [hcursor, auxKeys_length]; exact le_rfl) ?_
  rintro b ⟨bo, _, _⟩
  rw [bo, hout, List.nil_append, prepared_output_map]

end NearCubicGates.Adapters.Proximity.TrimHonest
