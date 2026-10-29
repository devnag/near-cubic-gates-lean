import SourceAdapters.Proximity.AddressDock
import SourceAdapters.Proximity.TrimFinal

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": both ordinary trimming outputs specialized to the
Appendix A verifier, using the proved shared supplier without a join premise. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

theorem trimming_algorithms {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :
    SourcePolyTime (fun C => trimRequestWord (clauseTrimRequest V C))
      (fun C => (trimVerifier (clauseVerifier (V C))).word) ∧
    SourcePolyTime (fun C => trimRequestWord (clauseTrimRequest V C))
      (fun C => trimAddressWord (clauseTrimRequest V C)) := by
  obtain ⟨K, e, _, hv, ha⟩ := trimming_ordinary_dock Trim.trimVerifier_join V
  exact ⟨⟨K, e, hv⟩, ⟨K, e, ha⟩⟩

end NearCubicGates.Adapters.Proximity
