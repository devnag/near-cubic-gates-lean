import SourceAdapters.Joins.TrimVerifier
import SourceAdapters.Proximity.TrimOrder
import SourceAdapters.Proximity.ClauseQueries

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": consumer specialization of both ordinary trimming
outputs to the exact Appendix A verifier. This remains conditional on the
shared trimming interface until its supplier is proved. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

def clauseTrimRequest {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (C : SourceCircuit) : TrimRequest := ⟨C.arity, clauseVerifier (V C)⟩

theorem trimming_ordinary_dock (hTrim : TrimVerifier) {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :
    ∃ K e : ℕ, 1 ≤ K ∧
      Nonempty (WordFunction SourceCircuit (fun C => trimRequestWord (clauseTrimRequest V C))
        (fun C => (trimVerifier (clauseVerifier (V C))).word)
        (fun C => K * ((trimRequestWord (clauseTrimRequest V C)).length + 1) ^ e)) ∧
      Nonempty (WordFunction SourceCircuit (fun C => trimRequestWord (clauseTrimRequest V C))
        (fun C => trimAddressWord (clauseTrimRequest V C))
        (fun C => K * ((trimRequestWord (clauseTrimRequest V C)).length + 1) ^ e)) := by
  obtain ⟨K, e, hK, ⟨verifier⟩, ⟨addresses⟩⟩ := hTrim
  exact ⟨K, e, hK, ⟨⟨verifier.program, fun C => verifier.realizes (clauseTrimRequest V C)⟩⟩,
    ⟨⟨addresses.program, fun C => addresses.realizes (clauseTrimRequest V C)⟩⟩⟩

theorem sorted_address_restriction {n : ℕ} (V : ThreeQueryVerifier n) (proof : ℕ → Bool) :
    (trimSortedAddresses ⟨n, V⟩).map proof = List.ofFn (restrictProof V proof) := by
  rw [trimSortedAddresses, Trim.sortedAddresses_eq_ofFn, List.map_ofFn]
  rfl

end NearCubicGates.Adapters.Proximity
