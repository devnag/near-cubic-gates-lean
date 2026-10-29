import SourceAdapters.Joins.HonestRestriction

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": exact consumer of the paid source honest restriction
interface, with target accepted-input conversion kept as an explicit adapter. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicGates.Published.CW19Proximity
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Adapters.Joins

theorem honest_restriction_dock (h : HonestRestriction) {q : ℕ}
    (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (hP : SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest)) :
    SourcePolyTime (fun p => preparedHonestInput V (sourceAcceptedInput p))
      (fun p => List.ofFn (convertedHonest V proofLength honest p)) := by
  obtain ⟨K, e, ⟨P⟩⟩ := h q V proofLength honest a hr hP
  exact ⟨K, e, ⟨{ program := P.program, realizes := fun p => P.realizes (sourceAcceptedInput p) }⟩⟩

theorem honest_preparation_dock (h : HonestRestriction) {q : ℕ}
    (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (hP : SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest))
    (hprepare : SourcePolyTime acceptedCircuitInputWord
      (fun p => preparedHonestInput V (sourceAcceptedInput p))) :
    SourcePolyTime acceptedCircuitInputWord (fun p => List.ofFn (convertedHonest V proofLength honest p)) :=
  source_composite_polynomial _ _ _ hprepare (honest_restriction_dock h V proofLength honest a hr hP)

end NearCubicGates.Adapters.Proximity
