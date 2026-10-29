import SourceAdapters.Proximity.AcceptedSplitting
import SourceAdapters.Proximity.PrefixCompilation
import SourceAdapters.Proximity.PairComposition
import SourceAdapters.Proximity.ConstructorPolynomial

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": physically split the target accepted input, convert
its circuit and compute the exact retained proof-address schedule. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Published.CW19Proximity
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Adapters.Joins

theorem accepted_split_polynomial : SourcePolyTime acceptedCircuitInputWord AcceptedSplitting.output :=
  PrefixCompilation.polynomial _ _ AcceptedSplitting.wrappedWordFunction

theorem accepted_source_pair_polynomial : SourcePolyTime acceptedCircuitInputWord
    (fun p => frame (sourceCircuitWord (sourceCircuit p.1)) ++ frame (List.ofFn p.2.val)) := by
  apply source_composite_polynomial _ _ _ accepted_split_polynomial
  obtain ⟨K, e, ⟨P⟩⟩ := source_map_first_polynomial _ _ target_source_polynomial
  exact ⟨K, e, ⟨{ program := P.program, realizes := fun p => P.realizes (p.1, List.ofFn p.2.val) }⟩⟩

def unorderedHonestInput {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (p : AcceptedSourceInput) : List Bool :=
  frame (sourceCircuitWord p.1) ++ frame (trimAddressWord (clauseTrimRequest V p.1)) ++ List.ofFn p.2.val

theorem honest_unordered_polynomial {q : ℕ}
    (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (hP : SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest)) :
    SourcePolyTime acceptedCircuitInputWord (fun p => unorderedHonestInput V (sourceAcceptedInput p)) := by
  let R : SourceCircuit → List Bool := fun S => frame (sourceCircuitWord S) ++
    frame (trimAddressWord (clauseTrimRequest V S))
  have hR : SourcePolyTime sourceCircuitWord R := source_retained_polynomial _ _
    (source_addresses_polynomial V proofLength honest a hr hP)
  have hpair : SourcePolyTime acceptedCircuitInputWord
      (fun p => frame (R (sourceCircuit p.1)) ++ frame (List.ofFn p.2.val)) := by
    apply source_composite_polynomial _ _ _ accepted_source_pair_polynomial
    obtain ⟨K, e, ⟨P⟩⟩ := source_map_first_polynomial _ _ hR
    exact ⟨K, e, ⟨{ program := P.program, realizes := fun p => P.realizes (sourceCircuit p.1, List.ofFn p.2.val) }⟩⟩
  apply source_composite_polynomial _ _ _ hpair
  obtain ⟨K, e, ⟨P⟩⟩ := source_concatenate_polynomial
  exact ⟨K, e, ⟨{ program := P.program, realizes := fun p => P.realizes (R (sourceCircuit p.1), List.ofFn p.2.val) }⟩⟩

end NearCubicGates.Adapters.Proximity
