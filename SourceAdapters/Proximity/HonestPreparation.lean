import SourceAdapters.Proximity.ConsumerDock
import SourceAdapters.Code.TriplePreparation

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the proved generic serializer completes every
upstream ordinary representation adapter for the honest restriction machine. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Published.CW19Proximity NearCubicGates.PublishedSources.PCPP
open NearCubicGates.Adapters.Joins

theorem triple_serializer_polynomial : SourcePolyTime
    (fun p : List Bool × List Bool × List Bool => frame p.1 ++ frame p.2.1 ++ p.2.2)
    (fun p => natWord p.1.length ++ p.1 ++ frame p.2.2 ++ p.2.1) := by
  refine ⟨Code.TriplePreparation.coefficient, 4, ⟨?_⟩⟩
  exact {
    program := Code.TriplePreparation.wordFunction.program
    realizes := fun p => Code.TriplePreparation.wordFunction.realizes p }

theorem honest_preparation_polynomial {q : ℕ}
    (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (hP : SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest)) :
    SourcePolyTime acceptedCircuitInputWord (fun p => preparedHonestInput V (sourceAcceptedInput p)) :=
  honest_preparation_of_serializer triple_serializer_polynomial V proofLength honest a hr hP

theorem perfect_from_honest_restriction (restriction : HonestRestriction)
    (source : Lemma22Half) : PerfectThreeQueryProximityLiteral :=
  perfect_from_restriction_and_serializer triple_serializer_polynomial restriction source

end NearCubicGates.Adapters.Proximity
