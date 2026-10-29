import SourceAdapters.Proximity.NormalizedCalls
import SourceAdapters.Proximity.AddressDock
import SourceAdapters.Proximity.CanonicalHonest

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid honest proof restriction from the source request,
accepted raw input bits and the explicitly serialized retained address list.
This interface consumes ordinary source algorithms in their own encodings;
it supplies an actual ordinary output machine, not just an output-size bound. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open NearCubicGates.Adapters.Proximity

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": all data and framing are physically supplied and charged. -/
def preparedHonestInput {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (p : AcceptedSourceInput) : List Bool :=
  natWord (sourceCircuitWord p.1).length ++ sourceCircuitWord p.1 ++
    frame (List.ofFn p.2.val) ++ trimAddressWord (clauseTrimRequest V p.1)

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": exact canonical extension restricted in sorted address order. -/
def preparedHonestOutput {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (p : AcceptedSourceInput) : List Bool :=
  List.ofFn (trimmedCanonicalProof (V p.1) p.2.val (finiteProofOracle (honest p)))

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": actual polynomial-time source calls, enumeration and restriction. -/
def HonestRestriction : Prop :=
  ∀ (q : ℕ) (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1)) (a : ℕ),
    (∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2)) →
    SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest) →
    SourcePolyTime (preparedHonestInput V) (preparedHonestOutput V proofLength honest)

end NearCubicGates.Adapters.Joins
