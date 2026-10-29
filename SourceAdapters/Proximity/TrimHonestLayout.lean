import SourceAdapters.Proximity.TrimHonestCoinState

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the paid input prefix exposes the exact source cursor,
and the stored sorted schedule gives precisely the required raw output. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

def preparedPrefix {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (p : AcceptedSourceInput) : List Bool :=
  natWord (preparedHonestInput V p).length ++ natWord (sourceCircuitWord p.1).length
def preparedTail {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (p : AcceptedSourceInput) : List Bool :=
  frame (List.ofFn p.2.val) ++ trimAddressWord (clauseTrimRequest V p.1)

theorem prepared_shape {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (p : AcceptedSourceInput) :
    LengthPrefix.wrapped (preparedHonestInput V p) =
      preparedPrefix V p ++ sourceCircuitWord p.1 ++ preparedTail V p := by
  simp only [LengthPrefix.wrapped, preparedHonestInput, preparedPrefix, preparedTail, List.append_assoc]

theorem prepared_output_map {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (p : AcceptedSourceInput) :
    (trimSortedAddresses (clauseTrimRequest V p.1)).map
      (canonicalClauseProof (V p.1) p.2.val (finiteProofOracle (honest p))) =
      preparedHonestOutput V proofSize honest p :=
  sorted_address_restriction (clauseVerifier (V p.1)) _

end NearCubicGates.Adapters.Proximity.TrimHonest
