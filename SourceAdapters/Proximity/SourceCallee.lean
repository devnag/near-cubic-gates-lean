import SourceAdapters.Proximity.NormalizedCalls
import SourceAdapters.Proximity.QueryRows

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the checked dispatcher as an actual Cells callee,
and its exact source-domain requests. This packages an existing WordFunction;
it makes no new algorithm-existence assumption. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)

def callee (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget) : Callee :=
  ⟨ProofCall V, proofCallInput V, normalizedProofOutput V proofLength honest, budget, P⟩

def randomRequest (S : SourceCircuit) : ProofCall V := .inl (.inl S)
def countRequest (p : CoinRequest V) : ProofCall V := .inl (.inr (.inl p))
def queryRequest (p : QueryRequest V) : ProofCall V := .inl (.inr (.inr (.inl p)))
def decisionRequest (p : DecisionRequest V) : ProofCall V := .inl (.inr (.inr (.inr (.inl p))))

def addressPair {n : ℕ} : QueryAddress n → Bool × ℕ
  | .inl i => (false, i.val)
  | .inr a => (true, a)

theorem addressPair_word {n : ℕ} (a : QueryAddress n) :
    queryAddressWord a = (addressPair a).1 :: frame (addressPair a).2.bits := by cases a <;> rfl

theorem random_input (S : SourceCircuit) :
    proofCallInput V (randomRequest V S) = [false, false] ++ sourceCircuitWord S := rfl

theorem count_input (p : CoinRequest V) :
    proofCallInput V (countRequest V p) = [false, true, false] ++ sourceCircuitWord p.1 ++ frame p.2.val.bits := rfl

theorem query_input (p : QueryRequest V) :
    proofCallInput V (queryRequest V p) = QueryStep.queryTag ++ sourceCircuitWord p.1 ++
      frame p.2.1.val.bits ++ frame p.2.2.val.bits := rfl

theorem decision_input (p : DecisionRequest V) :
    proofCallInput V (decisionRequest V p) = [false, true, true, true, false] ++ sourceCircuitWord p.1 ++
      frame p.2.1.val.bits ++ List.ofFn p.2.2 := rfl

variable (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))

theorem random_output (S : SourceCircuit) :
    normalizedProofOutput V proofLength honest (randomRequest V S) = frame (V S).randomBits.bits := rfl

theorem count_output (p : CoinRequest V) :
    normalizedProofOutput V proofLength honest (countRequest V p) = frame ((V p.1).queryCount p.2).bits := rfl

theorem query_output (p : QueryRequest V) :
    normalizedProofOutput V proofLength honest (queryRequest V p) =
      (addressPair ((V p.1).query p.2.1 p.2.2)).1 :: frame (addressPair ((V p.1).query p.2.1 p.2.2)).2.bits :=
  addressPair_word _

theorem decision_output (p : DecisionRequest V) :
    normalizedProofOutput V proofLength honest (decisionRequest V p) = [(V p.1).decision p.2.1 p.2.2] := rfl

theorem padded_address {n : ℕ} (verifier : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ verifier.randomBits)) (j : Fin q) :
    QueryStep.paddedAddress (fun i => addressPair (verifier.query coins i)) j.val =
      addressPair ((padQueries verifier).query coins j) := by
  by_cases h : j.val < verifier.queryCount coins
  all_goals simp [QueryStep.paddedAddress, padQueries, h, addressPair]

end NearCubicGates.Adapters.Proximity.SourceCallee
