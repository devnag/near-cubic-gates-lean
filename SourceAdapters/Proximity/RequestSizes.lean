import SourceAdapters.Proximity.ConstructorRun
import Proof.Gates.Cells.OutLen

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": lengths of the exact source request tuples and
query-output words. Output width follows from the actual ordinary output. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

def requestCap (q a L : ℕ) : ℕ := (2 * a + 2 * q + 2 ^ q + 20) * (L + 2)

theorem bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem random_linear {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (S : SourceCircuit) : (V S).randomBits ≤ a * ((sourceCircuitWord S).length + 2) :=
  (hr S).trans (Nat.mul_le_mul_left a (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le))

structure RequestLengths {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits)) (L : ℕ) : Prop where
  random : (proofCallInput V (randomRequest V S)).length ≤ L
  count : (proofCallInput V (countRequest V ⟨S, coins⟩)).length ≤ L
  query : ∀ j, (proofCallInput V (queryRequest V ⟨S, coins, j⟩)).length ≤ L
  decision : ∀ bits : BitInput q, (proofCallInput V (decisionRequest V ⟨S, coins,
    fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩)).length ≤ L
  block : 5 + 2 ^ q ≤ L

theorem request_lengths {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (a : ℕ) (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    (hr : (V S).randomBits ≤ a * ((sourceCircuitWord S).length + 2)) :
    RequestLengths V S coins (requestCap q a (sourceCircuitWord S).length) := by
  have hcoin : coins.val.bits.length ≤ (V S).randomBits := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr coins.isLt
  have hcount := (V S).queryCount_le coins
  have hpow : 0 ≤ (2 ^ q : ℕ) := Nat.zero_le _
  have hcap : (sourceCircuitWord S).length + 2 * (V S).randomBits + 2 * q + 2 ^ q + 10 ≤
      requestCap q a (sourceCircuitWord S).length := by
    unfold requestCap
    nlinarith [Nat.zero_le (q * (sourceCircuitWord S).length),
      Nat.zero_le ((2 ^ q) * (sourceCircuitWord S).length)]
  refine ⟨?_, ?_, ?_, ?_, by omega⟩
  · simp only [random_input, List.length_append, List.length_cons, List.length_nil]
    omega
  · simp only [count_input, List.length_append, List.length_cons, List.length_nil, frame_length]
    omega
  · intro j
    have hj := j.isLt
    have hjb := bits_length_le j.val
    simp only [query_input, QueryStep.queryTag, List.length_append, List.length_cons, List.length_nil, frame_length]
    omega
  · intro bits
    simp only [decision_input, List.length_append, List.length_cons, List.length_nil, frame_length,
      List.length_ofFn]
    omega

theorem query_output_bits {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)
    (p : QueryRequest V) :
    (addressPair ((V p.1).query p.2.1 p.2.2)).2.bits.length ≤ budget (queryRequest V p) := by
  have h := wf_out_len P (queryRequest V p)
  rw [query_output] at h
  simp only [List.length_cons, frame_length] at h
  omega

end NearCubicGates.Adapters.Proximity.SourceCallee
