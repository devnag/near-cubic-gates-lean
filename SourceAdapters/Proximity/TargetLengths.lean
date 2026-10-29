import SourceAdapters.Proximity.SerializationSize
import Proof.Circuits.ValidatorCompositeLeafBounds

/-!
Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the target's balanced circuit word controls node count.
Reuse the released balanced-code counting ledger, rather than a different
generic List Encodable codec. This turns the proved output-size bound in m
into a polynomial in the actual target input-word length.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.CanonicalBinary NearCubicWires.ExecutableInterfaces
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Published.CW19Proximity

theorem natBitLength_le_bits_succ (value : ℕ) : natBitLength value ≤ value.bits.length + 1 := by
  rw [Nat.size_eq_bits_len]
  by_cases hzero : value = 0
  · simp [hzero, natBitLength]
  · have hlog := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) hzero).mpr (Nat.lt_size_self value)
    unfold natBitLength
    omega

theorem balanced_length_le_bits (values : List ℕ) :
    values.length + 1 ≤ 2 * ((encodeBalancedList values).bits.length + 1) := by
  have h := ValidatorCompositeLeafBounds.balancedValidationMapCodes_length_succ_le
    (encodeBalancedList values)
  rw [ValidatorCompositeLeafBounds.balancedValidationMapCodes_encodeBalancedList] at h
  exact h.trans (Nat.mul_le_mul_left 2 (natBitLength_le_bits_succ _))

theorem target_nodes_le_word (C : Circuit) : C.m + 1 ≤ 2 * (C.word.length + 1) := by
  let nodesCode := encodeBalancedList (C.D.nodes.map encodeBooleanNode)
  have hcode : nodesCode ≤ encodeBooleanCircuit C.D := by
    change nodesCode ≤ Nat.pair 1 (Nat.pair nodesCode _)
    exact (Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _)
  have hnodes := balanced_length_le_bits (C.D.nodes.map encodeBooleanNode)
  simp only [List.length_map] at hnodes
  have hsize : nodesCode.bits.length ≤ (encodeBooleanCircuit C.D).bits.length := by
    simp only [Nat.size_eq_bits_len]
    exact Nat.size_le_size hcode
  have hword : (encodeBooleanCircuit C.D).bits.length ≤ C.word.length := by
    simp only [Circuit.word, List.length_append]
    omega
  change C.D.nodes.length + 1 ≤ _
  dsimp only [nodesCode] at hsize
  omega

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the exact output word fits a polynomial in its actual input word. -/
theorem converted_word_input_bound {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) (a : ℕ)
    (hr : ∀ C, (V C).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord C).length + 2)) :
    ∃ K e : ℕ, ∀ C : Circuit,
      (convertedVerifier V C).word.length ≤ K * (C.word.length + 1) ^ e := by
  obtain ⟨K, e, houtput⟩ := converted_word_polynomial V a hr
  refine ⟨K * 2 ^ e, e, fun C => ?_⟩
  calc
    (convertedVerifier V C).word.length ≤ K * (C.m + 1) ^ e := houtput C
    _ ≤ K * (2 * (C.word.length + 1)) ^ e :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (target_nodes_le_word C) e)
    _ = (K * 2 ^ e) * (C.word.length + 1) ^ e := by rw [mul_pow, Nat.mul_assoc]

end NearCubicGates.Adapters.Proximity
