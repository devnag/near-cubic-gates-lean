import SourceAdapters.Proximity.SizeBounds

/-!
Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the exact serialized target word has polynomial length.
This is an output-size bound only; a writing algorithm with a proved ordinary
clock is a separate construction.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Published.CW19Proximity NearCubicGates.PublishedSources.PCPP

theorem literal_word_length {n : ℕ} (literal : Literal n) :
    (RepairOrdinary.frame (literalCode literal).bits).length ≤ 4 * n + 1 := by
  have hcode : literalCode literal ≤ 2 * n := by
    cases literal with
    | positive i => simp only [literalCode]; have := i.isLt; omega
    | negative i => simp only [literalCode]; have := i.isLt; omega
  have h := framed_nat_length_le hcode
  omega

private theorem flatten_bound {α : Type} (words : List (List α)) (B : ℕ)
    (h : ∀ word ∈ words, word.length ≤ B) : words.flatten.length ≤ words.length * B := by
  induction words with
  | nil => simp
  | cons word rest ih =>
      have hword := h word (by simp)
      have hrest := ih (fun next hnext => h next (by simp [hnext]))
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem raw_word_length {n : ℕ} (P : RawThreeQueryPCPP n) :
    P.word.length ≤ 20 * (n + P.proofBits + 2 ^ P.randomBits + 1) ^ 2 := by
  have hp := framed_nat_length_le (Nat.le_refl P.proofBits)
  have hr := framed_nat_length_le (Nat.lt_two_pow_self (n := P.randomBits)).le
  have hc (coins : Fin (2 ^ P.randomBits)) :
      (List.ofFn fun i : Fin 3 => RepairOrdinary.frame (literalCode (P.clause coins i)).bits).flatten.length ≤
        3 * (4 * (n + P.proofBits) + 1) := by
    have h := flatten_bound (List.ofFn fun i : Fin 3 =>
      RepairOrdinary.frame (literalCode (P.clause coins i)).bits) (4 * (n + P.proofBits) + 1) (by
        intro word hword
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hword
        exact literal_word_length _)
    simpa only [List.length_ofFn] using h
  have hall := flatten_bound (List.ofFn fun coins : Fin (2 ^ P.randomBits) =>
    (List.ofFn fun i : Fin 3 => RepairOrdinary.frame (literalCode (P.clause coins i)).bits).flatten)
    (3 * (4 * (n + P.proofBits) + 1)) (by
      intro word hword
      obtain ⟨coins, rfl⟩ := List.mem_ofFn.mp hword
      exact hc coins)
  simp only [List.length_ofFn] at hall
  simp only [RawThreeQueryPCPP.word, List.length_append]
  nlinarith [sq_nonneg ((n + P.proofBits + 2 ^ P.randomBits : ℕ) : ℤ)]

theorem raw_word_polynomial {n m K e : ℕ} (P : RawThreeQueryPCPP n) (hn : n ≤ m)
    (hp : P.proofBits ≤ K * (m + 1) ^ e) (hr : 2 ^ P.randomBits ≤ K * (m + 1) ^ e) :
    P.word.length ≤ (20 * (2 * K + 1) ^ 2) * (m + 1) ^ (2 * (e + 1)) := by
  have hmono : (m + 1) ^ e ≤ (m + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hbase : m + 1 ≤ (m + 1) ^ (e + 1) := Nat.le_self_pow (by omega) _
  have hb : n + P.proofBits + 2 ^ P.randomBits + 1 ≤ (2 * K + 1) * (m + 1) ^ (e + 1) := by
    have hkp := Nat.mul_le_mul_left K hmono
    nlinarith
  calc
    P.word.length ≤ 20 * (n + P.proofBits + 2 ^ P.randomBits + 1) ^ 2 := raw_word_length P
    _ ≤ 20 * ((2 * K + 1) * (m + 1) ^ (e + 1)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)
    _ = (20 * (2 * K + 1) ^ 2) * (m + 1) ^ (2 * (e + 1)) := by
      simp only [mul_pow, ← pow_mul]
      rw [Nat.mul_comm (e + 1) 2]
      ring

theorem converted_word_polynomial {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) (a : ℕ)
    (hr : ∀ C, (V C).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord C).length + 2)) :
    ∃ K e : ℕ, ∀ C : Circuit, (convertedVerifier V C).word.length ≤ K * (C.m + 1) ^ e := by
  let B := 3 * (28 ^ a * predicateBlockSize q)
  refine ⟨20 * (2 * B + 1) ^ 2, 2 * (2 * a + 1), fun C => ?_⟩
  exact raw_word_polynomial _ C.sizeAtLeast (convertedVerifier_size V a hr C).1
    (convertedVerifier_size V a hr C).2

end NearCubicGates.Adapters.Proximity
