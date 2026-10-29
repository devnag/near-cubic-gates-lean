import SourceAdapters.Proximity.CircuitRepresentation
import SourceAdapters.Proximity.HonestBlocks
import SourceAdapters.Proximity.Trimming

/-!
Q01/Q03, `app:sources`, "Uniform three-query PCPP and code interfaces". Source logarithmic randomness and the
flat source word bound give one all-circuit polynomial for both coin count
and trimmed proof length. The constants depend only on the fixed source
verifier/proximity and the fixed clause block, including all small lengths.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Published.CW19Proximity
open NearCubicGates.PublishedSources.PCPP

theorem logarithmic_coin_bound (C : Circuit) (r a k : ℕ)
    (hr : r ≤ a * Nat.clog 2 ((sourceCircuitWord (sourceCircuit C)).length + 2)) :
    2 ^ (r + k) ≤ (28 ^ a * 2 ^ k) * (C.m + 1) ^ (2 * a) := by
  let L := (sourceCircuitWord (sourceCircuit C)).length
  have hword : L ≤ 11 * (C.m + 1) ^ 2 := source_word_length_target C
  have hbase : 2 ^ Nat.clog 2 (L + 2) ≤ 28 * (C.m + 1) ^ 2 := by
    have hround := binaryBlockSize_le (L + 2)
    have hone : 1 ≤ (C.m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    dsimp [binaryBlockSize] at hround
    nlinarith
  have hrpow : 2 ^ r ≤ (28 * (C.m + 1) ^ 2) ^ a := by
    calc
      2 ^ r ≤ 2 ^ (a * Nat.clog 2 (L + 2)) := Nat.pow_le_pow_right (by decide) hr
      _ = (2 ^ Nat.clog 2 (L + 2)) ^ a := by rw [Nat.mul_comm a, pow_mul]
      _ ≤ (28 * (C.m + 1) ^ 2) ^ a := Nat.pow_le_pow_left hbase a
  rw [pow_add]
  calc
    2 ^ r * 2 ^ k ≤ (28 * (C.m + 1) ^ 2) ^ a * 2 ^ k := Nat.mul_le_mul_right _ hrpow
    _ = (28 ^ a * 2 ^ k) * (C.m + 1) ^ (2 * a) := by
      simp only [mul_pow, pow_mul]
      ring

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the concrete exact-three-query, densely trimmed output. -/
def convertedVerifier {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (C : Circuit) : RawThreeQueryPCPP C.n :=
  trimVerifier (clauseVerifier (V (sourceCircuit C)))

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": one pair of constants bounds both quantities for every C. -/
theorem convertedVerifier_size {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) (a : ℕ)
    (hr : ∀ C, (V C).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord C).length + 2)) :
    ∀ C : Circuit,
      (convertedVerifier V C).proofBits ≤ (3 * (28 ^ a * predicateBlockSize q)) * (C.m + 1) ^ (2 * a) ∧
      2 ^ (convertedVerifier V C).randomBits ≤
        (3 * (28 ^ a * predicateBlockSize q)) * (C.m + 1) ^ (2 * a) := by
  intro C
  exact trim_size_bounds (clauseVerifier (V (sourceCircuit C)))
    (logarithmic_coin_bound C _ a (predicateBlockBits q) (hr (sourceCircuit C)))

end NearCubicGates.Adapters.Proximity
