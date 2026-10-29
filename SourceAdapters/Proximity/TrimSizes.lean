import SourceAdapters.Proximity.TrimData
import Proof.Gates.Cells.Mac

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": bounds in the actual serialized input length, including
all natural-address bits. No bound on numerical address values is assumed.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
open NearCubicGates.Close.Cells

def inputSize {n : ℕ} (V : ThreeQueryVerifier n) : ℕ :=
  (trimRequestWord ⟨n, V⟩).length

theorem fieldWords_count_le (xs : List ℕ) :
    xs.length ≤ (xs.flatMap natWord).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append,
      natWord_length]
    omega

theorem field_bitLength_le {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) :
    natBitLength x ≤ (xs.flatMap natWord).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.flatMap_cons, List.length_append, natWord_length]
    rcases hx with rfl | hx
    · omega
    · have := ih hx
      omega

theorem fields_word_le {n : ℕ} (V : ThreeQueryVerifier n) :
    ((fields V).flatMap natWord).length ≤ inputSize V := by
  simp only [inputSize, requestWord_eq, List.length_append]
  omega

theorem fields_count_le {n : ℕ} (V : ThreeQueryVerifier n) :
    (fields V).length ≤ inputSize V :=
  (fieldWords_count_le (fields V)).trans (fields_word_le V)

theorem field_bits_le {n : ℕ} (V : ThreeQueryVerifier n) {x : ℕ}
    (hx : x ∈ fields V) : natBitLength x ≤ inputSize V :=
  (field_bitLength_le hx).trans (fields_word_le V)

theorem arity_bits_le {n : ℕ} (V : ThreeQueryVerifier n) :
    natBitLength n ≤ inputSize V := by
  simp only [inputSize, requestWord_eq, List.length_append, natWord_length]
  omega

theorem random_bits_le {n : ℕ} (V : ThreeQueryVerifier n) :
    natBitLength V.randomBits ≤ inputSize V := by
  simp only [inputSize, requestWord_eq, List.length_append, natWord_length]
  omega

theorem rows_le {n : ℕ} (V : ThreeQueryVerifier n) :
    2 ^ V.randomBits ≤ inputSize V := by
  have h := fields_count_le V
  rw [fields_length] at h
  omega

theorem randomness_le {n : ℕ} (V : ThreeQueryVerifier n) :
    V.randomBits < inputSize V :=
  (Nat.lt_two_pow_self).trans_le (rows_le V)

end NearCubicGates.Adapters.Proximity.Trim
