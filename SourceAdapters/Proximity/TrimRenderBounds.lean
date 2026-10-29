import SourceAdapters.Proximity.TrimAddressRun
import SourceAdapters.Proximity.TrimChooseIndex

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": bit lengths of dense output addresses are bounded by serialized input
bit length, never by assuming a polynomial numerical input arity.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

theorem literal_cap {n : ℕ} (V : ThreeQueryVerifier n) :
    2 * (n + (trimSortedAddresses ⟨n, V⟩).length) + 1 < 2 ^ (inputSize V + 2) := by
  have hn : n < 2 ^ inputSize V :=
    (lt_natBitLength n).trans_le (Nat.pow_le_pow_right (by decide) (arity_bits_le V))
  have hs := (schedule_bounds V).1
  have hp : inputSize V < 2 ^ inputSize V := Nat.lt_two_pow_self
  simp only [Nat.pow_add, pow_two]
  omega

theorem literalValue_eq_index {n : ℕ} (V : ThreeQueryVerifier n) (q : SignedQuery n) :
    literalValue V q = 2 * queryIndex (trimSortedAddresses ⟨n, V⟩) q + q.negated.toNat := rfl

theorem literal_value_le {n : ℕ} (V : ThreeQueryVerifier n) (q : SignedQuery n) :
    literalValue V q ≤ 2 * (n + (trimSortedAddresses ⟨n, V⟩).length) + 1 := by
  have hi := queryIndex_le (trimSortedAddresses ⟨n, V⟩) q
  have hs : q.negated.toNat ≤ 1 := by cases q.negated <;> decide
  rw [literalValue_eq_index]
  omega

theorem literal_bits_le {n : ℕ} (V : ThreeQueryVerifier n) (q : SignedQuery n) :
    (literalValue V q).bits.length ≤ inputSize V + 2 := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr ((literal_value_le V q).trans_lt (literal_cap V))

end NearCubicGates.Adapters.Proximity.Trim
