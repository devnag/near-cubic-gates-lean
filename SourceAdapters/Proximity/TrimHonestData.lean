import SourceAdapters.Joins.HonestRestriction
import SourceAdapters.Proximity.HonestLoading
import SourceAdapters.Code.DictionaryBitLookup

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": finite auxiliary dictionaries retain the exact canonical
proof, including default-false values beyond each finite row assignment.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Published.CW19Proximity

def rowKeys (B row : ℕ) : List ℕ := (List.range B).map fun i => 2 * Nat.pair row i + 1
def auxKeys (R B : ℕ) : List ℕ := (List.range R).flatMap (rowKeys B)

@[simp] theorem rowKeys_length (B row : ℕ) : (rowKeys B row).length = B := by simp [rowKeys]
@[simp] theorem auxKeys_zero (B : ℕ) : auxKeys 0 B = [] := rfl

theorem auxKeys_succ (R B : ℕ) : auxKeys (R + 1) B = auxKeys R B ++ rowKeys B R := by
  simp [auxKeys, List.range_succ]

@[simp] theorem auxKeys_length (R B : ℕ) : (auxKeys R B).length = R * B := by
  induction R with
  | zero => simp
  | succ R ih => rw [auxKeys_succ, List.length_append, ih, rowKeys_length]; ring

theorem mem_auxKeys (R B address : ℕ) : address ∈ auxKeys R B ↔
    ∃ row < R, ∃ i < B, 2 * Nat.pair row i + 1 = address := by
  simp [auxKeys, rowKeys]

theorem canonical_zero {q : ℕ} (predicate : BitInput q → Bool) (input : BitInput q)
    (address : ℕ) (h : blockVariableBound q ≤ address) :
    canonicalBlockAssignment predicate input address = false := by
  simp [canonicalBlockAssignment, finiteProofOracle, Nat.not_lt.mpr h]

theorem canonical_word_lookup {q : ℕ} (predicate : BitInput q → Bool) (input : BitInput q)
    (address : ℕ) :
    (List.ofFn (fun i : Fin (blockVariableBound q) => canonicalBlockAssignment predicate input i.val)).getD
      address false = canonicalBlockAssignment predicate input address := by
  rw [HonestLoading.ofFn_getD]
  by_cases h : address < blockVariableBound q
  · simp [finiteProofOracle, h]
  · simp [finiteProofOracle, h, canonical_zero predicate input address (Nat.le_of_not_gt h)]

end NearCubicGates.Adapters.Proximity.TrimHonest
