import Proof.MachineModel.OrdinarySortCost
import Proof.Foundations.SupplierPrinter

/-! Fixed-width binary keys for the paper's exact signed-score/stable-id
order. The codec is a local representation lemma; its input-generation
program remains part of the matrix caller. -/
namespace NearCubicWires.RepairOrdinary.SignedSortKey
open StablePartition RadixSemantics SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def binary : ℕ → ℕ → List Bool
  | 0, _ => []
  | width + 1, n => (n % 2 == 1) :: binary width (n / 2)

@[simp] theorem binary_length (width n : ℕ) : (binary width n).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih => simp [binary, ih]

theorem low_bit (n : ℕ) : (n % 2 == 1).toNat = n % 2 := by
  have h := Nat.mod_lt n (by decide : 0 < 2)
  by_cases he : n % 2 = 1
  · simp [he]
  · have hz : n % 2 = 0 := by omega
    simp [hz]

theorem binary_value (width n : ℕ) (hn : n < 2 ^ width) : value (binary width n) = n := by
  induction width generalizing n with
  | zero =>
    have he : n = 0 := by simpa using hn
    subst n
    rfl
  | succ width ih =>
    have hd : n / 2 < 2 ^ width := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
      (by simpa [pow_succ] using hn)
    rw [binary, value, low_bit, ih _ hd]
    omega

def record : List Bool → Record
  | [] => (false, [])
  | b :: bs => (b, bs)

theorem word_record (bs : List Bool) (hne : bs ≠ []) : word (record bs) = bs := by
  cases bs
  · contradiction
  · rfl

def shifted (scoreBits : ℕ) (score : ℤ) : ℕ := (score + (2 ^ scoreBits : ℕ)).toNat

def encode (scoreBits idBits : ℕ) (score : ℤ) (id : ℕ) : Record :=
  record (binary idBits id ++ binary (scoreBits + 1) (shifted scoreBits score))

theorem encode_word (scoreBits idBits : ℕ) (score : ℤ) (id : ℕ) :
    word (encode scoreBits idBits score id) =
      binary idBits id ++ binary (scoreBits + 1) (shifted scoreBits score) := by
  apply word_record
  intro h
  have hl := congrArg List.length h
  simp at hl

@[simp] theorem encode_width (scoreBits idBits : ℕ) (score : ℤ) (id : ℕ) :
    (word (encode scoreBits idBits score id)).length = idBits + scoreBits + 1 := by
  rw [encode_word]
  simp
  omega

theorem shifted_bound (scoreBits : ℕ) (score : ℤ)
    (hlo : -(2 ^ scoreBits : ℕ) ≤ score) (hhi : score < (2 ^ scoreBits : ℕ)) :
    shifted scoreBits score < 2 ^ (scoreBits + 1) := by
  have hpos : 0 ≤ score + (2 ^ scoreBits : ℕ) := by omega
  unfold shifted
  rw [Int.toNat_lt hpos]
  have he : ((2 ^ (scoreBits + 1) : ℕ) : ℤ) = 2 * (2 ^ scoreBits : ℕ) := by
    push_cast
    rw [pow_succ]
    ring
  rw [he]
  omega

theorem encode_value (scoreBits idBits : ℕ) (score : ℤ) (id : ℕ)
    (hlo : -(2 ^ scoreBits : ℕ) ≤ score) (hhi : score < (2 ^ scoreBits : ℕ))
    (hid : id < 2 ^ idBits) :
    value (word (encode scoreBits idBits score id)) = id + 2 ^ idBits * shifted scoreBits score := by
  rw [encode_word, value_append, binary_value _ _ hid, binary_length,
    binary_value _ _ (shifted_bound scoreBits score hlo hhi)]

theorem key_lt_of_score_lt (base leftScore leftId rightScore rightId : ℕ)
    (hi : leftId < base) (hs : leftScore < rightScore) :
    leftId + base * leftScore < rightId + base * rightScore := by
  have hm := Nat.mul_le_mul_left base (show leftScore + 1 ≤ rightScore by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  omega

theorem numeric_key_le_iff (base leftScore leftId rightScore rightId : ℕ)
    (hl : leftId < base) (hr : rightId < base) :
    leftId + base * leftScore ≤ rightId + base * rightScore ↔
      leftScore < rightScore ∨ (leftScore = rightScore ∧ leftId ≤ rightId) := by
  by_cases he : leftScore = rightScore
  · simp [he]
  · rcases lt_or_gt_of_ne he with hlt | hgt
    · have hk := key_lt_of_score_lt base leftScore leftId rightScore rightId hl hlt
      omega
    · have hk := key_lt_of_score_lt base rightScore rightId leftScore leftId hr hgt
      omega

theorem encode_order (scoreBits idBits : ℕ) (a b : ℤ) (i j : ℕ)
    (ha : -(2 ^ scoreBits : ℕ) ≤ a) (ha' : a < (2 ^ scoreBits : ℕ))
    (hb : -(2 ^ scoreBits : ℕ) ≤ b) (hb' : b < (2 ^ scoreBits : ℕ))
    (hi : i < 2 ^ idBits) (hj : j < 2 ^ idBits) :
    value (word (encode scoreBits idBits a i)) ≤ value (word (encode scoreBits idBits b j)) ↔
      a < b ∨ (a = b ∧ i ≤ j) := by
  rw [encode_value _ _ _ _ ha ha' hi, encode_value _ _ _ _ hb hb' hj, numeric_key_le_iff _ _ _ _ _ hi hj]
  have hx := Int.toNat_of_nonneg (show 0 ≤ a + (2 ^ scoreBits : ℕ) by omega)
  have hy := Int.toNat_of_nonneg (show 0 ≤ b + (2 ^ scoreBits : ℕ) by omega)
  unfold shifted
  omega

def dominanceRecord {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (copy : StableDominanceCopy Rows Columns) : Record :=
  encode scoreBits idBits (stableDominanceCopyScore leftScore rightScore gate copy)
    (stableDominanceCopyId copy).val

theorem dominance_order {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ idBits)
    (hlo : ∀ copy, -(2 ^ scoreBits : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ scoreBits : ℕ))
    (a b : StableDominanceCopy Rows Columns) :
    value (word (dominanceRecord scoreBits idBits leftScore rightScore gate a)) ≤
        value (word (dominanceRecord scoreBits idBits leftScore rightScore gate b)) ↔
      stableDominanceKey leftScore rightScore gate a ≤ stableDominanceKey leftScore rightScore gate b := by
  rw [dominanceRecord, dominanceRecord,
    encode_order _ _ _ _ _ _ (hlo a) (hhi a) (hlo b) (hhi b)
      ((stableDominanceCopyId a).isLt.trans_le hsize) ((stableDominanceCopyId b).isLt.trans_le hsize)]
  exact (Prod.Lex.toLex_le_toLex
    (x := (stableDominanceCopyScore leftScore rightScore gate a, stableDominanceCopyId a))
    (y := (stableDominanceCopyScore leftScore rightScore gate b, stableDominanceCopyId b))).symm

def decodeId (idBits : ℕ) (r : Record) : ℕ := value (word r) % 2 ^ idBits

def decodeScore (scoreBits idBits : ℕ) (r : Record) : ℤ :=
  (value (word r) / 2 ^ idBits : ℕ) - (2 ^ scoreBits : ℕ)

theorem decode_id (scoreBits idBits : ℕ) (score : ℤ) (id : ℕ)
    (hlo : -(2 ^ scoreBits : ℕ) ≤ score) (hhi : score < (2 ^ scoreBits : ℕ))
    (hid : id < 2 ^ idBits) : decodeId idBits (encode scoreBits idBits score id) = id := by
  rw [decodeId, encode_value _ _ _ _ hlo hhi hid]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hid]

theorem decode_score (scoreBits idBits : ℕ) (score : ℤ) (id : ℕ)
    (hlo : -(2 ^ scoreBits : ℕ) ≤ score) (hhi : score < (2 ^ scoreBits : ℕ))
    (hid : id < 2 ^ idBits) : decodeScore scoreBits idBits (encode scoreBits idBits score id) = score := by
  rw [decodeScore, encode_value _ _ _ _ hlo hhi hid,
    Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ idBits), Nat.div_eq_of_lt hid, Nat.zero_add]
  have hs := Int.toNat_of_nonneg (show 0 ≤ score + (2 ^ scoreBits : ℕ) by omega)
  unfold shifted
  omega

end NearCubicWires.RepairOrdinary.SignedSortKey
