import Mathlib.Data.BitVec

/-! # Split a binary lane into its higher bits and low Boolean bit

Generic transport for the Beneš induction. No routing contract is imported.-/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.LanePair

def split {k : ℕ} (x : BitVec (k + 1)) : BitVec k × Bool :=
  (x.extractLsb' 1 k, x.getLsbD 0)

def join {k : ℕ} (p : BitVec k × Bool) : BitVec (k + 1) :=
  p.1 ++ BitVec.ofBool p.2

theorem split_join {k : ℕ} (p : BitVec k × Bool) : split (join p) = p := by
  rcases p with ⟨x, b⟩
  apply Prod.ext
  · exact BitVec.extractLsb'_append_eq_left
  · change (x ++ BitVec.ofBool b).getLsbD 0 = b
    rw [BitVec.getLsbD_append]
    simp

theorem join_split {k : ℕ} (x : BitVec (k + 1)) : join (split x) = x := by
  unfold join split
  rw [← BitVec.setWidth_one, BitVec.setWidth_eq_extractLsb' (by omega),
    BitVec.extractLsb'_append_extractLsb']

def equiv (k : ℕ) : BitVec (k + 1) ≃ BitVec k × Bool where
  toFun := split
  invFun := join
  left_inv := join_split
  right_inv := split_join

theorem join_xor {k : ℕ} (p q : BitVec k × Bool) :
    join (p.1 ^^^ q.1, p.2 ^^ q.2) = join p ^^^ join q := by
  simp [join, BitVec.xor_append]

theorem split_xor {k : ℕ} (x y : BitVec (k + 1)) :
    split (x ^^^ y) = ((split x).1 ^^^ (split y).1, (split x).2 ^^ (split y).2) := by
  apply (equiv k).symm.injective
  change join (split (x ^^^ y)) = join _
  rw [join_split, join_xor, join_split, join_split]

theorem join_toNat {k : ℕ} (p : BitVec k × Bool) :
    (join p).toNat = p.1.toNat * 2 + p.2.toNat :=
  BitVec.toNat_concat p.1 p.2

theorem join_zero_true (k : ℕ) :
    join ((0 : BitVec k), true) = BitVec.ofNat (k + 1) 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [join_toNat]

theorem join_single_bit {k d : ℕ} (hd : d < k) :
    join (BitVec.ofNat k (2 ^ d), false) = BitVec.ofNat (k + 1) (2 ^ (d + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [join_toNat]
  simp only [BitVec.toNat_ofNat, Bool.toNat_false, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hd),
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (Nat.succ_lt_succ hd)), pow_succ]

theorem split_one (k : ℕ) : split (BitVec.ofNat (k + 1) 1) = (0, true) := by
  rw [← join_zero_true, split_join]

theorem split_single_bit {k d : ℕ} (hd : d < k) :
    split (BitVec.ofNat (k + 1) (2 ^ (d + 1))) = (BitVec.ofNat k (2 ^ d), false) := by
  rw [← join_single_bit hd, split_join]

theorem split_flip_zero {k : ℕ} (x : BitVec (k + 1)) :
    split (x ^^^ BitVec.ofNat (k + 1) 1) = ((split x).1, !(split x).2) := by
  rw [split_xor, split_one]
  simp

theorem split_flip_succ {k d : ℕ} (hd : d < k) (x : BitVec (k + 1)) :
    split (x ^^^ BitVec.ofNat (k + 1) (2 ^ (d + 1))) =
      ((split x).1 ^^^ BitVec.ofNat k (2 ^ d), (split x).2) := by
  rw [split_xor, split_single_bit hd]
  simp

end NearCubicGates.Adapters.Routing.LanePair
