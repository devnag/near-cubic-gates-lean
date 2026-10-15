import Proof.Gates.Interfaces.CounterFormats
import Proof.Gates.Counter.Main

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells

open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-! ## Big-endian radix keys -/

/-- The big-endian radix-`2^b` number of a field list. -/
def rk (b : ℕ) (l : List ℕ) : ℕ := l.foldl (fun acc x => acc * 2 ^ b + x) 0

theorem rk_foldl (b : ℕ) (l : List ℕ) (a : ℕ) :
    l.foldl (fun acc x => acc * 2 ^ b + x) a = a * 2 ^ (b * l.length) + rk b l := by
  induction l generalizing a with
  | nil => simp [rk]
  | cons x l ih =>
    simp only [List.foldl_cons, rk]
    rw [ih, ih (0 * 2 ^ b + x)]
    simp only [List.length_cons, zero_mul, zero_add]
    rw [Nat.mul_succ, pow_add]; ring

theorem rk_snoc (b : ℕ) (l : List ℕ) (x : ℕ) : rk b (l ++ [x]) = rk b l * 2 ^ b + x := by
  simp [rk, List.foldl_append]

theorem rk_lt (b : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ b) : rk b l < 2 ^ (b * l.length) := by
  induction l using List.reverseRecOn with
  | nil => simp [rk]
  | append_singleton l x ih =>
    rw [rk_snoc]
    have h1 := ih (fun y hy => hl y (by simp [hy]))
    have h2 := hl x (by simp)
    rw [List.length_append, List.length_singleton, Nat.mul_succ, pow_add]
    calc rk b l * 2 ^ b + x < rk b l * 2 ^ b + 2 ^ b := by omega
      _ = (rk b l + 1) * 2 ^ b := by ring
      _ ≤ 2 ^ (b * l.length) * 2 ^ b := Nat.mul_le_mul_right _ h1

theorem rk_mod (b : ℕ) (l : List ℕ) (x : ℕ) (hx : x < 2 ^ b) : rk b (l ++ [x]) % 2 ^ b = x := by
  rw [rk_snoc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

theorem rk_div (b : ℕ) (l : List ℕ) (x : ℕ) (hx : x < 2 ^ b) : rk b (l ++ [x]) / 2 ^ b = rk b l := by
  rw [rk_snoc, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]

theorem radixKey_eq (b len : ℕ) (fs : List ℕ) :
    radixKey b len fs = rk b (fs ++ List.replicate (len - fs.length) 0) := rfl

/-! ## Residue vectors -/

theorem vecs_length (q : ℕ) : ∀ (d : ℕ) (v : List ℕ), v ∈ vecs q d → v.length = d
  | 0, v, hv => by simp [vecs] at hv; simp [hv]
  | d + 1, v, hv => by
    simp only [vecs, List.mem_flatMap, List.mem_range, List.mem_map] at hv
    obtain ⟨a, _, w, hw, rfl⟩ := hv
    simp [vecs_length q d w hw]

theorem vecs_lt (q : ℕ) : ∀ (d : ℕ) (v : List ℕ), v ∈ vecs q d → ∀ x ∈ v, x < q
  | 0, v, hv => by simp [vecs] at hv; simp [hv]
  | d + 1, v, hv => by
    simp only [vecs, List.mem_flatMap, List.mem_range, List.mem_map] at hv
    obtain ⟨a, ha, w, hw, rfl⟩ := hv
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact vecs_lt q d w hw x hx

/-! ## Field bounds -/

section Fields
variable (c : Call) (p : Params)

theorem keyFields_length_le (id : ReqId) (hid : id ∈ reqIds c p) : (keyFields id).length ≤ keyLen c p := by
  unfold reqIds at hid
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hid
  unfold keyLen
  rcases hid with ⟨part, _, q, _, κ, hκ, σ, hσ, rfl⟩ | ⟨r, _, hm⟩
  · simp only [keyFields, List.length_append, List.length_cons, List.length_nil]
    have h1 : κ.length = roleCount c.kind * p.J := vecs_length q _ κ hκ
    have h2 : σ.length = roleCount c.kind := vecs_length q _ σ hσ
    rw [h1, h2]; ring_nf; omega
  · simp only [List.mem_singleton] at hm
    rcases hm with ⟨j, _, rfl⟩ | rfl <;> simp [keyFields]

theorem lt_two_pow_size_of_le {x n : ℕ} (h : x ≤ n) : x < 2 ^ Nat.size n :=
  lt_of_le_of_lt h (Nat.lt_size_self n)

/-- Every key field is below `2^keyBits`. -/
theorem keyFields_lt {cT : ℕ} (hs : Spec cT (header c) p) (id : ReqId) (hid : id ∈ reqIds c p) :
    ∀ x ∈ keyFields id, x < 2 ^ keyBits p := by
  have hrc := roleCount_le_two c
  unfold reqIds at hid
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hid
  unfold keyBits
  rcases hid with ⟨part, hpart, q, hq, κ, hκ, σ, hσ, rfl⟩ | ⟨r, hr, hm⟩
  · have hqP : q ≤ p.P := primes_le hs q (by simpa using hq)
    intro x hx
    simp only [keyFields, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
    apply lt_two_pow_size_of_le
    rcases hx with ((rfl | rfl | rfl) | hx) | hx
    · omega
    · unfold partCode; split <;> omega
    · omega
    · have := vecs_lt q _ κ hκ x hx; omega
    · have := vecs_lt q _ σ hσ x hx; omega
  · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hm
    intro x hx
    apply lt_two_pow_size_of_le
    rcases hm with ⟨j, hj, rfl⟩ | rfl
    · simp only [keyFields, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega
    · simp only [keyFields, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega

/-- The key is below `2^{kb·kl}`. -/
theorem reqKey_lt {cT : ℕ} (hs : Spec cT (header c) p) (id : ReqId) (hid : id ∈ reqIds c p) :
    reqKey c p id < 2 ^ (keyBits p * keyLen c p) := by
  unfold reqKey
  rw [radixKey_eq]
  have hlen := keyFields_length_le c p id hid
  have h := rk_lt (keyBits p) (keyFields id ++ List.replicate (keyLen c p - (keyFields id).length) 0) (by
    intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact keyFields_lt c p hs id hid x hx
    · positivity)
  simpa [List.length_append, List.length_replicate, Nat.add_sub_cancel' hlen] using h

end Fields

end NearCubicGates.Close.Cells
