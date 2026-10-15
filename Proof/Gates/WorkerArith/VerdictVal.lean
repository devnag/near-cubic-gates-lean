import Proof.Gates.Worker.VerdictSpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Worker
open NearCubicGates.Close.Interfaces (listWord bitWord outputWord ratWord)

/-! ## The word as naturals -/

def sgnN (z : ℤ) : ℕ := if z < 0 then 1 else 0
def ratN (x : ℚ) : List ℕ := [sgnN x.num, x.num.natAbs, x.den]
def bitN (b : Bool) : ℕ := if b then 1 else 0
def termN (x : Bool × (ℚ × ℚ)) : List ℕ := bitN x.1 :: (ratN x.2.1 ++ ratN x.2.2)

/-- The fields of the request word. -/
def nats (r : VerdictReq) : List ℕ := [r.q, r.M, r.N, r.rb, r.cl, r.I.length] ++ r.I.flatMap termN

theorem termN_length (x : Bool × (ℚ × ℚ)) : (termN x).length = 7 := rfl

theorem ratWord_eq (x : ℚ) : ratWord x = (ratN x).flatMap natWord := by
  simp [ratWord, ratN, NearCubicGates.Close.Interfaces.intWord, sgnN]

theorem termWord_eq (x : Bool × (ℚ × ℚ)) : bitWord x.1 ++ outputWord x.2 = (termN x).flatMap natWord := by
  simp [termN, bitWord, outputWord, ratWord_eq, bitN]

theorem verdictWord_eq (r : VerdictReq) : verdictWord r = (nats r).flatMap natWord := by
  simp only [verdictWord, nats, listWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]
  congr 1; congr 1; congr 1; congr 1; congr 1; congr 1
  induction r.I with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.flatMap_append, ih, ← termWord_eq x, List.append_assoc]

theorem nats_length (r : VerdictReq) : (nats r).length = 6 + 7 * r.I.length := by
  simp only [nats, List.length_append, List.length_cons, List.length_nil, List.length_flatMap, termN_length]
  simp [List.sum_replicate, List.map_const']; omega

/-! ## Field access -/

theorem flatMap_getD7 {α : Type} (f : α → List ℕ) (hf : ∀ x, (f x).length = 7) (d : α) :
    ∀ (l : List α) (i j : ℕ), i < l.length → j < 7 → (l.flatMap f).getD (7 * i + j) 0 = (f (l.getD i d)).getD j 0
  | [], i, _, hi, _ => by simp at hi
  | x :: l, 0, j, _, hj => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
    rw [List.getD_append _ _ _ _ (by rw [hf]; exact hj)]
  | x :: l, i + 1, j, hi, hj => by
    simp only [List.flatMap_cons, List.getD_cons_succ]
    rw [List.getD_append_right _ _ _ _ (by rw [hf]; omega), hf]
    rw [show 7 * (i + 1) + j - 7 = 7 * i + j by omega]
    exact flatMap_getD7 f hf d l i j (by simpa using hi) hj

/-- The default term. -/
def dT : Bool × (ℚ × ℚ) := (false, (0, 0))

/-- Field `j` of term `i` sits at index `6 + 7i + j`. -/
theorem nats_term (r : VerdictReq) (i j : ℕ) (hi : i < r.I.length) (hj : j < 7) :
    (nats r).getD (6 + 7 * i + j) 0 = (termN (r.I.getD i dT)).getD j 0 := by
  unfold nats
  rw [List.getD_append_right _ _ _ _ (by simp; omega), show 6 + 7 * i + j - [r.q, r.M, r.N, r.rb, r.cl, r.I.length].length =
    7 * i + j by simp only [List.length_cons, List.length_nil]; omega]
  exact flatMap_getD7 termN termN_length dT r.I i j hi hj

/-- Splitting a concatenation at field `k`. -/
theorem flatMap_split {α β : Type} (f : α → List β) (l : List α) (k : ℕ) (d : α) (hk : k < l.length) :
    l.flatMap f = (l.take k).flatMap f ++ f (l.getD k d) ++ (l.drop (k + 1)).flatMap f := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  conv_lhs => rw [← List.take_append_drop k l, List.drop_eq_getElem_cons hk]
  rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem take_succ_flatMap {α β : Type} (f : α → List β) (l : List α) (k : ℕ) (d : α) (hk : k < l.length) :
    (l.take (k + 1)).flatMap f = (l.take k).flatMap f ++ f (l.getD k d) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.flatMap_append]
  simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk, Option.getD_some]

/-! ## Bounds -/

theorem natWord_len (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by
  simp [natWord, WilliamsPublishedForm.framedNatBits, WilliamsPublishedForm.fixedWidthNatBits]; omega

theorem lt_two_pow_nbl (v : ℕ) : v < 2 ^ natBitLength v := by
  unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) v

theorem len_le_flatMap {l : List ℕ} {v : ℕ} (hv : v ∈ l) : (natWord v).length ≤ (l.flatMap natWord).length := by
  induction l with
  | nil => simp at hv
  | cons x l ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 hv with rfl | h
    · omega
    · have := ih h; omega

/-- Every field has at most `L` bits. -/
theorem field_nbl (r : VerdictReq) {v : ℕ} (hv : v ∈ nats r) : natBitLength v ≤ (verdictWord r).length := by
  have := len_le_flatMap hv
  rw [natWord_len, ← verdictWord_eq] at this; omega

theorem field_lt (r : VerdictReq) {v : ℕ} (hv : v ∈ nats r) : v < 2 ^ (verdictWord r).length :=
  lt_of_lt_of_le (lt_two_pow_nbl v) (Nat.pow_le_pow_right (by norm_num) (field_nbl r hv))

theorem getD_mem (l : List ℕ) (k : ℕ) (hk : k < l.length) : l.getD k 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk

theorem mem_nats_term (r : VerdictReq) (i j : ℕ) (hi : i < r.I.length) (hj : j < 7) :
    (termN (r.I.getD i dT)).getD j 0 ∈ nats r := by
  rw [← nats_term r i j hi hj]; apply getD_mem; rw [nats_length]; omega

/-- The word is at least six fields long, and every term takes seven fields of at least three bits. -/
theorem len_ge (r : VerdictReq) : 21 * r.I.length + 6 ≤ (verdictWord r).length := by
  rw [verdictWord_eq]
  have key : ∀ l : List ℕ, 3 * l.length ≤ (l.flatMap natWord).length := by
    intro l; induction l with
    | nil => simp
    | cons x l ih =>
      have : 1 ≤ natBitLength x := by unfold natBitLength; omega
      simp only [List.flatMap_cons, List.length_append, List.length_cons, natWord_len]; omega
  have := key (nats r); rw [nats_length] at this; omega

/-! ## Endpoints over the common denominator -/

theorem den_dvd_pow (q L : ℕ) (x : ℚ) (hx : (x * 2 ^ (q + 1)).den = 1) (hd : x.den < 2 ^ L) : x.den ∣ 2 ^ L := by
  have hz : ((x * 2 ^ (q + 1)).num : ℚ) = x * 2 ^ (q + 1) := Rat.coe_int_num_of_den_eq_one hx
  have e : x = Rat.divInt (x * 2 ^ (q + 1)).num ((2 : ℤ) ^ (q + 1)) := by
    rw [Rat.divInt_eq_div, hz]; push_cast; field_simp
  have h1 := Rat.den_dvd (x * 2 ^ (q + 1)).num ((2 : ℤ) ^ (q + 1))
  rw [← e] at h1
  have h1' : x.den ∣ 2 ^ (q + 1) := by exact_mod_cast h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1'
  rw [hj] at hd ⊢
  apply Nat.pow_dvd_pow 2
  by_contra h
  have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_of_not_le h)
  omega

/-! ## Contributions: the sum as `POS − NEG` -/

/-- `|num|·(D/den)`: the endpoint's magnitude over the denominator `D`. -/
def mag (D : ℕ) (x : ℚ) : ℕ := x.num.natAbs * (D / x.den)

/-- The endpoint `x` with sign flag `f` (`f` = negate) goes to `POS` or to `NEG`. -/
def posC (D : ℕ) (f : Bool) (x : ℚ) : ℕ := if xor (decide (x.num < 0)) f then 0 else mag D x
def negC (D : ℕ) (f : Bool) (x : ℚ) : ℕ := if xor (decide (x.num < 0)) f then mag D x else 0

def sgnQ (f : Bool) : ℚ := if f then -1 else 1

theorem mul_D (D : ℕ) (x : ℚ) (h : x.den ∣ D) : x * D = x.num * ((D / x.den : ℕ) : ℚ) := by
  obtain ⟨k, hk⟩ := h
  rw [hk, Nat.mul_div_cancel_left _ x.den_pos, Nat.cast_mul, ← mul_assoc, Rat.mul_den_eq_num]

theorem natAbs_cast (n : ℤ) : ((n.natAbs : ℕ) : ℚ) = |(n : ℚ)| := by exact_mod_cast (Nat.cast_natAbs n)

theorem pos_sub_neg (D : ℕ) (f : Bool) (x : ℚ) (h : x.den ∣ D) :
    ((posC D f x : ℚ) - negC D f x) = sgnQ f * (x * D) := by
  rw [mul_D D x h]
  unfold posC negC mag sgnQ
  by_cases hn : x.num < 0
  · have hq : (x.num : ℚ) < 0 := by exact_mod_cast hn
    have ha : ((x.num.natAbs : ℕ) : ℚ) = -(x.num : ℚ) := by rw [natAbs_cast, abs_of_neg hq]
    have hd : decide (x.num < 0) = true := decide_eq_true hn
    cases f <;> simp only [hd, Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_mul, Nat.cast_zero, ha] <;> ring
  · have hq : (0 : ℚ) ≤ x.num := by exact_mod_cast (not_lt.1 hn)
    have ha : ((x.num.natAbs : ℕ) : ℚ) = (x.num : ℚ) := by rw [natAbs_cast, abs_of_nonneg hq]
    have hd : decide (x.num < 0) = false := decide_eq_false hn
    cases f <;> simp only [hd, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_mul, Nat.cast_zero, ha] <;> ring

/-- `σ_t` as a flag: `true` iff `tenSigns t = −1`. -/
def fsOf (i : ℕ) : Bool := decide (tenSigns ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩ = -1)

theorem tenSigns_q (i : ℕ) : ((tenSigns ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩ : ℤ) : ℚ) = sgnQ (fsOf i) := by
  unfold fsOf sgnQ
  rcases tenSigns_cases ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩ with h | h <;> simp [h]

/-- A term `(b, (p, κ))` with sign flag `fs`: `σ·(flipI x).1 + (flipI x).2 = σ·[b] + (σ·(−1)^b)·p + κ`. -/
def posT (D : ℕ) (fs : Bool) (x : Bool × (ℚ × ℚ)) : ℕ :=
  (if (x.1 && !fs) then D else 0) + posC D (xor fs x.1) x.2.1 + posC D false x.2.2
def negT (D : ℕ) (fs : Bool) (x : Bool × (ℚ × ℚ)) : ℕ :=
  (if (x.1 && fs) then D else 0) + negC D (xor fs x.1) x.2.1 + negC D false x.2.2

theorem term_eq (D : ℕ) (fs : Bool) (x : Bool × (ℚ × ℚ)) (h1 : x.2.1.den ∣ D) (h2 : x.2.2.den ∣ D) :
    ((posT D fs x : ℚ) - negT D fs x) = (sgnQ fs * (flipI x).1 + (flipI x).2) * D := by
  have e1 := pos_sub_neg D (xor fs x.1) x.2.1 h1
  have e2 := pos_sub_neg D false x.2.2 h2
  unfold posT negT flipI
  unfold sgnQ at e1 e2 ⊢
  rcases x with ⟨b, p, k⟩
  cases b <;> cases fs <;> simp at e1 e2 ⊢ <;> linarith

def posS (D : ℕ) (I : List (Bool × (ℚ × ℚ))) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, posT D (fsOf i) (I.getD i dT)
def negS (D : ℕ) (I : List (Bool × (ℚ × ℚ))) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, negT D (fsOf i) (I.getD i dT)

theorem list_sum_range (f : ℕ → ℚ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The sum of `upperL`, times `D`, is `POS − NEG`. -/
theorem sum_eq_pos_sub_neg (D : ℕ) (I : List (Bool × (ℚ × ℚ))) (hdvd : ∀ x ∈ I, x.2.1.den ∣ D ∧ x.2.2.den ∣ D) :
    ((List.range I.length).map fun i => ((tenSigns ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩ : ℚ) *
      (flipI (I.getD i (false, (0, 0)))).1 + (flipI (I.getD i (false, (0, 0)))).2)).sum * D =
      (posS D I I.length : ℚ) - negS D I I.length := by
  rw [list_sum_range, Finset.sum_mul]
  unfold posS negS
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < I.length := Finset.mem_range.1 hi
  have hm : I.getD i dT ∈ I := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; exact List.getElem_mem hi'
  rw [term_eq D (fsOf i) _ (hdvd _ hm).1 (hdvd _ hm).2]
  rw [tenSigns_q i]; rfl

/-- **The acceptance test as one comparison of naturals.** With `γ − εT = c/e` and `Y = 2·max M 1·D`:
`upperL M I < γ − εT ⟺ (e + c⁻)·Y + e·POS < c⁺·Y + e·NEG`. -/
theorem upper_test (γ εT : ℚ) (M : ℕ) (I : List (Bool × (ℚ × ℚ))) (hlen : I.length = 10 * M) (D : ℕ) (hD : 0 < D)
    (hdvd : ∀ x ∈ I, x.2.1.den ∣ D ∧ x.2.2.den ∣ D) :
    upperL M I < γ - εT ↔
      ((γ - εT).den + (-(γ - εT).num).toNat) * (2 * max M 1 * D) + (γ - εT).den * posS D I (10 * M) <
        (γ - εT).num.toNat * (2 * max M 1 * D) + (γ - εT).den * negS D I (10 * M) := by
  set c := (γ - εT).num with hc
  set e := (γ - εT).den with he
  have hce : γ - εT = (c : ℚ) / e := (Rat.num_div_den _).symm
  have he0 : (0 : ℚ) < e := by positivity
  have hcc : ((c.toNat : ℕ) : ℚ) - (((-c).toNat : ℕ) : ℚ) = c := by
    have : ((c.toNat : ℕ) : ℤ) - (((-c).toNat : ℕ) : ℤ) = c := by omega
    exact_mod_cast this
  have hsum := sum_eq_pos_sub_neg D I hdvd
  set S := ((List.range I.length).map fun i => ((tenSigns ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩ : ℚ) *
      (flipI (I.getD i (false, (0, 0)))).1 + (flipI (I.getD i (false, (0, 0)))).2)).sum with hS
  have hU : upperL M I = 1 + S / (2 * M) := rfl
  rw [hlen] at hsum
  set P := posS D I (10 * M)
  set Q := negS D I (10 * M)
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  rw [hU, hce]
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · subst h0
    rw [show max 0 1 = 1 from rfl, ← Nat.cast_lt (α := ℚ)]
    push_cast
    have hI : I = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    have hS0 : S = 0 := by rw [hS, hI]; simp
    have hP : (P : ℚ) - Q = 0 := by rw [← hsum, hS0, zero_mul]
    simp only [hS0, Nat.cast_zero, mul_zero, div_zero, add_zero, max_eq_right (Nat.zero_le 1), Nat.cast_one]
    rw [lt_div_iff₀ he0]
    have key : (((e : ℚ) + ((-c).toNat : ℚ)) * (2 * 1 * D) + e * P) - ((c.toNat : ℚ) * (2 * 1 * D) + e * Q) =
        (2 * D) * (e - c) := by
      rw [← hcc]; linear_combination (e : ℚ) * hP
    constructor
    · intro h
      have : (2 * D : ℚ) * (e - c) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
      linarith
    · intro h
      by_contra hn
      have : (0 : ℚ) ≤ (2 * D : ℚ) * (e - c) := mul_nonneg (by positivity) (by linarith)
      linarith
  · have hm : max M 1 = M := max_eq_left hpos
    rw [hm, ← Nat.cast_lt (α := ℚ)]
    push_cast
    have hM : (0 : ℚ) < M := by exact_mod_cast hpos
    rw [show (1 : ℚ) + S / (2 * M) = (2 * M + S) / (2 * M) by field_simp, div_lt_div_iff₀ (by positivity) he0]
    have key : (((e : ℚ) + ((-c).toNat : ℚ)) * (2 * M * D) + e * P) - ((c.toNat : ℚ) * (2 * M * D) + e * Q) =
        D * ((2 * M + S) * e - c * (2 * M)) := by
      have : (P : ℚ) = Q + S * D := by linarith
      rw [this, ← hcc]; ring
    constructor
    · intro h
      have : D * ((2 * M + S) * e - c * (2 * M)) < 0 := mul_neg_of_pos_of_neg hD' (by linarith)
      linarith
    · intro h
      by_contra hn
      have : (0 : ℚ) ≤ D * ((2 * M + S) * e - c * (2 * M)) := mul_nonneg hD'.le (by linarith)
      linarith

/-- **The guard `γ < εT·N^{10}`** as one comparison of naturals. -/
theorem guard_test (γ εT : ℚ) (X : ℕ) :
    γ < εT * X ↔ (γ.num * εT.den).toNat + (-(εT.num * γ.den)).toNat * X <
      (-(γ.num * εT.den)).toNat + (εT.num * γ.den).toNat * X := by
  set u := γ.num * εT.den
  set v := εT.num * γ.den
  have hb : (0 : ℚ) < γ.den := by positivity
  have hk : (0 : ℚ) < εT.den := by positivity
  have hγ : γ = (γ.num : ℚ) / γ.den := (Rat.num_div_den _).symm
  have hε : εT = (εT.num : ℚ) / εT.den := (Rat.num_div_den _).symm
  have hu : ((u.toNat : ℕ) : ℚ) - (((-u).toNat : ℕ) : ℚ) = u := by
    have : ((u.toNat : ℕ) : ℤ) - (((-u).toNat : ℕ) : ℤ) = u := by omega
    exact_mod_cast this
  have hv : ((v.toNat : ℕ) : ℚ) - (((-v).toNat : ℕ) : ℚ) = v := by
    have : ((v.toNat : ℕ) : ℤ) - (((-v).toNat : ℕ) : ℤ) = v := by omega
    exact_mod_cast this
  rw [← Nat.cast_lt (α := ℚ)]
  push_cast
  have e1 : γ < εT * X ↔ (u : ℚ) < v * X := by
    rw [hγ, hε]
    simp only [u, v]
    push_cast
    rw [div_lt_iff₀ hb, show (εT.num : ℚ) / εT.den * X * γ.den = εT.num * γ.den * X / εT.den by ring,
      lt_div_iff₀ hk]
  rw [e1]
  have hvX : (v : ℚ) * X = ((v.toNat : ℕ) : ℚ) * X - (((-v).toNat : ℕ) : ℚ) * X := by rw [← hv]; ring
  constructor <;> intro h <;> linarith

end NearCubicGates.Close.WorkerArith
