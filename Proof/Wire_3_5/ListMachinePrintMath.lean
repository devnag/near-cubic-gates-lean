import Proof.Wire_3_5.ListMachineInterp
import Proof.Wire_3_5.BlockJoin

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Interp
open NearCubicWires.WireExponent3_5.Block

/-! ## Sub-bitmaps -/

/-- The sub-bitmap step's output bit: over a one of `X`, the target bit plus the carry. -/
def gS (t x c : Bool) : Bool := x && xor t c
/-- The sub-bitmap step's carry: it passes the zeros of `X`. -/
def hS (t x c : Bool) : Bool := if x then t && c else c

/-- The sub-bitmap of `xs` whose selected ones are the bits of `j` (bit `k` of `j` selects the `k`-th one). -/
def spread : List Bool → ℕ → List Bool
  | [], _ => []
  | x :: xs, j => if x then (j % 2 == 1) :: spread xs (j / 2) else false :: spread xs j

/-- The number of ones of a bit word. -/
def pop (xs : List Bool) : ℕ := xs.count true

@[simp] theorem spread_length (xs : List Bool) (j : ℕ) : (spread xs j).length = xs.length := by
  induction xs generalizing j with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [spread, ih]

/-- **One sub-bitmap step adds the carry**: `ripple gS hS c (spread xs j) xs = spread xs (j + c)`. -/
theorem ripple_spread (xs : List Bool) (j : ℕ) (c : Bool) :
    ripple gS hS c (spread xs j) xs = spread xs (j + c.toNat) := by
  induction xs generalizing j c with
  | nil => rfl
  | cons x xs ih =>
    cases x
    · simp only [spread, Bool.false_eq_true, ↓reduceIte, ripple, gS, hS, Bool.false_and, ih]
    · simp only [spread, ↓reduceIte, ripple, gS, hS, Bool.true_and, ih]
      congr 1
      · rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> cases c <;> simp [hj, Nat.add_mod]
      · congr 1
        rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> cases c <;> simp [hj] <;> omega

theorem spread_zero (xs : List Bool) : spread xs 0 = List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [spread, ih, List.replicate_succ]

/-- After `2^{|X|}` steps the sub-bitmap is zero again. -/
theorem spread_pow (xs : List Bool) : spread xs (2 ^ pop xs) = List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x
    · simp [spread, pop, ih, List.replicate_succ] at *
    · have e : pop (true :: xs) = pop xs + 1 := by simp [pop]
      rw [e, pow_succ]
      simp only [spread, ↓reduceIte, List.length_cons, List.replicate_succ]
      rw [show 2 ^ pop xs * 2 / 2 = 2 ^ pop xs by omega, ih]
      simp

/-- Below `2^{|X|}` the sub-bitmap has a one exactly when `j ≠ 0`. -/
theorem spread_any (xs : List Bool) (j : ℕ) (hj : j < 2 ^ pop xs) : (spread xs j).any id = decide (j ≠ 0) := by
  induction xs generalizing j with
  | nil =>
    have : j = 0 := by simpa [pop] using hj
    subst this; rfl
  | cons x xs ih =>
    cases x
    · have hj' : j < 2 ^ pop xs := by simpa [pop] using hj
      simpa [spread] using ih j hj'
    · have hj' : j / 2 < 2 ^ pop xs := by
        have e : pop (true :: xs) = pop xs + 1 := by simp [pop]
        rw [e, pow_succ] at hj; omega
      simp only [spread, ↓reduceIte, List.any_cons, id, ih (j / 2) hj']
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      omega

/-! ## The visited points are the points of the sublists -/

/-- The coordinates of the ones of `xs`, counted from `a`. -/
def posFrom : ℕ → List Bool → List ℕ
  | _, [] => []
  | a, x :: xs => if x then a :: posFrom (a + 1) xs else posFrom (a + 1) xs

theorem posFrom_ge (a : ℕ) (xs : List Bool) : ∀ i ∈ posFrom a xs, a ≤ i := by
  induction xs generalizing a with
  | nil => simp [posFrom]
  | cons x xs ih =>
    intro i hi
    cases x
    · simp only [posFrom, Bool.false_eq_true, ↓reduceIte] at hi
      exact Nat.le_of_succ_le (ih (a + 1) i hi)
    · simp only [posFrom, ↓reduceIte, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact le_refl _
      · exact Nat.le_of_succ_le (ih (a + 1) i hi)

theorem range_two_mul (n : ℕ) : List.range (2 * n) = (List.range n).flatMap fun k => [2 * k, 2 * k + 1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ, ih, List.range_succ,
      List.flatMap_append]
    simp

theorem flatMap_congr_mem {α β : Type} (l : List α) (f g : α → List β) (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The points `1_T` on the coordinates `a, …, a+n−1`. -/
def pointFrom (a n : ℕ) (T : List ℕ) : List Bool := (List.range' a n).map fun i => decide (i ∈ T)

theorem pointFrom_cons_notin (a n : ℕ) (T : List ℕ) (hT : a ∉ T) :
    pointFrom a (n + 1) T = false :: pointFrom (a + 1) n T := by
  simp [pointFrom, List.range'_succ, hT]

theorem pointFrom_cons_in (a n : ℕ) (T : List ℕ) :
    pointFrom a (n + 1) (a :: T) = true :: pointFrom (a + 1) n T := by
  simp only [pointFrom, List.range'_succ, List.map_cons, List.mem_cons, true_or, decide_true]
  congr 1
  apply List.map_congr_left
  intro i hi
  have : a < i := by
    rw [List.mem_range'_1] at hi; omega
  simp [Nat.ne_of_gt this]

/-- **The visited points are the points of the sublists of the support, in order.** -/
theorem spread_pointFrom (xs : List Bool) (a : ℕ) :
    (List.range (2 ^ pop xs)).map (spread xs) = (posFrom a xs).sublists.map (pointFrom a xs.length) := by
  induction xs generalizing a with
  | nil => simp [pop, spread, posFrom, pointFrom]
  | cons x xs ih =>
    cases x
    · have ep : pop (false :: xs) = pop xs := by simp [pop]
      rw [ep]
      simp only [posFrom, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hmap : (posFrom (a + 1) xs).sublists.map (pointFrom a (xs.length + 1)) =
          ((posFrom (a + 1) xs).sublists.map (pointFrom (a + 1) xs.length)).map (false :: ·) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro T hT
        have hnot : a ∉ T := fun h =>
          absurd (posFrom_ge (a + 1) xs a ((List.mem_sublists.mp hT).subset h)) (by omega)
        exact pointFrom_cons_notin a xs.length T hnot
      rw [hmap, ← ih (a + 1), List.map_map]
      rfl
    · have ep : pop (true :: xs) = pop xs + 1 := by simp [pop]
      rw [ep, pow_succ, mul_comm, range_two_mul, List.map_flatMap]
      simp only [posFrom, ↓reduceIte, List.length_cons]
      rw [List.sublists_cons, List.bind_eq_flatMap, List.map_flatMap]
      have hL : ∀ k ∈ List.range (2 ^ pop xs), [2 * k, 2 * k + 1].map (spread (true :: xs)) =
          [false :: spread xs k, true :: spread xs k] := by
        intro k _
        have h0 : (2 * k) % 2 = 0 := by omega
        have h1 : (2 * k) / 2 = k := by omega
        have h2 : (2 * k + 1) % 2 = 1 := by omega
        have h3 : (2 * k + 1) / 2 = k := by omega
        simp [spread, h0, h1, h2, h3]
      have hR : ∀ T ∈ (posFrom (a + 1) xs).sublists, [T, a :: T].map (pointFrom a (xs.length + 1)) =
          [false :: pointFrom (a + 1) xs.length T, true :: pointFrom (a + 1) xs.length T] := by
        intro T hT
        have hnot : a ∉ T := fun h =>
          absurd (posFrom_ge (a + 1) xs a ((List.mem_sublists.mp hT).subset h)) (by omega)
        simp [pointFrom_cons_notin a _ T hnot, pointFrom_cons_in]
      rw [flatMap_congr_mem _ _ _ hL, flatMap_congr_mem _ _ _ hR]
      have e2 : (posFrom (a + 1) xs).sublists.flatMap (fun T =>
          [false :: pointFrom (a + 1) xs.length T, true :: pointFrom (a + 1) xs.length T]) =
          ((posFrom (a + 1) xs).sublists.map (pointFrom (a + 1) xs.length)).flatMap
            (fun w => [false :: w, true :: w]) := by rw [List.flatMap_map]
      rw [e2, ← ih (a + 1), List.flatMap_map]

/-! ## The accumulated coefficient -/

theorem supp_cons (x : Bool) (xs : List Bool) :
    supp (x :: xs) = (if x then [0] else []) ++ (supp xs).map (· + 1) := by
  unfold supp
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  cases x <;> simp [Function.comp_def]

theorem posFrom_eq (a : ℕ) (xs : List Bool) : posFrom a xs = (supp xs).map (· + a) := by
  induction xs generalizing a with
  | nil => simp [posFrom, supp]
  | cons x xs ih =>
    rw [supp_cons]
    cases x
    · simp only [posFrom, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.map_map, ih]
      apply List.map_congr_left; intro i _; simp; omega
    · simp only [posFrom, ↓reduceIte, List.cons_append, List.nil_append, List.map_cons, List.map_map, ih]
      simp only [Nat.zero_add, List.cons.injEq, true_and]
      apply List.map_congr_left; intro i _; simp; omega

theorem posFrom_zero (xs : List Bool) : posFrom 0 xs = supp xs := by
  rw [posFrom_eq]; simp

theorem pointFrom_zero (n : ℕ) (T : List ℕ) : pointFrom 0 n T = pointOf n T := by
  simp [pointFrom, pointOf, List.range_eq_range']

/-- **The coefficient the machine accumulates**: the XOR of `f` over the sub-bitmaps `spread xs j`, `j < 2^{|X|}`. -/
theorem subsetX_eq_spread (f : List Bool → Bool) (xs : List Bool) :
    subsetX f xs.length (supp xs) =
      (List.range (2 ^ pop xs)).foldl (fun acc j => xor acc (f (spread xs j))) false := by
  have h := spread_pointFrom xs 0
  rw [posFrom_zero] at h
  unfold subsetX
  have e1 : (supp xs).sublists.foldl (fun acc T => xor acc (f (pointOf xs.length T))) false =
      ((supp xs).sublists.map (pointFrom 0 xs.length)).foldl (fun acc P => xor acc (f P)) false := by
    rw [List.foldl_map]
    congr 1
    funext acc T
    rw [pointFrom_zero]
  rw [e1, ← h, List.foldl_map]

/-! ## Binary words -/

open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.RepairOrdinary.RadixSemantics (value value_lt)
open NearCubicWires.RepairOrdinary.BoundedCounter (binary_of_value)

theorem binary_zero (n : ℕ) : binary n 0 = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binary, ih, List.replicate_succ]

theorem binary_split (a b x y : ℕ) (hx : x < 2 ^ a) :
    binary (a + b) (x + 2 ^ a * y) = binary a x ++ binary b y := by
  induction a generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    subst this; simp [binary]
  | succ a ih =>
    have hx2 : x / 2 < 2 ^ a := by rw [pow_succ] at hx; omega
    rw [show a + 1 + b = (a + b) + 1 by ring]
    have hk : x + 2 ^ (a + 1) * y = x + 2 * (2 ^ a * y) := by ring
    have e1 : (x + 2 ^ (a + 1) * y) % 2 = x % 2 := by rw [hk, Nat.add_mul_mod_self_left]
    have e2 : (x + 2 ^ (a + 1) * y) / 2 = x / 2 + 2 ^ a * y := by
      rw [hk, Nat.add_mul_div_left _ _ (by norm_num)]
    simp only [binary, e1, e2, ih (x / 2) hx2, List.cons_append]

theorem binary_pow (L : ℕ) : binary L (2 ^ L) = List.replicate L false := by
  have := binary_split L 0 0 1 (Nat.two_pow_pos L)
  simp only [Nat.add_zero, Nat.zero_add, mul_one] at this
  rw [this, binary_zero]
  simp [binary]

theorem pop_append (u v : List Bool) : pop (u ++ v) = pop u + pop v := by simp [pop]

theorem pop_binary_zero (n : ℕ) : pop (binary n 0) = 0 := by simp [binary_zero, pop, List.count_replicate]

theorem pop_binary_pos (n r : ℕ) (hr : 0 < r) (hr' : r < 2 ^ n) : 0 < pop (binary n r) := by
  by_contra h
  have h0 : pop (binary n r) = 0 := by omega
  have hz : binary n r = List.replicate n false := by
    apply List.eq_replicate_iff.mpr
    refine ⟨binary_length n r, fun b hb => ?_⟩
    cases b
    · rfl
    · exact absurd (List.count_pos_iff.mpr hb) (by simp [pop] at h0; omega)
  have := binary_value n r hr'
  rw [hz, ← binary_zero, binary_value n 0 (Nat.two_pow_pos n)] at this
  omega

/-- Adding one raises the number of ones by at most one. -/
theorem pop_binary_succ_le (n X : ℕ) : pop (binary n (X + 1)) ≤ pop (binary n X) + 1 := by
  induction n generalizing X with
  | zero => simp [binary, pop]
  | succ n ih =>
    rcases Nat.mod_two_eq_zero_or_one X with h | h
    · have e1 : (X + 1) % 2 = 1 := by omega
      have e2 : (X + 1) / 2 = X / 2 := by omega
      simp [binary, pop, h, e1, e2]
    · have e1 : (X + 1) % 2 = 0 := by omega
      have e2 : (X + 1) / 2 = X / 2 + 1 := by omega
      have := ih (X / 2)
      simp only [binary, pop, h, e1, e2] at this ⊢
      simp at this ⊢
      omega

/-- Adding one to an odd number does not raise the number of ones. -/
theorem pop_binary_succ_odd (n X : ℕ) (hX : X % 2 = 1) (hn : 0 < n) : pop (binary n (X + 1)) ≤ pop (binary n X) := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have e1 : (X + 1) % 2 = 0 := by omega
  have e2 : (X + 1) / 2 = X / 2 + 1 := by omega
  have := pop_binary_succ_le n (X / 2)
  simp only [binary, pop, hX, e1, e2] at this ⊢
  simp at this ⊢
  omega

/-! ## The outer loop: the supports of size `≤ d`, increasing -/

/-- The lowest-one mask's output bit (`s`: a one was seen). -/
def gL (x _ s : Bool) : Bool := x && !s
def hL (x _ s : Bool) : Bool := s || x

theorem ripple_gL_true (u v : List Bool) : ripple gL hL true u v = List.replicate (min u.length v.length) false := by
  induction u generalizing v with
  | nil => cases v <;> rfl
  | cons x u ih =>
    cases v with
    | nil => rfl
    | cons y v => simp [ripple, gL, hL, ih, List.replicate_succ, Nat.succ_min_succ]

/-- **The lowest-one mask** of `2^v·m` (`m` odd) is `2^v`. -/
theorem lowmask_binary (L v m : ℕ) (hm : m % 2 = 1) (hX : 2 ^ v * m < 2 ^ L) :
    ripple gL hL false (binary L (2 ^ v * m)) (binary L (2 ^ v * m)) = binary L (2 ^ v) := by
  induction v generalizing L with
  | zero =>
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := by
      rcases L with _ | L
      · simp at hX; omega
      · exact ⟨L, rfl⟩
    simp only [pow_zero, one_mul]
    have hb : binary (L + 1) m = true :: binary L (m / 2) := by simp [binary, hm]
    have hb1 : binary (L + 1) 1 = true :: binary L 0 := by simp [binary]
    rw [hb, hb1]
    simp [ripple, gL, hL, ripple_gL_true, binary_zero]
  | succ v ih =>
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := by
      rcases L with _ | L
      · have h1 := Nat.one_le_two_pow (n := v + 1)
        have h2 : 1 ≤ m := by omega
        simp at hX
        nlinarith
      · exact ⟨L, rfl⟩
    have hk : 2 ^ (v + 1) * m = 2 * (2 ^ v * m) := by ring
    have hk1 : 2 ^ (v + 1) = 2 * 2 ^ v := by ring
    have hX' : 2 ^ v * m < 2 ^ L := by rw [hk, pow_succ] at hX; omega
    have hb : binary (L + 1) (2 ^ (v + 1) * m) = false :: binary L (2 ^ v * m) := by
      rw [hk]; simp [binary, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (show 0 < 2 by norm_num)]
    have hb1 : binary (L + 1) (2 ^ (v + 1)) = false :: binary L (2 ^ v) := by
      rw [hk1]; simp [binary, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (show 0 < 2 by norm_num)]
    rw [hb, hb1]
    simp only [ripple, gL, hL, Bool.false_and, Bool.or_false]
    rw [ih L hX']

/-- **The machine's successor word**: add the lowest one when the word has `d` ones, else add one. -/
def sw (d : ℕ) (xs : List Bool) : List Bool :=
  if pop xs = d then ripple sum3 carry3 false xs (ripple gL hL false xs xs)
  else ripple sum3 carry3 true xs (List.replicate xs.length false)

/-- A good bitmap: at most `d` ones. -/
def good (L d X : ℕ) : Prop := pop (binary L X) ≤ d

instance (L d X : ℕ) : Decidable (good L d X) := inferInstanceAs (Decidable (_ ≤ _))

/-- The good bitmaps, increasing. -/
def goods (L d : ℕ) : List ℕ := (List.range (2 ^ L)).filter fun X => decide (good L d X)

theorem pop_split (v w r m : ℕ) (hr : r < 2 ^ v) :
    pop (binary (v + w) (r + 2 ^ v * m)) = pop (binary v r) + pop (binary w m) := by
  rw [binary_split v w r m hr, pop_append]

/-- **The successor**: from a good `X`, the word `sw d (binary L X)` is the next good bitmap, or `2^L` (zero) when
there is none; nothing good is skipped. -/
theorem sw_next (L d X : ℕ) (hd : 1 ≤ d) (hX : X < 2 ^ L) (hg : good L d X) :
    ∃ Y, sw d (binary L X) = binary L Y ∧ X < Y ∧ Y ≤ 2 ^ L ∧ (∀ Z, X < Z → Z < Y → ¬ good L d Z) ∧
      (Y < 2 ^ L → good L d Y) := by
  unfold sw
  by_cases hp : pop (binary L X) = d
  · rw [if_pos hp]
    have hX0 : X ≠ 0 := by
      intro h0; subst h0; rw [pop_binary_zero] at hp; omega
    obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hX0
    have hmo : m % 2 = 1 := Nat.odd_iff.mp hm
    have hm1 : 1 ≤ m := by omega
    have hvL : v < L := by
      by_contra hc
      have : 2 ^ L ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith [Nat.two_pow_pos v]
    obtain ⟨w, rfl⟩ : ∃ w, L = v + w := ⟨L - v, by omega⟩
    have hw : 0 < w := by omega
    have hmw : m < 2 ^ w := by
      rw [pow_add] at hX
      exact Nat.lt_of_mul_lt_mul_left hX
    rw [lowmask_binary (v + w) v m hmo hX, ripple_add]
    refine ⟨2 ^ v * m + 2 ^ v, by simp, by have := Nat.two_pow_pos v; omega, ?_, ?_, ?_⟩
    · rw [pow_add]
      have : m + 1 ≤ 2 ^ w := hmw
      nlinarith [Nat.two_pow_pos v]
    · intro Z h1 h2 hgZ
      obtain ⟨r, rfl⟩ : ∃ r, Z = 2 ^ v * m + r := ⟨Z - 2 ^ v * m, by omega⟩
      have hr0 : 0 < r := by omega
      have hrv : r < 2 ^ v := by omega
      have e := pop_split v w r m hrv
      have e0 := pop_split v w 0 m (Nat.two_pow_pos v)
      rw [Nat.zero_add, pop_binary_zero, Nat.zero_add] at e0
      have hpos := pop_binary_pos v r hr0 hrv
      unfold good at hgZ
      rw [show 2 ^ v * m + r = r + 2 ^ v * m by ring, e] at hgZ
      rw [e0] at hp
      omega
    · intro _
      unfold good
      have e := pop_split v w 0 (m + 1) (Nat.two_pow_pos v)
      rw [Nat.zero_add, pop_binary_zero, Nat.zero_add] at e
      have e0 := pop_split v w 0 m (Nat.two_pow_pos v)
      rw [Nat.zero_add, pop_binary_zero, Nat.zero_add] at e0
      rw [show 2 ^ v * m + 2 ^ v = 2 ^ v * (m + 1) by ring, e]
      have := pop_binary_succ_odd w m hmo hw
      rw [e0] at hp
      omega
  · rw [if_neg hp]
    have hz : List.replicate (binary L X).length false = binary L 0 := by rw [binary_length, binary_zero]
    rw [hz, ripple_add]
    refine ⟨X + 1, by simp, by omega, by omega, fun Z h1 h2 => absurd h2 (by omega), fun _ => ?_⟩
    unfold good at hg ⊢
    have := pop_binary_succ_le L X
    omega

theorem goods_pairwise (L d : ℕ) : (goods L d).Pairwise (· < ·) := List.pairwise_lt_range.filter _

theorem mem_goods {L d X : ℕ} : X ∈ goods L d ↔ X < 2 ^ L ∧ good L d X := by
  simp [goods]

theorem goods_lt_of_lt {L d : ℕ} {i j : ℕ} (hi : i < (goods L d).length) (hj : j < (goods L d).length)
    (h : (goods L d)[i] < (goods L d)[j]) : i < j := by
  by_contra hc
  rcases Nat.lt_or_eq_of_le (Nat.not_lt.mp hc) with h' | h'
  · have := List.pairwise_iff_getElem.mp (goods_pairwise L d) j i hj hi h'
    omega
  · subst h'; omega

theorem goods_zero (L d : ℕ) : ∃ h : 0 < (goods L d).length, (goods L d)[0] = 0 := by
  have hmem : 0 ∈ goods L d := mem_goods.mpr ⟨Nat.two_pow_pos L, by unfold good; rw [pop_binary_zero]; omega⟩
  have hpos : 0 < (goods L d).length := List.length_pos_of_mem hmem
  refine ⟨hpos, ?_⟩
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hmem
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact hgi
  · have := List.pairwise_iff_getElem.mp (goods_pairwise L d) 0 i hpos hi hi0
    omega

/-- **The outer loop visits the good bitmaps in increasing order, then wraps to zero.** -/
theorem sw_iterate (L d : ℕ) (hd : 1 ≤ d) :
    (∀ k (hk : k < (goods L d).length), (sw d)^[k] (binary L 0) = binary L (goods L d)[k]) ∧
      (sw d)^[(goods L d).length] (binary L 0) = binary L 0 := by
  obtain ⟨h0len, h0⟩ := goods_zero L d
  have key : ∀ k (hk : k < (goods L d).length), (sw d)^[k] (binary L 0) = binary L (goods L d)[k] := by
    intro k
    induction k with
    | zero => intro hk; simp [h0]
    | succ k ih =>
      intro hk
      have hk' : k < (goods L d).length := by omega
      rw [Function.iterate_succ_apply', ih hk']
      set X := (goods L d)[k] with hXdef
      have hXm := mem_goods.mp (List.getElem_mem hk')
      obtain ⟨Y, hY, hXY, hYL, hgap, hgood⟩ := sw_next L d X hd hXm.1 hXm.2
      rw [hY]
      congr 1
      have hNm := mem_goods.mp (List.getElem_mem hk)
      have hXN : X < (goods L d)[k + 1] :=
        List.pairwise_iff_getElem.mp (goods_pairwise L d) k (k + 1) hk' hk (by omega)
      have hNY : Y ≤ (goods L d)[k + 1] := by
        by_contra hc
        exact hgap _ hXN (by omega) hNm.2
      have hYL' : Y < 2 ^ L := by omega
      obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem (mem_goods.mpr ⟨hYL', hgood hYL'⟩)
      have hki : k < i := goods_lt_of_lt hk' hi (by rw [hgi]; exact hXY)
      have : (goods L d)[k + 1] ≤ (goods L d)[i] := by
        rcases Nat.lt_or_eq_of_le (show k + 1 ≤ i by omega) with h' | h'
        · exact (List.pairwise_iff_getElem.mp (goods_pairwise L d) (k + 1) i hk hi h').le
        · subst h'; exact le_refl _
      omega
  refine ⟨key, ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, (goods L d).length = n + 1 := ⟨(goods L d).length - 1, by omega⟩
  have hlast : n < (goods L d).length := by omega
  rw [hn, Function.iterate_succ_apply', key n hlast]
  set X := (goods L d)[n]
  have hXm := mem_goods.mp (List.getElem_mem hlast)
  obtain ⟨Y, hY, hXY, hYL, _, hgood⟩ := sw_next L d X hd hXm.1 hXm.2
  rw [hY]
  rcases Nat.lt_or_eq_of_le hYL with hlt | heq
  · obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem (mem_goods.mpr ⟨hlt, hgood hlt⟩)
    have := goods_lt_of_lt hlast hi (by rw [hgi]; exact hXY)
    omega
  · rw [heq, binary_pow, binary_zero]

theorem supp_length (bs : List Bool) : (supp bs).length = pop bs := by
  induction bs with
  | nil => simp [supp, pop]
  | cons x xs ih => rw [supp_cons]; cases x <;> simp [pop, ih] at *

theorem filterMap_ite {α β : Type} (l : List α) (p : α → Bool) (f : α → β) :
    l.filterMap (fun x => if p x then some (f x) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons x l ih => cases h : p x <;> simp [h, ih]

/-- **The supports the machine visits are `Interp.monos`.** -/
theorem monos_eq_goods (L d : ℕ) : monos L d = (goods L d).map fun X => supp (binary L X) := by
  unfold monos goods
  have e : (fun X => if (supp (binary L X)).length ≤ d then some (supp (binary L X)) else none) =
      (fun X => if decide (good L d X) then some (supp (binary L X)) else none) := by
    funext X
    simp [good, supp_length]
  rw [e, filterMap_ite]

end NearCubicWires.WireExponent3_5.ListMachine.Interp
