import Proof.Wire_3_5.JoinEliminationRefs
import Proof.Wire_3_5.FilterGapDegree

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.WireExponent3_5.JoinElimination Finset

/-- `Σ_{i<n, i ∈ mask} x_i` over `𝔽₂`. -/
def rowDot {n : ℕ} (m : ℕ) (x : Fin n → ZMod 2) : ZMod 2 := ∑ i : Fin n, if m.testBit i then x i else 0

/-- `x` satisfies the row `(mask, rhs)`. -/
def RowSat {n : ℕ} (x : Fin n → ZMod 2) (r : Row) : Prop := rowDot r.1 x = bitF2 r.2

instance instDecidableRowSat {n : ℕ} (x : Fin n → ZMod 2) (r : Row) : Decidable (RowSat x r) := inferInstanceAs (Decidable (_ = _))

/-- The solutions of a system. -/
def solutions (n : ℕ) (rows : List Row) : Finset (Fin n → ZMod 2) :=
  Finset.univ.filter fun x => ∀ r ∈ rows, RowSat x r

theorem rowDot_xor {n : ℕ} (a b : ℕ) (x : Fin n → ZMod 2) : rowDot (a ^^^ b) x = rowDot a x + rowDot b x := by
  unfold rowDot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_xor]
  have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
  cases a.testBit i <;> cases b.testBit i <;> simp [h2]

theorem bitF2_xor (p q : Bool) : bitF2 (xor p q) = bitF2 p + bitF2 q := by
  cases p <;> cases q <;> decide

/-- The elimination step of `gauss` at column `col` (its local `step`). -/
def gaussStep (st : List Row × ℕ) (col : ℕ) : List Row × ℕ :=
  match st.1.find? (fun r => r.1.testBit col) with
  | none => (st.1, st.2)
  | some piv =>
    ((st.1.erase piv).map (fun r => if r.1.testBit col then (r.1 ^^^ piv.1, xor r.2 piv.2) else r), st.2 + 1)

theorem gauss_eq (n : ℕ) (rows : List Row) :
    gauss n rows = (((List.range n).foldl gaussStep (rows, 0)).1.all (fun r => !(r.1 == 0 && r.2)),
      ((List.range n).foldl gaussStep (rows, 0)).2) := by
  rfl

/-- Flipping coordinate `col`. -/
def flipAt {n : ℕ} (col : Fin n) (x : Fin n → ZMod 2) : Fin n → ZMod 2 := Function.update x col (x col + 1)

theorem flipAt_flipAt {n : ℕ} (col : Fin n) (x : Fin n → ZMod 2) : flipAt col (flipAt col x) = x := by
  funext i
  unfold flipAt
  by_cases h : i = col
  · subst h; simp only [Function.update_self]
    rw [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero]
  · simp [Function.update_of_ne h]

theorem rowDot_flipAt {n : ℕ} (col : Fin n) (x : Fin n → ZMod 2) (m : ℕ) :
    rowDot m (flipAt col x) = rowDot m x + (if m.testBit col then 1 else 0) := by
  unfold rowDot flipAt
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ col), ← Finset.add_sum_erase _ _ (Finset.mem_univ col)]
  have hrest : ∑ i ∈ Finset.univ.erase col, (if m.testBit i then Function.update x col (x col + 1) i else 0) =
      ∑ i ∈ Finset.univ.erase col, (if m.testBit i then x i else 0) :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest, Function.update_self]
  by_cases hb : m.testBit col
  · rw [if_pos hb, if_pos hb, if_pos hb]; ring
  · rw [if_neg hb, if_neg hb, if_neg hb]; ring

/-- Given the pivot's equation, a row with the pivot's column is equivalent to its sum with the pivot. -/
theorem rowSat_xor_iff {n : ℕ} (x : Fin n → ZMod 2) (piv r : Row) (hp : RowSat x piv) :
    RowSat x (r.1 ^^^ piv.1, xor r.2 piv.2) ↔ RowSat x r := by
  unfold RowSat at *
  simp only [rowDot_xor, bitF2_xor, hp]
  constructor <;> intro h
  · have := congrArg (· - bitF2 piv.2) h; simpa using this
  · rw [h]

/-- **One pivot step**: the eliminated system has exactly twice as many solutions. -/
theorem card_solutions_step (n : ℕ) (rows : List Row) (col : Fin n) (piv : Row) (hpiv : piv ∈ rows)
    (hcol : piv.1.testBit col = true) :
    (solutions n ((rows.erase piv).map fun r => if r.1.testBit col then (r.1 ^^^ piv.1, xor r.2 piv.2) else r)).card =
      2 * (solutions n rows).card := by
  set rs' := (rows.erase piv).map fun r => if r.1.testBit col then (r.1 ^^^ piv.1, xor r.2 piv.2) else r
  have hnocol : ∀ r' ∈ rs', r'.1.testBit col = false := by
    intro r' hr'
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hr'
    by_cases h : r.1.testBit col
    · simp [h, Nat.testBit_xor, hcol]
    · simp [h]
  -- solutions of `rows` = solutions of `rs'` that satisfy the pivot
  have hsplit : solutions n rows = (solutions n rs').filter fun x => RowSat x piv := by
    ext x
    simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have hp := hx piv hpiv
      refine ⟨fun r' hr' => ?_, hp⟩
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
      have hr0 := hx r (List.mem_of_mem_erase hr)
      split_ifs
      · exact (rowSat_xor_iff x piv r hp).mpr hr0
      · exact hr0
    · rintro ⟨hx, hp⟩ r hr
      have hperm := List.perm_cons_erase hpiv
      rcases List.mem_cons.mp (hperm.subset hr) with rfl | hre
      · exact hp
      · have := hx _ (List.mem_map_of_mem hre)
        by_cases h : r.1.testBit col
        · rw [if_pos h] at this; exact (rowSat_xor_iff x piv r hp).mp this
        · rw [if_neg h] at this; exact this
  -- the flip at `col` swaps the solutions of `rs'` satisfying and failing the pivot
  have hflip_sat : ∀ x, x ∈ solutions n rs' → flipAt col x ∈ solutions n rs' := by
    intro x hx
    simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro r' hr'
    have := hx r' hr'
    unfold RowSat at this ⊢
    rw [rowDot_flipAt, hnocol r' hr']; simpa using this
  have hflip_piv : ∀ x, RowSat (flipAt col x) piv ↔ ¬ RowSat x piv := by
    intro x
    unfold RowSat
    rw [rowDot_flipAt, hcol, if_pos rfl]
    have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hz (rowDot piv.1 x) with h | h <;> cases piv.2 <;> simp [h, bitF2]
    all_goals decide
  have hcard := Finset.card_filter_add_card_filter_not (s := solutions n rs') (fun x => RowSat x piv)
  have hbij : ((solutions n rs').filter fun x => ¬ RowSat x piv).card =
      ((solutions n rs').filter fun x => RowSat x piv).card := by
    apply Finset.card_bij (fun x _ => flipAt col x)
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hflip_sat x hx.1, (hflip_piv x).mpr hx.2⟩
    · intro a _ b _ h
      have := congrArg (flipAt col) h
      rwa [flipAt_flipAt, flipAt_flipAt] at this
    · intro y hy
      simp only [Finset.mem_filter] at hy
      refine ⟨flipAt col y, ?_, flipAt_flipAt col y⟩
      simp only [Finset.mem_filter]
      refine ⟨hflip_sat y hy.1, ?_⟩
      rw [hflip_piv]; exact not_not.mpr hy.2
  rw [hsplit]
  omega

/-- The invariant of the elimination after columns `< c`: masks below `2^n` and free of the processed columns. -/
def Reduced (n c : ℕ) (rows : List Row) : Prop := ∀ r ∈ rows, r.1 < 2 ^ n ∧ ∀ i < c, r.1.testBit i = false

theorem gaussStep_spec (n c : ℕ) (hc : c < n) (st : List Row × ℕ) (hred : Reduced n c st.1) :
    Reduced n (c + 1) (gaussStep st c).1 ∧
      (solutions n (gaussStep st c).1).card * 2 ^ st.2 = (solutions n st.1).card * 2 ^ (gaussStep st c).2 ∧
      (gaussStep st c).2 ≤ st.2 + 1 := by
  unfold gaussStep
  cases hf : st.1.find? (fun r => r.1.testBit c) with
  | none =>
    dsimp only
    refine ⟨fun r hr => ⟨(hred r hr).1, fun i hi => ?_⟩, rfl, by omega⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact (hred r hr).2 i hlt
    · have := List.find?_eq_none.mp hf r hr; simpa using this
  | some piv =>
    dsimp only
    have hpiv := List.mem_of_find?_eq_some hf
    have hcol : piv.1.testBit c = true := by simpa using List.find?_some hf
    refine ⟨?_, ?_, by omega⟩
    · intro r' hr'
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
      have hr0 := hred r (List.mem_of_mem_erase hr)
      have hp0 := hred piv hpiv
      split_ifs with hrc
      · refine ⟨Nat.xor_lt_two_pow hr0.1 hp0.1, fun i hi => ?_⟩
        rw [Nat.testBit_xor]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · rw [hr0.2 i hlt, hp0.2 i hlt]; rfl
        · rw [hrc, hcol]; rfl
      · refine ⟨hr0.1, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact hr0.2 i hlt
        · simpa using hrc
    · rw [card_solutions_step n st.1 ⟨c, hc⟩ piv hpiv hcol, pow_succ]; ring

theorem fold_spec (n : ℕ) (cs : List ℕ) (c : ℕ) (hcs : cs = List.range' c (n - c)) (hcn : c ≤ n)
    (st : List Row × ℕ) (hred : Reduced n c st.1) :
    Reduced n n (cs.foldl gaussStep st).1 ∧
      (solutions n (cs.foldl gaussStep st).1).card * 2 ^ st.2 =
        (solutions n st.1).card * 2 ^ (cs.foldl gaussStep st).2 ∧
      (cs.foldl gaussStep st).2 ≤ st.2 + (n - c) := by
  induction cs generalizing c st with
  | nil =>
    have hnc : n = c := by
      cases h : n - c with
      | zero => omega
      | succ k => rw [h, List.range'_succ] at hcs; simp at hcs
    subst hnc
    exact ⟨hred, rfl, by simp⟩
  | cons c' cs ih =>
    have hlt : c < n := by
      by_contra hge; have : n - c = 0 := by omega
      rw [this] at hcs; simp at hcs
    have hc' : c' = c ∧ cs = List.range' (c + 1) (n - (c + 1)) := by
      rw [show n - c = (n - (c + 1)) + 1 by omega, List.range'_succ] at hcs
      simp only [List.cons.injEq] at hcs
      exact hcs
    obtain ⟨rfl, hcs'⟩ := hc'
    obtain ⟨hred1, hcard1, hle1⟩ := gaussStep_spec n c' hlt st hred
    obtain ⟨hred2, hcard2, hle2⟩ := ih (c' + 1) hcs' (by omega) (gaussStep st c') hred1
    simp only [List.foldl_cons]
    refine ⟨hred2, ?_, by omega⟩
    -- chain the two multiplicative identities
    set A := (solutions n st.1).card
    set B1 := (solutions n (gaussStep st c').1).card
    set Cf := (solutions n (cs.foldl gaussStep (gaussStep st c')).1).card
    have h2pos : (0 : ℕ) < 2 ^ (gaussStep st c').2 := by positivity
    apply Nat.eq_of_mul_eq_mul_right h2pos
    calc Cf * 2 ^ st.2 * 2 ^ (gaussStep st c').2 = (Cf * 2 ^ (gaussStep st c').2) * 2 ^ st.2 := by ring
      _ = (B1 * 2 ^ (cs.foldl gaussStep (gaussStep st c')).2) * 2 ^ st.2 := by rw [hcard2]
      _ = (B1 * 2 ^ st.2) * 2 ^ (cs.foldl gaussStep (gaussStep st c')).2 := by ring
      _ = (A * 2 ^ (gaussStep st c').2) * 2 ^ (cs.foldl gaussStep (gaussStep st c')).2 := by rw [hcard1]
      _ = A * 2 ^ (cs.foldl gaussStep (gaussStep st c')).2 * 2 ^ (gaussStep st c').2 := by ring

/-- After all columns, every remaining mask is zero. -/
theorem mask_zero_of_reduced (n : ℕ) (rows : List Row) (h : Reduced n n rows) : ∀ r ∈ rows, r.1 = 0 := by
  intro r hr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < n
  · exact (h r hr).2 i hi
  · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (h r hr).1 (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem solutions_of_zero_masks (n : ℕ) (rows : List Row) (h0 : ∀ r ∈ rows, r.1 = 0) :
    solutions n rows = if rows.all (fun r => !(r.1 == 0 && r.2)) then Finset.univ else ∅ := by
  have hdot : ∀ x : Fin n → ZMod 2, rowDot 0 x = 0 := by intro x; simp [rowDot]
  split_ifs with hall
  · ext x
    simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    intro r hr
    have := List.all_eq_true.mp hall r hr
    unfold RowSat; rw [h0 r hr, hdot]
    rw [h0 r hr] at this
    cases hb : r.2
    · rfl
    · rw [hb] at this; exact absurd this (by decide)
  · ext x
    simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro hx
    obtain ⟨r, hr, hbad⟩ : ∃ r ∈ rows, ¬ (!(r.1 == 0 && r.2)) = true := by
      by_contra hno; push Not at hno; exact hall (List.all_eq_true.mpr hno)
    have := hx r hr
    unfold RowSat at this
    rw [h0 r hr, hdot] at this
    rw [h0 r hr] at hbad
    cases hb : r.2
    · rw [hb] at hbad; exact hbad rfl
    · rw [hb] at this; exact absurd this (by decide)

/-- The rank is at most the number of variables. -/
theorem gauss_rank_le (n : ℕ) (rows : List Row) (hmask : ∀ r ∈ rows, r.1 < 2 ^ n) : (gauss n rows).2 ≤ n := by
  rw [gauss_eq]
  have := (fold_spec n (List.range n) 0 (by simp [List.range_eq_range']) (Nat.zero_le _) (rows, 0)
    (fun r hr => ⟨hmask r hr, fun i hi => absurd hi (Nat.not_lt_zero _)⟩)).2.2
  simpa using this

theorem gauss_solutions_card (n : ℕ) (rows : List Row) (hmask : ∀ r ∈ rows, r.1 < 2 ^ n) :
    (solutions n rows).card = if (gauss n rows).1 then 2 ^ (n - (gauss n rows).2) else 0 := by
  have hle := gauss_rank_le n rows hmask
  rw [gauss_eq] at hle ⊢
  obtain ⟨hred, hcard, _⟩ := fold_spec n (List.range n) 0 (by simp [List.range_eq_range']) (Nat.zero_le _)
    (rows, 0) (fun r hr => ⟨hmask r hr, fun i hi => absurd hi (Nat.not_lt_zero _)⟩)
  simp only [pow_zero, mul_one] at hcard
  have h0 := mask_zero_of_reduced n _ hred
  rw [solutions_of_zero_masks n _ h0] at hcard
  set k := ((List.range n).foldl gaussStep (rows, 0)).2
  split_ifs at hcard ⊢ with hc
  · rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
    have : 2 ^ n = 2 ^ (n - k) * 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hle]
    rw [this] at hcard
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) hcard).symm
  · rw [Finset.card_empty] at hcard
    exact (Nat.mul_eq_zero.mp hcard.symm).resolve_right (by positivity)

/-- **Consistency**: the elimination reports a consistent system iff it has a solution. -/
theorem gauss_consistent_iff (n : ℕ) (rows : List Row) (hmask : ∀ r ∈ rows, r.1 < 2 ^ n) :
    (gauss n rows).1 = true ↔ ∃ x : Fin n → ZMod 2, ∀ r ∈ rows, RowSat x r := by
  have hcard := gauss_solutions_card n rows hmask
  constructor
  · intro hc
    rw [if_pos hc] at hcard
    have : (solutions n rows).Nonempty := Finset.card_pos.mp (by rw [hcard]; positivity)
    obtain ⟨x, hx⟩ := this
    exact ⟨x, by simpa [solutions] using hx⟩
  · rintro ⟨x, hx⟩
    by_contra hc
    simp only [Bool.not_eq_true] at hc
    rw [hc] at hcard
    have hmem : x ∈ solutions n rows := by
      simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx
    have h0 : (solutions n rows).card = 0 := by simpa using hcard
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hmem; simp at hmem

theorem gauss_probability (n : ℕ) (rows : List Row) (hmask : ∀ r ∈ rows, r.1 < 2 ^ n) :
    ((solutions n rows).card : ℚ) / 2 ^ n = if (gauss n rows).1 then 1 / 2 ^ (gauss n rows).2 else 0 := by
  rw [gauss_solutions_card n rows hmask]
  have hle := gauss_rank_le n rows hmask
  split_ifs
  · rw [show (2 : ℚ) ^ n = 2 ^ (n - (gauss n rows).2) * 2 ^ (gauss n rows).2 by
      rw [← pow_add, Nat.sub_add_cancel hle]]
    push_cast; field_simp
  · simp

end NearCubicWires.WireExponent3_5.Filters
