import SourceAdapters.RAMTrace.Basic

/-!
# `lem:trace-gadgets`: the arithmetic gadgets of (T4) and the incrementers of (T10)

`app:event-trace` `lem:trace-gadgets`: under (G), (a) every assignment of the auxiliary slots satisfying the gadget equations has
the canonical values (sum, difference, borrow `[X < Y]`, and, zero test), and (b) for all inputs the canonical
carries/borrows/prefix-ors satisfy them. Both directions are one `iff` per gadget, over Boolean bit functions.
Chains are stated with the catalog's storage convention: carry slot `k j` holds the carry INTO bit `j + 1`
(`cin k c0 j` is the carry into bit `j`, `c0` at `j = 0`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open BitVec

/-- The carry into bit `j`: `c0` at `j = 0`, the stored carry `k (j − 1)` otherwise. -/
def cin (k : ℕ → Bool) (c0 : Bool) (j : ℕ) : Bool := if j = 0 then c0 else k (j - 1)

@[simp] theorem cin_zero (k : ℕ → Bool) (c0 : Bool) : cin k c0 0 = c0 := rfl
@[simp] theorem cin_succ (k : ℕ → Bool) (c0 : Bool) (j : ℕ) : cin k c0 (j + 1) = k j := rfl

/-- The full-adder carry over `F₂` is the majority. -/
theorem maj_eq (a b c : Bool) : (Bool.xor (Bool.xor (a && b) (a && c)) (b && c)) = Bool.atLeastTwo a b c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xor_eq_false_iff (a b : Bool) : Bool.xor a b = false ↔ a = b := by
  cases a <;> cases b <;> simp

/-! ## Carry chains -/

/-- A stored carry chain satisfies the full-adder recurrence iff it is the binary carry of `X + Y + c0`. -/
theorem carry_chain_iff {w : ℕ} (X Y : BitVec w) (c0 : Bool) (k : ℕ → Bool) (m : ℕ) :
    (∀ j < m, k j = Bool.atLeastTwo (X.getLsbD j) (Y.getLsbD j) (cin k c0 j)) ↔
      ∀ j < m, k j = carry (j + 1) X Y c0 := by
  constructor
  · intro h
    have key : ∀ j < m, k j = carry (j + 1) X Y c0 := by
      intro j
      induction j with
      | zero => intro hj; rw [h 0 hj, carry_succ]; simp
      | succ j ih => intro hj; rw [h (j + 1) hj, carry_succ, cin_succ, ih (by omega)]
    exact key
  · intro h j hj
    rw [h j hj, carry_succ]
    rcases j with _ | j
    · simp
    · rw [cin_succ, h j (by omega)]

/-- The carry into bit `j` of a canonical chain. -/
theorem cin_carry {w : ℕ} (X Y : BitVec w) (c0 : Bool) (k : ℕ → Bool) (m j : ℕ) (hj : j ≤ m)
    (h : ∀ j < m, k j = carry (j + 1) X Y c0) : cin k c0 j = carry j X Y c0 := by
  rcases j with _ | j
  · simp
  · rw [cin_succ, h j (by omega)]

/-- **Ripple-carry sum.** Sum bits `s j = X_j ⊕ Y_j ⊕ c_j` and stored carries `k` (`j < m`, with `n ≤ m + 1`) satisfy
the chain iff they are the bits and carries of `X + Y + c0`. -/
theorem ripple_iff {w : ℕ} (X Y : BitVec w) (c0 : Bool) (s k : ℕ → Bool) (n m : ℕ) (hn : n ≤ w)
    (hnm : n ≤ m + 1) :
    ((∀ j < n, s j = Bool.xor (Bool.xor (X.getLsbD j) (Y.getLsbD j)) (cin k c0 j)) ∧
      ∀ j < m, k j = Bool.atLeastTwo (X.getLsbD j) (Y.getLsbD j) (cin k c0 j)) ↔
    ((∀ j < n, s j = (X + Y + setWidth w (ofBool c0)).getLsbD j) ∧ ∀ j < m, k j = carry (j + 1) X Y c0) := by
  rw [carry_chain_iff]
  constructor
  · rintro ⟨hs, hk⟩
    refine ⟨fun j hj => ?_, hk⟩
    rw [hs j hj, getLsbD_add_add_bool (by omega), cin_carry X Y c0 k m j (by omega) hk, Bool.xor_assoc]
  · rintro ⟨hs, hk⟩
    refine ⟨fun j hj => ?_, hk⟩
    rw [hs j hj, getLsbD_add_add_bool (by omega), cin_carry X Y c0 k m j (by omega) hk, Bool.xor_assoc]

/-! ## The adder, subtractor, and zero test of (T4) -/

/-- (T4) adder: `AD[j] = X[j] + Y[j] + ca_j` (`j < w`), `ca_{j+1} = maj` (`j + 1 < w`). -/
theorem adder_iff {w : ℕ} (X Y : BitVec w) (ad ca : ℕ → Bool) :
    ((∀ j < w, ad j = Bool.xor (Bool.xor (X.getLsbD j) (Y.getLsbD j)) (cin ca false j)) ∧
      ∀ j, j + 1 < w → ca j = Bool.atLeastTwo (X.getLsbD j) (Y.getLsbD j) (cin ca false j)) ↔
    ((∀ j < w, ad j = (X + Y).getLsbD j) ∧ ∀ j, j + 1 < w → ca j = carry (j + 1) X Y false) := by
  have h := ripple_iff X Y false ad ca w (w - 1) le_rfl (by omega)
  have e1 : (∀ j, j + 1 < w → ca j = Bool.atLeastTwo (X.getLsbD j) (Y.getLsbD j) (cin ca false j)) ↔
      ∀ j < w - 1, ca j = Bool.atLeastTwo (X.getLsbD j) (Y.getLsbD j) (cin ca false j) :=
    ⟨fun h j hj => h j (by omega), fun h j hj => h j (by omega)⟩
  have e2 : (∀ j, j + 1 < w → ca j = carry (j + 1) X Y false) ↔ ∀ j < w - 1, ca j = carry (j + 1) X Y false :=
    ⟨fun h j hj => h j (by omega), fun h j hj => h j (by omega)⟩
  rw [e1, e2, h]
  simp

/-- The borrow recurrence of (T4) is the negated carry recurrence of `X + ~~~Y + 1`. -/
theorem borrow_eq (x y b : Bool) :
    Bool.xor ((!x) && Bool.xor y b) (y && b) = !Bool.atLeastTwo x (!y) (!b) := by
  cases x <;> cases y <;> cases b <;> rfl

/-- (T4) subtractor: `SB[j] = X[j] + Y[j] + bo_j` (`j < w`), `bo_{j+1} = (1 + X[j])(Y[j] + bo_j) + Y[j]bo_j`
(`j < w`; `bo_w` is kept) iff `SB = X − Y` and `bo_{j+1} = [X mod 2^{j+1} < Y mod 2^{j+1}]`, i.e. the negated carry of
`X + ~~~Y + 1`; in particular `bo_w = [X < Y]`. -/
theorem subtractor_iff {w : ℕ} (X Y : BitVec w) (sb bo : ℕ → Bool) :
    ((∀ j < w, sb j = Bool.xor (Bool.xor (X.getLsbD j) (Y.getLsbD j)) (cin bo false j)) ∧
      ∀ j < w, bo j = Bool.xor ((!X.getLsbD j) && Bool.xor (Y.getLsbD j) (cin bo false j))
        (Y.getLsbD j && cin bo false j)) ↔
    ((∀ j < w, sb j = (X - Y).getLsbD j) ∧ ∀ j < w, bo j = !carry (j + 1) X (~~~Y) true) := by
  -- pass to the complemented chain `k j = !bo j`
  set k : ℕ → Bool := fun j => !bo j with hk
  have hcin : ∀ j, cin bo false j = !cin k true j := by
    intro j; rcases j with _ | j <;> simp [cin, hk]
  have hsub : X - Y = X + ~~~Y + setWidth w (ofBool true) := by
    rw [sub_eq_add_neg, neg_eq_not_add, BitVec.add_assoc]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  have h := ripple_iff X (~~~Y) true sb k w w le_rfl (by omega)
  rw [← hsub] at h
  have e1 : (∀ j < w, sb j = Bool.xor (Bool.xor (X.getLsbD j) (Y.getLsbD j)) (cin bo false j)) ↔
      ∀ j < w, sb j = Bool.xor (Bool.xor (X.getLsbD j) ((~~~Y).getLsbD j)) (cin k true j) := by
    refine forall_congr' fun j => forall_congr' fun hj => ?_
    rw [hcin, getLsbD_not]
    simp only [hj, decide_true, Bool.true_and]
    cases X.getLsbD j <;> cases Y.getLsbD j <;> cases cin k true j <;> simp
  have e2 : (∀ j < w, bo j = Bool.xor ((!X.getLsbD j) && Bool.xor (Y.getLsbD j) (cin bo false j))
        (Y.getLsbD j && cin bo false j)) ↔
      ∀ j < w, k j = Bool.atLeastTwo (X.getLsbD j) ((~~~Y).getLsbD j) (cin k true j) := by
    refine forall_congr' fun j => forall_congr' fun hj => ?_
    rw [hcin, borrow_eq, getLsbD_not]
    simp only [Bool.not_not, hj, decide_true, Bool.true_and]
    have hkj : k j = !bo j := rfl
    rw [hkj]
    generalize X.getLsbD j = a
    generalize Y.getLsbD j = b
    generalize cin k true j = c
    cases hb : bo j <;> cases a <;> cases b <;> cases c <;> simp
  have e3 : (∀ j < w, bo j = !carry (j + 1) X (~~~Y) true) ↔ ∀ j < w, k j = carry (j + 1) X (~~~Y) true := by
    refine forall_congr' fun j => forall_congr' fun _ => ?_
    simp only [hk]
    cases bo j <;> cases carry (j + 1) X (~~~Y) true <;> simp
  rw [e1, e2, e3, h]

/-- The final borrow is `[X < Y]` (the uniqueness part of `lem:trace-gadgets`). -/
theorem final_borrow {w : ℕ} (X Y : BitVec w) (hw : 1 ≤ w) :
    (!carry (w - 1 + 1) X (~~~Y) true) = decide (X.toNat < Y.toNat) := by
  rw [Nat.sub_add_cancel hw, ← ult_eq_not_carry, BitVec.ult]

/-- The prefix-or of the bits `0, …, j`. -/
def prefixOr (s : ℕ → Bool) (j : ℕ) : Bool := (List.range (j + 1)).any s

theorem prefixOr_zero (s : ℕ → Bool) : prefixOr s 0 = s 0 := by simp [prefixOr]

theorem prefixOr_succ (s : ℕ → Bool) (j : ℕ) : prefixOr s (j + 1) = (prefixOr s j || s (j + 1)) := by
  simp [prefixOr, List.range_succ, List.any_append, Bool.or_assoc]

theorem prefixOr_iff (s : ℕ → Bool) (j : ℕ) : prefixOr s j = true ↔ ∃ i ≤ j, s i = true := by
  simp only [prefixOr, List.any_eq_true, List.mem_range]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩, fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩⟩

/-- The or of two bits over `F₂`: `a + b + ab`. -/
theorem or_eq_xor (a b : Bool) : (a || b) = Bool.xor (Bool.xor a b) (a && b) := by
  cases a <;> cases b <;> rfl

/-- (T4) zero test: `oz_0 = SB[0]`, `oz_j = oz_{j−1} + SB[j] + oz_{j−1}SB[j]` iff `oz` is the prefix-or of `SB`. -/
theorem prefixOr_chain_iff (s oz : ℕ → Bool) (n : ℕ) :
    (oz 0 = s 0 ∧ ∀ j, 1 ≤ j → j < n → oz j = Bool.xor (Bool.xor (oz (j - 1)) (s j)) (oz (j - 1) && s j)) ↔
    (oz 0 = s 0 ∧ ∀ j, 1 ≤ j → j < n → oz j = prefixOr s j) := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    have key : ∀ j < n, oz j = prefixOr s j := by
      intro j
      induction j with
      | zero => intro _; rw [h0, prefixOr_zero]
      | succ j ih =>
        intro hj
        rw [h (j + 1) (by omega) hj, Nat.add_sub_cancel, ih (by omega), prefixOr_succ, or_eq_xor]
    exact fun j _ hj => key j hj
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun j hj1 hj => ?_⟩
    have hprev : oz (j - 1) = prefixOr s (j - 1) := by
      rcases Nat.eq_or_lt_of_le hj1 with h1 | h1
      · rw [← h1]; simp [h0, prefixOr_zero]
      · exact h (j - 1) (by omega) (by omega)
    have hs := prefixOr_succ s (j - 1)
    rw [Nat.sub_add_cancel hj1] at hs
    rw [h j hj1 hj, hprev, ← or_eq_xor, hs]

/-- A word is nonzero iff the prefix-or of all its bits is set. -/
theorem prefixOr_ne_zero {w : ℕ} (v : BitVec w) (hw : 1 ≤ w) :
    prefixOr v.getLsbD (w - 1) = decide (v ≠ 0) := by
  have key : (prefixOr v.getLsbD (w - 1) = true) ↔ v ≠ 0 := by
    rw [prefixOr_iff]
    constructor
    · rintro ⟨i, hi, h⟩ hv
      rw [hv] at h; simp at h
    · intro hv
      by_contra hc
      apply hv
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      cases hb : v.getLsbD i
      · simp
      · exact absurd ⟨i, by omega, hb⟩ hc
  by_cases hv : v = 0
  · have : prefixOr v.getLsbD (w - 1) ≠ true := fun h => key.mp h hv
    simp only [ne_eq, Bool.not_eq_true] at this
    rw [this]; simp [hv]
  · have : prefixOr v.getLsbD (w - 1) = true := key.mpr hv
    rw [this]; simpa using hv

end NearCubicGates.Adapters.RAMTrace
