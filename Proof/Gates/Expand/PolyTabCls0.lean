import Proof.Gates.Expand.PolyTabMain

/-! # PolyTab cost classes: the `Λ`-class combinators

`Λ r = 2^k·(1 + V·m_T)^D` (`D` the formula degree, `m_T` as in the printing condition). The printing condition gives
`Λ^100 ≤ 2^(s+1)` (**`lam_pow_le`**), so a cost in **`LCls a`** (`≤ C·Λ^a·tabSz^e`) with `a ≤ 100` is in the
tabulation class `TabCls` (**`tabCls_of_lcls`**). Closure under `+` (`max` degree), `·` (sum of degrees), powers,
constants, monotonicity; atoms: `tabSz`, `n, k, s, B, G, V, D`, `m_T`, `2^k`, the monomial count. -/

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.CounterMachine

/-- The printing condition's base. -/
def mTr (r : TabReq) : ℕ := Tabulator.mT r.s (r.B + Nat.clog 2 (r.n + 1))

def Xr (r : TabReq) : ℕ := 1 + r.V * mTr r

/-- **Λ.** -/
def Lam (r : TabReq) : ℕ := 2 ^ r.k * Xr r ^ r.F.degree

theorem Xr_pos (r : TabReq) : 1 ≤ Xr r := by unfold Xr; omega
theorem Lam_pos (r : TabReq) : 1 ≤ Lam r := Nat.one_le_iff_ne_zero.mpr (by unfold Lam; have := Xr_pos r; positivity)

theorem lam_pow_le (r : TabReq) : Lam r ^ 100 ≤ 2 * 2 ^ r.s := by
  have h := r.hc
  unfold PrintCondition at h
  have h1 : Lam r ≤ 2 ^ (r.k + 2) * (1 + r.V * mTr r) ^ r.F.degree := by
    unfold Lam Xr
    have : 2 ^ r.k ≤ 2 ^ (r.k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.mul_le_mul_right _ this
  have h2 : Lam r ^ 100 ≤ 2 ^ (r.s + r.s % 2) := le_trans (Nat.pow_le_pow_left h1 100) h
  have h3 : 2 ^ (r.s + r.s % 2) ≤ 2 * 2 ^ r.s := by
    rw [pow_add]
    have h4 : 2 ^ (r.s % 2) ≤ 2 := by
      calc 2 ^ (r.s % 2) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    nlinarith [Nat.one_le_two_pow (n := r.s)]
  omega

theorem tabSz_pos (r : TabReq) : 1 ≤ tabSz r := by unfold tabSz; omega

/-- **The Λ-class of degree `a`.** -/
def LCls (a : ℕ) (f : TabReq → ℕ) : Prop := ∃ C e : ℕ, ∀ r, f r ≤ C * Lam r ^ a * tabSz r ^ e

theorem tabCls_of_lcls {a : ℕ} {f : TabReq → ℕ} (h : LCls a f) (ha : a ≤ 100) : TabCls f := by
  obtain ⟨C, e, hf⟩ := h
  refine ⟨2 * C, e, fun r => ?_⟩
  have h1 : Lam r ^ a ≤ Lam r ^ 100 := Nat.pow_le_pow_right (Lam_pos r) ha
  have h2 := lam_pow_le r
  calc f r ≤ C * Lam r ^ a * tabSz r ^ e := hf r
    _ ≤ C * (2 * 2 ^ r.s) * tabSz r ^ e := by gcongr; exact h1.trans h2
    _ = 2 * C * 2 ^ r.s * tabSz r ^ e := by ring

theorem lc_mono {a : ℕ} {f g : TabReq → ℕ} (h : LCls a f) (hg : ∀ r, g r ≤ f r) : LCls a g := by
  obtain ⟨C, e, hf⟩ := h; exact ⟨C, e, fun r => (hg r).trans (hf r)⟩

theorem lc_up {a b : ℕ} {f : TabReq → ℕ} (h : LCls a f) (hab : a ≤ b) : LCls b f := by
  obtain ⟨C, e, hf⟩ := h
  exact ⟨C, e, fun r => (hf r).trans (by gcongr; exact Lam_pos r)⟩

theorem lc_const (c : ℕ) : LCls 0 (fun _ => c) :=
  ⟨c, 0, fun _ => by simp⟩

theorem lc_tabSz : LCls 0 tabSz := ⟨1, 1, fun _ => by simp⟩

theorem lc_lam : LCls 1 Lam := ⟨1, 0, fun _ => by simp⟩

theorem lc_add {a b : ℕ} {f g : TabReq → ℕ} (hf : LCls a f) (hg : LCls b g) :
    LCls (max a b) (fun r => f r + g r) := by
  obtain ⟨C1, e1, h1⟩ := hf
  obtain ⟨C2, e2, h2⟩ := hg
  refine ⟨C1 + C2, e1 + e2, fun r => ?_⟩
  have hl := Lam_pos r
  have ht := tabSz_pos r
  have a1 : Lam r ^ a ≤ Lam r ^ max a b := Nat.pow_le_pow_right hl (le_max_left _ _)
  have a2 : Lam r ^ b ≤ Lam r ^ max a b := Nat.pow_le_pow_right hl (le_max_right _ _)
  have t1 : tabSz r ^ e1 ≤ tabSz r ^ (e1 + e2) := Nat.pow_le_pow_right ht (by omega)
  have t2 : tabSz r ^ e2 ≤ tabSz r ^ (e1 + e2) := Nat.pow_le_pow_right ht (by omega)
  calc f r + g r ≤ C1 * Lam r ^ a * tabSz r ^ e1 + C2 * Lam r ^ b * tabSz r ^ e2 := Nat.add_le_add (h1 r) (h2 r)
    _ ≤ C1 * Lam r ^ max a b * tabSz r ^ (e1 + e2) + C2 * Lam r ^ max a b * tabSz r ^ (e1 + e2) := by gcongr
    _ = (C1 + C2) * Lam r ^ max a b * tabSz r ^ (e1 + e2) := by ring

theorem lc_mul {a b : ℕ} {f g : TabReq → ℕ} (hf : LCls a f) (hg : LCls b g) :
    LCls (a + b) (fun r => f r * g r) := by
  obtain ⟨C1, e1, h1⟩ := hf
  obtain ⟨C2, e2, h2⟩ := hg
  refine ⟨C1 * C2, e1 + e2, fun r => ?_⟩
  calc f r * g r ≤ (C1 * Lam r ^ a * tabSz r ^ e1) * (C2 * Lam r ^ b * tabSz r ^ e2) := Nat.mul_le_mul (h1 r) (h2 r)
    _ = C1 * C2 * Lam r ^ (a + b) * tabSz r ^ (e1 + e2) := by ring

theorem lc_pow {a : ℕ} {f : TabReq → ℕ} (hf : LCls a f) (m : ℕ) : LCls (a * m) (fun r => f r ^ m) := by
  induction m with
  | zero => simpa using lc_const 1
  | succ m ih =>
    have := lc_mul ih hf
    simpa [pow_succ, Nat.mul_succ] using this

theorem lc_sub {a : ℕ} {f : TabReq → ℕ} (hf : LCls a f) (c : ℕ) : LCls a (fun r => f r - c) :=
  lc_mono hf (fun _ => Nat.sub_le _ _)

theorem lc_div {a : ℕ} {f : TabReq → ℕ} (hf : LCls a f) (c : ℕ) : LCls a (fun r => f r / c) :=
  lc_mono hf (fun _ => Nat.div_le_self _ _)

/-- An atom bounded by a polynomial in `tabSz`. -/
theorem lc_poly {f : TabReq → ℕ} (h : ∃ C e : ℕ, ∀ r, f r ≤ C * tabSz r ^ e) : LCls 0 f := by
  obtain ⟨C, e, hf⟩ := h; exact ⟨C, e, fun r => by simpa using hf r⟩

theorem lc_le_tabSz {f : TabReq → ℕ} (h : ∀ r, f r ≤ tabSz r) : LCls 0 f := lc_mono lc_tabSz h

theorem le_tabSz_n (r : TabReq) : r.n ≤ tabSz r := by unfold tabSz; omega
theorem le_tabSz_G (r : TabReq) : r.G ≤ tabSz r := by unfold tabSz; omega
theorem le_tabSz_B (r : TabReq) : r.B ≤ tabSz r := by unfold tabSz; omega
theorem le_tabSz_V (r : TabReq) : r.V ≤ tabSz r := by unfold tabSz; omega
theorem le_tabSz_w (r : TabReq) : r.F.weight ≤ tabSz r := by unfold tabSz; omega
theorem le_tabSz_fw (r : TabReq) : (formulaWord ⟨r.V, r.F⟩).length ≤ tabSz r := by unfold tabSz; omega
theorem le_tabSz_size (r : TabReq) : r.F.size ≤ tabSz r := by unfold tabSz; omega

theorem k_add_s (r : TabReq) : r.k + r.s = r.n := by
  have := Fintype.card_congr r.layout; simp at this; omega

theorem le_tabSz_k (r : TabReq) : r.k ≤ tabSz r := by have := k_add_s r; have := le_tabSz_n r; omega
theorem le_tabSz_s (r : TabReq) : r.s ≤ tabSz r := by have := k_add_s r; have := le_tabSz_n r; omega

theorem degree_le_weight {V : ℕ} : ∀ F : Formula V, F.degree ≤ F.weight
  | .const _ => by simp [Formula.degree]
  | .var _ => by simp [Formula.degree, Formula.weight]
  | .add f g => by have := degree_le_weight f; have := degree_le_weight g; simp [Formula.degree, Formula.weight]; omega
  | .neg f => by have := degree_le_weight f; simp [Formula.degree, Formula.weight]; omega
  | .sub f g => by have := degree_le_weight f; have := degree_le_weight g; simp [Formula.degree, Formula.weight]; omega
  | .mul f g => by have := degree_le_weight f; have := degree_le_weight g; simp [Formula.degree, Formula.weight]; omega
  | .pow f e => by have := degree_le_weight f; simp [Formula.degree, Formula.weight]; exact Nat.mul_le_mul_left _ this

theorem le_tabSz_D (r : TabReq) : r.F.degree ≤ tabSz r := (degree_le_weight r.F).trans (le_tabSz_w r)

theorem lc_two_pow_k : LCls 1 (fun r => 2 ^ r.k) :=
  lc_mono lc_lam (fun r => by
    unfold Lam; exact Nat.le_mul_of_pos_right _ (Nat.one_le_iff_ne_zero.mpr (by have := Xr_pos r; positivity)))

theorem clog_le' (x : ℕ) : Nat.clog 2 (x + 1) ≤ x := by
  rcases Nat.lt_or_ge x 1 with h | h
  · interval_cases x; simp
  · exact Nat.clog_le_of_le_pow (by
      calc x + 1 ≤ 2 ^ x := Nat.lt_two_pow_self
        _ = 2 ^ x := rfl)

theorem mTr_le (r : TabReq) : mTr r ≤ 4 * (tabSz r + 1) ^ 3 := by
  unfold mTr Tabulator.mT Tabulator.blockBits
  have h1 := clog_le' r.n
  have h2 := clog_le' r.s
  have hs := le_tabSz_s r
  have hB := le_tabSz_B r
  have hn := le_tabSz_n r
  have h3 : (r.s + 1) / 2 ≤ tabSz r + 1 := by omega
  have h4 : r.B + Nat.clog 2 (r.n + 1) + Nat.clog 2 (r.s + 1) + 1 ≤ 3 * (tabSz r + 1) := by omega
  have h5 : r.s ≤ tabSz r + 1 := by omega
  calc 1 + (r.B + Nat.clog 2 (r.n + 1) + Nat.clog 2 (r.s + 1) + 1) * r.s * ((r.s + 1) / 2)
      ≤ 1 + (3 * (tabSz r + 1)) * (tabSz r + 1) * (tabSz r + 1) := by gcongr
    _ ≤ 4 * (tabSz r + 1) ^ 3 := by nlinarith [Nat.one_le_pow 3 (tabSz r + 1) (by omega)]

theorem lc_mTr : LCls 0 mTr :=
  lc_poly ⟨32, 3, fun r => by
    have := mTr_le r; have ht := tabSz_pos r
    calc mTr r ≤ 4 * (tabSz r + 1) ^ 3 := this
      _ ≤ 4 * (2 * tabSz r) ^ 3 := by gcongr; omega
      _ = 32 * tabSz r ^ 3 := by ring⟩

theorem lc_nbl {a : ℕ} {f : TabReq → ℕ} (hf : LCls a f) : LCls a (fun r => natBitLength (f r)) := by
  have h := lc_add hf (lc_const 1)
  simp only [Nat.max_zero] at h
  exact lc_mono h (fun r => by unfold natBitLength; have := Nat.log_le_self 2 (f r); omega)

theorem lc_two_pow_nbl {a : ℕ} {f : TabReq → ℕ} (hf : LCls a f) : LCls a (fun r => 2 ^ natBitLength (f r)) := by
  have h := lc_add (lc_mul (lc_const 2) hf) (lc_const 2)
  simp only [Nat.zero_add, Nat.max_zero] at h
  refine lc_mono h (fun r => ?_)
  unfold natBitLength
  rcases Nat.eq_zero_or_pos (f r) with h0 | h0
  · rw [h0]; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h0)
    rw [pow_succ]; omega

theorem lc_of_ex {b : ℕ} {f : TabReq → ℕ} (h : ∃ a, LCls a f ∧ a ≤ b) : LCls b f := by
  obtain ⟨a, h, ha⟩ := h; exact lc_up h ha

/-- Decompose a cost into `+`, `·`, constant powers, `-`, `/` down to the atoms in the context. -/
syntax "lcs" : tactic
macro_rules
  | `(tactic| lcs) => `(tactic| first
      | with_reducible exact lc_const _
      | with_reducible assumption
      | (with_reducible apply lc_add <;> lcs)
      | (with_reducible apply lc_mul <;> lcs)
      | (with_reducible apply lc_pow <;> lcs)
      | (with_reducible apply lc_sub <;> lcs)
      | (with_reducible apply lc_div <;> lcs)
      | (with_reducible apply lc_two_pow_nbl <;> lcs)
      | (with_reducible apply lc_nbl <;> lcs)
      | skip)

/-- Prove `LCls b f` by decomposition (`lcs`) and a numeric degree check. -/
macro "lcs_to" : tactic =>
  `(tactic| (apply lc_of_ex; apply Exists.intro; constructor; lcs; all_goals norm_num))

end NearCubicGates.Close.Expand.PolyTab
