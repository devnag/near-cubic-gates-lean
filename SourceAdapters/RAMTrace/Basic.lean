import SourceAdapters.RAMTrace.Defs
import Mathlib.Algebra.CharP.Two

/-!
# Event trace: bits, sums over the code, words (`app:event-trace`, preliminaries)

- `eval_boolF`, `eval_of_bits`: under (G) an equation with coefficients in `{0, 1}` takes the value of its Boolean
  evaluation (`+` = exclusive or, `·` = and) in any ring of characteristic two (the Boolean equations of `def:event-trace`).
- `evalB_sumCode_single`: a sum over the code whose terms vanish off one position is that term (the evaluation of
  the linear forms `e(Q)` under one-hot decoding, `lem:trace-step` (ii)).
- `bvOf`: the `w`-bit word with given bits (least significant first).
- `decode_iff`: `lem:trace-step` (ii), the prefix-or decoding of (T2).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr

/-! ## Bits of a ring of characteristic two -/

/-- `0` or `1` of a ring. -/
def boolF {F : Type} [CommRing F] (b : Bool) : F := if b then 1 else 0

section Transfer

variable {F : Type} [CommRing F] [CharP F 2]

theorem one_ne_zero_char2 : (1 : F) ≠ 0 :=
  haveI := CharP.nontrivial_of_char_ne_one (R := F) (v := 2) (by norm_num)
  one_ne_zero

theorem boolF_xor (p q : Bool) : boolF (F := F) (Bool.xor p q) = boolF p + boolF q := by
  cases p <;> cases q <;> simp [boolF, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem boolF_and (p q : Bool) : boolF (F := F) (p && q) = boolF p * boolF q := by
  cases p <;> cases q <;> simp [boolF]

theorem boolF_eq_zero (p : Bool) : boolF (F := F) p = 0 ↔ p = false := by
  cases p <;> simp [boolF, one_ne_zero_char2]

theorem boolF_eq_one (p : Bool) : boolF (F := F) p = 1 ↔ p = true := by
  cases p <;> simp [boolF, (one_ne_zero_char2 (F := F)).symm]

theorem boolF_inj (p q : Bool) : boolF (F := F) p = boolF q ↔ p = q := by
  cases p <;> cases q <;> simp [boolF, one_ne_zero_char2, (one_ne_zero_char2 (F := F)).symm]

omit [CharP F 2] in
theorem isBit_boolF (p : Bool) : IsBit (boolF (F := F) p) := by
  cases p <;> simp [boolF, IsBit]

open Classical in
theorem boolF_decide_of_isBit {z : F} (h : IsBit z) : boolF (decide (z = 1)) = z := by
  rcases h with h | h
  · subst h; simp [boolF, (one_ne_zero_char2 (F := F)).symm]
  · subst h; simp [boolF]

/-- The value of an expression at a bit assignment is its Boolean value. -/
theorem eval_boolF {ι : Type} (v : ι → Bool) (e : Expr ι) :
    e.eval (fun i => boolF (F := F) (v i)) = boolF (e.evalB v) := by
  induction e with
  | zero => simp [Expr.eval, Expr.evalB, boolF]
  | one => simp [Expr.eval, Expr.evalB, boolF]
  | var i => rfl
  | add a b iha ihb => simp only [Expr.eval, Expr.evalB, iha, ihb, boolF_xor]
  | mul a b iha ihb => simp only [Expr.eval, Expr.evalB, iha, ihb, boolF_and]

open Classical in
/-- Under Booleanity of the variables read, the value of an expression is its Boolean value. -/
theorem eval_of_bits {ι : Type} (val : ι → F) (e : Expr ι) (h : ∀ i ∈ e.vars, IsBit (val i)) :
    e.eval val = boolF (e.evalB fun i => decide (val i = 1)) := by
  induction e with
  | zero => simp [Expr.eval, Expr.evalB, boolF]
  | one => simp [Expr.eval, Expr.evalB, boolF]
  | var i =>
    simp only [Expr.eval, Expr.evalB]
    exact (boolF_decide_of_isBit (h i (by simp [Expr.vars]))).symm
  | add a b iha ihb =>
    simp only [Expr.vars, List.mem_append] at h
    simp only [Expr.eval, Expr.evalB, iha (fun i hi => h i (Or.inl hi)), ihb (fun i hi => h i (Or.inr hi)),
      boolF_xor]
  | mul a b iha ihb =>
    simp only [Expr.vars, List.mem_append] at h
    simp only [Expr.eval, Expr.evalB, iha (fun i hi => h i (Or.inl hi)), ihb (fun i hi => h i (Or.inr hi)),
      boolF_and]

end Transfer

/-! ## Boolean evaluation of sums -/

section Sums

variable {ι : Type}

@[simp] theorem evalB_zero (v : ι → Bool) : (Expr.zero : Expr ι).evalB v = false := rfl
@[simp] theorem evalB_one (v : ι → Bool) : (Expr.one : Expr ι).evalB v = true := rfl
@[simp] theorem evalB_var (v : ι → Bool) (i : ι) : (Expr.var i).evalB v = v i := rfl
@[simp] theorem evalB_add (v : ι → Bool) (a b : Expr ι) :
    (Expr.add a b).evalB v = Bool.xor (a.evalB v) (b.evalB v) := rfl
@[simp] theorem evalB_mul (v : ι → Bool) (a b : Expr ι) :
    (Expr.mul a b).evalB v = (a.evalB v && b.evalB v) := rfl
@[simp] theorem evalB_bit (v : ι → Bool) (b : Bool) : (Expr.bit b : Expr ι).evalB v = b := by
  cases b <;> rfl
@[simp] theorem evalB_compl (v : ι → Bool) (a : Expr ι) : (Expr.compl a).evalB v = !a.evalB v := by
  simp [Expr.compl]
@[simp] theorem evalB_maj (v : ι → Bool) (a b c : Expr ι) :
    (Expr.maj a b c).evalB v = Bool.xor (Bool.xor (a.evalB v && b.evalB v) (a.evalB v && c.evalB v))
      (b.evalB v && c.evalB v) := rfl

theorem evalB_sum (v : ι → Bool) (l : List (Expr ι)) :
    (Expr.sum l).evalB v = l.foldr (fun a acc => Bool.xor (a.evalB v) acc) false := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Expr.sum, ih]

/-- A sum over the code whose terms all vanish. -/
theorem evalB_sumCode_none {α : Type} (f : ℕ → α → Expr ι) (v : ι → Bool) :
    ∀ (l : List α) (p0 : ℕ), (∀ p I, p0 ≤ p → p < p0 + l.length → (f p I).evalB v = false) →
      (sumCode f p0 l).evalB v = false
  | [], _, _ => rfl
  | I :: l, p0, h => by
    simp only [sumCode, evalB_add, h p0 I le_rfl (by simp), Bool.false_xor]
    exact evalB_sumCode_none f v l (p0 + 1) fun p I hp hp' => h p I (by omega) (by simp; omega)

/-- A sum over the code whose terms vanish off position `pc` is its term at `pc`. -/
theorem evalB_sumCode_single {α : Type} (f : ℕ → α → Expr ι) (v : ι → Bool) (pc : ℕ) :
    ∀ (l : List α) (p0 : ℕ) (h1 : p0 ≤ pc) (h2 : pc < p0 + l.length),
      (∀ p I, p0 ≤ p → p < p0 + l.length → p ≠ pc → (f p I).evalB v = false) →
      (sumCode f p0 l).evalB v = (f pc (l[pc - p0]'(by omega))).evalB v
  | [], _, _, h2, _ => by simp at h2; omega
  | I :: l, p0, h1, h2, h => by
    simp only [sumCode, evalB_add]
    rcases Nat.lt_or_ge p0 pc with hlt | hge
    · rw [h p0 I le_rfl (by simp) (by omega), Bool.false_xor]
      rw [evalB_sumCode_single f v pc l (p0 + 1) (by omega) (by simp at h2; omega)
        (fun p I hp hp' hne => h p I (by omega) (by simp; omega) hne)]
      have : pc - p0 = (pc - (p0 + 1)) + 1 := by omega
      simp only [this, List.getElem_cons_succ]
    · have hp : p0 = pc := by omega
      subst hp
      rw [evalB_sumCode_none f v l (p0 + 1) (fun p I hp hp' => h p I (by omega) (by simp; omega) (by omega)),
        Bool.xor_false]
      simp

end Sums

/-! ## Words with given bits -/

/-- The `w`-bit word whose bit `j` is `g j` (least significant first). -/
def bvOf (w : ℕ) (g : ℕ → Bool) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn fun j : Fin w => g j.val)).cast (by simp)

@[simp] theorem getLsbD_bvOf (w : ℕ) (g : ℕ → Bool) (j : ℕ) :
    (bvOf w g).getLsbD j = (decide (j < w) && g j) := by
  unfold bvOf
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  by_cases hj : j < w
  · simp [List.getD_eq_getElem?_getD, hj]
  · simp [List.getD_eq_getElem?_getD, hj]

@[simp] theorem getElem_bvOf (w : ℕ) (g : ℕ → Bool) (j : ℕ) (hj : j < w) : (bvOf w g)[j] = g j := by
  rw [← BitVec.getLsbD_eq_getElem, getLsbD_bvOf]; simp [hj]

theorem bvOf_getLsbD {w : ℕ} (v : BitVec w) : bvOf w v.getLsbD = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_bvOf]; simp [hj]

theorem bvOf_congr (w : ℕ) (g g' : ℕ → Bool) (h : ∀ j < w, g j = g' j) : bvOf w g = bvOf w g' := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_bvOf, getLsbD_bvOf, h j hj]

theorem bvOf_eq_iff {w : ℕ} (g : ℕ → Bool) (v : BitVec w) : bvOf w g = v ↔ ∀ j < w, g j = v.getLsbD j := by
  constructor
  · rintro rfl j hj; rw [getLsbD_bvOf]; simp [hj]
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [getLsbD_bvOf, h j hj]; simp [hj]

/-! ## `lem:trace-step` (ii): one-hot decoding by the prefix-or chain -/

/-- **(T2) ⟺ `pc < L`, `e` the indicator of `pc`, `o_p = [pc ≤ p]`.** -/
theorem decode_iff (L : ℕ) (hL : 1 ≤ L) (e o : ℕ → Bool) :
    (o 0 = e 0 ∧ (∀ p, 1 ≤ p → p < L → o p = Bool.xor (o (p - 1)) (e p)) ∧
      (∀ p, 1 ≤ p → p < L → (e p && o (p - 1)) = false) ∧ o (L - 1) = true) ↔
    ∃ pc < L, ∀ p < L, e p = decide (p = pc) ∧ o p = decide (pc ≤ p) := by
  constructor
  · rintro ⟨h0, hrec, hex, hlast⟩
    -- invariant: `o p` is the or of `e 0 … e p`, and at most one of them is set
    have inv : ∀ p < L, (o p = true ↔ ∃ q ≤ p, e q = true) ∧
        ∀ q ≤ p, ∀ q' ≤ p, e q = true → e q' = true → q = q' := by
      intro p
      induction p with
      | zero =>
        intro _
        refine ⟨?_, fun q hq q' hq' _ _ => by omega⟩
        rw [h0]
        constructor
        · intro h; exact ⟨0, le_rfl, h⟩
        · rintro ⟨q, hq, h⟩; have : q = 0 := by omega
          subst this; exact h
      | succ p ih =>
        intro hp
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        have hr := hrec (p + 1) (by omega) hp
        have hx := hex (p + 1) (by omega) hp
        simp only [Nat.add_sub_cancel] at hr hx
        cases he : e (p + 1)
        · rw [he, Bool.xor_false] at hr
          refine ⟨?_, ?_⟩
          · rw [hr, ih1]
            constructor
            · rintro ⟨q, hq, h⟩; exact ⟨q, by omega, h⟩
            · rintro ⟨q, hq, h⟩
              rcases Nat.lt_or_ge p q with hpq | hpq
              · have : q = p + 1 := by omega
                subst this; rw [he] at h; exact absurd h (by simp)
              · exact ⟨q, hpq, h⟩
          · intro q hq q' hq' h1 h2
            have hq1 : q ≤ p := by
              rcases Nat.lt_or_ge p q with hpq | hpq
              · have : q = p + 1 := by omega
                subst this; rw [he] at h1; exact absurd h1 (by simp)
              · exact hpq
            have hq2 : q' ≤ p := by
              rcases Nat.lt_or_ge p q' with hpq | hpq
              · have : q' = p + 1 := by omega
                subst this; rw [he] at h2; exact absurd h2 (by simp)
              · exact hpq
            exact ih2 q hq1 q' hq2 h1 h2
        · rw [he, Bool.true_and] at hx
          rw [he, hx] at hr
          have hnone : ∀ q ≤ p, e q = false := by
            intro q hq
            cases hq' : e q
            · rfl
            · exact absurd (ih1.2 ⟨q, hq, hq'⟩) (by rw [hx]; simp)
          refine ⟨?_, ?_⟩
          · rw [hr]; simp only [Bool.false_xor, true_iff]; exact ⟨p + 1, le_rfl, he⟩
          · intro q hq q' hq' h1 h2
            have a1 : q = p + 1 := by
              rcases Nat.lt_or_ge p q with hpq | hpq
              · omega
              · rw [hnone q hpq] at h1; exact absurd h1 (by simp)
            have a2 : q' = p + 1 := by
              rcases Nat.lt_or_ge p q' with hpq | hpq
              · omega
              · rw [hnone q' hpq] at h2; exact absurd h2 (by simp)
            omega
    obtain ⟨pc, hpc, hepc⟩ := (inv (L - 1) (by omega)).1.mp hlast
    refine ⟨pc, by omega, fun p hp => ?_⟩
    have huniq := (inv (L - 1) (by omega)).2
    constructor
    · cases hep : e p
      · have : p ≠ pc := by rintro rfl; rw [hep] at hepc; exact absurd hepc (by simp)
        simp [this]
      · have := huniq p (by omega) pc hpc hep hepc
        simp [this]
    · have hop := (inv p hp).1
      cases ho : o p
      · rw [ho] at hop
        have : ¬ pc ≤ p := by
          intro hle
          exact absurd (hop.mpr ⟨pc, hle, hepc⟩) (by simp)
        simp [this]
      · rw [ho] at hop
        obtain ⟨q, hq, heq⟩ := hop.mp rfl
        have := huniq q (by omega) pc hpc heq hepc
        simp; omega
  · rintro ⟨pc, hpc, h⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [(h 0 (by omega)).1, (h 0 (by omega)).2]
      by_cases h0 : pc = 0
      · simp [h0]
      · simp [h0]; omega
    · intro p hp1 hp
      rw [(h p hp).1, (h p hp).2, (h (p - 1) (by omega)).2]
      by_cases hpp : p = pc
      · subst hpp; simp; omega
      · by_cases hle : pc ≤ p - 1
        · simp [hpp, hle, show pc ≤ p by omega]
        · simp [hpp, hle, show ¬ pc ≤ p by omega]
    · intro p hp1 hp
      rw [(h p hp).1, (h (p - 1) (by omega)).2]
      by_cases hpp : p = pc
      · subst hpp; simp; omega
      · simp [hpp]
    · rw [(h (L - 1) (by omega)).2]; simp; omega

end NearCubicGates.Adapters.RAMTrace
