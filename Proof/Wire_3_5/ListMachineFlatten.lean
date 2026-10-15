import Proof.Wire_3_5.ListMachineNormal
import Proof.Wire_3_5.ListFlatten

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.SupplierWalk

/-! ## Integer expressions -/

/-- A factored integer expression over the coordinates (S0's `IntExpression ℕ`). -/
abbrev Expr := IntExpression ℕ

theorem expr_eval_nil (ρ : ℕ → Bool) : IntExpression.eval ([] : Expr) ρ = 0 := rfl

theorem expr_eval_cons (c : ℤ) (fs : List Poly) (V : Expr) (ρ : ℕ → Bool) :
    IntExpression.eval ((c, fs) :: V) ρ = c * (fs.map fun p => bitZ (F2Poly.eval p ρ)).prod + IntExpression.eval V ρ := by
  simp [IntExpression.eval]

theorem expr_eval_append (V W : Expr) (ρ : ℕ → Bool) :
    IntExpression.eval (V ++ W) ρ = IntExpression.eval V ρ + IntExpression.eval W ρ := by
  simp [IntExpression.eval]

/-- Negate every term. -/
def exprNeg (V : Expr) : Expr := V.map fun t => (-t.1, t.2)

theorem expr_eval_neg (V : Expr) (ρ : ℕ → Bool) : IntExpression.eval (exprNeg V) ρ = -IntExpression.eval V ρ := by
  induction V with
  | nil => rfl
  | cons t V ih =>
    obtain ⟨c, fs⟩ := t
    simp only [exprNeg, List.map_cons] at *
    rw [expr_eval_cons, expr_eval_cons, ih]
    ring

theorem expr_eval_flatMap {β : Type} (l : List β) (f : β → Expr) (ρ : ℕ → Bool) :
    IntExpression.eval (l.flatMap f) ρ = (l.map fun b => IntExpression.eval (f b) ρ).sum := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, expr_eval_append, ih, List.map_cons, List.sum_cons]

/-! ## The truth-table majority expansion -/

/-- All `2^t` Boolean rows of length `t`. -/
def allRows : ℕ → List (List Bool)
  | 0 => [[]]
  | t + 1 => (allRows t).flatMap fun r => [false :: r, true :: r]

/-- The factors of a row, from position `o`: `P_k` where the row is true, `1 − P_k` where it is false. -/
def rowFactors (P : ℕ → Poly) : ℕ → List Bool → List Poly
  | _, [] => []
  | o, x :: r => (if x then P o else nnot (P o)) :: rowFactors P (o + 1) r

/-- The factor product of a row at an assignment. -/
def rowProd (P : ℕ → Poly) (ρ : ℕ → Bool) (o : ℕ) (r : List Bool) : ℤ :=
  ((rowFactors P o r).map fun p => bitZ (F2Poly.eval p ρ)).prod

/-- The bits the factors take at an assignment, from position `o`. -/
def bitsFrom (P : ℕ → Poly) (ρ : ℕ → Bool) (o t : ℕ) : List Bool := (List.range t).map fun k => F2Poly.eval (P (o + k)) ρ

theorem bitsFrom_succ (P : ℕ → Poly) (ρ : ℕ → Bool) (o t : ℕ) :
    bitsFrom P ρ o (t + 1) = F2Poly.eval (P o) ρ :: bitsFrom P ρ (o + 1) t := by
  unfold bitsFrom
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero, Function.comp_def]
  congr 2
  funext k
  rw [Nat.add_assoc, Nat.add_comm 1 k]

theorem sum_flatMap_pair (l : List (List Bool)) (F : List Bool → ℤ) :
    ((l.flatMap fun r => [false :: r, true :: r]).map F).sum = (l.map fun r => F (false :: r) + F (true :: r)).sum := by
  induction l with
  | nil => rfl
  | cons r l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih]; simp [add_assoc]

/-- **Exactly one row matches**: `Σ_r g(r) Π_k [r_k = b_k] = g(b)` (the rows' indicators are disjoint). -/
theorem sum_rows_select (P : ℕ → Poly) (ρ : ℕ → Bool) (t : ℕ) :
    ∀ (o : ℕ) (g : List Bool → ℤ),
      ((allRows t).map fun r => g r * rowProd P ρ o r).sum = g (bitsFrom P ρ o t) := by
  induction t with
  | zero => intro o g; simp [allRows, rowProd, rowFactors, bitsFrom]
  | succ t ih =>
    intro o g
    set b := F2Poly.eval (P o) ρ with hb
    have hrow : ∀ r, rowProd P ρ o (false :: r) = bitZ (!b) * rowProd P ρ (o + 1) r ∧
        rowProd P ρ o (true :: r) = bitZ b * rowProd P ρ (o + 1) r := by
      intro r
      simp [rowProd, rowFactors, eval_nnot, hb]
    have hsum : ((allRows (t + 1)).map fun r => g r * rowProd P ρ o r).sum =
        ((allRows t).map fun r => (bitZ (!b) * g (false :: r) + bitZ b * g (true :: r)) * rowProd P ρ (o + 1) r).sum := by
      simp only [allRows]
      rw [sum_flatMap_pair]
      congr 1
      apply List.map_congr_left
      intro r _
      rw [(hrow r).1, (hrow r).2]
      ring
    rw [hsum, ih (o + 1) (fun r => bitZ (!b) * g (false :: r) + bitZ b * g (true :: r)), bitsFrom_succ, ← hb]
    cases b <;> simp [bitZ]

def majTerms (t θ : ℕ) (P : ℕ → Poly) : Expr :=
  ((allRows t).filter fun r => decide (θ ≤ r.count true)).map fun r => (1, rowFactors P 0 r)

theorem eval_filter_map (l : List (List Bool)) (p : List Bool → Bool) (F : List Bool → List Poly) (ρ : ℕ → Bool) :
    IntExpression.eval ((l.filter p).map fun r => ((1 : ℤ), F r)) ρ =
      (l.map fun r => bitZ (p r) * ((F r).map fun q => bitZ (F2Poly.eval q ρ)).prod).sum := by
  induction l with
  | nil => rfl
  | cons r rs ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    cases hp : p r
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]; simp [bitZ]
    · simp only [↓reduceIte, List.map_cons]
      rw [expr_eval_cons, ih]; simp [bitZ]

theorem majTerms_eval (t θ : ℕ) (P : ℕ → Poly) (ρ : ℕ → Bool) :
    IntExpression.eval (majTerms t θ P) ρ = bitZ (decide (θ ≤ (bitsFrom P ρ 0 t).count true)) := by
  rw [← sum_rows_select P ρ t 0 fun r => bitZ (decide (θ ≤ r.count true))]
  unfold majTerms
  rw [eval_filter_map]
  rfl

/-! ## The amplified states -/

def flatExpr (M t : ℕ) (visit : ℕ → ℕ → Poly) (s : ℕ) : Expr :=
  if s = 0 then (1, []) :: (List.range M).flatMap fun i => exprNeg (majTerms t ((t + 1) / 2) fun k => visit k (i + 1))
  else majTerms t ((t + 1) / 2) fun k => visit k s

theorem count_ofFn_true : ∀ (t : ℕ) (y : Fin t → Bool),
    (List.ofFn y).count true = (Finset.univ.filter fun k => y k = true).card
  | 0, y => by simp
  | t + 1, y => by
    rw [List.ofFn_succ, List.count_cons, count_ofFn_true t, Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_succ]
    cases y 0 <;> simp [add_comm]

theorem count_bitsFrom (P : ℕ → Poly) (ρ : ℕ → Bool) (t : ℕ) (y : Fin t → Bool)
    (hy : ∀ k : Fin t, F2Poly.eval (P k) ρ = y k) :
    (bitsFrom P ρ 0 t).count true = (Finset.univ.filter fun k => y k = true).card := by
  have : bitsFrom P ρ 0 t = List.ofFn y := by
    apply List.ext_getElem
    · simp [bitsFrom]
    · intro i h1 h2
      simp only [bitsFrom, List.getElem_map, List.getElem_range, List.getElem_ofFn, Nat.zero_add]
      exact hy ⟨i, by simpa using h2⟩
  rw [this, count_ofFn_true]

def visitPolys (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (k s : ℕ) : Poly :=
  if h : k < P.walkLen then stateRefN (P.base.data (P.decode (e.vertex ⟨k, h⟩))) L s else pzero

def flatExprOf (P : FlatListParams) (e : P.FlatSeed) (L s : ℕ) : Expr := flatExpr P.M P.walkLen (visitPolys P e L) s

theorem visitPolys_eval (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (z : Fin L → Bool) (k : Fin P.walkLen)
    (s : ℕ) (hs : s ≤ P.M) :
    F2Poly.eval (visitPolys P e L k s) (ext z) = decide (P.visitReport e k (List.ofFn z) = s) := by
  unfold visitPolys
  rw [dif_pos k.isLt]
  have hst := stateRefN_eval (P.base.data (P.decode (e.vertex k))) (fun j i h => P.base.inLevel_nest _ j i h) L s z
  have hiff := (P.base.data (P.decode (e.vertex k))).listStates_eq_one_iff (List.ofFn z) s hs
  have hrep : P.visitReport e k (List.ofFn z) = (P.base.data (P.decode (e.vertex k))).listReport (List.ofFn z) := rfl
  rw [hrep]
  cases hb : F2Poly.eval (stateRefN (P.base.data (P.decode (e.vertex k))) L s) (ext z)
  · rw [hb] at hst
    simp only [bitF2] at hst
    symm
    rw [decide_eq_false_iff_not]
    intro heq
    have := hiff.mpr heq.symm
    rw [← hst] at this
    exact zero_ne_one this
  · rw [hb] at hst
    simp only [bitF2] at hst
    symm
    rw [decide_eq_true_iff]
    exact (hiff.mp hst.symm).symm

theorem flatExprOf_eval (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (z : Fin L → Bool) (s : ℕ) (hs : s ≤ P.M) :
    IntExpression.eval (flatExprOf P e L s) (ext z) = bitInt (decide (P.flatReport e (List.ofFn z) = s)) := by
  have hmaj : ∀ s', s' ≤ P.M → IntExpression.eval (majTerms P.walkLen ((P.walkLen + 1) / 2) fun k => visitPolys P e L k s')
      (ext z) = ∑ T ∈ majoritySets P.walkLen (majorityThreshold P.walkLen),
        indicatorProduct (fun k => decide (P.visitReport e k (List.ofFn z) = s')) T := by
    intro s' hs'
    rw [majTerms_eval, count_bitsFrom _ _ _ (fun k => decide (P.visitReport e k (List.ofFn z) = s'))
      (fun k => visitPolys_eval P e L z k s' hs'), ← majority_expansion]
    rfl
  rw [P.flatState_expansion e (List.ofFn z) s hs]
  unfold flatExprOf flatExpr
  split_ifs with h0
  · rw [expr_eval_cons, expr_eval_flatMap]
    simp only [List.map_nil, List.prod_nil, mul_one]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib, show Finset.Icc 1 P.M = Finset.Ico 1 (P.M + 1) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel, ← sum_range_list]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [expr_eval_neg, hmaj (i + 1) (by have := List.mem_range.mp hi; omega), Nat.add_comm 1 i]
  · exact hmaj s hs

/-! ## Size -/

theorem length_allRows (t : ℕ) : (allRows t).length = 2 ^ t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [allRows, List.length_flatMap, ih, pow_succ]

theorem mem_allRows_length {t : ℕ} {r : List Bool} (h : r ∈ allRows t) : r.length = t := by
  induction t generalizing r with
  | zero => simp [allRows] at h; subst h; rfl
  | succ t ih =>
    simp only [allRows, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at h
    obtain ⟨r', hr', rfl | rfl⟩ := h <;> simp [ih hr']

theorem length_rowFactors (P : ℕ → Poly) (o : ℕ) (r : List Bool) : (rowFactors P o r).length = r.length := by
  induction r generalizing o with
  | nil => rfl
  | cons x r ih => simp [rowFactors, ih]

theorem flatExpr_size (M t : ℕ) (visit : ℕ → ℕ → Poly) (s : ℕ) :
    (flatExpr M t visit s).length ≤ (M + 1) * 2 ^ t ∧ ∀ term ∈ flatExpr M t visit s, term.2.length ≤ t := by
  have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hmaj : ∀ P : ℕ → Poly, (majTerms t ((t + 1) / 2) P).length ≤ 2 ^ t ∧
      ∀ term ∈ majTerms t ((t + 1) / 2) P, term.2.length = t := by
    intro P
    refine ⟨?_, ?_⟩
    · unfold majTerms
      rw [List.length_map]
      exact (List.length_filter_le _ _).trans (length_allRows t).le
    · intro term hterm
      unfold majTerms at hterm
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hterm
      rw [length_rowFactors, mem_allRows_length (List.mem_filter.mp hr).1]
  unfold flatExpr
  split_ifs
  · refine ⟨?_, ?_⟩
    · rw [List.length_cons, List.length_flatMap]
      have : ∀ i ∈ List.range M, (exprNeg (majTerms t ((t + 1) / 2) fun k => visit k (i + 1))).length ≤ 2 ^ t := by
        intro i _; simp only [exprNeg, List.length_map]; exact (hmaj _).1
      have hs := List.sum_le_card_nsmul ((List.range M).map fun i =>
        (exprNeg (majTerms t ((t + 1) / 2) fun k => visit k (i + 1))).length) (2 ^ t)
        (by intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact this i hi)
      simp only [List.length_map, List.length_range, smul_eq_mul] at hs
      rw [Nat.add_mul, one_mul]
      omega
    · intro term hterm
      rcases List.mem_cons.mp hterm with rfl | hterm
      · simp
      · obtain ⟨i, _, hterm⟩ := List.mem_flatMap.mp hterm
        unfold exprNeg at hterm
        obtain ⟨term', hterm', rfl⟩ := List.mem_map.mp hterm
        exact ((hmaj _).2 term' hterm').le
  · exact ⟨((hmaj _).1).trans (by rw [Nat.add_mul, one_mul]; omega), fun term h => ((hmaj _).2 term h).le⟩

end NearCubicWires.WireExponent3_5.ListMachine
