import Proof.Wire_3_5.ListMachineRowPopRow
import Proof.Wire_3_5.ListMachineRowsI

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.SupplierWalk
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord polyWord termWord exprWord)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.ListMachine (Expr allRows rowFactors rowProd bitsFrom sum_rows_select)

/-! ## The expression -/

/-- The selected factors of a row. -/
def selFacs (r : List Bool) (ps : List (Poly × Poly)) : List Poly := (r.zip ps).map fun bq => if bq.1 then bq.2.2 else bq.2.1

/-- The truth-table rows with at least `θ` ones, coefficient `c`. -/
def rowsExpr (n θ : ℕ) (c : ℤ) (ps : List (Poly × Poly)) : Expr :=
  ((List.range (2 ^ n)).filter fun i => decide (θ ≤ Interp.pop (binary n i))).map fun i => (c, selFacs (binary n i) ps)

/-- **The population expression**: the constant term(s), then every visited state's rows. -/
def popExprP (oneT : Expr) (n θ : ℕ) (sts : List (ℤ × List (Poly × Poly))) : Expr :=
  oneT ++ sts.flatMap fun st => rowsExpr n θ st.1 st.2

theorem selW_eq (r : List Bool) (ps : List (Poly × Poly)) :
    selW r ps = (selFacs r ps).flatMap fun p => true :: polyWord p := by
  simp [selW, selFacs, List.flatMap_map]

theorem rowsW_eq (n θ : ℕ) (c : ℤ) (ps : List (Poly × Poly)) :
    rowsW n θ c ps = (rowsExpr n θ c ps).flatMap fun t => true :: termWord t := by
  unfold rowsW rowsAt rowsExpr
  rw [List.flatMap_map]
  induction (List.range (2 ^ n)) with
  | nil => rfl
  | cons i l ih =>
    rw [List.flatMap_cons, List.filter_cons]
    by_cases h : θ ≤ Interp.pop (binary n i)
    · simp only [rowTerm, h, if_true, decide_true, List.flatMap_cons, ih, termWord, selW_eq]
      simp [List.append_assoc]
    · simp only [rowTerm, h, if_false, decide_false, Bool.false_eq_true, List.nil_append, ih]

/-- **The POP row prints `exprWord` of the population expression.** -/
theorem popOut_eq {F : EvalFam} (oneT : Expr) (n θ : ℕ) (sts : List (SSpec F)) :
    popOut (oneT.flatMap fun t => true :: termWord t) n θ sts =
      exprWord (popExprP oneT n θ (sts.map fun st => (st.1, statePairs st.2))) := by
  unfold popOut exprWord popExprP outAt
  rw [List.take_length, List.flatMap_append, List.flatMap_map]
  simp only [List.append_assoc]
  congr 2
  induction sts with
  | nil => rfl
  | cons st sts ih =>
    simp only [List.flatMap_cons, List.flatMap_append]
    rw [← ih, rowsW_eq]

/-! ## Its value -/

theorem allRows_binary : ∀ n : ℕ, (List.range (2 ^ n)).map (binary n) = allRows n
  | 0 => rfl
  | n + 1 => by
    rw [pow_succ, mul_comm, Interp.range_two_mul, List.map_flatMap, allRows, ← allRows_binary n, List.flatMap_map]
    congr 1
    funext k
    have h1 : binary (n + 1) (2 * k) = false :: binary n k := by
      show ((2 * k) % 2 == 1) :: binary n ((2 * k) / 2) = _
      rw [show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega]; rfl
    have h2 : binary (n + 1) (2 * k + 1) = true :: binary n k := by
      show ((2 * k + 1) % 2 == 1) :: binary n ((2 * k + 1) / 2) = _
      rw [show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]; rfl
    simp [h1, h2]

theorem prod_selFacs (σ : ℕ → Bool) (P : ℕ → Poly) :
    ∀ (r : List Bool) (ps : List (Poly × Poly)) (o : ℕ), r.length = ps.length →
      (∀ k, P (o + k) = (ps.getD k ([], [])).2) → (∀ q ∈ ps, F2Poly.eval q.1 σ = !F2Poly.eval q.2 σ) →
      ((selFacs r ps).map fun p => bitZ (F2Poly.eval p σ)).prod = rowProd P σ o r
  | [], [], _, _, _, _ => rfl
  | b :: r, q :: ps, o, hl, hP, hN => by
    have ih := prod_selFacs σ P r ps (o + 1) (by simpa using hl)
      (fun k => by rw [show o + 1 + k = o + (k + 1) by omega, hP (k + 1)]; simp)
      (fun q' hq' => hN q' (List.mem_cons_of_mem _ hq'))
    have h0 : P o = q.2 := by simpa using hP 0
    unfold rowProd at ih ⊢
    simp only [selFacs, List.zip_cons_cons, List.map_cons, List.prod_cons, rowFactors] at ih ⊢
    rw [ih]
    cases b
    · simp [hN q List.mem_cons_self, eval_nnot, h0]
    · simp [h0]
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl

theorem eval_filter_map_c (l : List (List Bool)) (p : List Bool → Bool) (c : ℤ) (F : List Bool → List Poly)
    (ρ : ℕ → Bool) :
    IntExpression.eval ((l.filter p).map fun r => (c, F r)) ρ =
      (l.map fun r => bitZ (p r) * (c * ((F r).map fun q => bitZ (F2Poly.eval q ρ)).prod)).sum := by
  induction l with
  | nil => rfl
  | cons r rs ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    cases hp : p r
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]; simp [bitZ]
    · simp only [↓reduceIte, List.map_cons]
      rw [expr_eval_cons, ih]; simp [bitZ]

/-- **The rows' value**: `c · [θ ≤ #{k : P_k}]`, when each `N_k` is the complement of `P_k`. -/
theorem rowsExpr_eval (n θ : ℕ) (c : ℤ) (ps : List (Poly × Poly)) (hlen : ps.length = n) (σ : ℕ → Bool)
    (hN : ∀ q ∈ ps, F2Poly.eval q.1 σ = !F2Poly.eval q.2 σ) :
    IntExpression.eval (rowsExpr n θ c ps) σ =
      c * bitZ (decide (θ ≤ (ps.map fun q => F2Poly.eval q.2 σ).count true)) := by
  set P : ℕ → Poly := fun k => (ps.getD k ([], [])).2 with hP
  have e1 : rowsExpr n θ c ps = ((allRows n).filter fun r => decide (θ ≤ Interp.pop r)).map fun r => (c, selFacs r ps) := by
    rw [← allRows_binary, List.filter_map, List.map_map]
    rfl
  rw [e1, eval_filter_map_c]
  have e2 : ∀ r ∈ allRows n, ((selFacs r ps).map fun q => bitZ (F2Poly.eval q σ)).prod = rowProd P σ 0 r := by
    intro r hr
    exact prod_selFacs σ P r ps 0 (by rw [mem_allRows_length hr, hlen])
      (fun k => by simp [hP]) hN
  rw [List.map_congr_left (fun r hr => by rw [e2 r hr])]
  have e3 := sum_rows_select P σ n 0 fun r => bitZ (decide (θ ≤ Interp.pop r)) * c
  simp only [mul_assoc] at e3
  rw [e3]
  have e4 : bitsFrom P σ 0 n = ps.map fun q => F2Poly.eval q.2 σ := by
    apply List.ext_getElem
    · simp [bitsFrom, hlen]
    · intro i h1 h2
      simp [bitsFrom, hP, List.getElem?_eq_getElem (by simpa [hlen] using h2 : i < ps.length)]
  rw [e4]
  exact mul_comm _ _

/-! ## The population expression's value -/

theorem bitZ_eq_bitInt (b : Bool) : bitZ b = bitInt b := by cases b <;> rfl

theorem eval_pads (n : ℕ) (σ : ℕ → Bool) : IntExpression.eval [((1 : ℤ), List.replicate n ([[]] : Poly))] σ = 1 := by
  simp [IntExpression.eval, F2Poly.eval, bitZ]

/-- The count of visits reporting `s'`, from the printed factors' values. -/
theorem count_visits (P : FlatListParams) (e : P.FlatSeed) (Z : List Bool) (σ : ℕ → Bool) (s' : ℕ)
    (ps : List (Poly × Poly)) (hlen : ps.length = P.walkLen)
    (hP : ∀ (k : ℕ) (hk : k < ps.length), F2Poly.eval ps[k].2 σ = decide (P.visitReport e ⟨k, hlen ▸ hk⟩ Z = s')) :
    (ps.map fun q => F2Poly.eval q.2 σ).count true =
      (Finset.univ.filter fun k : Fin P.walkLen => decide (P.visitReport e k Z = s') = true).card := by
  have : (ps.map fun q => F2Poly.eval q.2 σ) = List.ofFn fun k : Fin P.walkLen => decide (P.visitReport e k Z = s') := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_ofFn]
      exact hP i (by simpa using h1)
  rw [this, count_ofFn_true]

theorem popExpr_eval (P : FlatListParams) (e : P.FlatSeed) (Z : List Bool) (σ : ℕ → Bool) (s : ℕ) (hs : s ≤ P.M)
    (pss : ℕ → List (Poly × Poly)) (hlen : ∀ s', s' ≤ P.M → (pss s').length = P.walkLen)
    (hP : ∀ s' (hs' : s' ≤ P.M) (k : ℕ) (hk : k < (pss s').length),
      F2Poly.eval (pss s')[k].2 σ = decide (P.visitReport e ⟨k, hlen s' hs' ▸ hk⟩ Z = s'))
    (hN : ∀ s', s' ≤ P.M → ∀ q, q ∈ pss s' → F2Poly.eval q.1 σ = !F2Poly.eval q.2 σ) :
    IntExpression.eval (popExprP (if s = 0 then [(1, List.replicate P.walkLen [[]])] else []) P.walkLen
      (majorityThreshold P.walkLen)
      (if s = 0 then (List.range P.M).map (fun i => ((-1 : ℤ), pss (i + 1))) else [(1, pss s)])) σ =
      bitInt (decide (P.flatReport e Z = s)) := by
  have hrow : ∀ s' (c : ℤ), s' ≤ P.M → IntExpression.eval (rowsExpr P.walkLen (majorityThreshold P.walkLen) c (pss s')) σ =
      c * ∑ T ∈ majoritySets P.walkLen (majorityThreshold P.walkLen),
        indicatorProduct (fun k => decide (P.visitReport e k Z = s')) T := by
    intro s' c hs'
    rw [rowsExpr_eval _ _ c (pss s') (hlen s' hs') σ (hN s' hs'),
      count_visits P e Z σ s' (pss s') (hlen s' hs') (hP s' hs'), bitZ_eq_bitInt, ← majority_expansion]
  rw [P.flatState_expansion e Z s hs]
  unfold popExprP
  split_ifs with h0
  · rw [expr_eval_append, eval_pads, expr_eval_flatMap, sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib, show Finset.Icc 1 P.M = Finset.Ico 1 (P.M + 1) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel, ← sum_range_list, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply]
    rw [hrow (i + 1) (-1) (by have := List.mem_range.mp hi; omega), Nat.add_comm 1 i]
    ring
  · simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hrow s 1 hs, one_mul]

end NearCubicWires.WireExponent3_5.ListMachine.Row
