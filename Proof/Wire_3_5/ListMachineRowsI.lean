import Proof.Wire_3_5.ListMachineFlatten
import Proof.Wire_3_5.ListMachineContractsI

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.SupplierWalk

/-! ## A list's state bits, printed -/

/-- The state bit of a list at an input, through the final pass's fast report. -/
def listBit (D : ListData) (s : ℕ) (Z : List Bool) : Bool := decide (FinalPass.ListFast.listReportFast D Z = s)

theorem listBit_eq (D : ListData) (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true) (L s : ℕ)
    (hs : s ≤ D.M) (Z : List Bool) (hZ : Z.length = L) :
    listBit D s Z = F2Poly.eval (stateRef D L s) fun i => Z.getD i false := by
  set z : Fin L → Bool := fun i => Z[i.val]'(by rw [hZ]; exact i.isLt) with hz
  have hext : (fun i => Z.getD i false) = ext z := by
    funext i
    unfold ext
    split_ifs with hi
    · rw [List.getD_eq_getElem _ _ (by omega)]
    · rw [List.getD_eq_default _ _ (by omega)]
  have hofFn : List.ofFn z = Z := by
    apply List.ext_getElem (by simp [hZ])
    intro k h1 h2
    simp [hz]
  have he := stateRef_eval D hnest L s z
  rw [hofFn] at he
  rw [hext]
  apply ListTable.bitF2_inj
  rw [he]
  unfold listBit
  have hiff := D.listStates_eq_one_iff Z s hs
  rw [FinalPass.ListFast.listReport_eq_fast] at hiff
  by_cases h : FinalPass.ListFast.listReportFast D Z = s
  · rw [decide_eq_true h, hiff.mpr h.symm]; rfl
  · rw [decide_eq_false h]
    have h1 : D.listStates Z s ≠ 1 := fun h' => h (hiff.mp h').symm
    have h0 : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
    rw [h0 _ h1]; rfl

/-- A list's enumeration bound: `Σ_{j<J} 4W_j + 1`. -/
def listBound (D : ListData) : ℕ := ∑ j ∈ range D.J, 4 * D.W j + 1

theorem ell_bound' (D : ListData) (j : ℕ) : 2 ^ D.ell j - 1 ≤ 4 * D.W j := by
  rcases Nat.eq_zero_or_pos (D.ell j) with h0 | hpos
  · rw [h0]; simp
  · have hlt : 2 ^ (D.ell j - 1) < 2 * D.W j + 1 := by
      unfold ListData.ell at hpos ⊢
      have h1 : 1 < 2 * D.W j + 1 := by
        by_contra hc
        have : 2 * D.W j + 1 ≤ 1 := by omega
        have := Nat.clog_of_right_le_one (b := 2) this
        omega
      exact Nat.pow_pred_clog_lt_self (by norm_num) h1
    have e : 2 ^ D.ell j = 2 * 2 ^ (D.ell j - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem listBound_ge (D : ListData) : ∑ j ∈ range D.J, (2 ^ D.ell j - 1) ≤ listBound D := by
  unfold listBound
  have := Finset.sum_le_sum fun j (_ : j ∈ range D.J) => ell_bound' D j
  omega

/-- **The printed list state** `P_s` of `D` on `Z_0, …, Z_{L−1}`, by interpolation. -/
def listPrint (D : ListData) (L s : ℕ) : Poly := Interp.interpPrint (listBit D s) L (listBound D)

theorem listPrint_eval (D : ListData) (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true)
    (L s : ℕ) (hs : s ≤ D.M) (ρ : ℕ → Bool) :
    F2Poly.eval (listPrint D L s) ρ = F2Poly.eval (stateRef D L s) ρ := by
  obtain ⟨hdeg, hat⟩ := stateRef_size D L s
  have h := Interp.interpPrint_eval (listBit D s) L (listBound D) (stateRef D L s)
    (fun m hm => (hdeg m hm).trans (listBound_ge D)) hat
    (fun U => listBit_eq D hnest L s hs _ (ListTable.length_pointOf L U)) ρ
  rwa [evalP_eq, evalP_eq] at h

/-! ## The amplified states with printed visits -/

/-- The visited base states, printed by interpolation. -/
def visitPrint (P : FlatListParams) (e : P.FlatSeed) (L k s : ℕ) : Poly :=
  if h : k < P.walkLen then listPrint (P.base.data (P.decode (e.vertex ⟨k, h⟩))) L s else pzero

theorem visitPrint_eval (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (z : Fin L → Bool) (k : Fin P.walkLen)
    (s : ℕ) (hs : s ≤ P.M) :
    F2Poly.eval (visitPrint P e L k s) (ext z) = decide (P.visitReport e k (List.ofFn z) = s) := by
  have h := visitPolys_eval P e L z k s hs
  unfold visitPrint
  unfold visitPolys at h
  rw [dif_pos k.isLt] at h ⊢
  rw [listPrint_eval _ (fun j i hh => P.base.inLevel_nest _ j i hh) L s hs, ← eval_stateRefN]
  exact h

theorem flatExpr_eval_of (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (z : Fin L → Bool) (visit : ℕ → ℕ → Poly)
    (hv : ∀ (k : Fin P.walkLen) s, s ≤ P.M →
      F2Poly.eval (visit k s) (ext z) = decide (P.visitReport e k (List.ofFn z) = s))
    (s : ℕ) (hs : s ≤ P.M) :
    IntExpression.eval (flatExpr P.M P.walkLen visit s) (ext z) = bitInt (decide (P.flatReport e (List.ofFn z) = s)) := by
  have hmaj : ∀ s', s' ≤ P.M → IntExpression.eval (majTerms P.walkLen ((P.walkLen + 1) / 2) fun k => visit k s')
      (ext z) = ∑ T ∈ majoritySets P.walkLen (majorityThreshold P.walkLen),
        indicatorProduct (fun k => decide (P.visitReport e k (List.ofFn z) = s')) T := by
    intro s' hs'
    rw [majTerms_eval, count_bitsFrom _ _ _ (fun k => decide (P.visitReport e k (List.ofFn z) = s'))
      (fun k => hv k s' hs'), ← majority_expansion]
    rfl
  rw [P.flatState_expansion e (List.ofFn z) s hs]
  unfold flatExpr
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

def flatExprI (P : FlatListParams) (e : P.FlatSeed) (L s : ℕ) : Expr := flatExpr P.M P.walkLen (visitPrint P e L) s

theorem flatExprI_eval (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (z : Fin L → Bool) (s : ℕ) (hs : s ≤ P.M) :
    IntExpression.eval (flatExprI P e L s) (ext z) = bitInt (decide (P.flatReport e (List.ofFn z) = s)) :=
  flatExpr_eval_of P e L z (visitPrint P e L) (fun k s' hs' => visitPrint_eval P e L z k s' hs') s hs

end NearCubicWires.WireExponent3_5.ListMachine
