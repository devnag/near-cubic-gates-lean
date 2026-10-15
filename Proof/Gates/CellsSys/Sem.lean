import Proof.Gates.CellsSys.Box2

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

theorem getD_flatMap_fixed {α : Type} (f : α → List ℕ) (k : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = k) → ∀ (i s : ℕ) (hi : i < l.length), s < k →
      (l.flatMap f).getD (k * i + s) 0 = (f l[i]).getD s 0
  | [], _, i, _, hi, _ => absurd hi (by simp)
  | a :: l, hk, 0, s, _, hs => by
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hk a (by simp)]; exact hs)]
    rfl
  | a :: l, hk, i + 1, s, hi, hs => by
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [hk a (by simp)]; nlinarith), hk a (by simp)]
    have : k * (i + 1) + s - k = k * i + s := by rw [Nat.mul_succ]; omega
    rw [this, getD_flatMap_fixed f k l (fun b hb => hk b (by simp [hb])) i s (by simpa using hi) hs]
    rfl

theorem toNat_sub_toNat_neg' (z : ℤ) : (z.toNat : ℤ) - ((-z).toNat : ℤ) = z := by omega

section Stores
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

theorem tailL_getD (j : ℕ) (hj : j < p.J) : ((tailL p).getD j 0 : ℤ) = tailProd p j := by
  unfold tailL
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  have : 0 ≤ tailProd p j := Finset.prod_nonneg (fun t _ => rateOf_nonneg p t)
  omega

theorem ctrL_getD (r j s : ℕ) (hr : r < roleCount c.kind) (hj : j < p.J) (hs : s < 2) :
    (ctrL c p wt y).getD (2 * (r * p.J + j) + s) 0 = (pairOf (ctr c p wt y (⟨r, hr⟩, ⟨j, hj⟩))).getD s 0 := by
  unfold ctrL
  have h1 : 2 * (r * p.J + j) + s = (2 * p.J) * r + (2 * j + s) := by ring
  rw [h1, getD_flatMap_fixed _ (2 * p.J) _ (fun a _ => by simp [pairOf]; ring) r (2 * j + s) (by simpa using hr)
    (by omega), getD_flatMap_fixed _ 2 _ (fun a _ => by simp [pairOf]) j s (by simpa using hj) hs]
  simp

theorem kxL_getD (r s : ℕ) (hr : r < roleCount c.kind) (hs : s < 4) :
    (kxL c p wt y).getD (4 * r + s) 0 =
      (pairOf (stageForm c wt r (p.J - 1) (extend wt.I y (zeroPoint wt.I))) ++
        pairOf (scoreForm c r (extend wt.I y (zeroPoint wt.I)))).getD s 0 := by
  unfold kxL
  rw [getD_flatMap_fixed _ 4 _ (fun a _ => by simp [pairOf]) r s (by simpa using hr) hs]
  simp

end Stores

/-! ## The box of a role, value level -/

section Val
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

/-- The digit vector of the counter value `t`. -/
def kap (t : ℕ) : Role c × Fin p.J → ℤ := kappaOf c p wt y (digitsM (List.replicate (nDig c p) (wWin p)) t)

theorem pairOf_getD0 (z : ℤ) : (pairOf z).getD 0 0 = z.toNat := rfl
theorem pairOf_getD1 (z : ℤ) : (pairOf z).getD 1 0 = (-z).toNat := rfl

theorem ctrL_pos (r j : ℕ) (hr : r < roleCount c.kind) (hj : j < p.J) :
    (ctrL c p wt y).getD (2 * (r * p.J + j)) 0 = (ctr c p wt y (⟨r, hr⟩, ⟨j, hj⟩)).toNat := by
  have := ctrL_getD c p wt y r j 0 hr hj (by norm_num)
  simpa [pairOf] using this

theorem ctrL_neg (r j : ℕ) (hr : r < roleCount c.kind) (hj : j < p.J) :
    (ctrL c p wt y).getD (2 * (r * p.J + j) + 1) 0 = (-ctr c p wt y (⟨r, hr⟩, ⟨j, hj⟩)).toNat := by
  have := ctrL_getD c p wt y r j 1 hr hj (by norm_num)
  simpa [pairOf] using this

/-- **The digit sums of a role**: `accPf − accNf = Σ_j A_j κ(r, j)`. -/
theorem acc_eq (r : ℕ) (hr : r < roleCount c.kind) (t : ℕ) :
    (accPf (tailL p) (ctrL c p wt y) r p.J (nDig c p) (wWin p) t p.J : ℤ) -
      (accNf (tailL p) (ctrL c p wt y) r p.J p.hE p.J : ℤ) =
    ∑ j : Fin p.J, tailProd p j.val * kap c p wt y t (⟨r, hr⟩, j) := by
  unfold accPf accNf
  push_cast
  rw [← Finset.sum_sub_distrib, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  have hj := j.isLt
  have hidx : r * p.J + j.val < nDig c p := idx_lt c p (⟨r, hr⟩, j)
  have eA := tailL_getD p j.val hj
  have e0 := ctrL_pos c p wt y r j.val hr hj
  have e1 := ctrL_neg c p wt y r j.val hr hj
  have ed : dig (wWin p) (nDig c p) t (r * p.J + j.val) =
      (digitsM (List.replicate (nDig c p) (wWin p)) t).getD (r * p.J + j.val) 0 := by
    rw [digitsM_rep_getD _ _ _ _ hidx]; rfl
  rw [eA, e0, e1, ed]
  have hE := toNat_sub_toNat_neg' (ctr c p wt y (⟨r, hr⟩, ⟨j.val, hj⟩))
  simp only [kap, kappaOf, Fin.eta] at hE ⊢
  linear_combination (tailProd p j.val) * hE

/-- The centre of the box of role `r`, from the digit sums and `K_{J−1}`. -/
theorem center_eq (r : ℕ) (hr : r < roleCount c.kind) (t : ℕ) :
    zOf (p.M1 * (accPf (tailL p) (ctrL c p wt y) r p.J (nDig c p) (wWin p) t p.J + (kxL c p wt y).getD (4 * r + 1) 0))
      (p.M1 * (accNf (tailL p) (ctrL c p wt y) r p.J p.hE p.J + (kxL c p wt y).getD (4 * r) 0)) =
    boxCenter c p wt y (kap c p wt y t) ⟨r, hr⟩ := by
  have h := acc_eq c p wt y r hr t
  have e0 := kxL_getD c p wt y r 0 hr (by norm_num)
  have e1 := kxL_getD c p wt y r 1 hr (by norm_num)
  simp only [Nat.add_zero, pairOf, List.cons_append, List.getD_cons_zero, List.getD_cons_succ] at e0 e1
  rw [e0, e1]
  have hK := toNat_sub_toNat_neg' (stageForm c wt r (p.J - 1) (extend wt.I y (zeroPoint wt.I)))
  unfold zOf boxCenter
  push_cast
  linear_combination (p.M1 : ℤ) * h - (p.M1 : ℤ) * hK

theorem score_eq (r : ℕ) (hr : r < roleCount c.kind) :
    zOf ((kxL c p wt y).getD (4 * r + 2) 0) ((kxL c p wt y).getD (4 * r + 3) 0) =
      scoreForm c r (extend wt.I y (zeroPoint wt.I)) := by
  have e2 := kxL_getD c p wt y r 2 hr (by norm_num)
  have e3 := kxL_getD c p wt y r 3 hr (by norm_num)
  simp [pairOf] at e2 e3
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, e2, e3]; unfold zOf; omega

/-- The pair inputs of the box program of role `r` at counter value `t`. -/
noncomputable def cpV (r t : ℕ) : ℕ :=
  p.M1 * (accPf (tailL p) (ctrL c p wt y) r p.J (nDig c p) (wWin p) t p.J + (kxL c p wt y).getD (4 * r + 1) 0)
noncomputable def cnV (r : ℕ) : ℕ :=
  p.M1 * (accNf (tailL p) (ctrL c p wt y) r p.J p.hE p.J + (kxL c p wt y).getD (4 * r) 0)

theorem lo_eq (r : ℕ) (hr : r < roleCount c.kind) (t : ℕ) (hA : 0 < p.A) :
    zOf (loP (cpV c p wt y r t) (cnV c p wt y r) ((kxL c p wt y).getD (4 * r + 2) 0)
        ((kxL c p wt y).getD (4 * r + 3) 0) p.A p.Lambda (circ c r).topWeight).1
      (loP (cpV c p wt y r t) (cnV c p wt y r) ((kxL c p wt y).getD (4 * r + 2) 0)
        ((kxL c p wt y).getD (4 * r + 3) 0) p.A p.Lambda (circ c r).topWeight).2 =
    boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩ := by
  rw [loP_eq _ _ _ _ _ _ _ hA]
  unfold cpV cnV
  rw [center_eq c p wt y r hr t, score_eq c p wt y r hr]
  rfl

theorem hi_eq (r : ℕ) (hr : r < roleCount c.kind) (t : ℕ) (hA : 0 < p.A) :
    zOf (hiP (cpV c p wt y r t) (cnV c p wt y r) ((kxL c p wt y).getD (4 * r + 2) 0)
        ((kxL c p wt y).getD (4 * r + 3) 0) p.A p.Lambda (circ c r).topWeight).1
      (hiP (cpV c p wt y r t) (cnV c p wt y r) ((kxL c p wt y).getD (4 * r + 2) 0)
        ((kxL c p wt y).getD (4 * r + 3) 0) p.A p.Lambda (circ c r).topWeight).2 =
    boxHi c p wt y (kap c p wt y t) ⟨r, hr⟩ := by
  rw [hiP_eq _ _ _ _ _ _ _ hA]
  unfold cpV cnV
  rw [center_eq c p wt y r hr t, score_eq c p wt y r hr]
  rfl

end Val

/-- A normalized pair: `(P − N, 0)` or `(0, N − P)` is `(z.toNat, (−z).toNat)` for `z = P − N`. -/
theorem norm_pos (P N : ℕ) (h : ¬ P < N) : P - N = (zOf P N).toNat ∧ 0 = (-zOf P N).toNat := by
  unfold zOf; omega

theorem norm_neg (P N : ℕ) (h : P < N) : 0 = (zOf P N).toNat ∧ N - P = (-zOf P N).toNat := by
  unfold zOf; omega

end NearCubicGates.Close.Cells.SystemsPhase
