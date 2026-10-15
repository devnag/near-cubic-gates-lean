import Proof.Gates.Expand.Setup7

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

section Consts
variable {cap Wb V W : ℕ} {σ : WState NS NR}

theorem CB.zF {τ : WState NS NR} {w : Fin 53 → ℕ} (h : CB Wb σ τ w) (hF : σ.val F0 = 0) : τ.val F0 = 0 := by
  rw [h.regs _ (by simp [F0]), hF]
theorem CB.zR {τ : WState NS NR} {w : Fin 53 → ℕ} (h : CB Wb σ τ w) (hR : σ.val R0 = 0) : τ.val R0 = 0 := by
  rw [h.regs _ (by simp [R0]), hR]
theorem CB.z5 {τ : WState NS NR} {w : Fin 53 → ℕ} (h : CB Wb σ τ w) (h5 : σ.val (GR 5) = 0) : τ.val (GR 5) = 0 := by
  rw [h.regs _ (grN (by decide)), h5]

theorem constB1_spec (D : ℕ) (h0 : MV NB Wb (fun _ => 0) σ) (hF : σ.val F0 = 0)
    (hR : σ.val R0 = 0) (h5 : σ.val (GR 5) = 0) (h3 : σ.val (GR 3) = D + 1) (hV : σ.val (RF 10) = V)
    (h1 : σ.val (GR 1) = W) (hVb : 2 ^ V < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap)
    (hcV : 2 * (V + W + D + 2) ≤ cap) :
    Runs cap constB1 σ (constB1Cost Wb V W D) (fun τ => (∃ w, CB Wb σ τ w ∧ w 34 = 2 ^ W ∧ w 35 = 1 ∧ w 37 = 2 ^ V ∧
      ∀ j, j ≠ 34 → j ≠ 35 → j ≠ 37 → w j = 0) ∧ τ.val (GR 3) = 0) := by
  have hFR : F0 ≠ R0 := grN (by decide)
  have hV0 : 0 < 2 ^ V := Nat.two_pow_pos V
  have c0 : CB Wb σ σ (fun _ => 0) := ⟨h0, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, rfl⟩
  refine Runs.seq (mInc cap Wb 35 0 (by decide) hFR c0.mv (c0.zF hF) (c0.zR hR) (by show 0 + 1 < 2 ^ Wb; omega) hcap)
    (fun τ1 ⟨m1, f1⟩ => ?_)
  have c1 := c0.step m1 f1 (nbS 35)
  have u13 : τ1.val (GR 3) = D + 1 := by rw [f1.val (by simp), h3]
  refine Runs.seq ((rClrR cap (GR 3) τ1 (by rw [u13]; omega)).cost (le_of_eq (by rw [u13])))
    (fun τ2 ⟨f2, v2⟩ => ?_)
  have c2 := c1.reg f2
  have u2V : τ2.val (RF 10) = V := by rw [c2.regs _ (by simp [(gr_ne_rf 3 10).symm]), hV]
  refine Runs.seq ((rAddR cap (A := RF 10) (B := GR 3) (T := GR 7) (gr_ne_rf 3 10).symm (gr_ne_rf 7 10).symm
    (grN (by decide)) τ2 (c2.zR hR) (by rw [v2, u2V]; omega)).cost (le_of_eq (by rw [u2V])))
    (fun τ3 ⟨f3, v3⟩ => ?_)
  have c3 := c2.reg f3
  refine Runs.seq (mCopy cap Wb 37 35 (by decide) hFR c3.mv (c3.zF hF) (c3.zR hR) hcap) (fun τ4 ⟨m4, f4⟩ => ?_)
  have c4 := c3.step m4 f4 (nbS 37)
  have u43 : τ4.val (GR 3) = V := by rw [f4.val (by simp), v3, v2, u2V]; simp
  refine Runs.seq (shlLoop_spec cap Wb 37 35 (by decide) V τ4 _ c4.mv (c4.zF hF) (c4.zR hR) u43 (c4.z5 h5) hcap
    (by omega)) (fun τ5 ⟨m5, f5⟩ => ?_)
  have c5 := c4.step m5 f5 (nbS 37)
  have u53 : τ5.val (GR 3) = V := by rw [f5.val (by simp), u43]
  refine Runs.seq ((rClrR cap (GR 3) τ5 (by rw [u53]; omega)).cost (le_of_eq (by rw [u53])))
    (fun τ6 ⟨f6, v6⟩ => ?_)
  have c6 := c5.reg f6
  have u61 : τ6.val (GR 1) = W := by rw [c6.regs _ (grN (by decide)), h1]
  refine Runs.seq ((rAddR cap (A := GR 1) (B := GR 3) (T := GR 7) (grN (by decide)) (grN (by decide))
    (grN (by decide)) τ6 (c6.zR hR) (by rw [v6, u61]; omega)).cost (le_of_eq (by rw [u61])))
    (fun τ7 ⟨f7, v7⟩ => ?_)
  have c7 := c6.reg f7
  refine Runs.seq (mCopy cap Wb 34 35 (by decide) hFR c7.mv (c7.zF hF) (c7.zR hR) hcap) (fun τ8 ⟨m8, f8⟩ => ?_)
  have c8 := c7.step m8 f8 (nbS 34)
  have u83 : τ8.val (GR 3) = W := by rw [f8.val (by simp), v7, v6, u61]; simp
  refine Runs.seq (shlLoop_spec cap Wb 34 35 (by decide) W τ8 _ c8.mv (c8.zF hF) (c8.zR hR) u83 (c8.z5 h5) hcap
    (by omega)) (fun τ9 ⟨m9, f9⟩ => ?_)
  have c9 := c8.step m9 f9 (nbS 34)
  have u93 : τ9.val (GR 3) = W := by rw [f9.val (by simp), u83]
  refine ((rClrR cap (GR 3) τ9 (by rw [u93]; omega)).cost (le_of_eq (by rw [u93]))).post
    (fun τ10 ⟨f10, v10⟩ => ⟨⟨_, c9.reg f10, ?_, ?_, ?_, fun j h34 h35 h37 => ?_⟩, v10⟩)
  · simp
  · simp
  · simp
  · simp [Function.update_apply, h34, h35, h37]

theorem constB2_spec {τ : WState NS NR} {w : Fin 53 → ℕ} (c : CB Wb σ τ w) (hF : σ.val F0 = 0)
    (hR : σ.val R0 = 0) (h5 : σ.val (GR 5) = 0) (w34 : w 34 = 2 ^ W) (w35 : w 35 = 1) (w37 : w 37 = 2 ^ V)
    (wz : ∀ j, j ≠ 34 → j ≠ 35 → j ≠ 37 → w j = 0) (hW : 2 ≤ W) (hVW : 2 ^ V * 2 ^ W < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap constB2 τ (constB2Cost Wb) (fun ρ => ∃ w', CB Wb σ ρ w' ∧ w' 31 = (2 ^ V - 1) * 2 ^ W ∧
      w' 32 = 2 ^ V * 2 ^ W ∧ w' 33 = 2 ^ W - 1 ∧ w' 34 = 2 ^ W ∧ w' 35 = 1 ∧ w' 36 = 2 ^ V - 1 ∧ w' 37 = 2 ^ V ∧
      w' 51 = 2 ^ (W - 1) ∧ (∀ j, j ∉ ([31, 32, 33, 34, 35, 36, 37, 51] : List (Fin 53)) → w' j = 0) ∧
      SameExcept τ ρ nbList []) := by
  have hFR : F0 ≠ R0 := grN (by decide)
  have hFG : F0 ≠ GR 5 := grN (by decide)
  have hRG : R0 ≠ GR 5 := grN (by decide)
  have hV0 : 0 < 2 ^ V := Nat.two_pow_pos V
  have hW0 : 4 ≤ 2 ^ W := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hVb : 2 ^ V < 2 ^ Wb := by nlinarith
  have hWb : 2 ^ W < 2 ^ Wb := by nlinarith
  refine Runs.seq (mMul cap Wb 37 34 32 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hFR hFG hRG c.mv (c.zF hF) (c.zR hR) (c.z5 h5) (by rw [w37, w34]; exact hVW) (by rw [w34]; exact hWb) hcap)
    (fun τ1 ⟨m1, f1⟩ => ?_)
  have c1 := c.step m1 f1 (nbS2 32 21)
  refine Runs.seq (mCopy cap Wb 36 37 (by decide) hFR c1.mv (c1.zF hF) (c1.zR hR) hcap) (fun τ2 ⟨m2, f2⟩ => ?_)
  have c2 := c1.step m2 f2 (nbS 36)
  refine Runs.seq (mSub cap Wb 36 35 (by decide) hFR c2.mv (c2.zF hF) (c2.zR hR) (by simp [w37, w35]; omega)
    (by simp [w37]; omega) hcap) (fun τ3 ⟨m3, f3⟩ => ?_)
  have c3 := c2.step m3 f3 (nbS 36)
  refine Runs.seq (mCopy cap Wb 33 34 (by decide) hFR c3.mv (c3.zF hF) (c3.zR hR) hcap) (fun τ4 ⟨m4, f4⟩ => ?_)
  have c4 := c3.step m4 f4 (nbS 33)
  refine Runs.seq (mSub cap Wb 33 35 (by decide) hFR c4.mv (c4.zF hF) (c4.zR hR) (by simp [w34, w35]; omega)
    (by simp [w34]; omega) hcap) (fun τ5 ⟨m5, f5⟩ => ?_)
  have c5 := c4.step m5 f5 (nbS 33)
  refine Runs.seq (mMul cap Wb 36 34 31 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hFR hFG hRG c5.mv (c5.zF hF) (c5.zR hR) (c5.z5 h5)
    (by simp [w37, w35, w34]; rw [Nat.sub_mul, one_mul]; omega) (by simp [w34]; omega) hcap)
    (fun τ6 ⟨m6, f6⟩ => ?_)
  have c6 := c5.step m6 f6 (nbS2 31 21)
  refine Runs.seq (mCopy cap Wb 51 34 (by decide) hFR c6.mv (c6.zF hF) (c6.zR hR) hcap) (fun τ7 ⟨m7, f7⟩ => ?_)
  have c7 := c6.step m7 f7 (nbS 51)
  refine (mHalf cap Wb 51 c7.mv (c7.zR hR) (by simp [w34]; omega) hcap).post (fun τ8 ⟨m8, f8⟩ => ?_)
  have c8 := c7.step m8 f8 (nbS 51)
  have hW1 : 2 ^ W / 2 = 2 ^ (W - 1) := by
    rw [show W = W - 1 + 1 by omega, pow_succ]; simp
  refine ⟨_, c8, by simp [w37, w35, w34], by simp [w37, w34], by simp [w34, w35], by simp [w34],
    by simp [w35], by simp [w37, w35], by simp [w37], by simp [w34, hW1], fun j hj => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    obtain ⟨j31, j32, j33, j34, j35, j36, j37, j51⟩ := hj
    simp [Function.update_apply, j31, j32, j33, j34, j35, j36, j37, j51, wz j j34 j35 j37]
  · have w1 := se_sub f1 (fun x hx => nbS2 32 21 x hx) (List.Subset.refl [])
    have w2 := se_sub f2 (fun x hx => nbS 36 x hx) (List.Subset.refl [])
    have w3 := se_sub f3 (fun x hx => nbS 36 x hx) (List.Subset.refl [])
    have w4 := se_sub f4 (fun x hx => nbS 33 x hx) (List.Subset.refl [])
    have w5 := se_sub f5 (fun x hx => nbS 33 x hx) (List.Subset.refl [])
    have w6 := se_sub f6 (fun x hx => nbS2 31 21 x hx) (List.Subset.refl [])
    have w7 := se_sub f7 (fun x hx => nbS 51 x hx) (List.Subset.refl [])
    have w8 := se_sub f8 (fun x hx => nbS 51 x hx) (List.Subset.refl [])
    exact ((((((w1.trans w2).trans w3).trans w4).trans w5).trans w6).trans w7).trans w8

end Consts

end NearCubicGates.Close.Expand.Layout
