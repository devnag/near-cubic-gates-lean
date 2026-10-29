import SourceAdapters.ShortPCP.Machines.FLangStep

/-!
# Single-run time, machine layer 13: iterating the levels

`D_{RS,=}` is the base test at the last level (`Time.dEqFF_iter`) and `Translate` is a fold over the levels
(`Time.translateF_iter`); both need `Lvl.step^[depth n x] x`. `iterP n` runs `n` guarded passes (one more level while
`κ > κ0 = 4`, proof of `thm:short-pcp-ours` "Its recursion roughly halves the dimension … at each level"), counting the levels
taken in `48` (`iterP_spec`). Loop variable `47`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicWires.CanonicalBinary

variable (G : Glob)

/-! ## Depth arithmetic -/

section Depth

variable {F : Type} [Field F]

theorem depth_succ_eq : ∀ (j : ℕ) (x : Lvl F),
    x.depth (j + 1) = if (Lvl.step^[x.depth j] x).stop then x.depth j else x.depth j + 1
  | 0, x => by by_cases h : x.stop <;> simp [Lvl.depth, h]
  | j + 1, x => by
    by_cases h : x.stop
    · simp [Lvl.depth, h]
    · have e1 : x.depth (j + 1 + 1) = x.step.depth (j + 1) + 1 := by rw [Lvl.depth, if_neg h]
      have e2 : x.depth (j + 1) = x.step.depth j + 1 := by rw [Lvl.depth, if_neg h]
      rw [e1, e2, depth_succ_eq j x.step, Function.iterate_succ_apply]
      split_ifs <;> rfl

theorem iterate_depth_succ (j : ℕ) (x : Lvl F) :
    Lvl.step^[x.depth (j + 1)] x =
      if (Lvl.step^[x.depth j] x).stop then Lvl.step^[x.depth j] x else (Lvl.step^[x.depth j] x).step := by
  rw [depth_succ_eq]
  split_ifs
  · rfl
  · rw [Function.iterate_succ_apply']

theorem depth_le : ∀ (j : ℕ) (x : Lvl F), x.depth j ≤ j
  | 0, x => by simp [Lvl.depth]
  | j + 1, x => by
    simp only [Lvl.depth]; split_ifs
    · omega
    · have := depth_le j x.step; omega

theorem step_length_le (x : Lvl F) (h : ¬ x.stop = true) : x.step.B.length ≤ x.B.length := by
  have h5 : 5 ≤ x.B.length := by simp [Lvl.stop] at h; omega
  unfold Lvl.step
  split_ifs with h1 h2
  · simp; omega
  · simp; omega
  · rw [zMulti_length]; simp

end Depth

/-! ## The routine -/

/-- One guarded pass: the next level while `κ > 4`, counted in `48`. -/
def gstepP : S := .ite (.lt (.k 4) (.v 39)) (.seq stepP (.set 48 (.add (.v 48) (.k 1)))) .skip

/-- `n` guarded passes (loop variable `47`). -/
def iterP (n : E) : S := .loop 47 n gstepP

/-- The variables `iterP` writes. -/
def iterW : List Var := 47 :: 48 :: stepW

/-- **The level iteration**: after `m = min n N` guarded passes from level `x`, the variables hold level
`step^[depth m x] x`, and `48` has grown by `depth m x`. -/
theorem iterP_spec {F : Type} [Field F] [CharP F 2] (s : FS)
    (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (x : Lvl F) (n : E) (m : ℕ)
    (hm : min (evalE G s n) G.N = m) (hx : LRep φ s.fl u s x) (h23 : s.env 23 = s.fl)
    (h42 : s.env 42 = bitsValue u) (h43 : s.env 43 = u.length) (hok : fieldOk G s.fl s.fp = true)
    (hK : s.fl * x.B.length + 1 ≤ G.K) (hN : x.B.length ≤ G.N)
    (hoff : s.env 41 + (m + 1) * (x.B.length + 2) ≤ G.K) (h48 : s.env 48 + m ≤ G.K) :
    let t := evalS G (iterP n) s
    LRep φ s.fl u t (Lvl.step^[x.depth m] x) ∧ t.env 48 = s.env 48 + x.depth m ∧ Wr iterW s t ∧
      t.env 41 ≤ s.env 41 + m * (x.B.length + 2) := by
  intro t
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hc4 : min 4 G.cap = 4 := min_eq_left (by
    unfold Glob.cap; have : 2 ^ 3 ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  have hl := loop_inv G (i := 47) (n := n) (body := gstepP) (s := s)
    (fun j w => LRep φ s.fl u w (Lvl.step^[x.depth j] x) ∧ w.env 48 = s.env 48 + x.depth j ∧
      (Lvl.step^[x.depth j] x).B.length ≤ x.B.length ∧ w.env 41 ≤ s.env 41 + j * (x.B.length + 2) ∧ Wr iterW s w)
    ⟨by simpa [Lvl.depth] using hx, by simp [Lvl.depth], by simp [Lvl.depth], by simp, Wr.refl _ _⟩ (by
      rw [hm]
      rintro j hj w ⟨wx, w48, wlen, w41, wW⟩
      obtain ⟨wenv, wout, wfl', wfp', wip, wbad⟩ := w
      obtain rfl : wfp' = s.fp := wW.fp
      set w : FS := ⟨wenv, wout, wfl', s.fp, wip, wbad⟩ with hwdef
      set y := Lvl.step^[x.depth j] x with hy
      have w1x : LRep φ s.fl u (w.setv 47 j) y := wx.setv 47 (by decide) j
      have w23 : (w.setv 47 j).env 23 = s.fl := by simp; rw [wW.env 23 (by decide), h23]
      have w42 : (w.setv 47 j).env 42 = bitsValue u := by simp; rw [wW.env 42 (by decide), h42]
      have w43 : (w.setv 47 j).env 43 = u.length := by simp; rw [wW.env 43 (by decide), h43]
      have wfl : (w.setv 47 j).fl = s.fl := by simp [wW.fl]
      have wfp : (w.setv 47 j).fp = s.fp := by simp [wW.fp]
      obtain ⟨l, l38, l39, -, llm, -⟩ := wx
      have hyl : y.B.length = l.length := by rw [← llm, List.length_map]
      have hcond : evalE G (w.setv 47 j) (.lt (.k 4) (.v 39)) = if 4 < y.B.length then 1 else 0 := by
        simp [evalE, hc4, l39, hyl]
      rw [iterate_depth_succ, depth_succ_eq]
      by_cases hs : y.stop = true
      · have hκ : ¬ 4 < y.B.length := by simp [Lvl.stop] at hs; omega
        simp only [← hy, hs, if_true]
        rw [show evalS G gstepP (w.setv 47 j) = w.setv 47 j by simp [gstepP, evalS_ite, hcond, hκ]]
        refine ⟨w1x, by simp [w48], wlen, ?_, wW.trans (Wr.setv _ (by decide) _)⟩
        simp only [FS.setv_env, Function.update_of_ne (show (41 : Var) ≠ 47 by decide)]
        have e : (j + 1) * (x.B.length + 2) = j * (x.B.length + 2) + (x.B.length + 2) := by ring
        omega
      · have hκ : 4 < y.B.length := by simp [Lvl.stop] at hs; omega
        simp only [← hy, hs, if_false, Bool.false_eq_true]
        have hst := stepP_spec G (w.setv 47 j) φ u y (by rw [wfl]; exact w1x)
          (by rw [w23, wfl]) w42 w43 (by rw [wfl, wfp]; exact hok) (by omega)
          (by rw [wfl]; have := Nat.mul_le_mul_left s.fl wlen; omega) (by omega)
          (by simp only [FS.setv_env, Function.update_of_ne (show (41 : Var) ≠ 47 by decide)]
              have : j * (x.B.length + 2) + (x.B.length + 2) ≤ (m + 1) * (x.B.length + 2) := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
              omega)
        obtain ⟨hstx, hstW, hst41⟩ := hst
        generalize hw2 : evalS G stepP (w.setv 47 j) = w2 at hstx hstW hst41
        have hdj := depth_le j x
        have e48 : evalS G gstepP (w.setv 47 j) = w2.setv 48 (s.env 48 + x.depth j + 1) := by
          rw [gstepP, evalS_ite, hcond, if_pos hκ]
          simp only [one_ne_zero, if_false, evalS_seq, hw2, evalS_set, evalE]
          have e2 : w2.env 48 = s.env 48 + x.depth j := by rw [hstW.env 48 (by decide)]; simp [w48]
          rw [e2, hc1, min_cap (show s.env 48 + x.depth j + 1 ≤ G.K by omega)]
        rw [e48]
        refine ⟨by rw [wfl] at hstx; exact hstx.setv 48 (by decide) _, by simp; omega,
          (step_length_le y hs).trans wlen, ?_, ?_⟩
        · simp only [FS.setv_env, Function.update_of_ne (show (41 : Var) ≠ 48 by decide)]
          have h41 : (w.setv 47 j).env 41 = w.env 41 := by simp
          have e : (j + 1) * (x.B.length + 2) = j * (x.B.length + 2) + (x.B.length + 2) := by ring
          omega
        · exact ((wW.trans (Wr.setv _ (by decide) _)).trans (hstW.mono (fun y hy => by
            simp only [iterW, List.mem_cons]; exact Or.inr (Or.inr hy)))).trans (Wr.setv _ (by decide) _))
  rw [hm] at hl
  obtain ⟨a, b, -, d, c⟩ := hl
  exact ⟨a, b, c, d⟩

end NearCubicGates.Adapters.ShortPCP.Machines.FL
