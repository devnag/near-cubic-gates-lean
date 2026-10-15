import Proof.Wire_3_5.FinalPassFiltTabSel

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.GF2

variable (cap : ℕ)

/-! ## The product in the layout -/

theorem w_accst (x : TSt) (a b : List Bool) : ({ x with acc := a, st := b } : TSt).w = (x.w.sets qACC a).sets qST b := by
  rw [w_acc, w_st]

theorem fmulT_spec (Y : Fin 12) (hY : Y = qFV ∨ Y = qPW) (x : TSt) (p y xv : ℕ) (hm : 1 ≤ x.m)
    (hcap : 2 * x.m + 2 ≤ cap) (hYw : x.w.st Y = frame (binary x.m y)) (hYh : x.w.sh Y = 0)
    (hacc : x.acc = frame (binary x.m 0)) (hst : x.st = frame (binary x.m xv))
    (hpm : x.pmw = frame (binary x.m p)) (hf : x.f = 0) :
    WExec cap (fmulW Y qACC qST qPM gF gG gR gRY) x.w
      { x with acc := frame (binary x.m (fmulShift p x.m xv y)),
               st := frame (binary x.m (mulFrom p x.m y 0 x.m 0 xv).2) }.w
      (x.m * (mulStepCost x.m + 2) + 14 * x.m + 3) := by
  have hYA : Y ≠ qACC := by rcases hY with rfl | rfl <;> decide
  have hYS : Y ≠ qST := by rcases hY with rfl | rfl <;> decide
  have hL : MulLayout Y qACC qST qPM gF gG gR gRY := by
    rcases hY with rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨τ, h, hI, hfr⟩ := fmulW_spec cap Y qACC qST qPM gF gG gR gRY hL x.m p xv y hm hcap x.w
    ⟨hYw, by rw [hYh], rfl, hacc, rfl, hst, rfl, hpm, rfl, hf, rfl, rfl⟩
  obtain ⟨hY', hhY', hRY', hA', hhA', hS', hhS', hP', hhP', hF', hG', hR'⟩ := hI
  refine WExec.cast cap h ?_ le_rfl
  rw [w_accst]
  refine WState.eq ?_ ?_ ?_ ?_
  · funext i
    simp only [WState.sets_sh]
    by_cases hi : i = Y ∨ i = qACC ∨ i = qST
    · rcases hi with rfl | rfl | rfl
      · rw [hhY', hYh]
      · rw [hhA']; rfl
      · rw [hhS']; rfl
    · exact (hfr.1 i hi).2
  · funext i
    simp only [WState.sets_st, Function.update_apply]
    by_cases hS : i = qST
    · subst hS; rw [hS', if_pos rfl]
    · rw [if_neg hS]
      by_cases hA : i = qACC
      · subst hA; rw [hA', if_pos rfl]
      · rw [if_neg hA]
        by_cases hYi : i = Y
        · subst hYi; rw [hY', hYw]
        · exact (hfr.1 i (by rintro (h | h | h) <;> contradiction)).1
  · funext r
    simp only [WState.sets_val]
    by_cases hr : r = gF ∨ r = gG ∨ r = gR ∨ r = gRY
    · rcases hr with rfl | rfl | rfl | rfl
      · rw [hF']; exact hf.symm
      · rw [hG']; rfl
      · rw [hR']; rfl
      · rw [hRY']; rfl
    · exact hfr.2.1 r hr
  · exact hfr.2.2

/-! ## One coordinate -/

/-- `PW := PW · v`. -/
def kPow : TProg :=
  .seq (mapPass copyOut keepS qST qPW gF gR) (.seq (mapPass zeroOut keepS qACC qPW gF gR)
    (.seq (fmulW qFV qACC qST qPM gF gG gR gRY) (mapPass copyOut keepS qPW qACC gF gR)))

/-- `ACC := u · PW`. -/
def kProd : TProg :=
  .seq (mapPass copyOut keepS qST qFU gF gR) (.seq (mapPass zeroOut keepS qACC qPW gF gR)
    (fmulW qPW qACC qST qPM gF gG gR gRY))

/-- `TF := ⟨ACC, τ⟩`. -/
def kTr : TProg := .seq (mapPass keepA parNxt qACC qTAU gF gR) (WM.move gF gTF)

/-- Append the marker and the coefficient `!NS && TF`; clear the flags. -/
def kOut : TProg :=
  .seq (emitC qO gOP true) (.seq (.ifr gNS (emitC qO gOP false) (.ifr gTF (emitC qO gOP true) (emitC qO gOP false)))
    (.seq (WM.clear gNS) (WM.clear gTF)))

/-- `K := K + 1`. -/
def kInc : TProg := .seq (setFlag gF true) (.seq (mapPass Hash4.incOut Hash4.incNxt qK qBW gF gR) (WM.clear gF))

/-- One coordinate `k` of one copy. -/
def kStep : TProg := .seq kPow (.seq kProd (.seq kTr (.seq selT (.seq kOut kInc))))

theorem frame_bin (n v : ℕ) : frame (binary n v) = frameP (binary n v) ++ [false] := frame_eq_frameP _

/-- The cost of a product step (two passes, a product, a pass). -/
def mulCost (m : ℕ) : ℕ := 3 * (m * 41 + 3) + (m * (mulStepCost m + 2) + 14 * m + 3) + 3

theorem kPow_spec (x : TSt) (p v a0 s0 k : ℕ) (hm : 1 ≤ x.m)
    (hfv : x.fv = frame (binary x.m v)) (hpw : x.pw = frame (binary x.m (powN p x.m v k)))
    (hacc : x.acc = frame (binary x.m a0)) (hst : x.st = frame (binary x.m s0)) (hpm : x.pmw = frame (binary x.m p))
    (hf : x.f = 0) (hcap : 2 * x.m + 2 ≤ cap) :
    ∃ s1 : ℕ, WExec cap kPow x.w
      { x with pw := frame (binary x.m (powN p x.m v (k + 1))), acc := frame (binary x.m (powN p x.m v (k + 1))),
               st := frame (binary x.m s1) }.w (mulCost x.m) := by
  obtain ⟨wk, hwk⟩ : ∃ l : List Bool, l = frameP (binary x.m (powN p x.m v k)) ++ false :: [] := ⟨_, rfl⟩
  have s1 := mapPass_spec cap copyOut keepS qST qPW gF gR (by decide) (by decide) (by omega)
    (binary x.m s0) (binary x.m (powN p x.m v k)) [] [false] false x.w (by simp)
    (by show x.st = _; rw [hst, frame_bin]) rfl (by show x.pw = _; rw [hpw, frame_bin]) rfl
    (by show x.f = _; simp [hf]) rfl (by simp; omega)
  rw [mapS_copy _ _ _ (by simp), ← hwk, w_st, w_f] at s1
  obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { { x with st := wk } with f := (false).toNat } := ⟨_, rfl⟩
  rw [← hx1] at s1
  have hm1 : x1.m = x.m := by rw [hx1]
  obtain ⟨w0, hw0⟩ : ∃ l : List Bool, l = frameP (binary x.m 0) ++ false :: [] := ⟨_, rfl⟩
  have s2 := mapPass_spec cap zeroOut keepS qACC qPW gF gR (by decide) (by decide) (by omega)
    (binary x.m a0) (binary x.m (powN p x.m v k)) [] [false] false x1.w (by simp)
    (by rw [hx1]; show x.acc = _; rw [hacc, frame_bin]) rfl (by rw [hx1]; show x.pw = _; rw [hpw, frame_bin]) rfl
    (by rw [hx1]; rfl) rfl (by simp; omega)
  rw [mapS_zero _ _ _ (by simp), binary_length, ← binary_zero', ← hw0, w_acc, w_f] at s2
  obtain ⟨x2, hx2⟩ : ∃ y : TSt, y = { { x1 with acc := w0 } with f := (false).toNat } := ⟨_, rfl⟩
  rw [← hx2] at s2
  have hm2 : x2.m = x.m := by rw [hx2]; exact hm1
  have s3 := fmulT_spec cap qFV (Or.inl rfl) x2 p v (powN p x.m v k) (by rw [hm2]; exact hm)
    (by rw [hm2]; omega) (by rw [hm2, hx2, hx1]; show x.fv = _; rw [hfv]) (by rw [hx2, hx1]; rfl)
    (by rw [hm2, hx2, hw0, frame_bin]) (by rw [hm2, hx2, hx1, hwk, frame_bin]) (by rw [hm2, hx2, hx1]; exact hpm)
    (by rw [hx2]; rfl)
  obtain ⟨wa, hwa⟩ : ∃ l : List Bool, l = frame (binary x2.m (fmulShift p x2.m (powN p x.m v k) v)) := ⟨_, rfl⟩
  obtain ⟨ws, hws⟩ : ∃ l : List Bool, l = frame (binary x2.m (mulFrom p x2.m v 0 x2.m 0 (powN p x.m v k)).2) :=
    ⟨_, rfl⟩
  rw [← hwa, ← hws] at s3
  rw [hm2] at hwa hws
  have hp1 : fmulShift p x.m (powN p x.m v k) v = powN p x.m v (k + 1) := rfl
  rw [hp1] at hwa
  obtain ⟨x3, hx3⟩ : ∃ y : TSt, y = { x2 with acc := wa, st := ws } := ⟨_, rfl⟩
  rw [← hx3] at s3
  obtain ⟨wk1, hwk1⟩ : ∃ l : List Bool, l = frameP (binary x.m (powN p x.m v (k + 1))) ++ false :: [] := ⟨_, rfl⟩
  have s4 := mapPass_spec cap copyOut keepS qPW qACC gF gR (by decide) (by decide) (by omega)
    (binary x.m (powN p x.m v k)) (binary x.m (powN p x.m v (k + 1))) [] [false] false x3.w (by simp)
    (by rw [hx3, hx2, hx1]; show x.pw = _; rw [hpw, frame_bin]) rfl
    (by rw [hx3]; show wa = _; rw [hwa, frame_bin]) rfl (by rw [hx3, hx2]; rfl) rfl (by simp; omega)
  rw [mapS_copy _ _ _ (by simp), ← hwk1, w_pw, w_f] at s4
  refine ⟨(mulFrom p x.m v 0 x.m 0 (powN p x.m v k)).2, ?_⟩
  rw [← hwa, ← hws]
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · have e : ({ { x3 with pw := wk1 } with f := (false).toNat } : TSt) = { x with pw := wa, acc := wa, st := ws } := by
      rw [hx3, hx2, hx1, hwk1, ← frame_bin, hwa]
      cases x
      simp only at hf ⊢
      subst hf
      rfl
    rw [e]
  · unfold mulCost; simp only [binary_length, hm2]; omega

theorem kProd_spec (x : TSt) (p u w a0 s0 : ℕ) (hm : 1 ≤ x.m)
    (hfu : x.fu = frame (binary x.m u)) (hpw : x.pw = frame (binary x.m w))
    (hacc : x.acc = frame (binary x.m a0)) (hst : x.st = frame (binary x.m s0)) (hpm : x.pmw = frame (binary x.m p))
    (hf : x.f = 0) (hcap : 2 * x.m + 2 ≤ cap) :
    ∃ s1 : ℕ, WExec cap kProd x.w
      { x with acc := frame (binary x.m (fmulShift p x.m u w)), st := frame (binary x.m s1) }.w (mulCost x.m) := by
  obtain ⟨wu, hwu⟩ : ∃ l : List Bool, l = frameP (binary x.m u) ++ false :: [] := ⟨_, rfl⟩
  have s1 := mapPass_spec cap copyOut keepS qST qFU gF gR (by decide) (by decide) (by omega)
    (binary x.m s0) (binary x.m u) [] [false] false x.w (by simp)
    (by show x.st = _; rw [hst, frame_bin]) rfl (by show x.fu = _; rw [hfu, frame_bin]) rfl
    (by show x.f = _; simp [hf]) rfl (by simp; omega)
  rw [mapS_copy _ _ _ (by simp), ← hwu, w_st, w_f] at s1
  obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { { x with st := wu } with f := (false).toNat } := ⟨_, rfl⟩
  rw [← hx1] at s1
  have hm1 : x1.m = x.m := by rw [hx1]
  obtain ⟨w0, hw0⟩ : ∃ l : List Bool, l = frameP (binary x.m 0) ++ false :: [] := ⟨_, rfl⟩
  have s2 := mapPass_spec cap zeroOut keepS qACC qPW gF gR (by decide) (by decide) (by omega)
    (binary x.m a0) (binary x.m w) [] [false] false x1.w (by simp)
    (by rw [hx1]; show x.acc = _; rw [hacc, frame_bin]) rfl (by rw [hx1]; show x.pw = _; rw [hpw, frame_bin]) rfl
    (by rw [hx1]; rfl) rfl (by simp; omega)
  rw [mapS_zero _ _ _ (by simp), binary_length, ← binary_zero', ← hw0, w_acc, w_f] at s2
  obtain ⟨x2, hx2⟩ : ∃ y : TSt, y = { { x1 with acc := w0 } with f := (false).toNat } := ⟨_, rfl⟩
  rw [← hx2] at s2
  have hm2 : x2.m = x.m := by rw [hx2]; exact hm1
  have s3 := fmulT_spec cap qPW (Or.inr rfl) x2 p w u (by rw [hm2]; exact hm)
    (by rw [hm2]; omega) (by rw [hm2, hx2, hx1]; show x.pw = _; rw [hpw]) (by rw [hx2, hx1]; rfl)
    (by rw [hm2, hx2, hw0, frame_bin]) (by rw [hm2, hx2, hx1, hwu, frame_bin]) (by rw [hm2, hx2, hx1]; exact hpm)
    (by rw [hx2]; rfl)
  obtain ⟨wa, hwa⟩ : ∃ l : List Bool, l = frame (binary x2.m (fmulShift p x2.m u w)) := ⟨_, rfl⟩
  obtain ⟨ws, hws⟩ : ∃ l : List Bool, l = frame (binary x2.m (mulFrom p x2.m w 0 x2.m 0 u).2) := ⟨_, rfl⟩
  rw [← hwa, ← hws] at s3
  rw [hm2] at hwa hws
  refine ⟨(mulFrom p x.m w 0 x.m 0 u).2, ?_⟩
  rw [← hwa, ← hws]
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ ?_
  · have e : ({ x2 with acc := wa, st := ws } : TSt) = { x with acc := wa, st := ws } := by
      rw [hx2, hx1]
      cases x
      simp only at hf ⊢
      subst hf
      rfl
    rw [e]
  · unfold mulCost; simp only [binary_length, hm2]; omega

theorem kTr_spec (x : TSt) (pr tv : ℕ) (hacc : x.acc = frame (binary x.m pr)) (htau : x.tauw = frame (binary x.m tv))
    (hf : x.f = 0) (htf : x.tf = 0) (hcap : 2 * x.m + 2 ≤ cap) :
    WExec cap kTr x.w { x with tf := (parW (binary x.m pr) (binary x.m tv)).toNat }.w (x.m * 41 + 13) := by
  have s1 := mapPass_spec cap keepA parNxt qACC qTAU gF gR (by decide) (by decide) (by omega)
    (binary x.m pr) (binary x.m tv) [] [false] false x.w (by simp)
    (by show x.acc = _; rw [hacc, frame_bin]) rfl (by show x.tauw = _; rw [htau, frame_bin]) rfl
    (by show x.f = _; simp [hf]) rfl (by simp; omega)
  rw [mapS_par _ _ _ (by simp), Bool.false_xor] at s1
  have hacc' : frameP (binary x.m pr) ++ false :: [] = x.acc := by rw [hacc, frame_bin]
  rw [hacc', w_acc, w_f] at s1
  obtain ⟨tb, htb⟩ : ∃ b : Bool, b = parW (binary x.m pr) (binary x.m tv) := ⟨_, rfl⟩
  rw [← htb] at s1 ⊢
  obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { { x with acc := x.acc } with f := tb.toNat } := ⟨_, rfl⟩
  rw [← hx1] at s1
  have htb1 := Bool.toNat_le tb
  have s2 := wmove_spec cap gF gTF (by decide) tb.toNat x1.w (by rw [hx1]; rfl)
    (by rw [hx1]; show tb.toNat ≤ cap; omega)
    (by rw [hx1]; show x.tf + tb.toNat ≤ cap; omega)
  have h1 : x1.w.val gTF = 0 := by rw [hx1]; exact htf
  have h2 : x1.w.val gF = tb.toNat := by rw [hx1]; rfl
  rw [w_f, w_tf, h1, h2, Nat.zero_add] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by simp only [binary_length]; omega)
  rw [hx1]
  cases x
  simp only at hf ⊢
  subst hf
  rfl

theorem kOut_spec (x : TSt) (nb tb : Bool) (hns : x.ns = nb.toNat) (htf : x.tf = tb.toNat)
    (hO : x.ow.length + 2 < cap) :
    WExec cap kOut x.w { x with ow := x.ow ++ [true, !nb && tb], ns := 0, tf := 0 }.w 30 := by
  have s1 := emitC_spec cap qO gOP true x.w (by show x.ow.length = x.ow.length; rfl) (by show x.ow.length < cap; omega)
  rw [w_o_emit] at s1
  obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { x with ow := x.ow ++ [true] } := ⟨_, rfl⟩
  rw [← hx1] at s1
  have hO1 : x1.w.sh qO = (x1.w.st qO).length := by rw [hx1]; rfl
  have hc1 : x1.w.val gOP < cap := by rw [hx1]; show (x.ow ++ [true]).length < cap; simp; omega
  obtain ⟨x2, hx2⟩ : ∃ y : TSt, y = { x1 with ow := x1.ow ++ [!nb && tb] } := ⟨_, rfl⟩
  have s2 : WExec cap (.ifr gNS (emitC qO gOP false) (.ifr gTF (emitC qO gOP true) (emitC qO gOP false))) x1.w x2.w 9 := by
    have hns1 : x1.w.val gNS = nb.toNat := by rw [hx1]; exact hns
    have htf1 : x1.w.val gTF = tb.toNat := by rw [hx1]; exact htf
    cases nb
    · cases tb
      · have h := emitC_spec cap qO gOP false x1.w hO1 hc1
        rw [w_o_emit] at h
        exact WExec.mono (WExec.ifrF hns1 (WExec.ifrF htf1 (by rw [hx2]; exact h))) (by omega)
      · have h := emitC_spec cap qO gOP true x1.w hO1 hc1
        rw [w_o_emit] at h
        exact WExec.mono (WExec.ifrF hns1 (WExec.ifrT (by rw [htf1]; decide) (by rw [hx2]; exact h))) (by omega)
    · have h := emitC_spec cap qO gOP false x1.w hO1 hc1
      rw [w_o_emit] at h
      exact WExec.mono (WExec.ifrT (by rw [hns1]; decide) (by rw [hx2]; exact h)) (by omega)
  have hnb1 := Bool.toNat_le nb
  have htb1 := Bool.toNat_le tb
  have s3 := wclear_spec cap gNS nb.toNat x2.w (by rw [hx2, hx1]; exact hns)
    (by rw [hx2, hx1]; show x.ns ≤ cap; rw [hns]; omega)
  rw [w_ns] at s3
  obtain ⟨x3, hx3⟩ : ∃ y : TSt, y = { x2 with ns := 0 } := ⟨_, rfl⟩
  rw [← hx3] at s3
  have s4 := wclear_spec cap gTF tb.toNat x3.w (by rw [hx3, hx2, hx1]; exact htf)
    (by rw [hx3, hx2, hx1]; show x.tf ≤ cap; rw [htf]; omega)
  rw [w_tf] at s4
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · rw [hx3, hx2, hx1]
    cases x
    simp
  · omega

theorem kInc_spec (x : TSt) (k : ℕ) (bwb : List Bool) (hkw : x.kw = frame (binary x.lb k)) (hbw : x.bw = frame bwb)
    (hbwl : bwb.length = x.lb) (hf : x.f = 0) (hbwh : x.bwh = 0) (hcap : 2 * x.lb + 2 ≤ cap) :
    WExec cap kInc x.w { x with kw := frame (binary x.lb (k + 1)) }.w (x.lb * 41 + 3 * 1 + 12) := by
  have s1 := setFlag_spec cap gF true false x.w (by show x.f = _; simp [hf]) (by omega)
  rw [w_f] at s1
  obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { x with f := (true).toNat } := ⟨_, rfl⟩
  rw [← hx1] at s1
  have s2 := mapPass_spec cap Hash4.incOut Hash4.incNxt qK qBW gF gR (by decide) (by decide) (by omega)
    (binary x.lb k) bwb [] [false] true x1.w (by simp [hbwl])
    (by rw [hx1]; show x.kw = _; rw [hkw, frame_bin]) rfl (by rw [hx1]; show x.bw = _; rw [hbw, frame_eq_frameP])
    (by rw [hx1]; exact hbwh) (by rw [hx1]; rfl) rfl (by simp; omega)
  have hinc := Hash4.mapS_inc x.lb k bwb hbwl
  rw [hinc, w_kw, w_f] at s2
  obtain ⟨cb, hcb⟩ : ∃ b : Bool, b = (mapS Hash4.incOut Hash4.incNxt (binary x.lb k) bwb true).2 := ⟨_, rfl⟩
  rw [← hcb] at s2
  obtain ⟨x2, hx2⟩ : ∃ y : TSt, y = { { x1 with kw := frameP (binary x.lb (k + 1)) ++ false :: [] } with
                                            f := cb.toNat } := ⟨_, rfl⟩
  rw [← hx2] at s2
  have hcb1 := Bool.toNat_le cb
  have s3 := wclear_spec cap gF cb.toNat x2.w (by rw [hx2]; rfl) (by rw [hx2]; show cb.toNat ≤ cap; omega)
  rw [w_f] at s3
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ ?_
  · rw [hx2, hx1, ← frame_bin]
    cases x
    simp only at hf ⊢
    subst hf
    rfl
  · simp only [binary_length]; omega

/-- The cost of one coordinate. -/
def kStepCost (m lb a : ℕ) : ℕ :=
  mulCost m + 1 + (mulCost m + 1 + ((m * 41 + 13) + 1 + (selTCost lb a + 1 + (30 + 1 + (lb * 41 + 3 * 1 + 12)))))

/-- The coefficient bit of coordinate `k`: not excluded by the prefix test, and the trace bit. -/
def coefBit (kb epb bwb : List Bool) (lb a : ℕ) (prod tv : List Bool) : Bool :=
  !mism kb epb bwb lb 0 a && parW prod tv

/-- **One coordinate**: the power, the product, the trace bit, the inclusion test, the output, the next label. -/
theorem kStep_spec (x : TSt) (p v u tv a0 s0 k : ℕ) (epb bwb : List Bool)
    (hm : 1 ≤ x.m) (hlbE : x.lb = epb.length / 2 + 1) (hepl : 1 ≤ epb.length ∧ epb.length % 2 = 1)
    (hbwl : bwb.length = x.lb) (ha : x.a ≤ x.lb)
    (hfv : x.fv = frame (binary x.m v)) (hfu : x.fu = frame (binary x.m u))
    (hpw : x.pw = frame (binary x.m (powN p x.m v k))) (hacc : x.acc = frame (binary x.m a0))
    (hst : x.st = frame (binary x.m s0)) (htau : x.tauw = frame (binary x.m tv)) (hpm : x.pmw = frame (binary x.m p))
    (hkw : x.kw = frame (binary x.lb k)) (hbw : x.bw = frame bwb) (hep : x.ep = frame epb)
    (hf : x.f = 0) (hns : x.ns = 0) (htf : x.tf = 0) (hs : x.s = 0) (hj : x.j = 0) (heph : x.eph = 0)
    (hbwh : x.bwh = 0) (hcap : 4 * x.lb + 2 * x.m + 8 ≤ cap) (hO : x.ow.length + 2 < cap) :
    ∃ a1 s1 : ℕ, WExec cap kStep x.w
      { x with pw := frame (binary x.m (powN p x.m v (k + 1))), acc := frame (binary x.m a1),
               st := frame (binary x.m s1), kw := frame (binary x.lb (k + 1)),
               ow := x.ow ++ [true, coefBit (binary x.lb k) epb bwb x.lb x.a
                 (binary x.m (fmulShift p x.m u (powN p x.m v (k + 1)))) (binary x.m tv)] }.w
      (kStepCost x.m x.lb x.a) := by
  -- the power
  obtain ⟨s1, h1⟩ := kPow_spec cap x p v a0 s0 k hm hfv hpw hacc hst hpm hf (by omega)
  obtain ⟨P1, hP1⟩ : ∃ l : List Bool, l = frame (binary x.m (powN p x.m v (k + 1))) := ⟨_, rfl⟩
  obtain ⟨S1, hS1⟩ : ∃ l : List Bool, l = frame (binary x.m s1) := ⟨_, rfl⟩
  rw [← hP1, ← hS1] at h1
  obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { x with pw := P1, acc := P1, st := S1 } := ⟨_, rfl⟩
  rw [← hx1] at h1
  have hm1 : x1.m = x.m := by rw [hx1]
  -- the product
  obtain ⟨pr, hpr⟩ : ∃ n : ℕ, n = fmulShift p x.m u (powN p x.m v (k + 1)) := ⟨_, rfl⟩
  obtain ⟨s2, h2⟩ := kProd_spec cap x1 p u (powN p x.m v (k + 1)) (powN p x.m v (k + 1)) s1 (by rw [hm1]; exact hm)
    (by rw [hm1, hx1]; exact hfu) (by rw [hm1, hx1, hP1]) (by rw [hm1, hx1, hP1]) (by rw [hm1, hx1, hS1])
    (by rw [hm1, hx1]; exact hpm) (by rw [hx1]; exact hf) (by rw [hm1]; omega)
  obtain ⟨A2, hA2⟩ : ∃ l : List Bool, l = frame (binary x1.m (fmulShift p x1.m u (powN p x.m v (k + 1)))) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ l : List Bool, l = frame (binary x1.m s2) := ⟨_, rfl⟩
  rw [← hA2, ← hS2] at h2
  rw [hm1, ← hpr] at hA2
  rw [hm1] at hS2
  obtain ⟨x2, hx2⟩ : ∃ y : TSt, y = { x1 with acc := A2, st := S2 } := ⟨_, rfl⟩
  rw [← hx2] at h2
  have hm2 : x2.m = x.m := by rw [hx2]; exact hm1
  -- the trace bit
  have h3 := kTr_spec cap x2 pr tv (by rw [hm2, hx2, hA2]) (by rw [hm2, hx2, hx1]; exact htau)
    (by rw [hx2, hx1]; exact hf) (by rw [hx2, hx1]; exact htf) (by rw [hm2]; omega)
  obtain ⟨tb, htb⟩ : ∃ b : Bool, b = parW (binary x2.m pr) (binary x2.m tv) := ⟨_, rfl⟩
  rw [← htb] at h3
  rw [hm2] at htb
  obtain ⟨x3, hx3⟩ : ∃ y : TSt, y = { x2 with tf := tb.toNat } := ⟨_, rfl⟩
  rw [← hx3] at h3
  have hlb3 : x3.lb = x.lb := by rw [hx3, hx2, hx1]
  have ha3 : x3.a = x.a := by rw [hx3, hx2, hx1]
  -- the inclusion test
  have h4 := selT_spec cap x3 (binary x.lb k) epb bwb (by rw [hlb3]; exact hlbE) (by simp [hlbE]) hepl
    (by rw [hbwl, hlbE]) (by rw [hx3, hx2, hx1, hkw, frame_bin]) (by rw [hx3, hx2, hx1, hep, frame_eq_frameP])
    (by rw [hx3, hx2, hx1, hbw, frame_eq_frameP]) (by rw [hlb3, ha3]; exact ha) (by rw [hx3, hx2, hx1]; exact hs)
    (by rw [hx3, hx2, hx1]; exact hj) (by rw [hx3, hx2, hx1]; exact heph) (by rw [hx3, hx2, hx1]; exact hbwh)
    (by rw [hx3, hx2, hx1]; exact hf) (by rw [hx3, hx2, hx1]; exact hns) (by rw [hlb3]; omega)
  obtain ⟨nb, hnb⟩ : ∃ b : Bool, b = mism (binary x.lb k) epb bwb x3.lb 0 x3.a := ⟨_, rfl⟩
  rw [← hnb] at h4
  rw [hlb3, ha3] at hnb
  obtain ⟨x4, hx4⟩ : ∃ y : TSt, y = { x3 with ns := nb.toNat } := ⟨_, rfl⟩
  rw [← hx4] at h4
  -- the output
  have h5 := kOut_spec cap x4 nb tb (by rw [hx4]) (by rw [hx4, hx3]) (by rw [hx4, hx3, hx2, hx1]; exact hO)
  obtain ⟨x5, hx5⟩ : ∃ y : TSt, y = { x4 with ow := x4.ow ++ [true, !nb && tb], ns := 0, tf := 0 } := ⟨_, rfl⟩
  rw [← hx5] at h5
  have hlb5 : x5.lb = x.lb := by rw [hx5, hx4]; exact hlb3
  -- the next label
  have h6 := kInc_spec cap x5 k bwb (by rw [hlb5, hx5, hx4, hx3, hx2, hx1]; exact hkw)
    (by rw [hx5, hx4, hx3, hx2, hx1]; exact hbw) (by rw [hlb5]; exact hbwl) (by rw [hx5, hx4, hx3, hx2, hx1]; exact hf)
    (by rw [hx5, hx4, hx3, hx2, hx1]; exact hbwh) (by rw [hlb5]; omega)
  refine ⟨pr, s2, ?_⟩
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 h6))))) ?_ ?_
  · have e : ({ x5 with kw := frame (binary x5.lb (k + 1)) } : TSt) =
        { x with pw := P1, acc := A2, st := S2, kw := frame (binary x.lb (k + 1)),
                 ow := x.ow ++ [true, !nb && tb] } := by
      rw [hlb5, hx5, hx4, hx3, hx2, hx1]
      cases x
      simp only at hns htf ⊢
      subst hns htf
      rfl
    rw [e, hP1, hA2, hS2, hnb, htb, hpr]
    rfl
  · have hm3 : x3.m = x.m := by rw [hx3]; exact hm2
    rw [hm1, hm2, hlb3, ha3, hlb5]
    unfold kStepCost; omega

end NearCubicWires.WireExponent3_5.FinalPass.Filt
