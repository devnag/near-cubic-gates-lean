import Proof.Wire_3_5.FinalPassFlatWord
import Proof.Wire_3_5.FinalPassFlatRef
import Proof.Wire_3_5.FinalPassFiltTabStep

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Flat
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Filt

/-! ## The layout with the extra heads -/

/-- The emitter's state: stage 6's record, the heads of `TAU` and `PM`, and the counters `G`, `RY`. -/
structure LSt extends TSt where
  tauh : ℕ
  pmh : ℕ
  g1 : ℕ
  g3 : ℕ

/-- The word state of an emitter record. -/
def LSt.w (x : LSt) : TState :=
  ⟨![x.vh, x.ow.length, x.tauh, x.pmh, 0, 0, 0, 0, 0, 0, x.bwh, x.eph],
   ![x.vw, x.ow, x.tauw, x.pmw, x.fv, x.fu, x.pw, x.acc, x.st, x.kw, x.bw, x.ep],
   ![x.f, x.g1, 0, x.g3, x.vh, x.ow.length, x.m, x.lb, x.lb - 1, x.a, x.L, 0, x.ck, x.s, x.ns, x.tf, x.eph, x.j,
     x.bwh],
   x.cell⟩

/-- Close an equality of word states against emitter records. -/
syntax "lst_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lst_eq) => `(tactic| lst_eq [])
  | `(tactic| lst_eq [$ts,*]) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | (funext i; fin_cases i <;> first | rfl | (simp [LSt.w, TSt.w, $ts,*]; done) |
            (simp [LSt.w, TSt.w, $ts,*] <;> omega))
        | rfl
        | (simp [LSt.w, TSt.w, $ts,*]; done)))

/-- With the extra heads and counters at `0`, the emitter record is stage 6's record. -/
theorem LSt.w_eq (x : LSt) (h1 : x.tauh = 0) (h2 : x.pmh = 0) (h3 : x.g1 = 0) (h4 : x.g3 = 0) :
    x.w = x.toTSt.w := by
  lst_eq [h1, h2, h3, h4]

section Upd
variable (x : LSt)

@[simp] theorem l_valF : x.w.val gF = x.f := rfl
@[simp] theorem l_valG : x.w.val gG = x.g1 := rfl
@[simp] theorem l_valRY : x.w.val gRY = x.g3 := rfl
@[simp] theorem l_valT : x.w.val gT = 0 := rfl
@[simp] theorem l_valR : x.w.val gR = 0 := rfl
@[simp] theorem l_valM : x.w.val gM = x.m := rfl
@[simp] theorem l_valLB : x.w.val gLB = x.lb := rfl
@[simp] theorem l_valLB1 : x.w.val gLB1 = x.lb - 1 := rfl
@[simp] theorem l_valA : x.w.val gA = x.a := rfl
@[simp] theorem l_valL : x.w.val gL = x.L := rfl
@[simp] theorem l_valCK : x.w.val gCK = x.ck := rfl
@[simp] theorem l_valS : x.w.val gS = x.s := rfl
@[simp] theorem l_valNS : x.w.val gNS = x.ns := rfl
@[simp] theorem l_valTF : x.w.val gTF = x.tf := rfl
@[simp] theorem l_valEP : x.w.val gEP = x.eph := rfl
@[simp] theorem l_valJ : x.w.val gJ = x.j := rfl
@[simp] theorem l_valVP : x.w.val gVP = x.vh := rfl
@[simp] theorem l_valBWP : x.w.val gBWP = x.bwh := rfl
@[simp] theorem l_shV : x.w.sh qV = x.vh := rfl
@[simp] theorem l_shTAU : x.w.sh qTAU = x.tauh := rfl
@[simp] theorem l_shPM : x.w.sh qPM = x.pmh := rfl
@[simp] theorem l_shEP : x.w.sh qEP = x.eph := rfl
@[simp] theorem l_stV : x.w.st qV = x.vw := rfl
@[simp] theorem l_stTAU : x.w.st qTAU = x.tauw := rfl
@[simp] theorem l_stPM : x.w.st qPM = x.pmw := rfl
@[simp] theorem l_stEP : x.w.st qEP = x.ep := rfl
@[simp] theorem l_stBW : x.w.st qBW = x.bw := rfl

theorem l_s (n : ℕ) : x.w.setv gS n = { x with s := n }.w := by lst_eq
theorem l_tau_adv (n : ℕ) : (x.w.seth qTAU (x.w.sh qTAU + 2 * n)).setv gG (x.w.val gG + 2 * n) =
    { x with tauh := x.tauh + 2 * n, g1 := x.g1 + 2 * n }.w := by lst_eq
theorem l_tau_ret (n : ℕ) : (x.w.seth qTAU (x.w.sh qTAU - 2 * n)).setv gG (x.w.val gG - 2 * n) =
    { x with tauh := x.tauh - 2 * n, g1 := x.g1 - 2 * n }.w := by lst_eq
theorem l_pm_ret (n : ℕ) : (x.w.seth qPM (x.w.sh qPM - 2 * n)).setv gG (x.w.val gG - 2 * n) =
    { x with pmh := x.pmh - 2 * n, g1 := x.g1 - 2 * n }.w := by lst_eq
theorem l_pm_rew : (x.w.setv gRY 0).seth qPM (x.w.sh qPM - x.g3) = { x with pmh := x.pmh - x.g3, g3 := 0 }.w := by
  lst_eq
theorem l_v_rew : (x.w.setv gVP 0).seth qV (x.w.sh qV - x.vh) = { x with vh := 0 }.w := by lst_eq
theorem l_ep_adv (n : ℕ) : (x.w.seth qEP (x.w.sh qEP + 2 * n)).setv gEP (x.w.val gEP + 2 * n) =
    { x with eph := x.eph + 2 * n }.w := by lst_eq
theorem l_pm_adv (n : ℕ) : (x.w.seth qPM (x.w.sh qPM + 2 * n)).setv gG (x.w.val gG + 2 * n) =
    { x with pmh := x.pmh + 2 * n, g1 := x.g1 + 2 * n }.w := by lst_eq
theorem l_pm_retRY (n : ℕ) : (x.w.seth qPM (x.w.sh qPM - 2 * n)).setv gRY (x.w.val gRY - 2 * n) =
    { x with pmh := x.pmh - 2 * n, g3 := x.g3 - 2 * n }.w := by lst_eq
theorem l_pm_rewG : (x.w.setv gG 0).seth qPM (x.w.sh qPM - x.g1) = { x with pmh := x.pmh - x.g1, g1 := 0 }.w := by
  lst_eq
theorem l_ep_rew : (x.w.setv gEP 0).seth qEP (x.w.sh qEP - x.eph) = { x with eph := 0 }.w := by lst_eq
theorem l_bw_rew : (x.w.setv gBWP 0).seth qBW (x.w.sh qBW - x.bwh) = { x with bwh := 0 }.w := by lst_eq
theorem l_rev (sa : List Bool) (hb : ℕ) (vp : ℕ) :
    ((((((x.w.sets qEP sa).sets qPM x.pmw).seth qEP 0).seth qPM hb).setv gS 0).setv gRY vp).setv gEP 0 =
      { x with ep := sa, eph := 0, pmh := hb, s := 0, g3 := vp }.w := by lst_eq
theorem l_fcE (sa : List Bool) (ha hb vc : ℕ) :
    (((((x.w.sets qEP sa).sets qPM x.pmw).seth qEP ha).seth qPM hb).setv gS vc).setv gEP ha =
      { x with ep := sa, eph := ha, pmh := hb, s := vc }.w := by lst_eq
theorem l_fcB (sa : List Bool) (ha hb vc : ℕ) :
    (((((x.w.sets qBW sa).sets qPM x.pmw).seth qBW ha).seth qPM hb).setv gS vc).setv gBWP ha =
      { x with bw := sa, bwh := ha, pmh := hb, s := vc }.w := by lst_eq
theorem l_fcY (sa : List Bool) (ha hb vc vp : ℕ) :
    (((((x.w.sets qPM sa).sets qTAU x.tauw).seth qPM ha).seth qTAU hb).setv gS vc).setv gRY vp =
      { x with pmw := sa, pmh := ha, tauh := hb, s := vc, g3 := vp }.w := by lst_eq
theorem l_fcX (sa : List Bool) (ha hb vc : ℕ) :
    (((((x.w.sets qPM sa).sets qV x.vw).seth qPM ha).seth qV hb).setv gS vc).setv gVP hb =
      { x with pmw := sa, pmh := ha, vh := hb, s := vc }.w := by lst_eq
theorem l_g1 (n : ℕ) : x.w.setv gG n = { x with g1 := n }.w := by lst_eq
theorem l_g3 (n : ℕ) : x.w.setv gRY n = { x with g3 := n }.w := by lst_eq

end Upd

variable (cap : ℕ)

/-! ## The seed bits -/

/-- **The seed word**: `PM := N[pad, 2s)` from `y` (on `TAU`, after its first `pad` bits) and `x` (on `V`). -/
def mkSeed : TProg :=
  .seq (advC qTAU gTF gT gG) (.seq (Hash4.wcopyR gM gS gT) (.seq (.ifr gTF (.dec gS) .skip)
  (.seq (fcLoop qPM qTAU gS gRY) (.seq (retC qTAU gM gT gG) (.seq (Hash4.wcopyR gM gS gT)
  (.seq (fcLoop qPM qV gS gVP) (.seq (WM.rewind qPM gRY) (.seq (retC qPM gM gT gG) (WM.rewind qV gVP)))))))))

/-- The seed word's cost. -/
def mkSeedCost (sd : ℕ) : ℕ := 200 * sd + 100

theorem mkSeed_spec (x : LSt) (yb xb pmOld restY restX restP : List Bool)
    (hty : x.tauw = frameP yb ++ restY) (htx : x.vw = frameP xb ++ restX) (hpm : x.pmw = frameP pmOld ++ restP)
    (hyl : yb.length = x.m) (hxl : xb.length = x.m) (hpl : pmOld.length = 2 * x.m - x.tf) (hpad : x.tf ≤ 1)
    (hps : x.tf ≤ x.m)
    (htauh : x.tauh = 0) (hpmh : x.pmh = 0) (hvh : x.vh = 0) (hg1 : x.g1 = 0) (hg3 : x.g3 = 0) (hs : x.s = 0)
    (hcap : 8 * x.m + 8 ≤ cap) :
    WExec cap mkSeed x.w { x with pmw := frameP ((yb ++ xb).drop x.tf) ++ restP }.w (mkSeedCost x.m) := by
  -- TAU past the padding
  have s1 := advC_spec cap qTAU gTF gT gG (by decide) (by decide) (by decide) x.tf x.w rfl rfl (by omega)
    (by simp [hg1]; omega)
  rw [l_tau_adv] at s1
  obtain ⟨y1, hy1⟩ : ∃ y : LSt, y = { x with tauh := x.tauh + 2 * x.tf, g1 := x.g1 + 2 * x.tf } := ⟨_, rfl⟩
  rw [← hy1] at s1
  -- S := side − pad
  have s2 := Hash4.wcopyR_spec cap gM gS gT (by decide) (by decide) (by decide) y1.w (by rw [hy1]; simp [hs]) rfl
    (by rw [hy1]; simp; omega)
  rw [l_s] at s2
  obtain ⟨y2, hy2⟩ : ∃ y : LSt, y = { y1 with s := y1.w.val gM } := ⟨_, rfl⟩
  rw [← hy2] at s2
  have hy2s : y2.s = x.m := by rw [hy2, hy1]; rfl
  have s3 : WExec cap (.ifr gTF (.dec gS) .skip) y2.w { y2 with s := x.m - x.tf }.w 2 := by
    rcases Nat.lt_or_ge x.tf 1 with h0 | h1
    · have e : x.tf = 0 := by omega
      refine WExec.cast cap (WExec.ifrF (by rw [hy2, hy1]; simp [e]) (WExec.skip _)) ?_ (by omega)
      congr 1; rw [hy2, hy1]; simp [e]
    · have e : x.tf = 1 := by omega
      have d := WExec.dec (cap := cap) gS y2.w (by simp [hy2s]; omega)
      rw [l_valS, l_s, hy2s] at d
      exact WExec.cast cap (WExec.ifrT (by rw [hy2, hy1]; simp [e]) d) (by rw [e]) (by omega)
  obtain ⟨y3, hy3⟩ : ∃ y : LSt, y = { y2 with s := x.m - x.tf } := ⟨_, rfl⟩
  rw [← hy3] at s3
  -- copy y
  have hyb : yb = yb.take x.tf ++ yb.drop x.tf := (List.take_append_drop _ _).symm
  obtain ⟨t4, e4, h41, h42, h43, h44, h45, h46, hf4⟩ := fcLoop_spec cap qPM qTAU gS gRY (by decide) (by decide)
    (x.m - x.tf) pmOld (yb.drop x.tf) [] (frameP (yb.take x.tf)) restP restY y3.w
    (by rw [hy3]; rfl) (by omega) (by simp; omega) (by rw [hy3, hy2, hy1]; simp [hpm])
    (by rw [hy3, hy2, hy1]; simp [hpmh])
    (by rw [hy3, hy2, hy1]; show x.tauw = _; rw [hty, hyb, frameP_append]; simp)
    (by rw [hy3, hy2, hy1]; simp [htauh]; omega) (by rw [hy3, hy2, hy1]; simp [hg3]; omega) (by omega)
  rw [wframe_eq y3.w t4 qPM qTAU gS gRY (by decide) (by decide) _ _ _ _ _ _ hf4 h41 h42 h43 h44 h46 h45] at e4
  rw [show y3.w.st qTAU = y3.tauw from rfl, l_fcY, l_valRY] at e4
  obtain ⟨p4, hp4⟩ : ∃ l : List Bool, l = [] ++ frameP ((yb.drop x.tf).take (x.m - x.tf) ++
      pmOld.drop (x.m - x.tf)) ++ restP := ⟨_, rfl⟩
  obtain ⟨th4, hth4⟩ : ∃ n : ℕ, n = (frameP (yb.take x.tf)).length + 2 * (x.m - x.tf) := ⟨_, rfl⟩
  rw [← hp4, ← hth4] at e4
  obtain ⟨y4, hy4⟩ : ∃ y : LSt, y = { y3 with pmw := p4, pmh := ([] : List Bool).length + 2 * (x.m - x.tf), tauh := th4, s := 0, g3 := y3.g3 + 2 * (x.m - x.tf) } :=
    ⟨_, rfl⟩
  rw [← hy4] at e4
  -- TAU back
  have s5 := retC_spec cap qTAU gM gT gG (by decide) (by decide) (by decide) x.m y4.w
    (by rw [hy4, hy3, hy2, hy1]; rfl) rfl
    (by omega) (by rw [hy4, hy3, hy2, hy1]; simp; omega)
  rw [l_tau_ret] at s5
  obtain ⟨y5, hy5⟩ : ∃ y : LSt, y = { y4 with tauh := y4.tauh - 2 * x.m, g1 := y4.g1 - 2 * x.m } := ⟨_, rfl⟩
  rw [← hy5] at s5
  -- S := side
  have s6 := Hash4.wcopyR_spec cap gM gS gT (by decide) (by decide) (by decide) y5.w (by rw [hy5, hy4]; rfl) rfl
    (by rw [hy5, hy4, hy3, hy2, hy1]; simp; omega)
  rw [l_s] at s6
  obtain ⟨y6, hy6⟩ : ∃ y : LSt, y = { y5 with s := y5.w.val gM } := ⟨_, rfl⟩
  rw [← hy6] at s6
  -- copy x
  have hpm6 : y6.pmw = frameP (yb.drop x.tf) ++ frameP (pmOld.drop (x.m - x.tf)) ++ restP := by
    rw [hy6, hy5, hy4]; simp only [hp4, List.nil_append]
    rw [List.take_of_length_le (by simp; omega), frameP_append]
  obtain ⟨t7, e7, h71, h72, h73, h74, h75, h76, hf7⟩ := fcLoop_spec cap qPM qV gS gVP (by decide) (by decide)
    x.m (pmOld.drop (x.m - x.tf)) xb (frameP (yb.drop x.tf)) [] restP restX y6.w
    (by rw [hy6, hy5, hy4, hy3, hy2, hy1]; rfl) (by simp; omega) (by omega) hpm6
    (by rw [hy6, hy5, hy4]; simp; omega)
    (by rw [hy6, hy5, hy4, hy3, hy2, hy1]; simp [htx])
    (by rw [hy6, hy5, hy4, hy3, hy2, hy1]; simp [hvh]) (by rw [hy6, hy5, hy4, hy3, hy2, hy1]; simp [hvh]; omega)
    (by omega)
  rw [wframe_eq y6.w t7 qPM qV gS gVP (by decide) (by decide) _ _ _ _ _ _ hf7 h71 h72 h73 h74 h76 h75] at e7
  have hvp : y6.w.val gVP + 2 * x.m = ([] : List Bool).length + 2 * x.m := by rw [hy6, hy5, hy4, hy3, hy2, hy1]; simp [hvh]
  rw [hvp, show y6.w.st qV = y6.vw from rfl, l_fcX] at e7
  obtain ⟨p7, hp7⟩ : ∃ l : List Bool, l = frameP (yb.drop x.tf) ++ frameP (xb.take x.m ++
      (pmOld.drop (x.m - x.tf)).drop x.m) ++ restP := ⟨_, rfl⟩
  rw [← hp7] at e7
  obtain ⟨y7, hy7⟩ : ∃ y : LSt, y = { y6 with pmw := p7, pmh := (frameP (yb.drop x.tf)).length + 2 * x.m, vh := ([] : List Bool).length + 2 * x.m, s := 0 } :=
    ⟨_, rfl⟩
  rw [← hy7] at e7
  -- PM back by the first copy, then by the second
  have s8 := wrewind_spec cap qPM gRY y7.g3 y7.w rfl (by rw [l_valRY, hy7, hy6, hy5, hy4, hy3, hy2, hy1]; simp only []; omega)
  rw [l_pm_rew] at s8
  obtain ⟨y8, hy8⟩ : ∃ y : LSt, y = { y7 with pmh := y7.pmh - y7.g3, g3 := 0 } := ⟨_, rfl⟩
  rw [← hy8] at s8
  have s9 := retC_spec cap qPM gM gT gG (by decide) (by decide) (by decide) x.m y8.w
    (by rw [hy8, hy7, hy6, hy5, hy4, hy3, hy2, hy1]; rfl) rfl (by omega)
    (by rw [l_valG, hy8, hy7, hy6, hy5, hy4, hy3, hy2, hy1]; simp only []; omega)
  rw [l_pm_ret] at s9
  obtain ⟨y9, hy9⟩ : ∃ y : LSt, y = { y8 with pmh := y8.pmh - 2 * x.m, g1 := y8.g1 - 2 * x.m } := ⟨_, rfl⟩
  rw [← hy9] at s9
  -- V back
  have s10 := wrewind_spec cap qV gVP y9.vh y9.w rfl (by rw [l_valVP, hy9, hy8, hy7]; simp only [List.length_nil]; omega)
  rw [l_v_rew] at s10
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq e4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq e7 (WExec.seq s8 (WExec.seq s9 s10))))))))) ?_ ?_
  · rw [hy9, hy8, hy7, hy6, hy5, hy4, hy3, hy2, hy1, hp7, hth4]
    congr 1
    have hd : (pmOld.drop (x.m - x.tf)).drop x.m = [] := by simp; omega
    simp only [List.take_of_length_le (by omega : xb.length ≤ x.m), hd, List.append_nil, frameP_length,
      List.length_drop]
    have hyx : (yb ++ xb).drop x.tf = yb.drop x.tf ++ xb := List.drop_append_of_le_length (by omega)
    rw [hyx, frameP_append]
    congr 1 <;> simp [htauh, hpmh, hvh, hg1, hg3, hs] <;> omega
  · unfold mkSeedCost
    rw [hy9, hy8, hy7, hy6, hy5, hy4, hy3, hy2, hy1]
    simp only [List.length_nil, frameP_length, List.length_take, hth4, hg3, hvh, hg1, htauh, hpmh, l_valM]
    omega

/-! ## The diagonal word and the translation -/

/-- **The diagonal word**: `EP := reverse (seed bits 0‥rank) ++ seed bits rank‥2rank−1`. -/
def mkEP : TProg :=
  .seq (advC qEP gLB1 gT gEP) (.seq (Hash4.wcopyR gLB gS gT) (.seq (.seq (revLoop qEP qPM gS gRY) (WM.clear gEP))
  (.seq (advC qEP gLB gT gEP) (.seq (Hash4.wcopyR gLB1 gS gT) (.seq (fcLoop qEP qPM gS gEP)
  (.seq (WM.rewind qPM gRY) (.seq (retC qPM gLB1 gT gG) (WM.rewind qEP gEP))))))))

def mkEPCost (lb : ℕ) : ℕ := 300 * lb + 100

theorem mkEP_spec (x : LSt) (sw epOld restP : List Bool) (hpm : x.pmw = frameP sw ++ restP)
    (hsw : 2 * x.lb - 1 ≤ sw.length) (hep : x.ep = frameP epOld ++ [false]) (hepl : epOld.length = x.lb + (x.lb - 1))
    (hlb : 1 ≤ x.lb) (hpmh : x.pmh = 0) (heph : x.eph = 0) (hg1 : x.g1 = 0) (hg3 : x.g3 = 0) (hs : x.s = 0)
    (hcap : 8 * x.lb + 8 ≤ cap) :
    WExec cap mkEP x.w { x with ep := frameP ((sw.take x.lb).reverse ++ (sw.drop x.lb).take (x.lb - 1)) ++ [false] }.w
      (mkEPCost x.lb) := by
  have hl1 : (frameP ((sw.take x.lb).reverse)).length = 2 * x.lb := by simp; omega
  have hl2 : (frameP (sw.take x.lb)).length = 2 * x.lb := by simp; omega
  -- EP to its last main cell
  have s1 := advC_spec cap qEP gLB1 gT gEP (by decide) (by decide) (by decide) (x.lb - 1) x.w rfl rfl (by omega)
    (by simp [heph]; omega)
  rw [l_ep_adv, heph, Nat.zero_add] at s1
  have s2 := Hash4.wcopyR_spec cap gLB gS gT (by decide) (by decide) (by decide) { x with eph := 2 * (x.lb - 1) }.w
    (by simp [hs]) rfl (by simp; omega)
  rw [l_s] at s2
  obtain ⟨y2, hy2⟩ : ∃ y : LSt, y = { x with eph := 2 * (x.lb - 1), s := x.lb } := ⟨_, rfl⟩
  have e2 : { { x with eph := 2 * (x.lb - 1) } with s := ({ x with eph := 2 * (x.lb - 1) } : LSt).w.val gLB } = y2 := by
    rw [hy2]; rfl
  rw [e2] at s2
  -- the reversal, then the counter of EP cleared
  obtain ⟨t3, e3, h31, h32, h33, h34, h35, h36, hf3⟩ := revLoop_spec cap qEP qPM gS gRY (by decide) (by decide)
    x.lb epOld sw [] [false] restP y2.w (by rw [hy2]; rfl) (by omega) (by omega)
    (by rw [hy2]; simp [hep]) (by rw [hy2]; rfl) (by rw [hy2]; simp [hpm]) (by rw [hy2]; simp [hpmh])
    (by rw [hy2]; simp [hg3]; omega) (by omega)
  rw [wframe_eq y2.w t3 qEP qPM gS gRY (by decide) (by decide) _ _ _ _ _ _ hf3 h31 h32 h33 h34 h36 h35] at e3
  have e34 := WExec.seq e3 (wclear_spec cap gEP (2 * (x.lb - 1)) _ (by simp [hy2]) (by simp [hy2]; omega))
  rw [show y2.w.st qPM = y2.pmw from rfl, l_rev] at e34
  obtain ⟨y4, hy4⟩ : ∃ y : LSt, y = { x with ep := frameP ((sw.take x.lb).reverse ++ epOld.drop x.lb) ++ [false], eph := 0, pmh := 2 * x.lb, s := 0, g3 := 2 * x.lb } :=
    ⟨_, rfl⟩
  have e4 : { y2 with ep := frameP ((sw.take x.lb).reverse ++ epOld.drop x.lb) ++ [false], eph := 0, pmh := ([] : List Bool).length + 2 * x.lb, s := 0, g3 := y2.w.val gRY + 2 * x.lb } = y4 := by
    rw [hy2, hy4]; simp [hg3]
  rw [e4] at e34
  -- EP to the upper diagonals
  have s5 := advC_spec cap qEP gLB gT gEP (by decide) (by decide) (by decide) x.lb y4.w (by rw [hy4]; rfl) rfl
    (by omega) (by rw [hy4]; simp; omega)
  rw [l_ep_adv] at s5
  have s6 := Hash4.wcopyR_spec cap gLB1 gS gT (by decide) (by decide) (by decide) { y4 with eph := y4.eph + 2 * x.lb }.w
    (by rw [hy4]; rfl) rfl (by rw [hy4]; simp; omega)
  rw [l_s] at s6
  obtain ⟨y6, hy6⟩ : ∃ y : LSt, y = { x with ep := frameP ((sw.take x.lb).reverse ++ epOld.drop x.lb) ++ [false], eph := 2 * x.lb, pmh := 2 * x.lb, s := x.lb - 1, g3 := 2 * x.lb } :=
    ⟨_, rfl⟩
  have e6 : { { y4 with eph := y4.eph + 2 * x.lb } with s := ({ y4 with eph := y4.eph + 2 * x.lb } : LSt).w.val gLB1 } = y6 := by
    rw [hy4, hy6]; simp
  rw [e6] at s6
  -- the upper diagonals
  have hsp2 : frameP sw = frameP (sw.take x.lb) ++ frameP (sw.drop x.lb) := by
    rw [← frameP_append, List.take_append_drop]
  obtain ⟨t7, e7, h71, h72, h73, h74, h75, h76, hf7⟩ := fcLoop_spec cap qEP qPM gS gEP (by decide) (by decide)
    (x.lb - 1) (epOld.drop x.lb) (sw.drop x.lb) (frameP ((sw.take x.lb).reverse)) (frameP (sw.take x.lb)) [false]
    restP y6.w (by rw [hy6]; rfl) (by simp; omega) (by simp; omega)
    (by rw [hy6]; simp [frameP_append]) (by rw [hy6]; simp [hl1])
    (by rw [hy6]; show x.pmw = _; rw [hpm, hsp2, List.append_assoc]) (by rw [hy6]; simp [hl2])
    (by rw [hy6]; simp; omega) (by omega)
  rw [wframe_eq y6.w t7 qEP qPM gS gEP (by decide) (by decide) _ _ _ _ _ _ hf7 h71 h72 h73 h74 h76 h75] at e7
  have hpc : y6.w.val gEP + 2 * (x.lb - 1) = (frameP ((sw.take x.lb).reverse)).length + 2 * (x.lb - 1) := by
    rw [hy6, hl1]; rfl
  rw [hpc, show y6.w.st qPM = y6.pmw from rfl, l_fcE] at e7
  have hd : (epOld.drop x.lb).drop (x.lb - 1) = [] := by simp; omega
  obtain ⟨y7, hy7⟩ : ∃ y : LSt, y = { x with ep := frameP ((sw.take x.lb).reverse ++ (sw.drop x.lb).take (x.lb - 1)) ++ [false], eph := 2 * x.lb + 2 * (x.lb - 1), pmh := 2 * x.lb + 2 * (x.lb - 1), s := 0, g3 := 2 * x.lb } :=
    ⟨_, rfl⟩
  have e7' : { y6 with ep := frameP ((sw.take x.lb).reverse) ++ frameP ((sw.drop x.lb).take (x.lb - 1) ++ (epOld.drop x.lb).drop (x.lb - 1)) ++ [false], eph := (frameP ((sw.take x.lb).reverse)).length + 2 * (x.lb - 1), pmh := (frameP (sw.take x.lb)).length + 2 * (x.lb - 1), s := 0 } = y7 := by
    rw [hy6, hy7, hd, List.append_nil, hl1, hl2, ← frameP_append]
  rw [e7'] at e7
  -- rewinds
  have s8 := wrewind_spec cap qPM gRY y7.g3 y7.w rfl (by rw [l_valRY, hy7]; dsimp only; omega)
  rw [l_pm_rew] at s8
  have s9 := retC_spec cap qPM gLB1 gT gG (by decide) (by decide) (by decide) (x.lb - 1)
    { y7 with pmh := y7.pmh - y7.g3, g3 := 0 }.w (by rw [hy7]; rfl) rfl (by omega) (by rw [hy7]; simp [hg1])
  rw [l_pm_ret] at s9
  obtain ⟨y9, hy9⟩ : ∃ y : LSt, y = { x with ep := frameP ((sw.take x.lb).reverse ++ (sw.drop x.lb).take (x.lb - 1)) ++ [false], eph := 2 * x.lb + 2 * (x.lb - 1), pmh := 0, s := 0, g3 := 0, g1 := 0 } :=
    ⟨_, rfl⟩
  have e9 : { { y7 with pmh := y7.pmh - y7.g3, g3 := 0 } with pmh := ({ y7 with pmh := y7.pmh - y7.g3, g3 := 0 } : LSt).pmh - 2 * (x.lb - 1), g1 := ({ y7 with pmh := y7.pmh - y7.g3, g3 := 0 } : LSt).g1 - 2 * (x.lb - 1) } = y9 := by
    rw [hy7, hy9]; simp [hg1]
  rw [e9] at s9
  have s10 := wrewind_spec cap qEP gEP y9.eph y9.w rfl (by rw [l_valEP, hy9]; dsimp only; omega)
  rw [l_ep_rew] at s10
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq e34 (WExec.seq s5 (WExec.seq s6 (WExec.seq e7
    (WExec.seq s8 (WExec.seq s9 s10)))))))) ?_ ?_
  · rw [hy9]; congr 1; cases x; simp_all
  · have h2 : y2.w.val gRY = 0 := by rw [hy2]; exact hg3
    have h4 : y4.lb = x.lb := by rw [hy4]
    have h6 : y6.lb = x.lb := by rw [hy6]
    have h7 : y7.lb = x.lb ∧ y7.g3 = 2 * x.lb := by rw [hy7]; exact ⟨rfl, rfl⟩
    have h9 : y9.eph = 2 * x.lb + 2 * (x.lb - 1) := by rw [hy9]
    unfold mkEPCost
    simp only [l_valLB, l_valLB1, l_valRY] at h2 ⊢
    omega

/-! ## The translation word -/

def mkBW : TProg :=
  .seq (advC qPM gLB gT gG) (.seq (advC qPM gLB1 gT gG) (.seq (Hash4.wcopyR gLB gS gT)
  (.seq (fcLoop qBW qPM gS gBWP) (.seq (WM.rewind qBW gBWP) (.seq (WM.rewind qPM gG) (retC qPM gLB gT gG))))))

def mkBWCost (lb : ℕ) : ℕ := 200 * lb + 100

theorem mkBW_spec (x : LSt) (sw bwOld restP : List Bool) (hpm : x.pmw = frameP sw ++ restP)
    (hsw : 2 * x.lb - 1 + x.lb ≤ sw.length) (hbw : x.bw = frameP bwOld ++ [false]) (hbwl : bwOld.length = x.lb)
    (hlb : 1 ≤ x.lb) (hpmh : x.pmh = 0) (hbwh : x.bwh = 0) (hg1 : x.g1 = 0) (hs : x.s = 0)
    (hcap : 8 * x.lb + 8 ≤ cap) :
    WExec cap mkBW x.w { x with bw := frameP ((sw.drop (2 * x.lb - 1)).take x.lb) ++ [false] }.w (mkBWCost x.lb) := by
  -- PM to the translation bits
  have s1 := advC_spec cap qPM gLB gT gG (by decide) (by decide) (by decide) x.lb x.w rfl rfl (by omega)
    (by simp [hg1]; omega)
  rw [l_pm_adv, hpmh, hg1, Nat.zero_add] at s1
  have s2 := advC_spec cap qPM gLB1 gT gG (by decide) (by decide) (by decide) (x.lb - 1)
    { x with pmh := 2 * x.lb, g1 := 2 * x.lb }.w rfl rfl (by omega) (by simp; omega)
  rw [l_pm_adv] at s2
  have s3 := Hash4.wcopyR_spec cap gLB gS gT (by decide) (by decide) (by decide)
    { { x with pmh := 2 * x.lb, g1 := 2 * x.lb } with pmh := 2 * x.lb + 2 * (x.lb - 1), g1 := 2 * x.lb + 2 * (x.lb - 1) }.w
    (by simp [hs]) rfl (by simp; omega)
  rw [l_s] at s3
  obtain ⟨y3, hy3⟩ : ∃ y : LSt, y = { x with pmh := 2 * (2 * x.lb - 1), g1 := 2 * (2 * x.lb - 1), s := x.lb } :=
    ⟨_, rfl⟩
  have e3 : { { { x with pmh := 2 * x.lb, g1 := 2 * x.lb } with pmh := 2 * x.lb + 2 * (x.lb - 1), g1 := 2 * x.lb + 2 * (x.lb - 1) } with s := ({ { x with pmh := 2 * x.lb, g1 := 2 * x.lb } with pmh := 2 * x.lb + 2 * (x.lb - 1), g1 := 2 * x.lb + 2 * (x.lb - 1) } : LSt).w.val gLB } = y3 := by
    rw [hy3]; simp only [l_valLB]; congr 1 <;> omega
  rw [e3] at s3
  -- the copy
  have hsp : frameP sw = frameP (sw.take (2 * x.lb - 1)) ++ frameP (sw.drop (2 * x.lb - 1)) := by
    rw [← frameP_append, List.take_append_drop]
  have hl0 : (frameP (sw.take (2 * x.lb - 1))).length = 2 * (2 * x.lb - 1) := by simp; omega
  obtain ⟨t4, e4, h41, h42, h43, h44, h45, h46, hf4⟩ := fcLoop_spec cap qBW qPM gS gBWP (by decide) (by decide)
    x.lb bwOld (sw.drop (2 * x.lb - 1)) [] (frameP (sw.take (2 * x.lb - 1))) [false] restP y3.w
    (by rw [hy3]; rfl) (by omega) (by simp; omega)
    (by rw [hy3]; simp [hbw]) (by rw [hy3]; exact hbwh)
    (by rw [hy3]; show x.pmw = _; rw [hpm, hsp, List.append_assoc]) (by rw [hy3, hl0]; rfl)
    (by rw [hy3]; simp [hbwh]; omega) (by omega)
  rw [wframe_eq y3.w t4 qBW qPM gS gBWP (by decide) (by decide) _ _ _ _ _ _ hf4 h41 h42 h43 h44 h46 h45] at e4
  have hv4 : y3.w.val gBWP + 2 * x.lb = ([] : List Bool).length + 2 * x.lb := by rw [hy3]; simp [hbwh]
  rw [hv4, show y3.w.st qPM = y3.pmw from rfl, l_fcB] at e4
  have hd : bwOld.drop x.lb = [] := by simp; omega
  obtain ⟨y4, hy4⟩ : ∃ y : LSt, y = { x with bw := frameP ((sw.drop (2 * x.lb - 1)).take x.lb) ++ [false], bwh := 2 * x.lb, pmh := 2 * (2 * x.lb - 1) + 2 * x.lb, g1 := 2 * (2 * x.lb - 1), s := 0 } :=
    ⟨_, rfl⟩
  have e4' : { y3 with bw := ([] : List Bool) ++ frameP ((sw.drop (2 * x.lb - 1)).take x.lb ++ bwOld.drop x.lb) ++ [false], bwh := ([] : List Bool).length + 2 * x.lb, pmh := (frameP (sw.take (2 * x.lb - 1))).length + 2 * x.lb, s := 0 } = y4 := by
    rw [hy3, hy4, hd, hl0]; simp
  rw [e4'] at e4
  -- the rewinds
  have s5 := wrewind_spec cap qBW gBWP y4.bwh y4.w rfl (by rw [l_valBWP, hy4]; dsimp only; omega)
  rw [l_bw_rew] at s5
  have s6 := wrewind_spec cap qPM gG ({ y4 with bwh := 0 } : LSt).g1 { y4 with bwh := 0 }.w rfl
    (by rw [l_valG, hy4]; dsimp only; omega)
  rw [l_pm_rewG] at s6
  have s7 := retC_spec cap qPM gLB gT gG (by decide) (by decide) (by decide) x.lb
    { { y4 with bwh := 0 } with pmh := ({ y4 with bwh := 0 } : LSt).pmh - ({ y4 with bwh := 0 } : LSt).g1, g1 := 0 }.w
    (by rw [hy4]; rfl) rfl (by omega) (by simp)
  rw [l_pm_ret] at s7
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq e4 (WExec.seq s5 (WExec.seq s6 s7))))))
    ?_ ?_
  · rw [hy4]; congr 1; cases x; simp_all
  · have h4 : y4.bwh = 2 * x.lb ∧ y4.g1 = 2 * (2 * x.lb - 1) := by rw [hy4]; exact ⟨rfl, rfl⟩
    have h3 : y3.lb = x.lb := by rw [hy3]
    unfold mkBWCost
    simp only [l_valLB]
    omega

end NearCubicWires.WireExponent3_5.FinalPass.Flat
