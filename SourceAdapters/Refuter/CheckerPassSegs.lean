import SourceAdapters.Refuter.CheckerCopy

/-!
# The segments around one pass (input 7, F01 machine layer, part 11)

`passSetup` (flag on, control := start, loop on), `finalChk` (the final control must be halted and
its acceptance bit equal the requested verdict `VD`: proof of `lem:multitape-refuter`, "accepting only upon,
respectively, an accepting or a rejecting halt of `M`"), `restore` (heads back, the witness head
back to the trace start, its distance kept in `WS`), `accum` (`ALL := ALL ∧ OK`). Exact-state specs.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

def passSetup : Pg := .seq (WMX.inc rOK) (.seq (addR rSTART rQ rTA) (WMX.inc rCONT))

theorem passSetup_spec (σ : St) (hOK : σ.val rOK = 0) (hQ : σ.val rQ = 0) (hC : σ.val rCONT = 0)
    (hTA : σ.val rTA = 0) (hcap : σ.val rSTART + 2 ≤ cap) :
    WXExec cap passSetup σ (((σ.setv rOK 1).setv rQ (σ.val rSTART)).setv rCONT 1)
      (18 * σ.val rSTART + 11) := by
  have e1 := WXExec.inc cap rOK σ (by lomega)
  have e2 := addR_spec cap (A := rSTART) (B := rQ) (T := rTA) (by decide) (by decide) (by decide)
    (σ.setv rOK (σ.val rOK + 1)) (by simp [Function.update_apply, hTA]) (by simp [Function.update_apply]; lomega)
  have e3 := WXExec.inc cap rCONT ((σ.setv rOK (σ.val rOK + 1)).setv rQ
    ((σ.setv rOK (σ.val rOK + 1)).val rQ + (σ.setv rOK (σ.val rOK + 1)).val rSTART))
    (by simp [Function.update_apply]; lomega)
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by simp [Function.update_apply]; lomega)
  wst

def finalChk : Pg :=
  .seq (addR rHB rOFF rTA) (.seq (addR rQ rOFF rTA) (.seq (addR rQ rOFF rTA)
  (.seq (peek sCODE rOFF rTB rBIT) (.seq (ifNotClr rBIT rOK) (.seq (clr rBIT) (.seq (WMX.inc rOFF)
  (.seq (peek sCODE rOFF rTB rBIT) (.seq (.ifr rBIT (ifNotClr rVD rOK) (ifClr rVD rOK))
  (.seq (clr rBIT) (clr rOFF))))))))))

theorem finalChk_spec (σ : St) (hOFF : σ.val rOFF = 0) (hTA : σ.val rTA = 0) (hTB : σ.val rTB = 0)
    (hBIT : σ.val rBIT = 0) (hOK : σ.val rOK ≤ 1) (hcap : 4 * (σ.val rHB + 2 * σ.val rQ) + 8 ≤ cap) :
    WXExec cap finalChk σ
      (σ.setv rOK (if readTapeBit (σ.st sCODE) (σ.sh sCODE + (σ.val rHB + σ.val rQ + σ.val rQ)) = true ∧
        readTapeBit (σ.st sCODE) (σ.sh sCODE + (σ.val rHB + σ.val rQ + σ.val rQ + 1)) =
          decide (σ.val rVD ≠ 0) then σ.val rOK else 0))
      (200 * (σ.val rHB + σ.val rQ) + 150) := by
  have e1 := addR_spec cap (A := rHB) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ hTA
    (by lomega)
  obtain ⟨σ1, e1, h1⟩ := exEq cap e1
  have e2 := addR_spec cap (A := rQ) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ1
    (by simp [h1, Function.update_apply, hTA]) (by simp [h1, Function.update_apply]; lomega)
  obtain ⟨σ2, e2, h2⟩ := exEq cap e2
  have e3 := addR_spec cap (A := rQ) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ2
    (by simp [h2, h1, Function.update_apply, hTA]) (by simp [h2, h1, Function.update_apply]; lomega)
  obtain ⟨σ3, e3, h3⟩ := exEq cap e3
  have e4 := peek_spec cap (S := sCODE) (K := rOFF) (K2 := rTB) (RES := rBIT) (by decide) (by decide)
    (by decide) σ3 (by simp [h3, h2, h1, Function.update_apply, hTB])
    (by simp [h3, h2, h1, Function.update_apply]; lomega) (by simp [h3, h2, h1, Function.update_apply]; lomega)
  obtain ⟨σ4, e4, h4⟩ := exEq cap e4
  have e5 := ifNotClr_spec cap rBIT rOK σ4 (by simp [h4, h3, h2, h1, Function.update_apply]; lomega) (by lomega)
  obtain ⟨σ5, e5, h5⟩ := exEq cap e5
  have e6 := clr_spec cap rBIT σ5 (by simp [h5, h4, h3, h2, h1, Function.update_apply]; lomega)
  obtain ⟨σ6, e6, h6⟩ := exEq cap e6
  have e7 := WXExec.inc cap rOFF σ6 (by simp [h6, h5, h4, h3, h2, h1, Function.update_apply]; lomega)
  obtain ⟨σ7, e7, h7⟩ := exEq cap e7
  have e8 := peek_spec cap (S := sCODE) (K := rOFF) (K2 := rTB) (RES := rBIT) (by decide) (by decide)
    (by decide) σ7 (by simp [h7, h6, h5, h4, h3, h2, h1, Function.update_apply, hTB])
    (by simp [h7, h6, h5, h4, h3, h2, h1, Function.update_apply]; lomega)
    (by simp [h7, h6, h5, h4, h3, h2, h1, Function.update_apply]; lomega)
  obtain ⟨σ8, e8, h8⟩ := exEq cap e8
  have hok8 : σ8.val rOK ≤ 1 := by simp [h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply]; lomega
  have hvd8 : σ8.val rVD = σ.val rVD := by simp [h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply]
  obtain ⟨σ9, e9, h9⟩ : ∃ σ9, WXExec cap (.ifr rBIT (ifNotClr rVD rOK) (ifClr rVD rOK)) σ8 σ9 6 ∧
      σ9 = σ8.setv rOK (if (σ8.val rBIT ≠ 0) = (σ8.val rVD ≠ 0) then σ8.val rOK else 0) := by
    by_cases hb : σ8.val rBIT = 0
    · refine ⟨_, WXExec.ifrF hb (ifClr_spec cap rVD rOK σ8 hok8 (by lomega)), ?_⟩
      by_cases hv : σ8.val rVD = 0 <;> simp [hb, hv]
    · refine ⟨_, WXExec.ifrT hb (ifNotClr_spec cap rVD rOK σ8 hok8 (by lomega)), ?_⟩
      by_cases hv : σ8.val rVD = 0 <;> simp [hb, hv]
  have e10 := clr_spec cap rBIT σ9 (by simp [h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply]; lomega)
  obtain ⟨σ10, e10, h10⟩ := exEq cap e10
  have e11 := clr_spec cap rOFF σ10
    (by simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply]; lomega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 (WXExec.seq e8 (WXExec.seq e9 (WXExec.seq e10 e11)))))))))).cast cap ?_ (by
      simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply]; lomega)
  rw [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1]
  wst

def restore : Pg :=
  .seq (bwdK sSIM rH rTB) (.seq (bwdK sRS rH rTB) (.seq (clr rH) (.seq (clr rWS) (.seq (addR rWP rWS rTA)
  (.seq (bwdK sWIT rWP rTB) (.seq (clr rWP) (clr rQ)))))))

theorem restore_spec (σ : St) (hTB : σ.val rTB = 0) (hTA : σ.val rTA = 0)
    (hcap : 2 * (σ.val rH + σ.val rWP + σ.val rWS + σ.val rQ) + 2 ≤ cap) :
    WXExec cap restore σ
      (((((((σ.seth sSIM (σ.sh sSIM - σ.val rH)).seth sRS (σ.sh sRS - σ.val rH)).setv rH 0).setv rWS
        (σ.val rWP)).seth sWIT (σ.sh sWIT - σ.val rWP)).setv rWP 0).setv rQ 0)
      (40 * (σ.val rH + σ.val rWP + σ.val rWS + σ.val rQ) + 30) := by
  have e1 := bwdK_spec cap (S := sSIM) (K := rH) (K2 := rTB) (by decide) σ hTB (by lomega)
  obtain ⟨σ1, e1, h1⟩ := exEq cap e1
  have e2 := bwdK_spec cap (S := sRS) (K := rH) (K2 := rTB) (by decide) σ1 (by simp [h1, hTB])
    (by simp [h1]; lomega)
  obtain ⟨σ2, e2, h2⟩ := exEq cap e2
  have e3 := clr_spec cap rH σ2 (by simp [h2, h1]; lomega)
  obtain ⟨σ3, e3, h3⟩ := exEq cap e3
  have e4 := clr_spec cap rWS σ3 (by simp [h3, h2, h1, Function.update_apply]; lomega)
  obtain ⟨σ4, e4, h4⟩ := exEq cap e4
  have e5 := addR_spec cap (A := rWP) (B := rWS) (T := rTA) (by decide) (by decide) (by decide) σ4
    (by simp [h4, h3, h2, h1, Function.update_apply, hTA]) (by simp [h4, h3, h2, h1, Function.update_apply]; lomega)
  obtain ⟨σ5, e5, h5⟩ := exEq cap e5
  have e6 := bwdK_spec cap (S := sWIT) (K := rWP) (K2 := rTB) (by decide) σ5
    (by simp [h5, h4, h3, h2, h1, Function.update_apply, hTB]) (by simp [h5, h4, h3, h2, h1, Function.update_apply]; lomega)
  obtain ⟨σ6, e6, h6⟩ := exEq cap e6
  have e7 := clr_spec cap rWP σ6 (by simp [h6, h5, h4, h3, h2, h1, Function.update_apply]; lomega)
  obtain ⟨σ7, e7, h7⟩ := exEq cap e7
  have e8 := clr_spec cap rQ σ7 (by simp [h7, h6, h5, h4, h3, h2, h1, Function.update_apply]; lomega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 e8))))))).cast cap ?_ (by simp [h7, h6, h5, h4, h3, h2, h1, Function.update_apply]; lomega)
  rw [h7, h6, h5, h4, h3, h2, h1]
  wst

def accum : Pg := .seq (ifNotClr rOK rALL) (clr rOK)

theorem accum_spec (σ : St) (hA : σ.val rALL ≤ 1) (hOK : σ.val rOK ≤ 1) (hcap : 1 ≤ cap) :
    WXExec cap accum σ ((σ.setv rALL (if σ.val rOK = 0 then 0 else σ.val rALL)).setv rOK 0) 10 := by
  have e1 := ifNotClr_spec cap rOK rALL σ hA hcap
  have e2 := clr_spec cap rOK (σ.setv rALL (if σ.val rOK = 0 then 0 else σ.val rALL))
    (by simp [Function.update_apply]; lomega)
  exact (WXExec.seq e1 e2).mono (by simp [Function.update_apply]; lomega)

end NearCubicGates.Adapters.Refuter.Mach
