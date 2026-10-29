import SourceAdapters.Refuter.CheckerStep

/-!
# The replay segments of one checking step (input 7, F01 machine layer, part 6)

SFM78 l.227–230 ("letting the first tape of M' play the role of the tape while running through the
guessed sequence of displays and actions"), with the protected cutoff in the proof of `lem:multitape-refuter`: the cutoff
stream `RS` holds `1^r` and moves in lockstep with the work tape `SIM`, so its scanned cell says
whether the head is before the cutoff.

* `replayChk`: flag cleared unless the cutoff cell is `1` and the work cell equals display bit `i`;
* `replayWr`: the write code `W0 W1` (`writeCode`: none `00`, `0` as `10`, `1` as `11`);
* `replayMv`: the move code `M0 M1` (`moveCode`: left `00`, stay `10`, right `01`);
* `clears`, `finish`: scratch cleared, `Q := QN`.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

def replayChk : Pg :=
  .seq (ifCellClr sRS rOK) (.seq (peek sDISP rI rTB rDI)
  (.seq (.ifs sSIM (ifNotClr rDI rOK) (ifClr rDI rOK)) (clr rDI)))

theorem replayChk_spec (σ : St) (hOK : σ.val rOK ≤ 1) (hDI : σ.val rDI = 0) (hTB : σ.val rTB = 0)
    (hcap : 2 * σ.val rI + 4 ≤ cap) :
    WXExec cap replayChk σ
      (σ.setv rOK (if wbit σ sRS = true ∧
        wbit σ sSIM = readTapeBit (σ.st sDISP) (σ.sh sDISP + σ.val rI) then σ.val rOK else 0))
      (32 * σ.val rI + 40) := by
  have e1 := ifCellClr_spec cap sRS rOK σ hOK (by lomega)
  set σ1 := σ.setv rOK (if wbit σ sRS = false then 0 else σ.val rOK) with hσ1
  have e2 := peek_spec cap (S := sDISP) (K := rI) (K2 := rTB) (RES := rDI) (by decide) (by decide)
    (by decide) σ1 (by simp [σ1, Function.update_apply, hTB]) (by simp [σ1, Function.update_apply]; lomega)
    (by simp [σ1, Function.update_apply, hDI]; lomega)
  set σ2 := σ1.setv rDI (σ1.val rDI + (readTapeBit (σ1.st sDISP) (σ1.sh sDISP + σ1.val rI)).toNat)
    with hσ2
  have hok2 : σ2.val rOK ≤ 1 := by simp [σ2, σ1, Function.update_apply]; split <;> lomega
  have hdi2 : σ2.val rDI = (readTapeBit (σ.st sDISP) (σ.sh sDISP + σ.val rI)).toNat := by
    simp [σ2, σ1, Function.update_apply, hDI]
  have hs2 : wbit σ2 sSIM = wbit σ sSIM := by simp [σ2, σ1, wbit]
  cases hsim : wbit σ sSIM
  · have e3 := ifClr_spec cap rDI rOK σ2 hok2 (by lomega)
    set σ3 := σ2.setv rOK (if σ2.val rDI ≠ 0 then 0 else σ2.val rOK) with hσ3
    have e4 := clr_spec cap rDI σ3 (by simp [σ3, hdi2, Function.update_apply]; lomega)
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.ifsF (by rw [hs2, hsim]) e3) e4))).cast cap ?_
      (by simp [σ3, hdi2, σ1, Function.update_apply]; lomega)
    simp only [σ3, σ2, σ1]
    wst
  · have e3 := ifNotClr_spec cap rDI rOK σ2 hok2 (by lomega)
    set σ3 := σ2.setv rOK (if σ2.val rDI = 0 then 0 else σ2.val rOK) with hσ3
    have e4 := clr_spec cap rDI σ3 (by simp [σ3, hdi2, Function.update_apply]; lomega)
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.ifsT (by rw [hs2, hsim]) e3) e4))).cast cap ?_
      (by simp [σ3, hdi2, σ1, Function.update_apply]; lomega)
    simp only [σ3, σ2, σ1]
    wst

def replayWr : Pg := .ifr rW0 (.ifr rW1 (WMX.wr sSIM true) (WMX.wr sSIM false)) WMX.skip

theorem replayWr_spec (σ : St) :
    WXExec cap replayWr σ
      (σ.sets sSIM (if σ.val rW0 ≠ 0 then writeTapeBit (σ.st sSIM) (σ.sh sSIM) (decide (σ.val rW1 ≠ 0))
        else σ.st sSIM)) 3 := by
  by_cases h0 : σ.val rW0 = 0
  · refine (WXExec.ifrF h0 (WXExec.skip cap σ)).cast cap ?_ (by omega)
    simp only [h0, ne_eq, not_true_eq_false, if_false]
    exact (BinW.sets_same rfl).symm
  · by_cases h1 : σ.val rW1 = 0
    · refine (WXExec.ifrT h0 (WXExec.ifrF h1 (WXExec.wr cap sSIM false σ))).cast cap ?_ (by omega)
      simp [h0, h1]
    · refine (WXExec.ifrT h0 (WXExec.ifrT h1 (WXExec.wr cap sSIM true σ))).cast cap ?_ (by omega)
      simp [h0, h1]

def replayMv : Pg :=
  .ifr rM1 (.seq (WMX.fwd sSIM) (.seq (WMX.fwd sRS) (WMX.inc rH)))
    (.ifr rM0 WMX.skip (.seq (WMX.bwd sSIM) (.seq (WMX.bwd sRS) (WMX.dec rH))))

/-- The head after the move code `M0 M1`. -/
def mvHead (m0 m1 : ℕ) (h : ℕ) : ℕ := if m1 ≠ 0 then h + 1 else if m0 ≠ 0 then h else h - 1

theorem replayMv_spec (σ : St) (h : ℕ) (hs : σ.sh sSIM = h) (hr : σ.sh sRS = h) (hH : σ.val rH = h)
    (hcap : h + 1 < cap) :
    WXExec cap replayMv σ
      (((σ.seth sSIM (mvHead (σ.val rM0) (σ.val rM1) h)).seth sRS (mvHead (σ.val rM0) (σ.val rM1) h)).setv
        rH (mvHead (σ.val rM0) (σ.val rM1) h)) 8 := by
  by_cases h1 : σ.val rM1 = 0
  · by_cases h0 : σ.val rM0 = 0
    · have e1 := WXExec.bwd cap sSIM σ
      have e2 := WXExec.bwd cap sRS (σ.seth sSIM (σ.sh sSIM - 1))
      have e3 := WXExec.dec cap rH ((σ.seth sSIM (σ.sh sSIM - 1)).seth sRS
        ((σ.seth sSIM (σ.sh sSIM - 1)).sh sRS - 1)) (by simp; lomega)
      refine (WXExec.ifrF h1 (WXExec.ifrF h0 (WXExec.seq e1 (WXExec.seq e2 e3)))).cast cap ?_ (by omega)
      simp only [mvHead, h0, h1, ne_eq, not_true_eq_false, if_false]
      wst
    · refine (WXExec.ifrF h1 (WXExec.ifrT h0 (WXExec.skip cap σ))).cast cap ?_ (by omega)
      simp only [mvHead, h0, h1, ne_eq, not_true_eq_false, not_false_eq_true, if_true, if_false]
      wst
  · have e1 := WXExec.fwd cap sSIM σ
    have e2 := WXExec.fwd cap sRS (σ.seth sSIM (σ.sh sSIM + 1))
    have e3 := WXExec.inc cap rH ((σ.seth sSIM (σ.sh sSIM + 1)).seth sRS
      ((σ.seth sSIM (σ.sh sSIM + 1)).sh sRS + 1)) (by simp; lomega)
    refine (WXExec.ifrT h1 (WXExec.seq e1 (WXExec.seq e2 e3))).cast cap ?_ (by omega)
    simp only [mvHead, h1, ne_eq, not_false_eq_true, if_true]
    wst

def clears : Pg := .seq (clr rW0) (.seq (clr rW1) (.seq (clr rM0) (clr rM1)))

theorem clears_spec (σ : St) (h0 : σ.val rW0 ≤ 1) (h1 : σ.val rW1 ≤ 1) (h2 : σ.val rM0 ≤ 1)
    (h3 : σ.val rM1 ≤ 1) (hcap : 1 ≤ cap) :
    WXExec cap clears σ ((((σ.setv rW0 0).setv rW1 0).setv rM0 0).setv rM1 0) 23 := by
  have e1 := clr_spec cap rW0 σ (by lomega)
  have e2 := clr_spec cap rW1 (σ.setv rW0 0) (by simp; lomega)
  have e3 := clr_spec cap rM0 ((σ.setv rW0 0).setv rW1 0) (by simp; lomega)
  have e4 := clr_spec cap rM1 (((σ.setv rW0 0).setv rW1 0).setv rM0 0) (by simp; lomega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap rfl (by simp; lomega)

def finish : Pg := .seq (clr rQ) (.seq (.wm (WM.move rQN rQ)) (clr rMK))

theorem finish_spec (σ : St) (hcap : σ.val rQ + σ.val rQN + σ.val rMK ≤ cap) :
    WXExec cap finish σ (((σ.setv rQ (σ.val rQN)).setv rQN 0).setv rMK 0)
      (3 * σ.val rQ + 7 * σ.val rQN + 3 * σ.val rMK + 6) := by
  have e1 := clr_spec cap rQ σ (by lomega)
  have e2 := WXExec.wm (wmove_spec (cap := cap) rQN rQ (by decide) (σ.val rQN) (σ.setv rQ 0)
    (by simp) (by simp; lomega) (by simp; lomega))
  have e3 := clr_spec cap rMK (((σ.setv rQ 0).setv rQN 0).setv rQ
    ((σ.setv rQ 0).val rQ + (σ.setv rQ 0).val rQN)) (by simp [Function.update_apply]; lomega)
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by simp [Function.update_apply]; lomega)
  wst

end NearCubicGates.Adapters.Refuter.Mach
