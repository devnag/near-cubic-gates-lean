import Proof.Gates.Recovery.HTParts4
import Proof.Gates.CheckedPCPP.ClauseFront
import Proof.Gates.CheckedPCPP.EncSetup
import Proof.Gates.CheckedPCPP.WMXReady
import Proof.Gates.CheckedPCPP.FramedWord
import Proof.Gates.CheckedPCPP.DockRd
import Proof.CaseAnalysis.CaseTwoConverter

set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts

/-! ## Streams -/

section Streams
variable (tK tE tH : ℕ)

/-- The number of streams minus one. -/
def NS : ℕ := 144 + tK + tE + tH

def P0 : Fin (NS tK tE tH + 1) := ⟨0, by unfold NS; omega⟩
def P1 : Fin (NS tK tE tH + 1) := ⟨1, by unfold NS; omega⟩
def P2 : Fin (NS tK tE tH + 1) := ⟨2, by unfold NS; omega⟩
def P3 : Fin (NS tK tE tH + 1) := ⟨3, by unfold NS; omega⟩
def P4 : Fin (NS tK tE tH + 1) := ⟨4, by unfold NS; omega⟩
def DS : Fin (NS tK tE tH + 1) := ⟨5, by unfold NS; omega⟩
def EI : Fin (NS tK tE tH + 1) := ⟨6, by unfold NS; omega⟩
def AS : Fin (NS tK tE tH + 1) := ⟨7, by unfold NS; omega⟩
def HI : Fin (NS tK tE tH + 1) := ⟨8, by unfold NS; omega⟩
def OUT : Fin (NS tK tE tH + 1) := ⟨9, by unfold NS; omega⟩

def bC (j : Fin 135) : Fin (NS tK tE tH + 1) := ⟨10 + j.val, by have := j.isLt; unfold NS; omega⟩
def bK (j : Fin tK) : Fin (NS tK tE tH + 1) := ⟨145 + j.val, by have := j.isLt; unfold NS; omega⟩
def bE (j : Fin tE) : Fin (NS tK tE tH + 1) := ⟨145 + tK + j.val, by have := j.isLt; unfold NS; omega⟩
def bH (j : Fin tH) : Fin (NS tK tE tH + 1) := ⟨145 + tK + tE + j.val, by have := j.isLt; unfold NS; omega⟩

@[simp] theorem P0_val : (P0 tK tE tH).val = 0 := rfl
@[simp] theorem P1_val : (P1 tK tE tH).val = 1 := rfl
@[simp] theorem P2_val : (P2 tK tE tH).val = 2 := rfl
@[simp] theorem P3_val : (P3 tK tE tH).val = 3 := rfl
@[simp] theorem P4_val : (P4 tK tE tH).val = 4 := rfl
@[simp] theorem DS_val : (DS tK tE tH).val = 5 := rfl
@[simp] theorem EI_val : (EI tK tE tH).val = 6 := rfl
@[simp] theorem AS_val : (AS tK tE tH).val = 7 := rfl
@[simp] theorem HI_val : (HI tK tE tH).val = 8 := rfl
@[simp] theorem OUT_val : (OUT tK tE tH).val = 9 := rfl
@[simp] theorem bC_val (j : Fin 135) : (bC tK tE tH j).val = 10 + j.val := rfl
@[simp] theorem bK_val (j : Fin tK) : (bK tK tE tH j).val = 145 + j.val := rfl
@[simp] theorem bE_val (j : Fin tE) : (bE tK tE tH j).val = 145 + tK + j.val := rfl
@[simp] theorem bH_val (j : Fin tH) : (bH tK tE tH j).val = 145 + tK + tE + j.val := rfl

end Streams

theorem fin_ne {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-- Distinct streams of the layout. -/
macro "hdst" : tactic => `(tactic| (apply fin_ne; first
  | (simp only [P0_val, P1_val, P2_val, P3_val, P4_val, DS_val, EI_val, AS_val, HI_val, OUT_val, bC_val, bK_val,
      bE_val, bH_val]; done)
  | (simp only [P0_val, P1_val, P2_val, P3_val, P4_val, DS_val, EI_val, AS_val, HI_val, OUT_val, bC_val, bK_val,
      bE_val, bH_val]; omega)))

section Maps
variable (tK tE tH : ℕ)

/-- The converter's tapes: its five ports are the producer's ports. -/
def convMap (j : Fin 135) : Fin (NS tK tE tH + 1) :=
  if h : j.val < 5 then ⟨j.val, by unfold NS; omega⟩ else bC tK tE tH j

def compMap (hIn dIn : Fin tK) (j : Fin tK) : Fin (NS tK tE tH + 1) :=
  if j = hIn then P0 tK tE tH else if j = dIn then DS tK tE tH else bK tK tE tH j

/-- The encoder's tapes: its input tape is `EI`. -/
def encMap (j : Fin tE) : Fin (NS tK tE tH + 1) := if j.val = 0 then EI tK tE tH else bE tK tE tH j

/-- The honest prover's tapes: its input tape is `HI`. -/
def honMap (j : Fin tH) : Fin (NS tK tE tH + 1) := if j.val = 0 then HI tK tE tH else bH tK tE tH j

theorem convMap_inj : Function.Injective (convMap tK tE tH) := by
  intro a b h
  have := congrArg Fin.val h
  unfold convMap at this
  apply Fin.ext
  split_ifs at this with h1 h2 h2 <;> simp at this <;> omega

theorem compMap_inj (hIn dIn : Fin tK) : Function.Injective (compMap tK tE tH hIn dIn) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [compMap] at hv
  split_ifs at hv with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [P0_val, DS_val, bK_val] at hv <;> (try omega)

theorem encMap_inj : Function.Injective (encMap tK tE tH) := by
  intro a b h
  have := congrArg Fin.val h
  unfold encMap at this
  apply Fin.ext
  split_ifs at this with h1 h2 h2 <;> simp at this <;> omega

theorem honMap_inj : Function.Injective (honMap tK tE tH) := by
  intro a b h
  have := congrArg Fin.val h
  unfold honMap at this
  apply Fin.ext
  split_ifs at this with h1 h2 h2 <;> simp at this <;> omega

end Maps

/-! ## Registers -/

/-- The clause front end's registers `0 … 17`. -/
def R : Fin 18 ↪ Fin 64 := ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

@[simp] theorem R_val (i : Fin 18) : (R i).val = i.val := rfl

abbrev rR : Fin 64 := 18
abbrev rC2 : Fin 64 := 19
abbrev rT1 : Fin 64 := 20
abbrev rT : Fin 64 := 21
abbrev pX : Fin 64 := 22
abbrev pY : Fin 64 := 23
abbrev pZ : Fin 64 := 24
abbrev pA2 : Fin 64 := 25
abbrev pT : Fin 64 := 26
abbrev rCL : Fin 64 := 27
abbrev rH : Fin 64 := 28
abbrev rB : Fin 64 := 29
abbrev rS : Fin 64 := 30
abbrev rS2 : Fin 64 := 31
abbrev rU : Fin 64 := 32
abbrev rK : Fin 64 := 33
abbrev rF : Fin 64 := 34
abbrev opDS : Fin 64 := 35
abbrev scC : Fin 64 := 36
abbrev opEI : Fin 64 := 37
abbrev scP2 : Fin 64 := 38
abbrev opAS : Fin 64 := 39
abbrev scE : Fin 64 := 40
abbrev opHI : Fin 64 := 41
abbrev scK : Fin 64 := 42
abbrev scAS : Fin 64 := 43
abbrev scH : Fin 64 := 44
abbrev rJ : Fin 64 := 45
abbrev rM5 : Fin 64 := 46
abbrev rJ5 : Fin 64 := 47
abbrev rD5 : Fin 64 := 48
abbrev rK5 : Fin 64 := 49
abbrev b0 : Fin 64 := 50
abbrev b1 : Fin 64 := 51
abbrev b2 : Fin 64 := 52
abbrev rKr : Fin 64 := 53
abbrev opOUT : Fin 64 := 54
abbrev rRc : Fin 64 := 55
abbrev rT3 : Fin 64 := 56

/-- `r += k`. -/
def incN {ns : ℕ} (r : Fin 64) : ℕ → WMX ns 64
  | 0 => WMX.skip
  | k + 1 => .seq (WMX.inc r) (incN r k)

theorem incN_exec {ns cap : ℕ} (r : Fin 64) (k : ℕ) : ∀ (σ : WState ns 64), σ.val r + k ≤ cap →
    WXExec cap (incN r k) σ (σ.setv r (σ.val r + k)) (4 * k) := by
  induction k with
  | zero => intro σ _; simp only [incN, Nat.add_zero, wsetv_same, Nat.mul_zero]; exact WXExec.skip cap σ
  | succ k ih =>
    intro σ h
    have e1 := WXExec.inc (cap := cap) r σ (by omega)
    have e2 := ih (σ.setv r (σ.val r + 1)) (by simp only [WState.setv_val, Function.update_self]; omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 e2) ?_ le_rfl) (by omega)
    simp only [WState.setv_val, Function.update_self, LitDecode.setv_setv]; congr 1; omega

/-! ## The program -/

section Program
variable (tK tE tH : ℕ)

/-- Fit test, part 1: `rR := R` (port 3), `rC2 := 2n` (port 2), both ports back at head `0`. -/
def fitW1 : WMX (NS tK tE tH) 64 :=
  .seq (.wm (oneLoop (P3 tK tE tH) rR (fun _ => WM.skip)))
  (.seq (addR rR rT1 rT)
  (.seq (.wm (WM.rewind (P3 tK tE tH) rT1))
  (.seq (.wm (pairLoop (P2 tK tE tH) rC2 (fun _ => WM.skip) (fun _ => WM.skip)))
  (.seq (addR rC2 rT1 rT)
    (.wm (WM.rewind (P2 tK tE tH) rT1))))))

/-- Fit test, part 2: `pX := R + 2`, `rCL := size ((R+2)^d − 1)`. -/
def fitW2 (cd : ℕ) : WMX (NS tK tE tH) 64 :=
  .seq (addR rR pX pT)
  (.seq (WMX.inc pX) (.seq (WMX.inc pX) (.seq (WMX.inc pY)
  (.seq (EncSetup.powW pX pY pZ pA2 pT cd)
  (.seq (WMX.dec pY) (sizeW pY rH rB rCL))))))

/-- Fit test, part 3: `rS := R + cl + pl`, `rS2 := 2 rS`, `rF := [rS2 ≤ rC2]`. -/
def fitW3 (pl : ℕ) : WMX (NS tK tE tH) 64 :=
  .seq (addR rR rS rT) (.seq (addR rCL rS rT) (.seq (incN rS pl)
  (.seq (addR rS rS2 rT) (.seq (addR rS rS2 rT) (leW rS2 rC2 rU rK rT rF)))))

/-- The fit test: `rR = R`, `rC2 = 2n`, `rCL = cl`, `rF = [R + cl + pl ≤ n]`. -/
def fitW (cd pl : ℕ) : WMX (NS tK tE tH) 64 :=
  .seq (fitW1 tK tE tH) (.seq (fitW2 tK tE tH cd) (fitW3 tK tE tH pl))

/-- Converter, unframed native descriptor on `DS`. -/
noncomputable def convW : WMX (NS tK tE tH) 64 :=
  .seq (.mach CloseoutCaseTwo.Cold.machine (convMap tK tE tH))
  (.seq (.wm (pairLoop (bC tK tE tH 132) scC (fun _ => WM.skip) (fun b => emitC (DS tK tE tH) opDS b)))
    (.wm (WM.rewind (DS tK tE tH) opDS)))

/-- The encoder's input `frame (messageWord ⟨R, x⟩)` on `EI`. -/
noncomputable def eiW : WMX (NS tK tE tH) 64 :=
  .seq (addR rR rRc rT)
  (.seq (bitsQ rRc rH rB (EI tK tE tH) opEI)
  (.seq (.wm (Codec.emitMarks (EI tK tE tH) opEI [false]))
  (.seq (addR rR rK rT) (.seq (addR rR rK rT)
  (.seq (.wm (cntLoop (P2 tK tE tH) scP2 rK (fun b => emitPair (EI tK tE tH) opEI b)))
  (.seq (.wm (Codec.emitMarks (EI tK tE tH) opEI [false]))
  (.seq (.wm (emitC (EI tK tE tH) opEI false))
  (.seq (.wm (WM.rewind (EI tK tE tH) opEI)) (.wm (WM.rewind (P2 tK tE tH) scP2))))))))))

noncomputable def asW (eOut : Fin (NS tK tE tH + 1)) : WMX (NS tK tE tH) 64 :=
  .seq (addR rR rK rT) (.seq (addR rR rK rT)
  (.seq (.wm (cntLoop (P2 tK tE tH) scP2 rK (fun b => emitC (AS tK tE tH) opAS b)))
  (.seq (.wm (pairLoop eOut scE (fun b => emitC (AS tK tE tH) opAS b) (fun b => emitC (AS tK tE tH) opAS b)))
    (.wm (WM.rewind (P2 tK tE tH) scP2)))))

/-- `HI := frame (C.word ++ sysEnc x)`. -/
noncomputable def hiW (cOut : Fin (NS tK tE tH + 1)) : WMX (NS tK tE tH) 64 :=
  .seq (.wm (pairLoop cOut scK (fun b => emitC (HI tK tE tH) opHI b) (fun b => emitC (HI tK tE tH) opHI b)))
  (.seq (addR opAS rT1 rT)
  (.seq (.wm (WM.rewind (AS tK tE tH) rT1))
  (.seq (.wm (pairLoop (AS tK tE tH) scAS (fun b => emitC (HI tK tE tH) opHI b) (fun b => emitC (HI tK tE tH) opHI b)))
  (.seq (.wm (emitC (HI tK tE tH) opHI false)) (.wm (WM.rewind (HI tK tE tH) opHI))))))

noncomputable def as2W (hOut : Fin (NS tK tE tH + 1)) : WMX (NS tK tE tH) 64 :=
  .wm (pairLoop hOut scH (fun b => emitC (AS tK tE tH) opAS b) (fun b => emitC (AS tK tE tH) opAS b))

/-- The address fields: `R 0 := a`, `rJ := j`. -/
noncomputable def addrW (pl : ℕ) : WMX (NS tK tE tH) 64 :=
  .seq (addR rR rK rT) (.seq (addR rR rK rT)
  (.seq (.wm (skipN (P2 tK tE tH) scP2 rK))
  (.seq (addR rCL rK rT)
  (.seq (LitDecode.binK (P2 tK tE tH) rK (R 0) (R 10) (R 11) (R 12) scP2)
  (.seq (incN rK pl) (LitDecode.binK (P2 tK tE tH) rK rJ (R 10) (R 11) (R 12) scP2))))))

/-- `rKr := 2v + 1`. -/
def twoPlus (V : Fin 64) : WMX (NS tK tE tH) 64 := .seq (addR V rKr rT) (.seq (addR V rKr rT) (WMX.inc rKr))

/-- The three coordinates `b_t := asg[v_t]`. -/
noncomputable def rdW : WMX (NS tK tE tH) 64 :=
  .seq (addR opAS rT1 rT)
  (.seq (.wm (WM.rewind (AS tK tE tH) rT1))
  (.seq (twoPlus tK tE tH (R 1)) (.seq (readAt (AS tK tE tH) rT3 rKr b0)
  (.seq (twoPlus tK tE tH (R 2)) (.seq (readAt (AS tK tE tH) rT3 rKr b1)
  (.seq (twoPlus tK tE tH (R 3)) (readAt (AS tK tE tH) rT3 rKr b2)))))))

/-- `rJ5 := j mod 5`, then the output bit. -/
noncomputable def outPhase : WMX (NS tK tE tH) 64 :=
  .seq (incN rM5 5) (.seq (ClauseFront.modW rJ rM5 rJ5 rD5 rK5 rT)
    (outW (OUT tK tE tH) opOUT rJ5 b0 b1 b2 (R 4) (R 5) (R 6)))

end Program

end NearCubicGates.Close.Recovery.HT
