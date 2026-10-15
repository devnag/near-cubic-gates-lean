import Proof.Gates.Setup.Words
import Proof.Gates.Recovery.HTParts3
import Proof.Gates.CheckedPCPP.EmitNat
import Proof.Gates.CheckedPCPP.NodeEmit
import Proof.Gates.WordPrograms.BinW

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Recovery.HTParts (leW leW_exec)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-! ## The cold state -/

section Cold
variable (D : SetupData s P g) (xs bits : List Bool)

theorem sX_ne_sBW : sX D ≠ sBW D := by intro h; have := congrArg Fin.val h; simp [sX, sBW, fixS] at this

theorem coldState_X : (coldState D xs bits).st (sX D) = RepairOrdinary.frame xs := by simp [coldState]

theorem coldState_BW : (coldState D xs bits).st (sBW D) = RepairOrdinary.frame bits := by
  simp only [coldState]; rw [if_neg (Ne.symm (sX_ne_sBW D))]; simp

theorem coldState_other (i : Fin (nsW D + 1)) (h1 : i ≠ sX D) (h2 : i ≠ sBW D) : (coldState D xs bits).st i = [] := by
  simp [coldState, h1, h2]

@[simp] theorem coldState_sh : (coldState D xs bits).sh = fun _ => 0 := rfl
@[simp] theorem coldState_val : (coldState D xs bits).val = fun _ => 0 := rfl
@[simp] theorem coldState_cell : (coldState D xs bits).cell = false := rfl

end Cold

/-! ## Halving a register -/

/-- `X := X / 2` (`H`, `B` scratch at `0`). -/
def halfStep (X H B : Fin nrW) {ns : ℕ} : WMX ns nrW :=
  .seq (EmitNat.halve X H B) (.wm (.seq (WM.clear B) (WM.move H X)))

theorem halfStep_exec {ns cap : ℕ} {X H B : Fin nrW} (hXH : X ≠ H) (hXB : X ≠ B) (hHB : H ≠ B) (σ : WState ns nrW)
    (v : ℕ) (hv : σ.val X = v) (hH : σ.val H = 0) (hB : σ.val B = 0) (hc : 2 * v + 2 ≤ cap) :
    WXExec cap (halfStep X H B) σ (σ.setv X (v / 2)) (20 * v + 20) := by
  have e1 := EmitNat.halve_exec (cap := cap) X H B hXH hXB hHB v σ hv hB (by omega) (by omega) (by omega)
  set σ1 := ((σ.setv X 0).setv H (σ.val H + v / 2)).setv B (v % 2) with hσ1
  have e2 := WireExponent3_5.FinalPass.Tm.wclear_spec (cap := cap) B (v % 2) σ1 (by simp [hσ1])
    (by simp [hσ1]; omega)
  set σ2 := σ1.setv B 0 with hσ2
  have hX2 : σ2.val X = 0 := by simp [hσ2, hσ1, Function.update_apply, hXH, hXB]
  have hH2 : σ2.val H = v / 2 := by simp [hσ2, hσ1, Function.update_apply, hHB, hH]
  have e3 := WireExponent3_5.FinalPass.Tm.wmove_spec (cap := cap) H X (Ne.symm hXH) (v / 2) σ2 hH2 (by omega)
    (by omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.wm (WExec.seq e2 e3))) ?_ ?_
  · apply WState.eq <;> try rfl
    funext r
    simp only [hσ2, hσ1, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · have : v % 2 ≤ 1 := by omega
    have : v / 2 ≤ v := Nat.div_le_self _ _
    omega

/-- `X := X / 16`. -/
def div16 (X H B : Fin nrW) {ns : ℕ} : WMX ns nrW :=
  .seq (halfStep X H B) (.seq (halfStep X H B) (.seq (halfStep X H B) (halfStep X H B)))

theorem div16_exec {ns cap : ℕ} {X H B : Fin nrW} (hXH : X ≠ H) (hXB : X ≠ B) (hHB : H ≠ B) (σ : WState ns nrW)
    (v : ℕ) (hv : σ.val X = v) (hH : σ.val H = 0) (hB : σ.val B = 0) (hc : 2 * v + 2 ≤ cap) :
    WXExec cap (div16 X H B) σ (σ.setv X (v / 16)) (100 * v + 100) := by
  have hHv : ∀ (τ : WState ns nrW) (y : ℕ), (τ.setv X y).val H = τ.val H := fun τ y => by
    simp [Function.update_of_ne (Ne.symm hXH)]
  have hBv : ∀ (τ : WState ns nrW) (y : ℕ), (τ.setv X y).val B = τ.val B := fun τ y => by
    simp [Function.update_of_ne (Ne.symm hXB)]
  have e1 := halfStep_exec (cap := cap) hXH hXB hHB σ v hv hH hB hc
  have e2 := halfStep_exec (cap := cap) hXH hXB hHB (σ.setv X (v / 2)) (v / 2) (by simp) (by rw [hHv]; exact hH)
    (by rw [hBv]; exact hB) (by omega)
  have e3 := halfStep_exec (cap := cap) hXH hXB hHB ((σ.setv X (v / 2)).setv X (v / 2 / 2)) (v / 2 / 2) (by simp)
    (by rw [hHv, hHv]; exact hH) (by rw [hBv, hBv]; exact hB) (by omega)
  have e4 := halfStep_exec (cap := cap) hXH hXB hHB (((σ.setv X (v / 2)).setv X (v / 2 / 2)).setv X (v / 2 / 2 / 2))
    (v / 2 / 2 / 2) (by simp) (by rw [hHv, hHv, hHv]; exact hH) (by rw [hBv, hBv, hBv]; exact hB) (by omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))) ?_ ?_
  · simp only [LitDecode.setv_setv]
    congr 1
    omega
  · omega

/-! ## Registers of phase A -/

abbrev gN0 : Fin nrW := 49
abbrev gU : Fin nrW := 50
abbrev gK : Fin nrW := 51
abbrev gT : Fin nrW := 52
abbrev gF : Fin nrW := 53
abbrev kQ : Fin nrW := 54
abbrev dS : Fin nrW := 55
abbrev hH : Fin nrW := 56
abbrev hBr : Fin nrW := 57
abbrev oW : Fin nrW := 58
abbrev bR : Fin nrW := 59
abbrev tW : Fin nrW := 48

def phA0 (D : SetupData s P g) : WMX (nsW D) nrW :=
  .seq (BinW.width (sX D) rN tW) (.seq (.wm (NodeEmit.incN gN0 D.N0)) (leW gN0 rN gU gK gT gF))

def phA1 (D : SetupData s P g) : WMX (nsW D) nrW :=
  .seq (.wm (.seq (WM.clear gF) (WM.clear gN0)))
  (.seq (.wm (Codec.dupR rN kQ dS))
  (.seq (div16 kQ hH hBr)
  (.seq (.wm (Codec.unframeW (sBW D) (sWT D) oW kQ))
  (.wm (.seq (WM.rewind (sWT D) oW) (.seq (Codec.dupR rN bR dS) (WM.rewind (sBW D) bR)))))))

/-! ## Phase A, specs -/

theorem fixS_ne (D : SetupData s P g) {i j : ℕ} (hi : i < 16) (hj : j < 16) (h : i ≠ j) : fixS D i hi ≠ fixS D j hj := by
  intro e; exact h (congrArg Fin.val e)

def stA0 (D : SetupData s P g) (N : ℕ) (xs bits : List Bool) : WState (nsW D) nrW :=
  (((coldState D xs bits).setv rN N).setv gN0 D.N0).setv gF (if D.N0 ≤ N then 1 else 0)

theorem phA0_exec (D : SetupData s P g) {N : ℕ} (x : BitInput N) (bits : List Bool) (cap : ℕ)
    (hcap : N + D.N0 + 1 ≤ cap) :
    WXExec cap (phA0 D) (coldState D (List.ofFn x) bits) (stA0 D N (List.ofFn x) bits) (100 * (N + D.N0 + 1)) := by
  set σ0 := coldState D (List.ofFn x) bits with hσ0
  have hb := WireExponent3_5.CompilerMachine.Emit.binary_value_self (List.ofFn x)
  rw [List.length_ofFn] at hb
  have hnum : WireExponent3_5.SelectionMachine.Sort.NumOn σ0 (sX D) N (value (List.ofFn x)) := by
    refine ⟨?_, rfl⟩
    rw [hσ0, coldState_X, hb]
  have e1 := BinW.width_spec cap (A := sX D) (K := rN) (T := tW) (by decide) N _ σ0 hnum rfl rfl (by omega)
  have e2 := NodeEmit.incN_spec (cap := cap) gN0 D.N0 (σ0.setv rN N) (by simp [gN0, rN, hσ0]; omega)
  have e3 := leW_exec (cap := cap) (A := gN0) (B := rN) (U := gU) (K := gK) (T := gT) (F := gF) (by decide) D.N0 N
    (by omega) ((σ0.setv rN N).setv gN0 ((σ0.setv rN N).val gN0 + D.N0)) (by simp [gN0, rN, hσ0])
    (by simp [gN0, rN]) (by simp [gN0, rN, gU, hσ0]) (by simp [gN0, rN, gK, hσ0]) (by simp [gN0, rN, gT, hσ0])
    (by simp [gN0, rN, gF, hσ0])
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) e3)) ?_ ?_
  · simp [stA0, hσ0, gN0, rN]
  · omega

def stA1 (D : SetupData s P g) (N : ℕ) (xs bits : List Bool) : WState (nsW D) nrW :=
  ((coldState D xs bits).setv rN N).sets (sWT D) (Codec.prefixBits bits (N / 16))

theorem phA1_exec (D : SetupData s P g) {N : ℕ} (x : BitInput N) (bits : List Bool) (cap : ℕ)
    (hcap : 4 * N + D.N0 + 4 ≤ cap) (hG : D.N0 ≤ N) :
    WXExec cap (phA1 D) (stA0 D N (List.ofFn x) bits) (stA1 D N (List.ofFn x) bits) (1000 * (N + D.N0 + 1)) := by
  set σ0 := coldState D (List.ofFn x) bits with hσ0
  set m := N / 16 with hm
  have hWB : sBW D ≠ sWT D := fixS_ne D _ _ (by decide)
  have e1 := WireExponent3_5.FinalPass.Tm.wclear_spec (cap := cap) gF 1 (stA0 D N (List.ofFn x) bits)
    (by simp [hσ0, stA0, hG]) (by simp [hσ0, stA0, hG]; omega)
  have e2 := WireExponent3_5.FinalPass.Tm.wclear_spec (cap := cap) gN0 D.N0 ((stA0 D N (List.ofFn x) bits).setv gF 0)
    (by simp [hσ0, stA0, gF, gN0]) (by simp [hσ0, stA0, gF, gN0]; omega)
  have h12 : ((stA0 D N (List.ofFn x) bits).setv gF 0).setv gN0 0 = σ0.setv rN N := by
    apply WState.eq <;> try rfl
    funext r
    simp only [stA0, WState.setv_val, Function.update_apply, hσ0, coldState_val]
    split_ifs <;> simp_all (config := { decide := true })
  rw [h12] at e2
  have e3 := Codec.dupR_spec cap rN kQ dS (by decide) (by decide) (by decide) (σ0.setv rN N) (by simp [hσ0, rN, dS])
    (by simp [hσ0, rN, kQ]; omega)
  have h3 : (σ0.setv rN N).setv kQ ((σ0.setv rN N).val kQ + (σ0.setv rN N).val rN) = (σ0.setv rN N).setv kQ N := by
    simp [hσ0, rN, kQ]
  rw [h3] at e3
  set σ3 := (σ0.setv rN N).setv kQ N with hσ3
  have e4 := div16_exec (cap := cap) (X := kQ) (H := hH) (B := hBr) (by decide) (by decide) (by decide) σ3 N
    (by simp [hσ0, hσ3]) (by simp [hσ0, hσ3, kQ, hH, rN]) (by simp [hσ0, hσ3, kQ, hBr, rN]) (by omega)
  set σ4 := σ3.setv kQ m with hσ4
  have e5 := Codec.unframeW_spec cap (sBW D) (sWT D) hWB oW kQ (by decide) bits m σ4
    (by simp [hσ0, hσ4, hσ3, hσ0, coldState_BW]) (by simp [hσ0, hσ4, hσ3, hσ0])
    (by simp [hσ0, hσ4, hσ3, hσ0, coldState_other D _ _ (sWT D) (fixS_ne D _ _ (by decide)) (fixS_ne D _ _ (by decide))])
    (by simp [hσ0, hσ4]) (by omega) (by simp [hσ0, hσ4, hσ3, oW, kQ, rN]; omega)
  set σ5 := ((appendO σ4 (sWT D) oW (Codec.prefixBits bits m)).seth (sBW D) (2 * min m bits.length)).setv kQ 0
    with hσ5
  have hoW : σ5.val oW = m := by simp [hσ0, hσ5, hσ4, hσ3, oW, kQ, rN, Codec.prefixBits]
  have e6 := WireExponent3_5.FinalPass.Tm.wrewind_spec (cap := cap) (sWT D) oW m σ5 hoW (by omega)
  set σ6 := (σ5.setv oW 0).seth (sWT D) (σ5.sh (sWT D) - m) with hσ6
  have e7 := Codec.dupR_spec cap rN bR dS (by decide) (by decide) (by decide) σ6
    (by simp [hσ0, hσ6, hσ5, hσ4, hσ3, dS, oW, kQ, rN]) (by simp [hσ0, hσ6, hσ5, hσ4, hσ3, bR, oW, kQ, rN]; omega)
  set σ7 := σ6.setv bR (σ6.val bR + σ6.val rN) with hσ7
  have hbR : σ7.val bR = N := by simp [hσ0, hσ7, hσ6, hσ5, hσ4, hσ3, bR, oW, kQ, rN]
  have e8 := WireExponent3_5.FinalPass.Tm.wrewind_spec (cap := cap) (sBW D) bR N σ7 hbR (by omega)
  refine WXExec.cast cap (WXExec.seq (WXExec.wm (WExec.seq e1 e2)) (WXExec.seq (WXExec.wm e3)
    (WXExec.seq e4 (WXExec.seq (WXExec.wm e5) (WXExec.wm (WExec.seq e6 (WExec.seq e7 e8))))))) ?_ ?_
  · have hmN : 2 * min m bits.length ≤ N := by omega
    apply WState.eq
    · funext i
      simp only [stA1, hσ7, hσ6, hσ5, hσ4, hσ3, hσ0, WState.seth_sh, WState.setv_sh, WState.sets_sh, appendO_sh,
        coldState_sh, Function.update_apply, WState.setv_val, appendO_val]
      split_ifs <;> simp_all (config := { decide := true }) [Codec.prefixBits]
    · funext i
      simp only [stA1, hσ7, hσ6, hσ5, hσ4, hσ3, hσ0, WState.seth_st, WState.setv_st, WState.sets_st, appendO_st,
        Function.update_apply]
      split_ifs with h1 <;> simp_all (config := { decide := true }) [coldState_other D _ _ (sWT D) (fixS_ne D _ _ (by decide))
        (fixS_ne D _ _ (by decide))]
    · funext r
      simp only [stA1, hσ7, hσ6, hσ5, hσ4, hσ3, hσ0, WState.seth_val, WState.setv_val, WState.sets_val, appendO_val,
        Function.update_apply, coldState_val]
      split_ifs <;> simp_all (config := { decide := true }) [Codec.prefixBits]
    · rfl
  · have : m ≤ N := by omega
    have : min m bits.length ≤ m := min_le_left _ _
    have h1 : (σ0.setv rN N).val rN = N := by simp
    have h2 : σ6.val rN = N := by simp (config := { decide := true }) [hσ0, hσ6, hσ5, hσ4, hσ3, Function.update_apply]
    rw [h1, h2]
    omega

end

end NearCubicGates.Close.Setup
