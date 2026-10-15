import Proof.Gates.Dispatch.Lang
import Proof.Gates.WordPrograms.BinW
import Proof.Gates.WordPrograms.BinWDiv

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Dispatch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {V : ℕ}

/-! ## Layout -/

/-- Register count. -/
abbrev NR : ℕ := 12

def sIN : Fin (V + 3 + 1) := ⟨0, by omega⟩
def sOUT : Fin (V + 3 + 1) := ⟨1, by omega⟩
def sCW : Fin (V + 3 + 1) := ⟨2, by omega⟩
def sZ : Fin (V + 3 + 1) := ⟨3, by omega⟩
/-- The stream of variable `x`. -/
def vs (x : Fin V) : Fin (V + 3 + 1) := ⟨x.val + 4, by omega⟩

def rF : Fin NR := ⟨0, by decide⟩
def rR : Fin NR := ⟨1, by decide⟩
def rG : Fin NR := ⟨2, by decide⟩
def rK : Fin NR := ⟨3, by decide⟩
def rT : Fin NR := ⟨4, by decide⟩
def rCP : Fin NR := ⟨5, by decide⟩
def rIP : Fin NR := ⟨6, by decide⟩
def rOP : Fin NR := ⟨7, by decide⟩
def rLR : Fin NR := ⟨8, by decide⟩
def rWR : Fin NR := ⟨9, by decide⟩
def rA2 : Fin NR := ⟨10, by decide⟩
def rT2 : Fin NR := ⟨11, by decide⟩
@[simp] theorem rF_ne_rR : rF ≠ rR := by decide
@[simp] theorem rF_ne_rG : rF ≠ rG := by decide
@[simp] theorem rF_ne_rK : rF ≠ rK := by decide
@[simp] theorem rF_ne_rT : rF ≠ rT := by decide
@[simp] theorem rF_ne_rCP : rF ≠ rCP := by decide
@[simp] theorem rF_ne_rIP : rF ≠ rIP := by decide
@[simp] theorem rF_ne_rOP : rF ≠ rOP := by decide
@[simp] theorem rF_ne_rLR : rF ≠ rLR := by decide
@[simp] theorem rF_ne_rWR : rF ≠ rWR := by decide
@[simp] theorem rF_ne_rA2 : rF ≠ rA2 := by decide
@[simp] theorem rF_ne_rT2 : rF ≠ rT2 := by decide
@[simp] theorem rR_ne_rF : rR ≠ rF := by decide
@[simp] theorem rR_ne_rG : rR ≠ rG := by decide
@[simp] theorem rR_ne_rK : rR ≠ rK := by decide
@[simp] theorem rR_ne_rT : rR ≠ rT := by decide
@[simp] theorem rR_ne_rCP : rR ≠ rCP := by decide
@[simp] theorem rR_ne_rIP : rR ≠ rIP := by decide
@[simp] theorem rR_ne_rOP : rR ≠ rOP := by decide
@[simp] theorem rR_ne_rLR : rR ≠ rLR := by decide
@[simp] theorem rR_ne_rWR : rR ≠ rWR := by decide
@[simp] theorem rR_ne_rA2 : rR ≠ rA2 := by decide
@[simp] theorem rR_ne_rT2 : rR ≠ rT2 := by decide
@[simp] theorem rG_ne_rF : rG ≠ rF := by decide
@[simp] theorem rG_ne_rR : rG ≠ rR := by decide
@[simp] theorem rG_ne_rK : rG ≠ rK := by decide
@[simp] theorem rG_ne_rT : rG ≠ rT := by decide
@[simp] theorem rG_ne_rCP : rG ≠ rCP := by decide
@[simp] theorem rG_ne_rIP : rG ≠ rIP := by decide
@[simp] theorem rG_ne_rOP : rG ≠ rOP := by decide
@[simp] theorem rG_ne_rLR : rG ≠ rLR := by decide
@[simp] theorem rG_ne_rWR : rG ≠ rWR := by decide
@[simp] theorem rG_ne_rA2 : rG ≠ rA2 := by decide
@[simp] theorem rG_ne_rT2 : rG ≠ rT2 := by decide
@[simp] theorem rK_ne_rF : rK ≠ rF := by decide
@[simp] theorem rK_ne_rR : rK ≠ rR := by decide
@[simp] theorem rK_ne_rG : rK ≠ rG := by decide
@[simp] theorem rK_ne_rT : rK ≠ rT := by decide
@[simp] theorem rK_ne_rCP : rK ≠ rCP := by decide
@[simp] theorem rK_ne_rIP : rK ≠ rIP := by decide
@[simp] theorem rK_ne_rOP : rK ≠ rOP := by decide
@[simp] theorem rK_ne_rLR : rK ≠ rLR := by decide
@[simp] theorem rK_ne_rWR : rK ≠ rWR := by decide
@[simp] theorem rK_ne_rA2 : rK ≠ rA2 := by decide
@[simp] theorem rK_ne_rT2 : rK ≠ rT2 := by decide
@[simp] theorem rT_ne_rF : rT ≠ rF := by decide
@[simp] theorem rT_ne_rR : rT ≠ rR := by decide
@[simp] theorem rT_ne_rG : rT ≠ rG := by decide
@[simp] theorem rT_ne_rK : rT ≠ rK := by decide
@[simp] theorem rT_ne_rCP : rT ≠ rCP := by decide
@[simp] theorem rT_ne_rIP : rT ≠ rIP := by decide
@[simp] theorem rT_ne_rOP : rT ≠ rOP := by decide
@[simp] theorem rT_ne_rLR : rT ≠ rLR := by decide
@[simp] theorem rT_ne_rWR : rT ≠ rWR := by decide
@[simp] theorem rT_ne_rA2 : rT ≠ rA2 := by decide
@[simp] theorem rT_ne_rT2 : rT ≠ rT2 := by decide
@[simp] theorem rCP_ne_rF : rCP ≠ rF := by decide
@[simp] theorem rCP_ne_rR : rCP ≠ rR := by decide
@[simp] theorem rCP_ne_rG : rCP ≠ rG := by decide
@[simp] theorem rCP_ne_rK : rCP ≠ rK := by decide
@[simp] theorem rCP_ne_rT : rCP ≠ rT := by decide
@[simp] theorem rCP_ne_rIP : rCP ≠ rIP := by decide
@[simp] theorem rCP_ne_rOP : rCP ≠ rOP := by decide
@[simp] theorem rCP_ne_rLR : rCP ≠ rLR := by decide
@[simp] theorem rCP_ne_rWR : rCP ≠ rWR := by decide
@[simp] theorem rCP_ne_rA2 : rCP ≠ rA2 := by decide
@[simp] theorem rCP_ne_rT2 : rCP ≠ rT2 := by decide
@[simp] theorem rIP_ne_rF : rIP ≠ rF := by decide
@[simp] theorem rIP_ne_rR : rIP ≠ rR := by decide
@[simp] theorem rIP_ne_rG : rIP ≠ rG := by decide
@[simp] theorem rIP_ne_rK : rIP ≠ rK := by decide
@[simp] theorem rIP_ne_rT : rIP ≠ rT := by decide
@[simp] theorem rIP_ne_rCP : rIP ≠ rCP := by decide
@[simp] theorem rIP_ne_rOP : rIP ≠ rOP := by decide
@[simp] theorem rIP_ne_rLR : rIP ≠ rLR := by decide
@[simp] theorem rIP_ne_rWR : rIP ≠ rWR := by decide
@[simp] theorem rIP_ne_rA2 : rIP ≠ rA2 := by decide
@[simp] theorem rIP_ne_rT2 : rIP ≠ rT2 := by decide
@[simp] theorem rOP_ne_rF : rOP ≠ rF := by decide
@[simp] theorem rOP_ne_rR : rOP ≠ rR := by decide
@[simp] theorem rOP_ne_rG : rOP ≠ rG := by decide
@[simp] theorem rOP_ne_rK : rOP ≠ rK := by decide
@[simp] theorem rOP_ne_rT : rOP ≠ rT := by decide
@[simp] theorem rOP_ne_rCP : rOP ≠ rCP := by decide
@[simp] theorem rOP_ne_rIP : rOP ≠ rIP := by decide
@[simp] theorem rOP_ne_rLR : rOP ≠ rLR := by decide
@[simp] theorem rOP_ne_rWR : rOP ≠ rWR := by decide
@[simp] theorem rOP_ne_rA2 : rOP ≠ rA2 := by decide
@[simp] theorem rOP_ne_rT2 : rOP ≠ rT2 := by decide
@[simp] theorem rLR_ne_rF : rLR ≠ rF := by decide
@[simp] theorem rLR_ne_rR : rLR ≠ rR := by decide
@[simp] theorem rLR_ne_rG : rLR ≠ rG := by decide
@[simp] theorem rLR_ne_rK : rLR ≠ rK := by decide
@[simp] theorem rLR_ne_rT : rLR ≠ rT := by decide
@[simp] theorem rLR_ne_rCP : rLR ≠ rCP := by decide
@[simp] theorem rLR_ne_rIP : rLR ≠ rIP := by decide
@[simp] theorem rLR_ne_rOP : rLR ≠ rOP := by decide
@[simp] theorem rLR_ne_rWR : rLR ≠ rWR := by decide
@[simp] theorem rLR_ne_rA2 : rLR ≠ rA2 := by decide
@[simp] theorem rLR_ne_rT2 : rLR ≠ rT2 := by decide
@[simp] theorem rWR_ne_rF : rWR ≠ rF := by decide
@[simp] theorem rWR_ne_rR : rWR ≠ rR := by decide
@[simp] theorem rWR_ne_rG : rWR ≠ rG := by decide
@[simp] theorem rWR_ne_rK : rWR ≠ rK := by decide
@[simp] theorem rWR_ne_rT : rWR ≠ rT := by decide
@[simp] theorem rWR_ne_rCP : rWR ≠ rCP := by decide
@[simp] theorem rWR_ne_rIP : rWR ≠ rIP := by decide
@[simp] theorem rWR_ne_rOP : rWR ≠ rOP := by decide
@[simp] theorem rWR_ne_rLR : rWR ≠ rLR := by decide
@[simp] theorem rWR_ne_rA2 : rWR ≠ rA2 := by decide
@[simp] theorem rWR_ne_rT2 : rWR ≠ rT2 := by decide
@[simp] theorem rA2_ne_rF : rA2 ≠ rF := by decide
@[simp] theorem rA2_ne_rR : rA2 ≠ rR := by decide
@[simp] theorem rA2_ne_rG : rA2 ≠ rG := by decide
@[simp] theorem rA2_ne_rK : rA2 ≠ rK := by decide
@[simp] theorem rA2_ne_rT : rA2 ≠ rT := by decide
@[simp] theorem rA2_ne_rCP : rA2 ≠ rCP := by decide
@[simp] theorem rA2_ne_rIP : rA2 ≠ rIP := by decide
@[simp] theorem rA2_ne_rOP : rA2 ≠ rOP := by decide
@[simp] theorem rA2_ne_rLR : rA2 ≠ rLR := by decide
@[simp] theorem rA2_ne_rWR : rA2 ≠ rWR := by decide
@[simp] theorem rA2_ne_rT2 : rA2 ≠ rT2 := by decide
@[simp] theorem rT2_ne_rF : rT2 ≠ rF := by decide
@[simp] theorem rT2_ne_rR : rT2 ≠ rR := by decide
@[simp] theorem rT2_ne_rG : rT2 ≠ rG := by decide
@[simp] theorem rT2_ne_rK : rT2 ≠ rK := by decide
@[simp] theorem rT2_ne_rT : rT2 ≠ rT := by decide
@[simp] theorem rT2_ne_rCP : rT2 ≠ rCP := by decide
@[simp] theorem rT2_ne_rIP : rT2 ≠ rIP := by decide
@[simp] theorem rT2_ne_rOP : rT2 ≠ rOP := by decide
@[simp] theorem rT2_ne_rLR : rT2 ≠ rLR := by decide
@[simp] theorem rT2_ne_rWR : rT2 ≠ rWR := by decide
@[simp] theorem rT2_ne_rA2 : rT2 ≠ rA2 := by decide

@[simp] theorem rF_val : rF.val = 0 := rfl
@[simp] theorem rR_val : rR.val = 1 := rfl
@[simp] theorem rG_val : rG.val = 2 := rfl
@[simp] theorem rK_val : rK.val = 3 := rfl
@[simp] theorem rT_val : rT.val = 4 := rfl
@[simp] theorem rCP_val : rCP.val = 5 := rfl
@[simp] theorem rIP_val : rIP.val = 6 := rfl
@[simp] theorem rOP_val : rOP.val = 7 := rfl
@[simp] theorem rLR_val : rLR.val = 8 := rfl
@[simp] theorem rWR_val : rWR.val = 9 := rfl
@[simp] theorem rA2_val : rA2.val = 10 := rfl
@[simp] theorem rT2_val : rT2.val = 11 := rfl
@[simp] theorem sIN_val : (sIN : Fin (V + 3 + 1)).val = 0 := rfl
@[simp] theorem sOUT_val : (sOUT : Fin (V + 3 + 1)).val = 1 := rfl
@[simp] theorem sCW_val : (sCW : Fin (V + 3 + 1)).val = 2 := rfl
@[simp] theorem sZ_val : (sZ : Fin (V + 3 + 1)).val = 3 := rfl
@[simp] theorem sIN_ne_sOUT : (sIN : Fin (V + 3 + 1)) ≠ sOUT := by simp [sIN, sOUT]
@[simp] theorem sIN_ne_sCW : (sIN : Fin (V + 3 + 1)) ≠ sCW := by simp [sIN, sCW]
@[simp] theorem sIN_ne_sZ : (sIN : Fin (V + 3 + 1)) ≠ sZ := by simp [sIN, sZ]
@[simp] theorem sOUT_ne_sIN : (sOUT : Fin (V + 3 + 1)) ≠ sIN := by simp [sIN, sOUT]
@[simp] theorem sOUT_ne_sCW : (sOUT : Fin (V + 3 + 1)) ≠ sCW := by simp [sCW, sOUT]
@[simp] theorem sOUT_ne_sZ : (sOUT : Fin (V + 3 + 1)) ≠ sZ := by simp [sZ, sOUT]
@[simp] theorem sCW_ne_sIN : (sCW : Fin (V + 3 + 1)) ≠ sIN := by simp [sIN, sCW]
@[simp] theorem sCW_ne_sOUT : (sCW : Fin (V + 3 + 1)) ≠ sOUT := by simp [sCW, sOUT]
@[simp] theorem sCW_ne_sZ : (sCW : Fin (V + 3 + 1)) ≠ sZ := by simp [sCW, sZ]
@[simp] theorem sZ_ne_sIN : (sZ : Fin (V + 3 + 1)) ≠ sIN := by simp [sIN, sZ]
@[simp] theorem sZ_ne_sOUT : (sZ : Fin (V + 3 + 1)) ≠ sOUT := by simp [sZ, sOUT]
@[simp] theorem sZ_ne_sCW : (sZ : Fin (V + 3 + 1)) ≠ sCW := by simp [sCW, sZ]

theorem vs_val (x : Fin V) : (vs x).val = x.val + 4 := rfl
theorem vs_inj {x y : Fin V} (h : x ≠ y) : vs x ≠ vs y := by
  intro e; apply h; apply Fin.ext; have := congrArg Fin.val e; simp [vs] at this; omega
theorem vs_ne_Z (x : Fin V) : vs x ≠ sZ := by intro e; have := congrArg Fin.val e; simp [vs, sZ] at this
theorem Z_ne_vs (x : Fin V) : sZ ≠ vs x := fun e => vs_ne_Z x e.symm

/-! ## The encoding of a state -/

/-- Stream contents. -/
def stF (C : Ctx) (inp : List Bool) (a : DS V) (i : Fin (V + 3 + 1)) : List Bool :=
  if h : 4 ≤ i.val then frame (binary C.Wd (a.env ⟨i.val - 4, by have := i.isLt; omega⟩))
  else if i.val = 0 then inp else if i.val = 1 then a.out else if i.val = 2 then C.cw else frame (binary C.Wd 0)

/-- Stream heads. -/
def shF (p0 : ℕ) (a : DS V) (i : Fin (V + 3 + 1)) : ℕ :=
  if i.val = 0 then p0 + 4 * a.wq else if i.val = 1 then a.out.length else if i.val = 2 then a.cp else 0

/-- Registers. -/
def valF (p0 : ℕ) (a : DS V) (r : Fin NR) : ℕ :=
  if r.val = 5 then a.cp else if r.val = 6 then p0 + 4 * a.wq else if r.val = 7 then a.out.length else 0

/-- **The encoding.** -/
def E (C : Ctx) (inp : List Bool) (p0 : ℕ) (a : DS V) : WState (V + 3) NR :=
  ⟨shF p0 a, stF C inp a, valF p0 a, false⟩

section Enc
variable (C : Ctx) (inp : List Bool) (p0 : ℕ)

theorem stF_vs (a : DS V) (x : Fin V) : stF C inp a (vs x) = frame (binary C.Wd (a.env x)) := by
  simp [stF, vs]

theorem E_numOn (a : DS V) (x : Fin V) : NumOn (E C inp p0 a) (vs x) C.Wd (a.env x) := by
  refine ⟨?_, ?_⟩
  · exact stF_vs C inp a x
  · show shF p0 a (vs x) = 0
    unfold shF; simp [vs]

theorem E_numZ (a : DS V) : NumOn (E C inp p0 a) sZ C.Wd 0 := by
  refine ⟨?_, ?_⟩
  · show stF C inp a sZ = _
    unfold stF; simp [sZ]
  · show shF p0 a sZ = 0
    unfold shF; simp [sZ]

@[simp] theorem E_val_F (a : DS V) : (E C inp p0 a).val rF = 0 := by simp [E, valF, rF]
@[simp] theorem E_val_R (a : DS V) : (E C inp p0 a).val rR = 0 := by simp [E, valF, rR]
@[simp] theorem E_val_G (a : DS V) : (E C inp p0 a).val rG = 0 := by simp [E, valF, rG]
@[simp] theorem E_val_K (a : DS V) : (E C inp p0 a).val rK = 0 := by simp [E, valF, rK]
@[simp] theorem E_val_T (a : DS V) : (E C inp p0 a).val rT = 0 := by simp [E, valF, rT]
@[simp] theorem E_val_CP (a : DS V) : (E C inp p0 a).val rCP = a.cp := by simp [E, valF, rCP]
@[simp] theorem E_val_IP (a : DS V) : (E C inp p0 a).val rIP = p0 + 4 * a.wq := by simp [E, valF, rIP]
@[simp] theorem E_val_OP (a : DS V) : (E C inp p0 a).val rOP = a.out.length := by simp [E, valF, rOP]
@[simp] theorem E_st_CW (a : DS V) : (E C inp p0 a).st sCW = C.cw := by simp [E, stF, sCW]
@[simp] theorem E_sh_CW (a : DS V) : (E C inp p0 a).sh sCW = a.cp := by simp [E, shF, sCW]
@[simp] theorem E_st_OUT (a : DS V) : (E C inp p0 a).st sOUT = a.out := by simp [E, stF, sOUT]
@[simp] theorem E_sh_OUT (a : DS V) : (E C inp p0 a).sh sOUT = a.out.length := by simp [E, shF, sOUT]
@[simp] theorem E_st_IN (a : DS V) : (E C inp p0 a).st sIN = inp := by simp [E, stF, sIN]
@[simp] theorem E_sh_IN (a : DS V) : (E C inp p0 a).sh sIN = p0 + 4 * a.wq := by simp [E, shF, sIN]

/-- Writing a variable's stream. -/
theorem E_sets (a : DS V) (x : Fin V) (v : ℕ) :
    (E C inp p0 a).sets (vs x) (frame (binary C.Wd v)) = E C inp p0 (a.set x v) := by
  refine WState.eq rfl ?_ rfl rfl
  funext i
  simp only [WState.sets_st, E]
  by_cases hi : i = vs x
  · subst hi; rw [Function.update_self, stF_vs]; simp
  · rw [Function.update_of_ne hi]
    unfold stF
    by_cases h4 : 4 ≤ i.val
    · rw [dif_pos h4, dif_pos h4]
      have hne : (⟨i.val - 4, by have := i.isLt; omega⟩ : Fin V) ≠ x := by
        intro e; apply hi; ext; have := congrArg Fin.val e; simp at this; simp [vs]; omega
      simp [DS.set, Function.update_of_ne hne]
    · rw [dif_neg h4, dif_neg h4]; rfl

theorem E_setsZ (a : DS V) : (E C inp p0 a).sets sZ (frame (binary C.Wd 0)) = E C inp p0 a :=
  BinW.sets_same (E_numZ C inp p0 a).1

theorem E_setvF (a : DS V) : (E C inp p0 a).setv rF 0 = E C inp p0 a := BinW.setv_same (by simp)

/-- The call-word cursor moves. -/
theorem E_cp (a : DS V) :
    ((E C inp p0 a).seth sCW (a.cp + 1)).setv rCP (a.cp + 1) = E C inp p0 { a with cp := a.cp + 1 } := by
  refine WState.eq ?_ rfl ?_ rfl
  · funext i; simp only [WState.setv_sh, WState.seth_sh, E]
    by_cases hi : i = sCW
    · subst hi; simp [shF, sCW]
    · rw [Function.update_of_ne hi]; unfold shF
      have : i.val ≠ 2 := fun h => hi (Fin.ext h)
      simp [this]
  · funext r; simp only [WState.setv_val, WState.seth_val, E]
    by_cases hr : r = rCP
    · subst hr; simp [valF, rCP]
    · rw [Function.update_of_ne hr]; unfold valF
      have : r.val ≠ 5 := fun h => hr (Fin.ext h)
      simp [this]

theorem E_cp_back (a : DS V) (j : ℕ) :
    ((E C inp p0 a).setv rCP j).seth sCW j = E C inp p0 { a with cp := j } := by
  refine WState.eq ?_ rfl ?_ rfl
  · funext i; simp only [WState.setv_sh, WState.seth_sh, E]
    by_cases hi : i = sCW
    · subst hi; simp [shF, sCW]
    · rw [Function.update_of_ne hi]; unfold shF
      have : i.val ≠ 2 := fun h => hi (Fin.ext h)
      simp [this]
  · funext r; simp only [WState.setv_val, WState.seth_val, E]
    by_cases hr : r = rCP
    · subst hr; simp [valF, rCP]
    · rw [Function.update_of_ne hr]; unfold valF
      have : r.val ≠ 5 := fun h => hr (Fin.ext h)
      simp [this]

/-- The output grows by one bit. -/
theorem E_out (a : DS V) (b : Bool) :
    (((E C inp p0 a).sets sOUT (a.out ++ [b])).seth sOUT (a.out.length + 1)).setv rOP (a.out.length + 1) =
      E C inp p0 { a with out := a.out ++ [b] } := by
  refine WState.eq ?_ ?_ ?_ rfl
  · funext i; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, E]
    by_cases hi : i = sOUT
    · subst hi; simp [shF, sOUT]
    · rw [Function.update_of_ne hi]; unfold shF
      have : i.val ≠ 1 := fun h => hi (Fin.ext h)
      simp [this]
  · funext i; simp only [WState.setv_st, WState.seth_st, WState.sets_st, E]
    by_cases hi : i = sOUT
    · subst hi; simp [stF, sOUT]
    · rw [Function.update_of_ne hi]; unfold stF
      have : i.val ≠ 1 := fun h => hi (Fin.ext h)
      by_cases h4 : 4 ≤ i.val
      · rw [dif_pos h4, dif_pos h4]
      · rw [dif_neg h4, dif_neg h4]; simp [this]
  · funext r; simp only [WState.setv_val, WState.seth_val, WState.sets_val, E]
    by_cases hr : r = rOP
    · subst hr; simp [valF, rOP]
    · rw [Function.update_of_ne hr]; unfold valF
      have : r.val ≠ 7 := fun h => hr (Fin.ext h)
      simp [this]

/-- The entry tape at an arbitrary head position `h` (register `IP` alike). -/
def Ein (a : DS V) (h : ℕ) : WState (V + 3) NR := ((E C inp p0 a).seth sIN h).setv rIP h

theorem E_eq_Ein (a : DS V) : E C inp p0 a = Ein C inp p0 a (p0 + 4 * a.wq) := by
  unfold Ein
  rw [show (E C inp p0 a).seth sIN (p0 + 4 * a.wq) = E C inp p0 a from ?_]
  · exact (BinW.setv_same (by simp)).symm
  · refine WState.eq ?_ rfl rfl rfl
    funext i; simp only [WState.seth_sh]
    by_cases hi : i = sIN
    · subst hi; simp
    · rw [Function.update_of_ne hi]

theorem Ein_sh (a : DS V) (h : ℕ) : (Ein C inp p0 a h).sh sIN = h := by simp [Ein]
theorem Ein_val (a : DS V) (h : ℕ) : (Ein C inp p0 a h).val rIP = h := by simp [Ein]
theorem Ein_st (a : DS V) (h : ℕ) : (Ein C inp p0 a h).st sIN = inp := by simp [Ein]

theorem Ein_fwd (a : DS V) (h : ℕ) :
    ((Ein C inp p0 a h).seth sIN ((Ein C inp p0 a h).sh sIN + 1)).setv rIP h.succ = Ein C inp p0 a (h + 1) := by
  rw [Ein_sh]; unfold Ein
  refine WState.eq ?_ rfl ?_ rfl
  · funext i; simp only [WState.setv_sh, WState.seth_sh]
    by_cases hi : i = sIN
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  · funext r; simp only [WState.setv_val, WState.seth_val]
    by_cases hr : r = rIP
    · subst hr; simp
    · simp [Function.update_of_ne hr]

theorem Ein_bwd (a : DS V) (h : ℕ) :
    ((Ein C inp p0 a (h + 1)).seth sIN ((Ein C inp p0 a (h + 1)).sh sIN - 1)).setv rIP h = Ein C inp p0 a h := by
  rw [Ein_sh]; unfold Ein
  refine WState.eq ?_ rfl ?_ rfl
  · funext i; simp only [WState.setv_sh, WState.seth_sh]
    by_cases hi : i = sIN
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  · funext r; simp only [WState.setv_val, WState.seth_val]
    by_cases hr : r = rIP
    · subst hr; simp
    · simp [Function.update_of_ne hr]

theorem Ein_sets (a : DS V) (h : ℕ) (x : Fin V) (v : ℕ) :
    (Ein C inp p0 a h).sets (vs x) (frame (binary C.Wd v)) = Ein C inp p0 (a.set x v) h := by
  unfold Ein; rw [← E_sets C inp p0 a x v]
  refine WState.eq rfl ?_ rfl rfl
  funext i; simp

theorem Ein_numOn (a : DS V) (h : ℕ) (x : Fin V) : NumOn (Ein C inp p0 a h) (vs x) C.Wd (a.env x) := by
  have := E_numOn C inp p0 a x
  refine ⟨by simpa [Ein] using this.1, ?_⟩
  have hne : vs x ≠ sIN := by intro e; have := congrArg Fin.val e; simp [vs, sIN] at this
  simpa [Ein, Function.update_of_ne hne] using this.2

theorem Ein_numZ (a : DS V) (h : ℕ) : NumOn (Ein C inp p0 a h) sZ C.Wd 0 := by
  have := E_numZ C inp p0 a
  refine ⟨by simpa [Ein] using this.1, ?_⟩
  have hne : sZ ≠ (sIN : Fin (V + 3 + 1)) := by intro e; have := congrArg Fin.val e; simp [sZ, sIN] at this
  simpa [Ein, Function.update_of_ne hne] using this.2

theorem Ein_F (a : DS V) (h : ℕ) : (Ein C inp p0 a h).val rF = 0 := by
  simp only [Ein, WState.setv_val, WState.seth_val]
  rw [Function.update_of_ne (by decide)]; exact E_val_F C inp p0 a
theorem Ein_R (a : DS V) (h : ℕ) : (Ein C inp p0 a h).val rR = 0 := by
  simp only [Ein, WState.setv_val, WState.seth_val]
  rw [Function.update_of_ne (by decide)]; exact E_val_R C inp p0 a

theorem E_wq (a : DS V) (b : DS V) (hb : b = { a with wq := a.wq + 1 }) :
    Ein C inp p0 a (p0 + 4 * a.wq + 4) = E C inp p0 b := by
  rw [E_eq_Ein, hb]
  unfold Ein
  rw [show p0 + 4 * (a.wq + 1) = p0 + 4 * a.wq + 4 by ring]
  refine WState.eq ?_ ?_ ?_ rfl
  · funext i; simp only [WState.setv_sh, WState.seth_sh]
    by_cases hi : i = sIN
    · subst hi; simp
    · have : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp only [Function.update_of_ne hi]; simp [E, shF, this]
  · rfl
  · funext r; simp only [WState.setv_val, WState.seth_val]
    by_cases hr : r = rIP
    · subst hr; simp
    · have : r.val ≠ 6 := fun h => hr (Fin.ext h)
      simp only [Function.update_of_ne hr]; simp [E, valF, this]

end Enc

/-! ## Compiled operations -/

def cOne (x : Fin V) : WMX (V + 3) NR := BinW.one (vs x) sZ rF rR
def cZero (x : Fin V) : WMX (V + 3) NR := BinW.zero (vs x) sZ rF rR

/-- The program of one operation. -/
def compOp : Op V → WMX (V + 3) NR
  | .zero x => cZero x
  | .inc x => BinW.inc (vs x) sZ rF rR
  | .add x y => BinW.add (vs x) (vs y) rF rR
  | .sub x y => BinW.sub (vs x) (vs y) rF rR
  | .copy x y => BinW.copy (vs x) (vs y) rF rR
  | .half x => BinW.half (vs x) rR
  | .shl x => BinW.shl (vs x) sZ rF rR
  | .mul x y z => BinW.mul (vs x) (vs y) (vs z) sZ rF rR rG
  | .dm x y q r => BinW.divmod (vs x) (vs y) (vs q) (vs r) sZ rF rR rK rT
  | .rdC x => .seq (.ifs sCW (cOne x) (cZero x)) (.seq (WMX.fwd sCW) (WMX.inc rCP))
  | .rstC => .whr rCP (.seq (WMX.dec rCP) (WMX.bwd sCW))
  | .rdW x => .seq (WMX.fwd sIN) (.seq (WMX.inc rIP) (.ifs sIN
      (.seq (WMX.fwd sIN) (.seq (WMX.inc rIP) (.seq (WMX.fwd sIN) (.seq (WMX.inc rIP)
        (.seq (.ifs sIN (cOne x) (cZero x)) (.seq (WMX.fwd sIN) (WMX.inc rIP)))))))
      (.seq (WMX.bwd sIN) (.seq (WMX.dec rIP) (cZero x)))))
  | .emit b => .seq (WMX.wr sOUT b) (.seq (WMX.fwd sOUT) (WMX.inc rOP))

/-- The test of a condition into register `F`. -/
def condP : Cnd V → WMX (V + 3) NR
  | .lt x y => BinW.lt (vs x) (vs y) rF rR
  | .eq x y => BinW.eq (vs x) (vs y) rF rR

/-- The loop part of a compiled `while` (entered with the test in `F`). -/
def wpart (c : Cnd V) (S : WMX (V + 3) NR) : WMX (V + 3) NR :=
  .whr rF (.seq (WMX.dec rF) (.seq S (condP c)))

/-- **The compiler.** -/
def comp : St V → WMX (V + 3) NR
  | .op o => compOp o
  | .seq s t => .seq (comp s) (comp t)
  | .ite c s t => .seq (condP c) (.ifr rF (.seq (WMX.dec rF) (comp s)) (comp t))
  | .loop c s => .seq (condP c) (wpart c (comp s))

/-- Steps per language step. -/
def KC (Wd : ℕ) : ℕ := 500 * (Wd + 1) ^ 2

theorem KC_ge (Wd : ℕ) : 41 * Wd + 50 ≤ KC Wd := by unfold KC; nlinarith

/-- The witness layout of the entry tape: bit `j` at `p0 + 4j + 3`, presence at `p0 + 4j + 1`. -/
def WitLayout (inp : List Bool) (p0 : ℕ) (wit : List Bool) : Prop :=
  (∀ j < wit.length, readTapeBit inp (p0 + 4 * j + 1) = true ∧ readTapeBit inp (p0 + 4 * j + 3) = wit.getD j false) ∧
    readTapeBit inp (p0 + 4 * wit.length + 1) = false

theorem writeTapeBit_end (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [writeTapeBit, ih]

section Comp
variable (C : Ctx) (inp : List Bool) (p0 cap : ℕ)

theorem one_zero_ok (σ : WState (V + 3) NR) (x : Fin V) (a0 b : ℕ) (hA : NumOn σ (vs x) C.Wd a0)
    (hZ : NumOn σ sZ C.Wd 0) (hF : σ.val rF = 0) (hR : σ.val rR = 0) (hW : 1 ≤ C.Wd) (hcap : 2 * C.Wd + 1 ≤ cap)
    (bb : Bool) (hb : b = bb.toNat) :
    WXExec cap (if bb then cOne x else cZero x) σ (σ.sets (vs x) (frame (binary C.Wd b))) (41 * C.Wd + 7) := by
  have hFR : rF ≠ rR := by decide
  cases bb
  · subst hb; exact WXExec.mono (BinW.zero_spec cap C.Wd (vs_ne_Z x) hFR σ a0 0 hA hZ hF hR hcap) (by omega)
  · subst hb; exact BinW.one_spec cap C.Wd (vs_ne_Z x) hFR σ a0 0 hA hZ hF hR hW hcap

/-- **One operation.** -/
theorem compOp_ok (hlay : WitLayout inp p0 C.wit) (hW : 1 ≤ C.Wd) (hcw : C.cw.length ≤ C.Wd)
    (hcapW : 2 * C.Wd + 1 ≤ cap) (hcapC : C.cw.length + 1 ≤ cap) (hcapI : p0 + 4 * C.wit.length + 4 ≤ cap)
    {o : Op V} {a b : DS V} (h : OpEx C o a b) (ha : Valid C a) (hout : a.out.length + 1 ≤ cap) :
    WXExec cap (compOp o) (E C inp p0 a) (E C inp p0 b) (KC C.Wd) := by
  have hK := KC_ge C.Wd
  have hKq : 400 * (C.Wd + 1) ^ 2 ≤ KC C.Wd := by unfold KC; nlinarith
  have hFR : rF ≠ rR := by decide
  have nA := E_numOn C inp p0 a
  have nZ := E_numZ C inp p0 a
  cases h with
  | zero x a =>
    exact WXExec.cast cap (BinW.zero_spec cap C.Wd (vs_ne_Z x) hFR _ _ 0 (nA x) nZ (by simp) (by simp) hcapW)
      (E_sets C inp p0 a x 0) (by omega)
  | inc x a hv =>
    exact WXExec.cast cap (BinW.inc_spec cap C.Wd (vs_ne_Z x) hFR _ _ 0 (nA x) nZ (by simp) (by simp) hv hcapW)
      (E_sets C inp p0 a x _) (by omega)
  | add x y a hxy hv =>
    exact WXExec.cast cap (BinW.add_spec cap C.Wd (vs_inj hxy) hFR _ _ _ (nA x) (nA y) (by simp) (by simp) hv hcapW)
      (E_sets C inp p0 a x _) (by omega)
  | sub x y a hxy hv =>
    exact WXExec.cast cap (BinW.sub_spec cap C.Wd (vs_inj hxy) hFR _ _ _ (nA x) (nA y) (by simp) (by simp) hv
      (ha.env_lt x) hcapW) (E_sets C inp p0 a x _) (by omega)
  | copy x y a hxy =>
    exact WXExec.cast cap (BinW.copy_spec cap C.Wd (vs_inj hxy) hFR _ _ _ (nA x) (nA y) (by simp) (by simp) hcapW)
      (E_sets C inp p0 a x _) (by omega)
  | half x a =>
    exact WXExec.cast cap (BinW.half_spec cap C.Wd _ _ (nA x) (by simp) (ha.env_lt x) (by omega))
      (E_sets C inp p0 a x _) (by omega)
  | shl x a hv =>
    exact WXExec.cast cap (BinW.shl_spec cap C.Wd (vs_ne_Z x) hFR _ _ 0 (nA x) nZ (by simp) (by simp) hcapW)
      (E_sets C inp p0 a x _) (by omega)
  | mul x y z a hxy hxz hyz hv =>
    have hm := BinW.mul_spec cap C.Wd (vs_inj hxy) (vs_inj hxz) (vs_ne_Z x) (vs_inj hyz) (vs_ne_Z y) (vs_ne_Z z)
      hFR (by decide : rF ≠ rG) (by decide : rR ≠ rG) (E C inp p0 a) _ _ _ 0 (nA x) (nA y) (nA z) nZ (by simp)
      (by simp) (by simp) hv (ha.env_lt y) hcapW
    refine WXExec.cast cap hm ?_ (le_trans (BinW.mulCost_le _) (by unfold KC; nlinarith))
    rw [E_sets]; exact E_setsZ C inp p0 _
  | dm x y q r a hxy hxq hxr hyq hyr hqr hy h2y =>
    have hd := BinW.divmod_spec cap C.Wd (vs_inj hxq) (vs_inj hxr) (vs_ne_Z x) (vs_inj hyq) (vs_inj hyr)
      (vs_ne_Z y) (vs_inj hqr) (vs_ne_Z q) (vs_ne_Z r) hFR (by decide : rF ≠ rK) (by decide : rR ≠ rK)
      (by decide : rK ≠ rT) (E C inp p0 a) _ _ _ _ 0 (nA x) (nA y) (nA q) (nA r) nZ (by simp) (by simp) (by simp)
      (by simp) (ha.env_lt x) hy h2y hcapW
    refine WXExec.cast cap hd ?_ (le_trans (BinW.divCost_le _) hKq)
    rw [E_sets, E_sets]; exact E_setsZ C inp p0 _
  | rdC x a hc =>
    have hbit : wbit (E C inp p0 a) sCW = C.cw.getD a.cp false := by simp [wbit, readTapeBit]
    have h1 : WXExec cap (.ifs sCW (cOne x) (cZero x)) (E C inp p0 a) (E C inp p0 (a.set x (bitOf C.cw a.cp)))
        (41 * C.Wd + 8) := by
      rw [← E_sets]
      cases hcb : C.cw.getD a.cp false
      · have := one_zero_ok C cap (E C inp p0 a) x (a.env x) (bitOf C.cw a.cp) (nA x) nZ (by simp) (by simp) hW hcapW
          false (by rw [bitOf, hcb])
        exact WXExec.ifsF (by rw [hbit, hcb]) this
      · have := one_zero_ok C cap (E C inp p0 a) x (a.env x) (bitOf C.cw a.cp) (nA x) nZ (by simp) (by simp) hW hcapW
          true (by rw [bitOf, hcb])
        exact WXExec.ifsT (by rw [hbit, hcb]) this
    set a1 := a.set x (bitOf C.cw a.cp)
    have h2 := WXExec.fwd cap sCW (E C inp p0 a1)
    have h3 := WXExec.inc cap rCP ((E C inp p0 a1).seth sCW ((E C inp p0 a1).sh sCW + 1))
      (by simp [a1]; omega)
    simp only [E_sh_CW, WState.seth_val, E_val_CP] at h2 h3
    have e := E_cp C inp p0 a1
    rw [e] at h3
    exact WXExec.seq' cap h1 (WXExec.seq' cap h2 h3 le_rfl) (by omega)
  | rstC a =>
    have key : ∀ j : ℕ, ∀ a' : DS V, a'.cp = j → j ≤ cap →
        WXExec cap (.whr rCP (.seq (WMX.dec rCP) (WMX.bwd sCW))) (E C inp p0 a') (E C inp p0 { a' with cp := 0 })
          (5 * j + 1) := by
      intro j
      induction j with
      | zero =>
        intro a' h0 _
        have e : ({ a' with cp := 0 } : DS V) = a' := by cases a'; simp_all
        rw [e]; exact WXExec.whrF (by simp [h0])
      | succ j ih =>
        intro a' hj hjc
        have h1 : WXExec cap (WMX.dec rCP) (E C inp p0 a') ((E C inp p0 a').setv rCP j) 1 := by
          have := WXExec.dec cap rCP (E C inp p0 a') (by simp; omega)
          simpa [hj] using this
        have h2 := WXExec.bwd cap sCW ((E C inp p0 a').setv rCP j)
        simp only [WState.setv_sh, E_sh_CW, hj] at h2
        rw [show j + 1 - 1 = j by omega, E_cp_back C inp p0 a' j] at h2
        have h3 := ih { a' with cp := j } rfl (by omega)
        have e : ({ ({ a' with cp := j } : DS V) with cp := 0 } : DS V) = { a' with cp := 0 } := rfl
        rw [e] at h3
        exact WXExec.mono (WXExec.whrT (by simp [hj]) (WXExec.seq h1 h2) h3) (by omega)
    exact WXExec.mono (key a.cp a rfl (by have := ha.cp_le; omega)) (by have := ha.cp_le; nlinarith)
  | rdW x a =>
    rw [E_eq_Ein C inp p0 a]
    set h := p0 + 4 * a.wq with hh
    have hwq := ha.wq_le
    have s1 := WXExec.fwd cap sIN (Ein C inp p0 a h)
    have s2 := WXExec.inc cap rIP ((Ein C inp p0 a h).seth sIN ((Ein C inp p0 a h).sh sIN + 1))
      (by simp [Ein_val] <;> omega)
    simp only [WState.seth_val, Ein_val] at s2
    rw [Ein_fwd] at s2
    by_cases hin : a.wq < C.wit.length
    · obtain ⟨hp, hd⟩ := hlay.1 a.wq hin
      have t1 := WXExec.fwd cap sIN (Ein C inp p0 a (h + 1))
      have t2 := WXExec.inc cap rIP ((Ein C inp p0 a (h + 1)).seth sIN ((Ein C inp p0 a (h + 1)).sh sIN + 1))
        (by simp [Ein_val] <;> omega)
      simp only [WState.seth_val, Ein_val] at t2
      rw [Ein_fwd] at t2
      have t3 := WXExec.fwd cap sIN (Ein C inp p0 a (h + 1 + 1))
      have t4 := WXExec.inc cap rIP ((Ein C inp p0 a (h + 1 + 1)).seth sIN
        ((Ein C inp p0 a (h + 1 + 1)).sh sIN + 1)) (by simp [Ein_val] <;> omega)
      simp only [WState.seth_val, Ein_val] at t4
      rw [Ein_fwd] at t4
      set a1 := a.set x (bitOf C.wit a.wq)
      have hbit : wbit (Ein C inp p0 a (h + 1 + 1 + 1)) sIN = C.wit.getD a.wq false := by
        simp only [wbit, Ein_st, Ein_sh]; rw [← hd]
      have t5 : WXExec cap (.ifs sIN (cOne x) (cZero x)) (Ein C inp p0 a (h + 1 + 1 + 1))
          (Ein C inp p0 a1 (h + 1 + 1 + 1)) (41 * C.Wd + 8) := by
        rw [← Ein_sets]
        have nA' := Ein_numOn C inp p0 a (h + 1 + 1 + 1) x
        have nZ' := Ein_numZ C inp p0 a (h + 1 + 1 + 1)
        cases hcb : C.wit.getD a.wq false
        · exact WXExec.ifsF (by rw [hbit, hcb]) (one_zero_ok C cap _ x _ _ nA' nZ' (Ein_F ..) (Ein_R ..) hW hcapW
            false (by rw [bitOf, hcb]))
        · exact WXExec.ifsT (by rw [hbit, hcb]) (one_zero_ok C cap _ x _ _ nA' nZ' (Ein_F ..) (Ein_R ..) hW hcapW
            true (by rw [bitOf, hcb]))
      have t6 := WXExec.fwd cap sIN (Ein C inp p0 a1 (h + 1 + 1 + 1))
      have t7 := WXExec.inc cap rIP ((Ein C inp p0 a1 (h + 1 + 1 + 1)).seth sIN
        ((Ein C inp p0 a1 (h + 1 + 1 + 1)).sh sIN + 1)) (by simp [Ein_val] <;> omega)
      simp only [WState.seth_val, Ein_val] at t7
      rw [Ein_fwd, show h + 1 + 1 + 1 + 1 = p0 + 4 * a1.wq + 4 by simp only [a1, hh, DS.set_wq],
        E_wq C inp p0 a1 _ rfl] at t7
      have hpres : wbit (Ein C inp p0 a (h + 1)) sIN = true := by
        simp only [wbit, Ein_st, Ein_sh]; rw [← hp]
      have e : ({ a1 with wq := a1.wq + 1 } : DS V) =
          { a.set x (bitOf C.wit a.wq) with wq := if a.wq < C.wit.length then a.wq + 1 else a.wq } := by
        simp [a1, hin]
      rw [e] at t7
      refine WXExec.seq' cap s1 (WXExec.seq' cap s2 (WXExec.ifsT hpres
        (WXExec.seq' cap t1 (WXExec.seq' cap t2 (WXExec.seq' cap t3 (WXExec.seq' cap t4
          (WXExec.seq' cap t5 (WXExec.seq' cap t6 t7 le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)) le_rfl) ?_
      omega
    · have hend : a.wq = C.wit.length := by omega
      have hpres : wbit (Ein C inp p0 a (h + 1)) sIN = false := by
        simp only [wbit, Ein_st, Ein_sh]; rw [hh, hend]; exact hlay.2
      have t1 := WXExec.bwd cap sIN (Ein C inp p0 a (h + 1))
      have t2 := WXExec.dec cap rIP ((Ein C inp p0 a (h + 1)).seth sIN ((Ein C inp p0 a (h + 1)).sh sIN - 1))
        (by simp [Ein_val] <;> omega)
      simp only [WState.seth_val, Ein_val, show h + 1 - 1 = h by omega] at t2
      rw [Ein_bwd] at t2
      have t3 : WXExec cap (cZero x) (Ein C inp p0 a h) (Ein C inp p0 (a.set x (bitOf C.wit a.wq)) h)
          (41 * C.Wd + 7) := by
        have hb0 : bitOf C.wit a.wq = 0 := by
          simp [bitOf, List.getD_eq_getElem?_getD, hend]
        rw [← Ein_sets, hb0]
        exact WXExec.mono (BinW.zero_spec cap C.Wd (vs_ne_Z x) hFR _ _ 0 (Ein_numOn C inp p0 a h x)
          (Ein_numZ C inp p0 a h) (Ein_F ..) (Ein_R ..) hcapW) (by omega)
      have e : Ein C inp p0 (a.set x (bitOf C.wit a.wq)) h =
          E C inp p0 { a.set x (bitOf C.wit a.wq) with wq := if a.wq < C.wit.length then a.wq + 1 else a.wq } := by
        rw [if_neg hin, E_eq_Ein]; rfl
      rw [e] at t3
      refine WXExec.seq' cap s1 (WXExec.seq' cap s2 (WXExec.ifsF hpres
        (WXExec.seq' cap t1 (WXExec.seq' cap t2 t3 le_rfl) le_rfl)) le_rfl) ?_
      omega
  | emit bb a =>
    have h1 := WXExec.wr cap sOUT bb (E C inp p0 a)
    simp only [E_st_OUT, E_sh_OUT, writeTapeBit_end] at h1
    have h2 := WXExec.fwd cap sOUT ((E C inp p0 a).sets sOUT (a.out ++ [bb]))
    simp only [WState.sets_sh, E_sh_OUT] at h2
    have h3 := WXExec.inc cap rOP (((E C inp p0 a).sets sOUT (a.out ++ [bb])).seth sOUT (a.out.length + 1))
      (by simp; omega)
    simp only [WState.seth_val, WState.sets_val, E_val_OP] at h3
    rw [E_out] at h3
    exact WXExec.seq' cap h1 (WXExec.seq' cap h2 h3 le_rfl) (by omega)

theorem condP_ok {c : Cnd V} (hc : c.wf) (a : DS V) (ha : Valid C a) (hcapW : 2 * C.Wd + 1 ≤ cap) :
    WXExec cap (condP c) (E C inp p0 a) ((E C inp p0 a).setv rF (c.eval a).toNat) (41 * C.Wd + 7) := by
  have hFR : rF ≠ rR := by decide
  cases c with
  | lt x y =>
    exact WXExec.mono (BinW.lt_spec cap C.Wd (vs_inj hc) hFR _ _ _ (E_numOn C inp p0 a x) (E_numOn C inp p0 a y)
      (by simp) (by simp) (ha.env_lt x) (ha.env_lt y) hcapW) (by omega)
  | eq x y =>
    exact BinW.eq_spec cap C.Wd (vs_inj hc) hFR _ _ _ (E_numOn C inp p0 a x) (E_numOn C inp p0 a y)
      (by simp) (by simp) (ha.env_lt x) (ha.env_lt y) hcapW

/-- **The compiler is correct**: every derivation is a run of the compiled program, `KC Wd` steps per language
step. -/
theorem comp_ok (hlay : WitLayout inp p0 C.wit) (hW : 1 ≤ C.Wd) (hcw : C.cw.length ≤ C.Wd)
    (hcapW : 2 * C.Wd + 1 ≤ cap) (hcapC : C.cw.length + 1 ≤ cap) (hcapI : p0 + 4 * C.wit.length + 4 ≤ cap)
    {s : St V} {a b : DS V} {n : ℕ} (h : Ex C s a b n) (ha : Valid C a) (hout : a.out.length + n ≤ cap) :
    WXExec cap (comp s) (E C inp p0 a) (E C inp p0 b) (n * KC C.Wd) ∧
      ∀ c t, s = .loop c t →
        WXExec cap (wpart c (comp t)) ((E C inp p0 a).setv rF (c.eval a).toNat) (E C inp p0 b) ((n - 1) * KC C.Wd) := by
  have hK := KC_ge C.Wd
  induction h with
  | op h =>
    refine ⟨?_, fun c t e => by cases e⟩
    exact WXExec.mono (compOp_ok C inp p0 cap hlay hW hcw hcapW hcapC hcapI h ha (by omega))
      (Nat.le_of_eq (one_mul _).symm)
  | @seq s t a b d n k h1 h2 ih1 ih2 =>
    refine ⟨?_, fun c t e => by cases e⟩
    have hb := h1.valid hW ha
    have hl := h1.out_len
    have r1 := (ih1 ha (by omega)).1
    have r2 := (ih2 hb (by omega)).1
    exact WXExec.seq' cap r1 r2 (by nlinarith)
  | @iteT c s t a b n hc he h1 ih =>
    refine ⟨?_, fun c t e => by cases e⟩
    have r1 := (ih ha (by omega)).1
    have t0 := condP_ok C inp p0 cap hc a ha hcapW
    rw [he] at t0
    have d1 := WXExec.dec cap rF ((E C inp p0 a).setv rF (true.toNat)) (by simp; omega)
    simp only [WState.setv_val, Function.update_self, Bool.toNat_true, Nat.sub_self, wsetv_setv] at d1
    rw [E_setvF] at d1
    have hne : ((E C inp p0 a).setv rF (true.toNat)).val rF ≠ 0 := by simp
    exact WXExec.seq' cap t0 (WXExec.ifrT hne (WXExec.seq' cap d1 r1 le_rfl)) (by nlinarith)
  | @iteF c s t a b n hc he h1 ih =>
    refine ⟨?_, fun c t e => by cases e⟩
    have r1 := (ih ha (by omega)).1
    have t0 := condP_ok C inp p0 cap hc a ha hcapW
    rw [he, Bool.toNat_false, E_setvF] at t0
    exact WXExec.seq' cap t0 (WXExec.ifrF (by simp) r1) (by nlinarith)
  | @loopF c s a hc he =>
    have t0 := condP_ok C inp p0 cap hc a ha hcapW
    rw [he, Bool.toNat_false, E_setvF] at t0
    have w0 : WXExec cap (wpart c (comp s)) (E C inp p0 a) (E C inp p0 a) 1 :=
      WXExec.whrF (r := rF) (E_val_F C inp p0 a)
    refine ⟨WXExec.seq' cap t0 w0 (by omega), ?_⟩
    intro c' t' e
    cases e
    rw [he, Bool.toNat_false, E_setvF]
    exact WXExec.mono w0 (by simp; omega)
  | @loopT c s a b d n k hc he h1 h2 ih1 ih2 =>
    have hb := h1.valid hW ha
    have hl := h1.out_len
    have hk2 : 1 ≤ k := h2.pos
    have r1 := (ih1 ha (by omega)).1
    have r2 := (ih2 hb (by omega)).2 c s rfl
    have tb := condP_ok C inp p0 cap hc b hb hcapW
    have d1 := WXExec.dec cap rF ((E C inp p0 a).setv rF (true.toNat)) (by simp; omega)
    simp only [WState.setv_val, Function.update_self, Bool.toNat_true, Nat.sub_self, wsetv_setv] at d1
    rw [E_setvF] at d1
    have hne : ((E C inp p0 a).setv rF (true.toNat)).val rF ≠ 0 := by simp
    have w : WXExec cap (wpart c (comp s)) ((E C inp p0 a).setv rF (true.toNat)) (E C inp p0 d)
        ((n + k + 2 - 1) * KC C.Wd) := by
      refine WXExec.mono (WXExec.whrT hne (WXExec.seq' cap d1 (WXExec.seq' cap r1 tb le_rfl) le_rfl) r2) ?_
      have e1 : n + k + 2 - 1 = n + k + 1 := by omega
      rw [e1]
      have e2 : (k - 1) * KC C.Wd + KC C.Wd = k * KC C.Wd := by
        rw [← Nat.succ_mul]; congr 1; omega
      nlinarith
    refine ⟨?_, ?_⟩
    · have t0 := condP_ok C inp p0 cap hc a ha hcapW
      rw [he] at t0
      refine WXExec.seq' cap t0 w ?_
      have e1 : n + k + 2 - 1 = n + k + 1 := by omega
      rw [e1]; nlinarith
    · intro c' t' e
      cases e
      rw [he]; exact w
  | @mono s a b n m h1 hnm ih =>
    obtain ⟨r1, r2⟩ := ih ha (by omega)
    refine ⟨WXExec.mono r1 (Nat.mul_le_mul_right _ hnm), fun c t e => WXExec.mono (r2 c t e) ?_⟩
    exact Nat.mul_le_mul_right _ (by omega)

end Comp

end NearCubicGates.Close.Dispatch
