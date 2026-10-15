import Proof.Gates.CheckedPCPP.Glue
import Proof.Gates.CheckedPCPP.SupW
import Proof.Gates.CheckedPCPP.EncSetup
import Proof.Gates.CheckedPCPP.SubstitutedPoly
import Proof.Gates.CheckedPCPP.Word
import Proof.Gates.CheckedPCPP.PCPPWord

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP.Comp

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget

/-! ## Streams -/

section Streams
variable (t2 te t4 t5 : ℕ)

/-- The number of streams minus one. -/
def NS : ℕ := 11 + t2 + te + t4 + t5

def HS : Fin (NS t2 te t4 t5 + 1) := ⟨0, by unfold NS; omega⟩
def DS : Fin (NS t2 te t4 t5 + 1) := ⟨1, by unfold NS; omega⟩
def QS : Fin (NS t2 te t4 t5 + 1) := ⟨2, by unfold NS; omega⟩
def DD2 : Fin (NS t2 te t4 t5 + 1) := ⟨3, by unfold NS; omega⟩
def MAT : Fin (NS t2 te t4 t5 + 1) := ⟨4, by unfold NS; omega⟩
def TT : Fin (NS t2 te t4 t5 + 1) := ⟨5, by unfold NS; omega⟩
def LG : Fin (NS t2 te t4 t5 + 1) := ⟨6, by unfold NS; omega⟩
def SN : Fin (NS t2 te t4 t5 + 1) := ⟨7, by unfold NS; omega⟩
def SC : Fin (NS t2 te t4 t5 + 1) := ⟨8, by unfold NS; omega⟩
def PO : Fin (NS t2 te t4 t5 + 1) := ⟨9, by unfold NS; omega⟩
def RO : Fin (NS t2 te t4 t5 + 1) := ⟨10, by unfold NS; omega⟩
def SUP : Fin (NS t2 te t4 t5 + 1) := ⟨11, by unfold NS; omega⟩

def b2 (j : Fin t2) : Fin (NS t2 te t4 t5 + 1) := ⟨12 + j.val, by have := j.isLt; unfold NS; omega⟩
def bE (j : Fin te) : Fin (NS t2 te t4 t5 + 1) := ⟨12 + t2 + j.val, by have := j.isLt; unfold NS; omega⟩
def b4 (j : Fin t4) : Fin (NS t2 te t4 t5 + 1) := ⟨12 + t2 + te + j.val, by have := j.isLt; unfold NS; omega⟩
def b5 (j : Fin t5) : Fin (NS t2 te t4 t5 + 1) :=
  ⟨12 + t2 + te + t4 + j.val, by have := j.isLt; unfold NS; omega⟩

@[simp] theorem HS_val : (HS t2 te t4 t5).val = 0 := rfl
@[simp] theorem DS_val : (DS t2 te t4 t5).val = 1 := rfl
@[simp] theorem QS_val : (QS t2 te t4 t5).val = 2 := rfl
@[simp] theorem DD2_val : (DD2 t2 te t4 t5).val = 3 := rfl
@[simp] theorem MAT_val : (MAT t2 te t4 t5).val = 4 := rfl
@[simp] theorem TT_val : (TT t2 te t4 t5).val = 5 := rfl
@[simp] theorem LG_val : (LG t2 te t4 t5).val = 6 := rfl
@[simp] theorem SN_val : (SN t2 te t4 t5).val = 7 := rfl
@[simp] theorem SC_val : (SC t2 te t4 t5).val = 8 := rfl
@[simp] theorem PO_val : (PO t2 te t4 t5).val = 9 := rfl
@[simp] theorem RO_val : (RO t2 te t4 t5).val = 10 := rfl
@[simp] theorem SUP_val : (SUP t2 te t4 t5).val = 11 := rfl
@[simp] theorem b2_val (j : Fin t2) : (b2 t2 te t4 t5 j).val = 12 + j.val := rfl
@[simp] theorem bE_val (j : Fin te) : (bE t2 te t4 t5 j).val = 12 + t2 + j.val := rfl
@[simp] theorem b4_val (j : Fin t4) : (b4 t2 te t4 t5 j).val = 12 + t2 + te + j.val := rfl
@[simp] theorem b5_val (j : Fin t5) : (b5 t2 te t4 t5 j).val = 12 + t2 + te + t4 + j.val := rfl

theorem b2_inj : Function.Injective (b2 t2 te t4 t5) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp [b2] at this; omega)
theorem bE_inj : Function.Injective (bE t2 te t4 t5) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp [bE] at this; omega)
theorem b4_inj : Function.Injective (b4 t2 te t4 t5) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp [b4] at this; omega)
theorem b5_inj : Function.Injective (b5 t2 te t4 t5) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp [b5] at this; omega)

end Streams

/-! ## Registers -/

/-- The support-matrix registers. -/
def encR : Fin 14 ↪ Fin 64 := ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- The checked-descriptor registers' values (`16 ↦ 9 = encR 9`, the code length). -/
def descHf (i : Fin 19) : Fin 64 := if i.val = 16 then ⟨9, by omega⟩ else ⟨14 + i.val, by omega⟩

theorem descHf_inj : Function.Injective descHf := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have hv := congrArg Fin.val h
  unfold descHf at hv
  apply Fin.ext
  by_cases h1 : a.val = 16 <;> by_cases h2 : b.val = 16 <;> simp only [h1, h2, if_true, if_false] at hv <;> omega

/-- The checked-descriptor registers (`descH 16 = encR 9`, the code length). -/
def descH : Fin 19 ↪ Fin 64 := ⟨descHf, descHf_inj⟩

/-- The supports registers. -/
def supG : Fin 18 ↪ Fin 64 :=
  ⟨fun i => ⟨33 + i.val, by omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩

def rP : Fin 64 := 51
def rP2 : Fin 64 := 52
def rX : Fin 64 := 53
def rY : Fin 64 := 54
def rZ : Fin 64 := 55
def rA2 : Fin 64 := 56
def rT : Fin 64 := 57
def rC2 : Fin 64 := 58
def rCNT : Fin 64 := 59
def rf : Fin 64 := 60
def rc : Fin 64 := 61
def rp : Fin 64 := 62
def rt : Fin 64 := 63

@[simp] theorem rP_val : rP.val = 51 := rfl
@[simp] theorem rP2_val : rP2.val = 52 := rfl
@[simp] theorem rX_val : rX.val = 53 := rfl
@[simp] theorem rY_val : rY.val = 54 := rfl
@[simp] theorem rZ_val : rZ.val = 55 := rfl
@[simp] theorem rA2_val : rA2.val = 56 := rfl
@[simp] theorem rT_val : rT.val = 57 := rfl
@[simp] theorem rC2_val : rC2.val = 58 := rfl
@[simp] theorem rCNT_val : rCNT.val = 59 := rfl
@[simp] theorem rf_val : rf.val = 60 := rfl
@[simp] theorem rc_val : rc.val = 61 := rfl
@[simp] theorem rp_val : rp.val = 62 := rfl
@[simp] theorem rt_val : rt.val = 63 := rfl

theorem fin_ne {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-- Distinct streams of the layout. -/
macro "dst" : tactic => `(tactic| (apply fin_ne; first
  | (simp only [HS_val, DS_val, QS_val, DD2_val, MAT_val, TT_val, LG_val, SN_val, SC_val, PO_val, RO_val, SUP_val,
      b2_val, bE_val, b4_val, b5_val]; done)
  | (simp only [HS_val, DS_val, QS_val, DD2_val, MAT_val, TT_val, LG_val, SN_val, SC_val, PO_val, RO_val, SUP_val,
      b2_val, bE_val, b4_val, b5_val]; omega)))

@[simp] theorem encR_val (i : Fin 14) : (encR i).val = i.val := rfl
@[simp] theorem descH_val (i : Fin 19) : (descH i).val = if i.val = 16 then 9 else 14 + i.val := by
  simp only [descH, Function.Embedding.coeFn_mk, descHf]; split <;> rfl
@[simp] theorem supG_val (i : Fin 18) : (supG i).val = 33 + i.val := rfl

/-- Distinct registers of the layout. -/
macro "rdst" : tactic => `(tactic| (apply fin_ne; first
  | (simp only [encR_val, descH_val, supG_val, rP_val, rP2_val, rX_val, rY_val, rZ_val, rA2_val, rT_val, rC2_val,
      rCNT_val, rf_val, rc_val, rp_val, rt_val, Fin.val_ofNat]; done)
  | (simp only [encR_val, descH_val, supG_val, rP_val, rP2_val, rX_val, rY_val, rZ_val, rA2_val, rT_val, rC2_val,
      rCNT_val, rf_val, rc_val, rp_val, rt_val, Fin.val_ofNat]; omega)
  | (simp only [encR_val, descH_val, supG_val, rP_val, rP2_val, rX_val, rY_val, rZ_val, rA2_val, rT_val, rC2_val,
      rCNT_val, rf_val, rc_val, rp_val, rt_val, Fin.val_ofNat]; split_ifs <;> omega)
  | decide))

/-! ## The program -/

section Program
variable {t2 s2 : ℕ} (M2 : Machine t2 s2) (in2 out2 : Fin t2) (E : LinearCodeFamily) {bud : MessageRequest → ℕ}
  (wf : WordFunction MessageRequest messageWord (fun m => FramedSim.pairs (List.ofFn (E.enc m.1 m.2.val))) bud)
  {t4 s4 : ℕ} (M4 : Machine t4 s4) (in4 out4 : Fin t4) {t5 s5 : ℕ} (M5 : Machine t5 s5) (in5 out5 : Fin t5)
  (Cb eb : ℕ)

noncomputable def phaseA : WMX (NS t2 wf.program.tapeCount t4 t5) 64 :=
  let n2 := wf.program.tapeCount
  .seq (.wm (FrameIn.frameInW (HS t2 n2 t4 t5) (DS t2 n2 t4 t5) (b2 t2 n2 t4 t5 in2) (ChecksW.Rw (DescW.Gof descH))))
  (.seq (.mach M2 (b2 t2 n2 t4 t5))
  (.seq (.wm (Glue.copyFrameW (b2 t2 n2 t4 t5 out2) (DD2 t2 n2 t4 t5) rP))
  (.seq (.wm (Glue.readQW (DD2 t2 n2 t4 t5) (QS t2 n2 t4 t5) (ChecksW.Rw (DescW.Gof descH)) rP2 rT (encR 0) rf rc rp
    rt))
  (.seq (EncSetup.boundW (encR 0) rX rY rZ rA2 rT (encR 11) Cb eb)
  (.seq (EncSetup.fillW (TT t2 n2 t4 t5) (LG t2 n2 t4 t5) (encR 11) rC2 rCNT rT)
    (encCols E wf (bE t2 n2 t4 t5) (MAT t2 n2 t4 t5) (TT t2 n2 t4 t5) (LG t2 n2 t4 t5) encR))))))

noncomputable def phaseB : WMX (NS t2 wf.program.tapeCount t4 t5) 64 :=
  let n2 := wf.program.tapeCount
  .seq (DescW.descW descH (DD2 t2 n2 t4 t5) (SN t2 n2 t4 t5) (SC t2 n2 t4 t5) (b4 t2 n2 t4 t5 in4) (MAT t2 n2 t4 t5))
  (.seq (.wm (WM.rewind (b4 t2 n2 t4 t5 in4) (descH 7)))
  (.seq (.mach M4 (b4 t2 n2 t4 t5))
  (.seq (.wm (Glue.copyFrameW (b4 t2 n2 t4 t5 out4) (b5 t2 n2 t4 t5 in5) rP))
  (.seq (.mach M5 (b5 t2 n2 t4 t5))
    (.wm (Glue.headerW (b5 t2 n2 t4 t5 out5) (PO t2 n2 t4 t5) (RO t2 n2 t4 t5) rP))))))

/-- Phases 14–18: rewind the matrix, the supports. -/
noncomputable def phaseC : WMX (NS t2 wf.program.tapeCount t4 t5) 64 :=
  let n2 := wf.program.tapeCount
  .seq (mulR (descH 9) rA2 (descH 16) rP2 rT)
  (.seq (.wm (WM.rewind (MAT t2 n2 t4 t5) rP2))
  (.seq (addR (descH 9) (supG 9) rT)
  (.seq (addR (descH 16) (supG 16) rT)
    (SupW.supW supG (SUP t2 n2 t4 t5) (MAT t2 n2 t4 t5)))))

/-- **The composite.** -/
noncomputable def compW : WMX (NS t2 wf.program.tapeCount t4 t5) 64 :=
  .seq (phaseA M2 in2 out2 E wf (t4 := t4) (t5 := t5) Cb eb)
    (.seq (phaseB (t2 := t2) E wf M4 in4 out4 M5 in5 out5) (phaseC (t2 := t2) (t4 := t4) (t5 := t5) E wf))

end Program

end NearCubicGates.Close.CheckedPCPP.Comp
