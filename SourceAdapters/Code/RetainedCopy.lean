import SourceAdapters.Code.Composition
import Proof.Gates.Codec.Unframe
import Proof.Gates.CheckedPCPP.WMXReady

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid copies of existing frames used to retain
an input beside a computed framed output. Every copy and head reset executes. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.Retained

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec
open NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

def copyScript : WMX 2 1 := .wm (copyFrameW 0 2 0)

def pairScript : WMX 2 1 := .seq (.wm (copyFrameW 0 2 0)) (.wm (copyFrameW 1 2 0))

def pairStart (x : List Bool) (y : List Bool) : WState 2 1 :=
  ⟨fun _ => 0, ![frame x, y, []], fun _ => 0, false⟩

def bank (x y : List Bool) : Fin 6 → List Bool := ![frame x, [], y, [], [], []]

theorem start_bank (x y : List Bool) :
    (fun i => Fin.addCases (coldBank (pairStart x y)) (fun _ : Fin 1 => []) i) = bank x y := by
  funext i
  fin_cases i <;> rfl

noncomputable def copyMachine := Rewind.machine copyScript.compile

noncomputable def pairMachine := Rewind.machine pairScript.compile

theorem copy_ready (x : List Bool) :
    ∃ out, ClockJoin.ReadyRun copyMachine (44 * x.length + 20) (bank x []) out ∧
      out 0 = frame x ∧ out 3 = frame x := by
  let σ := pairStart x []
  have e := copyFrameW_spec (2 * x.length + 1) (0 : Fin 3) 2 (by decide)
    (0 : Fin 1) x [] σ (by simp [σ, pairStart]) rfl rfl (by simp [σ, pairStart])
  obtain ⟨out, hrun, hout⟩ := NearCubicGates.Close.CheckedPCPP.WXExec.readyRewound
    (WXExec.wm e) (fun _ => rfl) (fun _ => rfl) rfl
  refine ⟨out, ?_, ?_, ?_⟩
  · change ClockJoin.ReadyRun copyMachine _ (fun i => Fin.addCases (coldBank (pairStart x [])) (fun _ => []) i) out at hrun
    rw [start_bank] at hrun
    convert hrun using 1
    omega
  · simpa [sTape, σ, pairStart, appendO] using hout 0
  · simpa [sTape, σ, pairStart, appendO] using hout 2

theorem pair_ready (x y : List Bool) :
    ∃ out, ClockJoin.ReadyRun pairMachine (44 * x.length + 44 * y.length + 40)
      (bank x (frame y)) out ∧ out 3 = frame x ++ frame y := by
  let cap := 2 * x.length + 2 * y.length + 2
  let σ := pairStart x (frame y)
  let σ1 := (appendO σ 2 0 (frame x)).seth 0 (2 * x.length)
  have e1 := copyFrameW_spec cap (0 : Fin 3) 2 (by decide) (0 : Fin 1) x [] σ
    (by simp [σ, pairStart]) rfl rfl (by simp [σ, pairStart, cap]; omega)
  have e2 := copyFrameW_spec cap (1 : Fin 3) 2 (by decide) (0 : Fin 1) y [] σ1
    (by simp [σ1, σ, pairStart, appendO])
    (by simp [σ1, σ, pairStart, appendO])
    (by simp [σ1, σ, pairStart, appendO])
    (by simp [σ1, σ, pairStart, appendO, cap]; omega)
  obtain ⟨out, hrun, hout⟩ := NearCubicGates.Close.CheckedPCPP.WXExec.readyRewound
    (WXExec.seq (WXExec.wm e1) (WXExec.wm e2)) (fun _ => rfl) (fun _ => rfl) rfl
  refine ⟨out, ?_, ?_⟩
  · change ClockJoin.ReadyRun pairMachine _ (fun i => Fin.addCases (coldBank (pairStart x (frame y))) (fun _ => []) i) out at hrun
    rw [start_bank] at hrun
    convert hrun using 1
    omega
  · simpa [sTape, σ1, σ, pairStart, appendO] using hout 2

end NearCubicGates.Adapters.Code.Retained
