import SourceAdapters.Code.RetainedCopy
import Proof.Gates.CheckedPCPP.Glue
import Proof.Foundations.OrdinaryFramedSource

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid separation of two existing frames into disjoint tapes. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.PairTransform

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

def splitScript : WMX 2 1 := .wm (Glue.headerW 0 1 2 0)

def splitStart (x y : List Bool) : WState 2 1 :=
  ⟨fun _ => 0, ![frame x ++ frame y, [], []], fun _ => 0, false⟩

noncomputable def splitMachine := Rewind.machine splitScript.compile

theorem split_bank (x y : List Bool) :
    (fun i => Fin.addCases (coldBank (splitStart x y)) (fun _ : Fin 1 => []) i) =
      SourceHandoff.sourceTapes (frame x ++ frame y) := by
  funext i
  fin_cases i <;> rfl

theorem split_ready (x y : List Bool) :
    ∃ out, ClockJoin.ReadyRun splitMachine (44 * x.length + 44 * y.length + 62)
      (SourceHandoff.sourceTapes (frame x ++ frame y)) out ∧
      out 2 = frame x ∧ out 3 = frame y := by
  obtain ⟨τ, e, hx, hy, _, _⟩ := Glue.headerW_spec (2 * x.length + 2 * y.length + 2)
    (0 : Fin 3) 1 2 (by decide) (0 : Fin 1) x y [] (splitStart x y)
    (by simp [splitStart]) rfl rfl rfl rfl rfl (by simp [splitStart])
  obtain ⟨out, hrun, hout⟩ := NearCubicGates.Close.CheckedPCPP.WXExec.readyRewound
    (WXExec.wm e) (fun _ => rfl) (fun _ => rfl) rfl
  refine ⟨out, ?_, ?_, ?_⟩
  · change ClockJoin.ReadyRun splitMachine _
      (fun i => Fin.addCases (coldBank (splitStart x y)) (fun _ => []) i) out at hrun
    rw [split_bank] at hrun
    convert hrun using 1
    omega
  · exact (hout 1).trans hx
  · exact (hout 2).trans hy

end NearCubicGates.Adapters.Code.PairTransform
