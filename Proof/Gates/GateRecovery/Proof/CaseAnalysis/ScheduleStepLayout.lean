import Proof.Gates.GateRecovery.Bundle
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleReusable
import Proof.Amplification.RecoveryScratchErase

namespace GR

/-! Fixed physical bank for the canonical schedule iteration. Only the
index, input length, retained best, true erase driver and reset log survive
the common workspace sweep. No prepared field is a free machine input. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Step
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def workTapes (sources : GateEightSources) (k D : Nat) := Test.tapes sources k D+3
def tapes (sources : GateEightSources) (k D : Nat) := workTapes sources k D+5
def work (sources : GateEightSources) (k D : Nat) (i : Fin (workTapes sources k D)) : Fin (tapes sources k D) :=
  i.castAdd 5
def port (sources : GateEightSources) (k D : Nat) (i : Fin 5) : Fin (tapes sources k D) :=
  i.natAdd (workTapes sources k D)
def testSlots (sources : GateEightSources) (k D : Nat) (i : Fin (Test.tapes sources k D)) : Fin (tapes sources k D) :=
  work sources k D (i.castAdd 3)
def copyLog (sources : GateEightSources) (k D : Nat) (i : Fin 3) : Fin (tapes sources k D) :=
  work sources k D (i.natAdd (Test.tapes sources k D))
def indexSlots (sources : GateEightSources) (k D : Nat) : Fin 3→Fin (tapes sources k D) :=
  ![port sources k D 0,testSlots sources k D (Test.old sources k D (Candidate.powerSlots sources k D 0)),copyLog sources k D 0]
def lengthSlots (sources : GateEightSources) (k D : Nat) : Fin 3→Fin (tapes sources k D) :=
  ![port sources k D 1,testSlots sources k D (Test.extra sources k D 0),copyLog sources k D 1]
def bestSlots (sources : GateEightSources) (k D : Nat) : Fin 3→Fin (tapes sources k D) :=
  ![testSlots sources k D (Test.old sources k D (Candidate.powerSlots sources k D 13)),
    port sources k D 2,copyLog sources k D 2]
def eraseBestSlots (sources : GateEightSources) (k D : Nat) : Fin 3→Fin (tapes sources k D) :=
  ![port sources k D 2,port sources k D 3,port sources k D 4]
def incrementSlots (sources : GateEightSources) (k D : Nat) : Fin 1→Fin (tapes sources k D) :=
  fun _=>port sources k D 0
def eraseSlots (sources : GateEightSources) (k D : Nat) (i : Fin (workTapes sources k D+2)) : Fin (tapes sources k D) :=
  ⟨if i.val<workTapes sources k D then i.val else i.val+3,by
    have:=i.isLt;dsimp [tapes];split_ifs <;> omega⟩
theorem work_injective (sources : GateEightSources) (k D : Nat) : Function.Injective (work sources k D) := by
  intro a b h;exact Fin.ext (congrArg (fun i : Fin (tapes sources k D)=>i.val) h)
theorem test_injective (sources : GateEightSources) (k D : Nat) : Function.Injective (testSlots sources k D) := by
  intro a b h;exact Fin.ext (congrArg (fun i : Fin (tapes sources k D)=>i.val) h)
theorem erase_injective (sources : GateEightSources) (k D : Nat) : Function.Injective (eraseSlots sources k D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  dsimp only [eraseSlots] at hv
  split_ifs at hv <;> omega
theorem small_injective (sources : GateEightSources) (k D : Nat) :
    Function.Injective (indexSlots sources k D) ∧ Function.Injective (lengthSlots sources k D) ∧
    Function.Injective (bestSlots sources k D) ∧ Function.Injective (eraseBestSlots sources k D) := by
  have hN : (Test.old sources k D (Candidate.powerSlots sources k D 13)).val<Test.tapes sources k D :=
    (Test.old sources k D (Candidate.powerSlots sources k D 13)).isLt
  have hn : (Test.extra sources k D 0).val<Test.tapes sources k D := (Test.extra sources k D 0).isLt
  have hs : (Test.old sources k D (Candidate.powerSlots sources k D 0)).val<Test.tapes sources k D :=
    (Test.old sources k D (Candidate.powerSlots sources k D 0)).isLt
  refine ⟨?_,?_,?_,?_⟩
  all_goals intro a b h
  all_goals have hv:=congrArg Fin.val h
  all_goals fin_cases a <;> fin_cases b <;>
    simp [indexSlots,lengthSlots,bestSlots,eraseBestSlots,testSlots,copyLog,port,work,workTapes] at hv ⊢ <;> omega

def persistent (C s n best : Nat) : Fin 5→List Bool :=
  ![UnaryTemplate.tape s,UnaryTemplate.tape n,ZeroPadding.pad C (List.replicate best true),
    List.replicate C true,List.replicate (C+1) false]
def bank (sources : GateEightSources) (k D C s n best : Nat) : Fin (tapes sources k D)→List Bool :=
  Fin.addCases (fun _ : Fin (workTapes sources k D)=>List.replicate C false) (persistent C s n best)
theorem bank_work (sources : GateEightSources) (k D C s n best : Nat) (i : Fin (workTapes sources k D)) :
    bank sources k D C s n best (work sources k D i)=List.replicate C false :=
  Fin.addCases_left i
theorem bank_port (sources : GateEightSources) (k D C s n best : Nat) (i : Fin 5) :
    bank sources k D C s n best (port sources k D i)=persistent C s n best i :=
  Fin.addCases_right i
theorem port_away (sources : GateEightSources) (k D : Nat) (i : Fin (workTapes sources k D)) (j : Fin 5) :
    work sources k D i≠port sources k D j := by
  intro h;have hv:=congrArg Fin.val h;have:=i.isLt
  change i.val=workTapes sources k D+j.val at hv;omega

def copyIndex (sources : GateEightSources) (k D : Nat) :=
  RecoveryFocus.machine (indexSlots sources k D) (UWalkUnary.machine false false)
def copyLength (sources : GateEightSources) (k D : Nat) :=
  RecoveryFocus.machine (lengthSlots sources k D) (UWalkUnary.machine false false)
def copyBest (sources : GateEightSources) (k D : Nat) :=
  RecoveryFocus.machine (bestSlots sources k D) (UWalkUnary.machine false false)
def eraseBest (sources : GateEightSources) (k D : Nat) :=
  RecoveryFocus.machine (eraseBestSlots sources k D) (RecoveryScratchErase.resetMachine 1)
def eraseWork (sources : GateEightSources) (k D : Nat) :=
  RecoveryFocus.machine (eraseSlots sources k D) (RecoveryScratchErase.resetMachine (workTapes sources k D))
def increment (sources : GateEightSources) (k D : Nat) :=
  RecoveryFocus.machine (incrementSlots sources k D) MatrixBucketDimensions.Increment.machine
def test (sources : GateEightSources) (k D copies ext : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) :=
  RecoveryFocus.machine (testSlots sources k D) (Test.machine sources k D copies ext clock)

end
end NearCubicWires.RepairSource.CloseoutSchedule.Step

end GR
