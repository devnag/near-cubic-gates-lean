import Proof.MachineModel.UWalkUnary
import Proof.CaseAnalysis.ScheduleCompare

/-! The canonical traversal's actual count is compared with a paid policy
cap. Only that bounded count is copied; a declared numeral is never expanded. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CountBound
open LocalBitMultitape RecoveryRootRound RepairSource VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def copySlots : Fin 3→Fin 8:=![0,2,3]
def compareSlots : Fin 6→Fin 8:=![2,1,4,5,6,7]
def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
def compare:=RecoveryFocus.machine compareSlots CloseoutSchedule.RawCompare.machine
def machine:=Composition.machine copy compare
def input (n cap : ℕ) : Fin 8→List Bool:=
  ![CompareMachine.word n,List.replicate cap true,[],[],[],[],[],[]]
def budget (n cap : ℕ):=(2*n+6)+1+CloseoutSchedule.RawCompare.budget n cap

theorem bound_run (n cap : ℕ) : ∃ output,
    ClockJoin.ReadyRun machine (budget n cap) (input n cap) output ∧
      output 0=CompareMachine.word n ∧ output 1=List.replicate cap true ∧
      output 2=List.replicate n true ∧ output 6=[decide (n≤cap)]:=by
  have hc:=(UWalkUnary.ready false false 0 n).focus copySlots (by decide) (input n cap) (by
    intro i;fin_cases i
    · simp only [copySlots,input,UWalkUnary.input,UWalkUnary.source,ZeroPadding.pad_zero]
      rfl
    all_goals rfl)
  let bank:=install copySlots (input n cap) (UWalkUnary.result false false 0 n)
  have fresh (i : Fin 8) (hi : i=1 ∨ 4 ≤ i.val) : bank i=input n cap i:=by
    apply install_other
    intro j h
    rcases hi with hi|hi
    · subst i;fin_cases j <;> contradiction
    · have hv:=congrArg (fun k : Fin 8=>k.val) h
      fin_cases j <;> simp [copySlots] at hv <;> omega
  have hv:bank 2=List.replicate n true:=by
    change install copySlots _ _ (copySlots 1)=_
    rw [install_slot _ (by decide)];rfl
  have hr:=(CloseoutSchedule.RawCompare.compare_run n cap).focus compareSlots (by decide) bank (by
    intro i;fin_cases i
    · exact hv
    · exact fresh 1 (Or.inl rfl)
    all_goals exact fresh _ (Or.inr (by decide)))
  refine ⟨_,ClockJoin.join copy compare _ _ _ _ _ hc hr,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide)]
    change install copySlots _ _ (copySlots 0)=_
    rw [install_slot _ (by decide)]
    simp only [UWalkUnary.result,UWalkUnary.source,ZeroPadding.pad_zero]
    rfl
  · exact install_slot compareSlots (by decide) _ _ 1
  · exact install_slot compareSlots (by decide) _ _ 0
  · exact install_slot compareSlots (by decide) _ _ 4

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.CountBound
