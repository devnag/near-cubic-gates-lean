import Proof.CaseAnalysis.CaseTwoLiteralIndices
import Proof.CaseAnalysis.ScheduleCompare
import Proof.MachineModel.OrdinaryMatrixTemplateEntries

/-! Prepare the actual selected variable for the original assignment split.
The same variable index supplies a query template and the physical comparison
with the source's actual systematic count. The auxiliary offset is paid only
in the branch where that comparison proves it is defined. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.VariablePrep
open LocalBitMultitape RecoveryRootRound RepairSource.CloseoutSchedule
  RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def templateSlots : Fin 3→Fin 6:=![0,2,3]
def compareSlots : Fin 4→Fin 6:=![1,0,4,5]
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def compare:=RecoveryFocus.machine compareSlots MatrixBucketDimensions.Compare.machine
def machine:=Composition.machine template compare
def input (index sys : ℕ) : Fin 6→List Bool:=![List.replicate index true,UnaryTemplate.tape sys,[],[],[],[]]
def budget (index sys : ℕ):=(2*index+8)+1+(2*min sys index+6)
theorem prepare_run (index sys : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget index sys) (input index sys) out ∧
      out 2=UnaryTemplate.tape index ∧ out 4=[decide (sys ≤ index)] ∧
      out 0=List.replicate index true ∧ out 1=UnaryTemplate.tape sys:=by
  have firstReady:=(DimensionTemplate.ready false index).focus templateSlots (by decide) (input index sys)
    (by intro j;fin_cases j <;>rfl)
  let mid:=install templateSlots (input index sys) (DimensionTemplate.output false index)
  have secondReady:=(RawCompare.compare_cold sys index).focus compareSlots (by decide) mid (by
    intro j;fin_cases j
    · exact install_other _ _ _ _ (by decide)
    · exact install_slot templateSlots (by decide) _ _ 0
    · exact install_other _ _ _ _ (by decide)
    · exact install_other _ _ _ _ (by decide))
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ firstReady secondReady,?_,?_,?_,?_⟩
  · exact (install_other compareSlots _ _ _ (by decide)).trans (install_slot templateSlots (by decide) _ _ 1)
  · exact install_slot compareSlots (by decide) _ _ 2
  · exact install_slot compareSlots (by decide) _ _ 1
  · exact install_slot compareSlots (by decide) _ _ 0

def differenceSlots (i : Fin 4) : Fin 8:=i.castAdd 4
def rawSlots : Fin 5→Fin 8:=![2,4,5,6,7]
def difference:=RecoveryFocus.machine differenceSlots MatrixUnaryDifference.resetMachine
def copyRaw:=RecoveryFocus.machine rawSlots MatrixTemplateCopy.resetMachine
def auxiliary:=Composition.machine difference copyRaw
def auxiliaryInput (index sys : ℕ) : Fin 8→List Bool:=
  ![UnaryTemplate.tape index,UnaryTemplate.tape sys,[],[],[],[],[],[]]
def auxiliaryBudget (index sys : ℕ):=(2*index+8)+1+(4*(index-sys)+12)
theorem auxiliary_run (index sys : ℕ) (h : sys ≤ index) : ∃ out,
    ClockJoin.ReadyRun auxiliary (auxiliaryBudget index sys) (auxiliaryInput index sys) out ∧
      out 4=List.replicate (index-sys) true:=by
  obtain ⟨d,hd,_,_,d2,dh,ds⟩:=MatrixUnaryDifference.reset_run index sys h
  have dr:ClockJoin.ReadyRun MatrixUnaryDifference.resetMachine _ _ d.final.tapes:=⟨d,hd,rfl,dh,ds.le⟩
  have firstReady:=dr.focus differenceSlots (by decide) (auxiliaryInput index sys)
    (by intro j;fin_cases j <;>rfl)
  let mid:=install differenceSlots (auxiliaryInput index sys) d.final.tapes
  obtain ⟨r,hr,_,r1,_,_,rh,rs⟩:=MatrixTemplateCopy.reset_run (index-sys)
  have rr:ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine _ _ r.final.tapes:=⟨r,hr,rfl,rh,rs.le⟩
  have lastReady:=rr.focus rawSlots (by decide) mid (by
    intro j;fin_cases j
    · exact (install_slot differenceSlots (by decide) _ _ 2).trans d2
    · exact install_other differenceSlots (auxiliaryInput index sys) d.final.tapes 4 (by decide)
    · exact install_other differenceSlots (auxiliaryInput index sys) d.final.tapes 5 (by decide)
    · exact install_other differenceSlots (auxiliaryInput index sys) d.final.tapes 6 (by decide)
    · exact install_other differenceSlots (auxiliaryInput index sys) d.final.tapes 7 (by decide))
  exact ⟨_,ClockJoin.join _ _ _ _ _ _ _ firstReady lastReady,
    (install_slot rawSlots (by decide) _ _ 1).trans r1⟩

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.VariablePrep
