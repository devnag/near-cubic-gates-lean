import Proof.PCP.ProjectionDimensionTemplate
import Proof.Circuits.MatrixBucketDimensionsCompare

/-! The schedule's raw-unary comparison reuses the existing template writer
and stopping test. Both inputs are retained and every head is restored. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.RawCompare
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem compare_cold (a b : Nat) : ClockJoin.ReadyRun MatrixBucketDimensions.Compare.machine
    (2*min a b+6) ![UnaryTemplate.tape a,List.replicate b true,[],[]]
    ![UnaryTemplate.tape a,List.replicate b true,[decide (a≤b)],List.replicate (min a b+2) false] := by
  obtain ⟨base,hb,hf,hs⟩:=MatrixBucketDimensions.Compare.raw_run a b
  obtain ⟨r,hr,ht,hlog,hh,hsteps,_⟩:=Rewind.Workspace.reset_workspace
    MatrixBucketDimensions.Compare.raw _ _ base hb 0
  have he : 2*base.steps+2=2*min a b+6 := by omega
  rw [he] at hr
  have hi : (Fin.addCases (motive:=fun _ : Fin 4=>List Bool)
      (MatrixBucketDimensions.Compare.input a b) (fun _ : Fin 1=>List.replicate 0 false))=
      ![UnaryTemplate.tape a,List.replicate b true,[],[]] := by
    funext i;fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i
  fin_cases i
  · simpa [hf,MatrixBucketDimensions.Compare.cfg] using ht 0
  · simpa [hf,MatrixBucketDimensions.Compare.cfg] using ht 1
  · simpa [hf,MatrixBucketDimensions.Compare.cfg] using ht 2
  · simpa [hs] using hlog

def templateSlots : Fin 3→Fin 6 := ![0,2,3]
def compareSlots : Fin 4→Fin 6 := ![2,1,4,5]
def input (a b : Nat) : Fin 6→List Bool :=
  ![List.replicate a true,List.replicate b true,[],[],[],[]]
def middle (a b : Nat) : Fin 6→List Bool :=
  ![List.replicate a true,List.replicate b true,UnaryTemplate.tape a,
    List.replicate (a+3) false,[],[]]
def output (a b : Nat) : Fin 6→List Bool :=
  ![List.replicate a true,List.replicate b true,UnaryTemplate.tape a,
    List.replicate (a+3) false,[decide (a≤b)],List.replicate (min a b+2) false]
def template := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def compare := RecoveryFocus.machine compareSlots MatrixBucketDimensions.Compare.machine
def machine := Composition.machine template compare
def budget (a b : Nat) := (2*a+8)+1+(2*min a b+6)

theorem compare_run (a b : Nat) :
    ClockJoin.ReadyRun machine (budget a b) (input a b) (output a b) := by
  have htemplate:=(DimensionTemplate.ready false a).focus templateSlots (by decide) (input a b)
    (by intro i;fin_cases i <;> rfl)
  have hm : install templateSlots (input a b) (DimensionTemplate.output false a)=middle a b := by
    funext i
    fin_cases i
    · exact install_slot templateSlots (by decide) _ _ 0
    · exact install_other templateSlots _ _ 1 (by decide)
    · exact install_slot templateSlots (by decide) _ _ 1
    · exact install_slot templateSlots (by decide) _ _ 2
    · exact install_other templateSlots _ _ 4 (by decide)
    · exact install_other templateSlots _ _ 5 (by decide)
  rw [hm] at htemplate
  have hcompare:=(compare_cold a b).focus compareSlots (by decide) (middle a b)
    (by intro i;fin_cases i <;> rfl)
  have ho : install compareSlots (middle a b)
      ![UnaryTemplate.tape a,List.replicate b true,[decide (a≤b)],List.replicate (min a b+2) false]=output a b := by
    funext i
    fin_cases i
    · exact install_other compareSlots _ _ 0 (by decide)
    · exact install_slot compareSlots (by decide) _ _ 1
    · exact install_slot compareSlots (by decide) _ _ 0
    · exact install_other compareSlots _ _ 3 (by decide)
    · exact install_slot compareSlots (by decide) _ _ 2
    · exact install_slot compareSlots (by decide) _ _ 3
  rw [ho] at hcompare
  exact ClockJoin.join _ _ _ _ _ _ _ htemplate hcompare

end
end NearCubicWires.RepairSource.CloseoutSchedule.RawCompare
