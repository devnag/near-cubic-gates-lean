import Proof.MachineModel.OccurrenceRun
import Proof.MachineModel.UWalkUnary

/-! Reuse the checked unary copier at a retained head-one template. Both
one-cell positioning moves are paid; zero uses the same construction. -/
namespace NearCubicWires.ExtDecompositionBatch.FinalUnary
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def position (forward : Bool) : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    ![if forward then .right else .left,.stay,.stay]⟩ else none

theorem position_step (forward : Bool) (A : Fin 3 → List Bool) :
    Step (position forward) 1 ![if forward then 0 else 1,0,0] A
      ![if forward then 1 else 0,0,0] A := by
  have path : Timed (position forward) 1
      ⟨0,![if forward then 0 else 1,0,0],A⟩
      ⟨1,![if forward then 1 else 0,0,0],A⟩ := by
    apply Timed.single (by rfl)
    simp only [step,position,Fin.isValue,↓reduceIte]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;cases forward <;> fin_cases i <;> rfl
    · funext i;rfl
  obtain ⟨r,hr,hf,hs⟩:=path.run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],hs.le⟩

noncomputable def machine:=Composition.machine
  (Composition.machine (position false) (UWalkUnary.machine false false)) (position true)
def input (n : ℕ) : Fin 3 → List Bool:=![UnaryTemplate.tape n,[],[]]
def output (n : ℕ) : Fin 3 → List Bool:=
  ![UnaryTemplate.tape n,List.replicate n true,List.replicate (n+2) false]

theorem copy_run (n : ℕ) : Step machine (2*n+10) ![1,0,0] (input n) ![1,0,0] (output n) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=UWalkUnary.ready false false (n+2) n
  have sourceEq:UWalkUnary.source (n+2) n=UnaryTemplate.tape n:=Records.template_pad n
  have hi:UWalkUnary.input (n+2) n=input n:=by
    funext i;fin_cases i <;> simp [UWalkUnary.input,input,sourceEq]
  have ho:UWalkUnary.result false false (n+2) n=output n:=by
    funext i;fin_cases i <;> simp [UWalkUnary.result,output,sourceEq,UWalkUnary.output,UWalkUnary.lead]
  have middle:Step (UWalkUnary.machine false false) (2*n+6) (fun _=>0) (input n)
      (fun _=>0) (output n) := by
    rw [hi] at hr
    refine ⟨r,hr,?_,ht.trans ho,hs⟩
    funext i;exact hh i
  have zero:(fun _ : Fin 3=>0)=![0,0,0]:=by funext i;fin_cases i <;> rfl
  rw [zero] at middle
  have run:=((position_step false (input n)).seq middle).seq (position_step true (output n))
  have time:1+1+(2*n+6)+1+1=2*n+10:=by omega
  rw [time] at run
  exact run

end NearCubicWires.ExtDecompositionBatch.FinalUnary
