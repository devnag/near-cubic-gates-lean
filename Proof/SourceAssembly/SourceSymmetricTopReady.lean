import Proof.SourceAssembly.SourceSymmetricTop

/- Pay the bounded recorded rewind of the small TOP writer. Its actual raw
count is now resident at head zero for the native-header producer. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricTopReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RecoveryRootRound RepairSource.VerifierDecoding RecoveryExecution
noncomputable section

def heads : Fin 5→Nat:=![0,0,0,1,0]
def recordedHeads : Fin 5→Nat:=Fin.addCases (motive:=fun _=>Nat) SourceAssemblySymmetricTop.inputHeads (fun _ : Fin 1=>1)
def input (n : Nat) : Fin 5→List Bool:=Fin.addCases (motive:=fun _=>List Bool)
  (SourceAssemblySymmetricTop.input n) (fun _ : Fin 1=>[])
def recordedInput (n : Nat) : Fin 5→List Bool:=Fin.addCases (motive:=fun _=>List Bool)
  (SourceAssemblySymmetricTop.input n) (fun _ : Fin 1=>[true])
def boot : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==1
  rule:=fun _ _=>some ⟨1,(fun i=>if i=4 then some true else none),(fun i=>if i=4 then .right else .stay)⟩
def machine:=Composition.machine boot (Rewind.machine SourceAssemblySymmetricTop.machine)
def budget (n : Nat):=2*SourceAssemblySymmetricTop.budget n+5

theorem boot_run (n : Nat) : Step boot 1 heads (input n) recordedHeads (recordedInput n) := by
  have hs : step boot (RecoveryCalls.restarted boot heads (input n))=
      some (⟨1,recordedHeads,recordedInput n⟩ : Configuration 5 2) := by
    simp [step,boot,RecoveryCalls.restarted]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>rfl
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem run (n : Nat) : ∃ A,Step machine (budget n) heads (input n) (fun _=>0) A ∧
    A 1=frame (SourceAssemblySymmetricTop.table n) ∧A 2=List.replicate n true ∧
    A 3=CompareMachine.word n := by
  obtain ⟨base,hb,bh,bt,bs⟩:=SourceAssemblySymmetricTop.run n
  obtain ⟨r,hr,rf,_⟩:=Rewind.recorded_run SourceAssemblySymmetricTop.machine
    (SourceAssemblySymmetricTop.budget n) _ base hb 1 (by intro i;change SourceAssemblySymmetricTop.inputHeads i ≤ 1;fin_cases i <;>decide)
  have middle : Step (Rewind.machine SourceAssemblySymmetricTop.machine)
      (2*SourceAssemblySymmetricTop.budget n+3)
      recordedHeads (recordedInput n) (fun _=>0) r.final.tapes := by
    apply (Step.of_run hr ?_ rfl).enlarge (by omega)
    rw [rf]
    funext i;fin_cases i <;>rfl
  refine ⟨r.final.tapes,((boot_run n).seq middle).enlarge (by unfold budget;omega),?_,?_,?_⟩
  · rw [rf];change base.final.tapes 1=_;rw [bt];rfl
  · rw [rf];change base.final.tapes 2=_;rw [bt];rfl
  · rw [rf];change base.final.tapes 3=_;rw [bt];rfl

end
end SourceAssemblySymmetricTopReady
