import Proof.SourceAssembly.SourceSymmetricScan

/- Boot the two real counters, then consume the produced q header/scratch and
bitmap. The original padded arity remains retained; output heads are exact. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricCold
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RecoveryRootRound RepairSource.VerifierDecoding RecoveryExecution
open SourceAssemblySymmetricScan (outputs selected)
noncomputable section

def heads (q : Nat) (bits : List Bool) (j : Nat) : Fin 9→Nat:=
  ![1,1,0,(outputs q bits j 0).length,(outputs q bits j 1).length,0,j,1,1]
def words (q C : Nat) (bits : List Bool) (j : Nat) : Fin 9→List Bool:=
  ![UnaryTemplate.tape q,CompareMachine.word j,frame (natWord q),outputs q bits j 0,
    outputs q bits j 1,List.replicate C false,bits,CompareMachine.word (selected bits j).length,CompareMachine.word q]
def rawWords (q C : Nat) (bits : List Bool) (j : Nat) : Fin 9→List Bool:=
  ![CompareMachine.word q,CompareMachine.word j,frame (natWord q),outputs q bits j 0,
    outputs q bits j 1,List.replicate C false,bits,CompareMachine.word (selected bits j).length,CompareMachine.word q]
def caps (q : Nat) (i : Fin 9):=if i=0 then q+2 else 0

theorem pad_words (q C : Nat) (bits : List Bool) (j : Nat) :
    (fun i=>ZeroPadding.pad (caps q i) (rawWords q C bits j i))=words q C bits j := by
  funext i;fin_cases i
  · exact (SourceAssemblyParityQuery.arity_eq q).symm
  all_goals simp [caps,rawWords,words,ZeroPadding.pad_zero]

theorem scan_run (q C : Nat) (bits : List Bool) (hC : 2*(natWord q).length+1 ≤ C) :
    Step SourceAssemblySymmetricScan.machine
      (SourceAssemblySymmetricScan.budget q)
      (heads q bits 0) (words q C bits 0) (heads q bits q) (words q C bits q) := by
  obtain ⟨r,hr,hf,_⟩:=SourceAssemblySymmetricScan.run q C [] bits hC
  have hi : RepeatMachine.cfg 0
      (SourceAssemblySymmetricScan.source SourceAssemblySymmetricScan.body q C [] bits 0) q 1=
      RecoveryCalls.restarted SourceAssemblySymmetricScan.machine (heads q bits 0) (rawWords q C bits 0) := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
        SourceAssemblySymmetricScan.source,SourceAssemblySymmetricScan.A,
        SymmetricBody.A,Gate.A,rawWords,RecoveryCalls.restarted] <;>rfl
  rw [hi] at hr
  have actual : Step SourceAssemblySymmetricScan.machine
      (SourceAssemblySymmetricScan.budget q)
      (heads q bits 0) (rawWords q C bits 0) (heads q bits q) (rawWords q C bits q) := by
    apply Step.of_run hr
    · rw [hf];funext i;fin_cases i <;>rfl
    · rw [hf];funext i;fin_cases i <;>simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
        SourceAssemblySymmetricScan.source,SourceAssemblySymmetricScan.A,
        SymmetricBody.A,Gate.A,rawWords] <;>rfl
  have padded:=actual.pad (caps q)
  rw [pad_words,pad_words] at padded
  exact padded

def input (q C : Nat) (bits : List Bool) : Fin 9→List Bool:=
  ![UnaryTemplate.tape q,[],frame (natWord q),[],[],List.replicate C false,bits,[],CompareMachine.word q]
def boot : Machine 9 2 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==1
  rule:=fun _ _=>some ⟨1,(fun i=>if i=1 ∨ i=7 then some false else none),
    (fun i=>if i=0 ∨ i=1 ∨ i=7 ∨ i=8 then .right else .stay)⟩
def machine:=Composition.machine boot SourceAssemblySymmetricScan.machine
def budget (q : Nat):=1+1+SourceAssemblySymmetricScan.budget q

theorem boot_run (q C : Nat) (bits : List Bool) :
    Step boot 1 (fun _=>0) (input q C bits) (heads q bits 0) (words q C bits 0) := by
  have hs : step boot (initialConfiguration boot (input q C bits))=
      some (⟨1,heads q bits 0,words q C bits 0⟩ : Configuration 9 2) := by
    simp [step,boot,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>simp [applyAction,HeadMove.apply,heads,outputs,selected]
    · funext i;fin_cases i <;>simp [applyAction,input,words,outputs,selected,writeTapeBit,CompareMachine.word]
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem run (q C : Nat) (bits : List Bool) (hC : 2*(natWord q).length+1 ≤ C) :
    Step machine (budget q) (fun _=>0) (input q C bits) (heads q bits q) (words q C bits q) :=
  (boot_run q C bits).seq (scan_run q C bits hC)

end
end SourceAssemblySymmetricCold
