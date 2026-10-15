import Proof.SourceAssembly.SourceSymmetricMeaning

/- The paid selected-count driver prints the complete native SYM TOP field,
including the mandatory initial false entry, and the raw count for its header. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricTop
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RecoveryRootRound RepairSource.VerifierDecoding RecoveryExecution
noncomputable section

def table (n : Nat):=List.ofFn (fun i : Fin (n+1)=>Alternating.flag i.val)
def initialOut : Fin 2→List Bool:=![[true,false],[]]
def out (n : Nat):=Alternating.emittedPrefix Alternating.symmetricStrokes n initialOut

theorem table_succ (n : Nat) : table (n+1)=table n++[Alternating.flag (n+1)] := by
  unfold table
  rw [List.ofFn_succ_last]
  rfl

theorem top_prefix (n : Nat) : out n 0=Fragment.body (table n) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    have h:=congrFun (Alternating.prefix_succ Alternating.symmetricStrokes n initialOut) 0
    change out (n+1) 0=out n 0++[true,!Alternating.flag n] at h
    rw [h,ih,table_succ]
    simp [Fragment.body,Alternating.flag,List.flatMap_append]

theorem raw_count (n : Nat) : out n 1=List.replicate n true := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    have h:=congrFun (Alternating.prefix_succ Alternating.symmetricStrokes n initialOut) 1
    change out (n+1) 1=out n 1++[true] at h
    rw [h,ih]
    exact (List.replicate_add n 1 true).symm

def heads (n : Nat) : Fin 4→Nat:=Fin.addCases (motive:=fun _=>Nat) (Glyph.heads 0 (out n)) (fun _ : Fin 1=>1)
def words (total n : Nat) : Fin 4→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (Glyph.data [Alternating.flag n] (out n)) (fun _ : Fin 1=>CompareMachine.word total)
def input (n : Nat) : Fin 4→List Bool:=![[],[],[],CompareMachine.word n]
def inputHeads : Fin 4→Nat:=![0,0,0,1]
def boot : Machine 4 3 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==2
  rule:=fun s _=>if s=0 then some ⟨1,![some false,some true,none,none],![.stay,.right,.stay,.stay]⟩
    else some ⟨2,![none,some false,none,none],![.stay,.right,.stay,.stay]⟩
def finish : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==1
  rule:=fun _ _=>some ⟨1,![none,some false,none,none],![.stay,.right,.stay,.stay]⟩
def finalHeads (n : Nat) : Fin 4→Nat:=![0,(frame (table n)).length,n,1]
def finalWords (n : Nat) : Fin 4→List Bool:=![[Alternating.flag n],frame (table n),List.replicate n true,CompareMachine.word n]
def machine:=Composition.machine boot (Composition.machine (Alternating.machine Alternating.symmetricStrokes) finish)
def budget (n : Nat):=9*n+8

theorem boot_run (n : Nat) : Step boot 2 inputHeads (input n) (heads 0) (words n 0) := by
  let middle : Configuration 4 3:=⟨1,![0,1,0,1],![[false],[true],[],CompareMachine.word n]⟩
  have h0 : step boot (RecoveryCalls.restarted boot inputHeads (input n))=some middle := by
    simp [step,boot,RecoveryCalls.restarted]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>rfl
  have h1 : step boot middle=some (⟨2,heads 0,words n 0⟩ : Configuration 4 3) := by
    simp [step,boot,middle]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>rfl
  obtain ⟨r,hr,hf,_⟩:=((Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem finish_run (n : Nat) : Step finish 1 (heads n) (words n n) (finalHeads n) (finalWords n) := by
  have hs : step finish (RecoveryCalls.restarted finish (heads n) (words n n))=
      some (⟨1,finalHeads n,finalWords n⟩ : Configuration 4 2) := by
    simp [step,finish,RecoveryCalls.restarted]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i
      · rfl
      · change (out n 0).length+1=(frame (table n)).length
        rw [top_prefix,Fragment.frame_eq,List.length_append];rfl
      · change (out n 1).length=n
        rw [raw_count,List.length_replicate]
      · rfl
    · funext i;fin_cases i
      · rfl
      · change writeTapeBit (out n 0) (out n 0).length false=frame (table n)
        rw [Streaming.write_append,top_prefix,Fragment.frame_eq]
      · exact raw_count n
      · rfl
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem run (n : Nat) : Step machine (budget n) inputHeads (input n) (finalHeads n) (finalWords n) := by
  have middle:=Alternating.alternating_run Alternating.symmetricStrokes [] n initialOut
  have he : Alternating.emittedPrefix Alternating.symmetricStrokes 0 initialOut=initialOut := by funext i;simp [Alternating.emittedPrefix]
  have first:=boot_run n
  have mid : Step (Alternating.machine Alternating.symmetricStrokes) (9*n+3) (heads 0) (words n 0) (heads n) (words n n) := by
    simpa only [heads,words,out,he,show Alternating.flag 0=false by rfl,show 2*Alternating.symmetricStrokes.length+5=9 by rfl,Nat.mul_comm n 9] using middle
  exact (first.seq (mid.seq (finish_run n))).enlarge (by unfold budget;omega)

end
end SourceAssemblySymmetricTop
