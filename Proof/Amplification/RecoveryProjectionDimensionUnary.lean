import Proof.Amplification.RecoveryProjectionWidthBudget
import Proof.PCP.ProjectionNormalizationUnary
import Proof.MachineModel.UWalkUnary

namespace NearCubicWires.RepairSource.RecoveryProjectionDimension
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def parserHeads (i : Fin 5) := if i=3 then 1 else 0
def retreat : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun i=>if i=3 then .left else .stay⟩ else none

theorem retreat_step (data : Fin 5→List Bool) :
    step retreat (⟨0,parserHeads,data⟩ : Configuration 5 2)=some ⟨1,fun _=>0,data⟩ := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; by_cases hi : i=3 <;> simp [applyAction,parserHeads,hi,HeadMove.apply]
  · rfl

noncomputable def parsedMachine := Composition.machine Unary.machine retreat

theorem parsed_ready (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun parsedMachine (Unary.budget bits+2) (Unary.input bits) out ∧
      out 3=VerifierDecoding.CompareMachine.word (value bits) := by
  obtain ⟨first,hfirst,ft,fh,fs⟩ := Unary.unary_run bits
  obtain ⟨last,hlast,lf,ls⟩ := (Timed.single (by rfl) (retreat_step first.final.tapes)).run (by rfl)
  have he : Composition.restart first.final retreat.start=
      (⟨0,parserHeads,first.final.tapes⟩ : Configuration 5 2) := by
    apply configuration_ext
    · rfl
    · exact funext fh
    · rfl
  rw [←he] at hlast
  have hall := Composition.run_join Unary.machine retreat _ 1 _ first last hfirst hlast
  have htime : Unary.budget bits+1+1=Unary.budget bits+2 := by omega
  rw [htime] at hall
  refine ⟨first.final.tapes,⟨_,hall,?_,?_,?_⟩,ft⟩
  · change last.final.tapes=_
    rw [lf]
  · intro i; change last.final.heads i=0; rw [lf]
  · change first.steps+1+last.steps ≤ Unary.budget bits+2
    omega

def copySlots : Fin 3→Fin 7 := ![3,5,6]
theorem copy_injective : Function.Injective copySlots := by decide
noncomputable def firstMachine := TapeEmbedding.machine 2 parsedMachine
noncomputable def copyMachine := RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
noncomputable def machine := Composition.machine firstMachine copyMachine
def input (bits : List Bool) (i : Fin 7) := if i=0 then RepairOrdinary.frame bits else []
def budget (bits : List Bool) := Unary.budget bits+2*value bits+9

theorem unary_ready (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget bits) (input bits) out ∧
      out 3=VerifierDecoding.CompareMachine.word (value bits) ∧ out 5=List.replicate (value bits) true := by
  obtain ⟨parsed,hparsed,hcount⟩ := parsed_ready bits
  obtain ⟨r,hr,ht,hh,hs⟩ := hparsed
  let out : Fin 7→List Bool := fun i=>Fin.addCases (m:=5) (n:=2) (motive:=fun _=>List Bool) parsed (fun _=>[]) i
  have first : ClockJoin.ReadyRun firstMachine (Unary.budget bits+2) (input bits) out := by
    refine ⟨TapeEmbedding.receipt (fun _ : Fin 2=>0) (fun _=>[]) r,?_,?_,?_,hs⟩
    · have h:=TapeEmbedding.run_embed parsedMachine (fun _ : Fin 2=>0) (fun _=>[]) _ _ r hr
      have hi : TapeEmbedding.config (fun _ : Fin 2=>0) (fun _=>[])
          (initialConfiguration parsedMachine (Unary.input bits))=
            initialConfiguration firstMachine (input bits) := by
        apply configuration_ext
        · rfl
        · funext i; refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;>
            simp [TapeEmbedding.config,initialConfiguration]
        · funext i; fin_cases i <;> rfl
      rw [hi] at h
      exact h
    · funext i
      refine Fin.addCases (m:=5) (n:=2) (fun j=>?_) (fun j=>?_) i
      · simpa only [TapeEmbedding.receipt_tapes_old,out,Fin.addCases_left] using congrFun ht j
      · simp only [TapeEmbedding.receipt_tapes_new,out,Fin.addCases_right]
    · intro i
      refine Fin.addCases (m:=5) (n:=2) (fun j=>?_) (fun j=>?_) i
      · simpa only [TapeEmbedding.receipt_heads_old] using hh j
      · simp only [TapeEmbedding.receipt_heads_new]
  have hcopy := (UWalkUnary.ready false false 0 (value bits)).focus copySlots copy_injective out (by
    intro j
    fin_cases j
    · change parsed 3=ZeroPadding.pad 0 (VerifierDecoding.CompareMachine.word (value bits))
      rw [ZeroPadding.pad_zero]
      exact hcount
    · rfl
    · rfl)
  have hall := ClockJoin.join _ _ _ _ _ _ _ first hcopy
  have htime : (Unary.budget bits+2)+1+(2*value bits+6)=budget bits := by unfold budget; omega
  rw [htime] at hall
  refine ⟨_,hall,?_,?_⟩
  · change install copySlots _ _ (copySlots 0)=_
    rw [install_slot _ copy_injective]
    simp [UWalkUnary.result,UWalkUnary.source]
  · change install copySlots _ _ (copySlots 1)=_
    rw [install_slot _ copy_injective]
    simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead]

end NearCubicWires.RepairSource.RecoveryProjectionDimension
