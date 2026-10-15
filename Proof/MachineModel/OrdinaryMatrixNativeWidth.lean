import Proof.MachineModel.OrdinaryMatrixBatchBucketSizesBounds
import Proof.MachineModel.ClockNumericPrep

/-! Recover the actual common width from a retained framed scalar, using
the existing length/reset program and unary field-copy program. -/
namespace NearCubicWires.RepairOrdinary.MatrixNativeWidth
open LocalBitMultitape RecoveryExecution RecoveryRootRound CompetitorRationalProducts
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem length_ready (bits : List Bool) : ClockJoin.ReadyRun ClockNumericPrep.ellMachine (4*bits.length+5)
    ![frame bits,[]] ![frame bits,CompareMachine.word bits.length] := by
  obtain ⟨base,hb,hf,hs,_⟩ := LengthMachine.length_run bits
  let tapes : Fin 2 → List Bool := ![frame bits,CompareMachine.word bits.length]
  have hstep : step ClockNumericPrep.ellReset ⟨0,![0,1],tapes⟩=some ⟨1,fun _ => 0,tapes⟩ := by
    simp [step,ClockNumericPrep.ellReset]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨last,hl,lf,ls⟩ := (Timed.single (by rfl) hstep).run (by rfl)
  have hi : Composition.restart base.final ClockNumericPrep.ellReset.start=⟨0,![0,1],tapes⟩ := by
    rw [hf]
    rfl
  rw [←hi] at hl
  have joined := Composition.run_join LengthMachine.machine ClockNumericPrep.ellReset _ _ _ base last hb hl
  have ht : (4*bits.length+3)+1+1=4*bits.length+5 := by omega
  rw [ht] at joined
  exact ⟨Composition.joinedReceipt base last,joined,by change last.final.tapes=_; rw [lf],
    by intro i; change last.final.heads i=0; rw [lf],by change base.steps+1+last.steps≤_; rw [hs,ls]⟩

def native (i : Fin 2) : Fin 6 := i.castAdd 4
def copySlots : Fin 5 → Fin 6 := ![1,2,3,4,5]
noncomputable def first := RecoveryFocus.machine native ClockNumericPrep.ellMachine
noncomputable def last := RecoveryFocus.machine copySlots MatrixTemplateCopy.resetMachine
noncomputable def machine := Composition.machine first last
def input (bits : List Bool) : Fin 6 → List Bool := fun i => if i=0 then frame bits else []
def budget (bits : List Bool) := 8*bits.length+18

theorem width_run (bits : List Bool) : ∃ out,ClockJoin.ReadyRun machine (budget bits) (input bits) out ∧
    out 0=frame bits ∧ out 2=List.replicate bits.length true ∧ out 3=List.replicate bits.length true ∧
    out 4=UnaryTemplate.tape bits.length := by
  let prepared := install native (input bits) ![frame bits,CompareMachine.word bits.length]
  have hf := bounded_focus native (by decide) _ _ _ (length_ready bits) (input bits)
    (by intro i; fin_cases i <;> rfl)
  obtain ⟨base,hb,b1,b2,b3,bh,bs⟩ := MatrixTemplateCopy.word_run bits.length
  have ready : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*bits.length+12)
      (MatrixTemplateCopy.wordInput bits.length) base.final.tapes := ⟨base,hb,rfl,bh,bs.le⟩
  have hi : ∀ i,prepared (copySlots i)=MatrixTemplateCopy.wordInput bits.length i := by
    intro i; fin_cases i
    · exact install_slot native (by decide) _ _ 1
    all_goals exact install_other native _ _ _ (by decide)
  let out := install copySlots prepared base.final.tapes
  have hl := bounded_focus copySlots (by decide) _ _ _ ready prepared hi
  have whole := ClockJoin.join first last _ _ _ _ _ hf hl
  have ht : (4*bits.length+5)+1+(4*bits.length+12)=budget bits := by unfold budget; omega
  rw [ht] at whole
  exact ⟨out,whole,(install_other copySlots _ _ 0 (by decide)).trans (install_slot native (by decide) _ _ 0),
    (install_slot copySlots (by decide) _ _ 1).trans b1,(install_slot copySlots (by decide) _ _ 2).trans b2,
    (install_slot copySlots (by decide) _ _ 3).trans b3⟩

end NearCubicWires.RepairOrdinary.MatrixNativeWidth
