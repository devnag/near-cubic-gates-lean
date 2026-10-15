import Proof.MachineModel.OrdinaryMatrixScoreHeaders

/-! Consume the actual head1 unary output of the header parser. Its one-cell
retreat and the reusable copy/reset execute before any raw unary consumer. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreTemplateEntry
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def retreat : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,
    fun i => if i=0 then .left else .stay⟩ else none
def machine : Machine 5 10 := Composition.machine retreat MatrixTemplateCopy.resetMachine
def input (d : ℕ) : Configuration 5 10 :=
  ⟨0,fun i => if i=0 then 1 else 0,MatrixTemplateCopy.resetInput d⟩

theorem entry_run (d : ℕ) :
    ∃ actual : ExecutionReceipt 5 10,
      runFrom machine (4*d+14) (input d)=some actual ∧
      actual.final.tapes 0=UnaryTemplate.tape d ∧
      actual.final.tapes 1=List.replicate d true ∧ actual.final.tapes 2=List.replicate d true ∧
      actual.final.tapes 3=UnaryTemplate.tape d ∧
      (∀ i,actual.final.heads i=0) ∧ actual.steps=4*d+14 := by
  let start : Configuration 5 2 := ⟨0,fun i => if i=0 then 1 else 0,MatrixTemplateCopy.resetInput d⟩
  let finish : Configuration 5 2 := ⟨1,fun _ => 0,MatrixTemplateCopy.resetInput d⟩
  have hstep : step retreat start=some finish := by
    simp [step,retreat,start]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,finish]
    · rfl
  obtain ⟨first,hf,hff,hfs⟩ := (RecoveryExecution.Timed.single (by rfl) hstep).run (by rfl)
  obtain ⟨last,hl,ht0,ht1,ht2,ht3,hh,hs⟩ := MatrixTemplateCopy.reset_run d
  have he : Composition.restart first.final MatrixTemplateCopy.resetMachine.start=
      initialConfiguration MatrixTemplateCopy.resetMachine (MatrixTemplateCopy.resetInput d) := by
    rw [hff]
    rfl
  have hl' : runFrom MatrixTemplateCopy.resetMachine (4*d+12)
      (Composition.restart first.final MatrixTemplateCopy.resetMachine.start)=some last := by
    rw [he]; exact hl
  have hj := Composition.run_join retreat MatrixTemplateCopy.resetMachine 1 (4*d+12) start first last hf hl'
  have htime : 1+1+(4*d+12)=4*d+14 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,ht0,ht1,ht2,ht3,hh,?_⟩
  change first.steps+1+last.steps=_
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreTemplateEntry
