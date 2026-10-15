import Proof.MachineModel.OrdinaryMatrixVariableCountEntry

/-! The generated native count driver starts at zero. This paid transition
positions it, then appends the complete sign/factor/count packet. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketDock
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advance : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,fun i => if i=1 then .right else .stay⟩ else none
noncomputable def machine (negative : Bool) := Composition.machine advance (MatrixPacketAppend.machine negative)
def initial (bit : ℕ) (bits out : List Bool) : Configuration 4 2 :=
  ⟨0,![1,0,0,out.length],![UnaryTemplate.tape (2*bit),UnaryTemplate.tape bits.length,bits,out]⟩
def input (bit : ℕ) (bits out : List Bool) := Composition.leftConfig 12 (initial bit bits out)
def budget (bit : ℕ) (bits : List Bool) := 4*bit+2*bits.length+12

theorem dock_run (negative : Bool) (bit : ℕ) (bits out : List Bool) : ∃ actual,
    runFrom (machine negative) (budget bit bits) (input bit bits out)=some actual ∧
    actual.final.heads= ![1,1,bits.length,(out++MatrixPacketPrefix.prefixWord negative bit++bits).length] ∧
    actual.final.tapes= ![UnaryTemplate.tape (2*bit),UnaryTemplate.tape bits.length,bits,
      out++MatrixPacketPrefix.prefixWord negative bit++bits] ∧ actual.steps=budget bit bits := by
  let middle : Configuration 4 2 := ⟨1,![1,1,0,out.length],(initial bit bits out).tapes⟩
  have hstep : step advance (initial bit bits out)=some middle := by
    simp only [step,advance,initial]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨pre,hp,pf,ps⟩ := (Timed.single (by rfl) hstep).run (by rfl)
  obtain ⟨post,hq,qf,qs⟩ := MatrixPacketAppend.append_run negative bit bits [] out
  simp only [List.append_nil] at hq qf
  have hi : Composition.restart pre.final (MatrixPacketAppend.machine negative).start=
      MatrixPacketAppend.input bit bits [] out := by
    rw [pf]
    apply configuration_ext
    · rfl
    · rfl
    · simp [Composition.restart,middle,initial,MatrixPacketAppend.input,MatrixPacketAppend.cfg]
  rw [←hi] at hq
  have hj := Composition.run_join advance (MatrixPacketAppend.machine negative) _ _ _ pre post hp hq
  have ht : 1+1+(4*bit+2*bits.length+10)=budget bit bits := by unfold budget; omega
  rw [ht] at hj
  refine ⟨Composition.joinedReceipt pre post,hj,?_,?_,?_⟩
  · change post.final.heads=_
    rw [qf]
    rfl
  · change post.final.tapes=_
    rw [qf]
    rfl
  · change pre.steps+1+post.steps=_
    rw [ps,qs]
    exact ht

end NearCubicWires.RepairOrdinary.MatrixPacketDock
