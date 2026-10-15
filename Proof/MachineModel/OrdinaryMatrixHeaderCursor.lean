import Proof.MachineModel.OrdinaryWilliamsPayloadCount

/-! Advance the retained external frame over the 2*w+1-bit dimension
header, using the width tape produced by the raw-header scan. -/
namespace NearCubicWires.RepairOrdinary.MatrixHeaderCursor
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tail : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q _ => if h : q.val<2 then
    some ⟨⟨q.val+1,by omega⟩,fun _ => none,![.stay,.right]⟩ else none

theorem tail_step (w : ℕ) (source : List Bool) (pos j : ℕ) (hj : j<2) :
    step tail (MatrixFramedBlock.config ⟨j,by omega⟩ w 1 source pos)=
      some (MatrixFramedBlock.config ⟨j+1,by omega⟩ w 1 source (pos+1)) := by
  have hj' : j≤1 := by omega
  simp [step,tail,MatrixFramedBlock.config,hj']
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem tail_run (w : ℕ) (source : List Bool) (pos : ℕ) :
    ∃ r : ExecutionReceipt 2 3,
      runFrom tail 2 (MatrixFramedBlock.config 0 w 1 source pos)=some r ∧
      r.final=MatrixFramedBlock.config 2 w 1 source (pos+2) ∧ r.steps=2 := by
  have h0 := Timed.single (by rfl) (tail_step w source pos 0 (by omega))
  have h1 := Timed.single (by rfl) (tail_step w source (pos+1) 1 (by omega))
  exact (h0.trans h1).run (by rfl)

def machine : Machine 2 15 := Composition.machine MatrixFramedBlock.double tail

theorem cursor_run (w : ℕ) (source : List Bool) (pos : ℕ) :
    ∃ r : ExecutionReceipt 2 15,
      runFrom machine (6*w+12) (MatrixFramedBlock.config 0 w 1 source pos)=some r ∧
      r.final=MatrixFramedBlock.config 14 w 1 source (pos+2*(2*w+1)) ∧ r.steps=6*w+12 := by
  obtain ⟨first,hr,hf,hs⟩ := MatrixFramedBlock.double_run w source pos
  obtain ⟨last,hl,hlf,hls⟩ := tail_run w source (pos+4*w)
  have hi : Composition.restart first.final tail.start=MatrixFramedBlock.config 0 w 1 source (pos+4*w) := by
    rw [hf]; rfl
  rw [← hi] at hl
  have hj := Composition.run_join MatrixFramedBlock.double tail (6*w+9) 2 _ first last hr hl
  refine ⟨Composition.joinedReceipt first last,?_,?_,?_⟩
  · have he : 6*w+9+1+2=6*w+12 := by omega
    rw [he] at hj
    exact hj
  · change Composition.rightConfig 12 last.final=_
    rw [hlf]
    have he : pos+4*w+2=pos+2*(2*w+1) := by omega
    rw [he]
    rfl
  · change first.steps+1+last.steps=_
    omega

end NearCubicWires.RepairOrdinary.MatrixHeaderCursor
