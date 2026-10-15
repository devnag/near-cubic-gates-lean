import Proof.Supplier.RowCoordinateIncrement
import Proof.Amplification.RecoveryEraseWidth
import Proof.Amplification.RecoveryTseitinRawIncrement

/-! The retained degree template advances using the existing unary scan.
The two head moves are actual transitions, so the source template returns
to the head-zero ABI required by the six metadata copies. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeAdvance
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def first := Composition.machine (RowCoordinateIncrement.shift .right) RecoveryEraseWidth.incrementMachine
def templateMachine := Composition.machine first (RowCoordinateIncrement.shift .left)

theorem template_ready (k : ℕ) :
    ReadyRun templateMachine (2*k+6) (fun _=>CompareMachine.word k)
      (fun _=>CompareMachine.word (k+1)) := by
  obtain ⟨a,ha,af,asteps⟩ := RowCoordinateIncrement.shift_run .right 0 (CompareMachine.word k)
  obtain ⟨b,hb,bf,bsteps⟩ := RecoveryEraseWidth.increment_run k
  have hi : RecoveryEraseWidth.cfg 0 k 1=
      Composition.restart a.final RecoveryEraseWidth.incrementMachine.start := by
    rw [af]
    rfl
  rw [hi] at hb
  have ab := Composition.run_join (RowCoordinateIncrement.shift .right) RecoveryEraseWidth.incrementMachine
    _ _ _ a b ha hb
  obtain ⟨c,hc,cf,csteps⟩ := RowCoordinateIncrement.shift_run .left 1 (CompareMachine.word (k+1))
  have hi' : RowCoordinateIncrement.cfg 0 1 (CompareMachine.word (k+1))=
      Composition.restart (Composition.joinedReceipt a b).final (RowCoordinateIncrement.shift .left).start := by
    change _=Composition.restart b.final _
    rw [bf]
    rfl
  rw [hi'] at hc
  have whole := Composition.run_join first (RowCoordinateIncrement.shift .left) _ _ _
    (Composition.joinedReceipt a b) c ab hc
  have ht : 1+1+(2*k+2)+1+1=2*k+6 := by omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a b) c,whole,?_,?_,?_⟩
  · change c.final.tapes=_
    rw [cf]
    rfl
  · intro i
    change c.final.heads i=0
    rw [cf]
    rfl
  · change (a.steps+1+b.steps)+1+c.steps=2*k+6
    rw [asteps,bsteps,csteps]
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeAdvance
