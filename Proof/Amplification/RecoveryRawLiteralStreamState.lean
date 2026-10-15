import Proof.Amplification.RecoveryRawLiteralWhole
import Proof.PCP.VerifierLookupWalk

/-! The raw literal loop retains the certificate cursor independently of
the decoded clause tail. Its unused two W-bit scalar fields are skipped by
the existing paid walk, whose actual 2W driver returns to head one. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  data : RecoveryRawLiteral.State
  source : List Bool
  pos : Nat

def State.width (x : State) := x.data.data.bits.length
def State.extra (x : State) : Fin 2 → List Bool := ![x.source,CompareMachine.word (2*x.width)]
def State.extraHeads (x : State) : Fin 2 → Nat := ![x.pos,1]
def State.cfg {s : Nat} (x : State) (q : Fin s) : Configuration 31 s :=
  RecoveryBankPair.cfg (fun _ : Fin 29=>0) x.data.tapes x.extraHeads x.extra q
def decoded (x : State) : State := {x with data:=RecoveryRawLiteral.output x.data}
def skipped (x : State) : State := {decoded x with pos:=x.pos+4*x.width}
def output (x : State) := if (decoded x).data.present then skipped x else decoded x

noncomputable def literalMachine := RecoveryBankPair.leftMachine (u:=2) RecoveryRawLiteral.machine
def skipMachine := RecoveryBankPair.rightMachine (t:=29) (LookupWalk.machine .right)
noncomputable def machine := RecoveryGatedSequence.machine literalMachine skipMachine 28
def cost (x : State) := RecoveryRawLiteral.cost x.data+(3*(2*x.width)+2)+2

theorem decoded_width (x : State) : (decoded x).width=x.width := RecoveryRawLiteral.output_width x.data
theorem decoded_extra (x : State) : (decoded x).extra=x.extra := by
  unfold State.extra
  rw [decoded_width]
  rfl

theorem output_width (x : State) : (output x).width=x.width := by
  unfold output
  split <;> exact decoded_width x

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralStream
