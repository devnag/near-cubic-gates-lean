import Proof.Amplification.RecoveryRawViewWholeState

/-! Literal loop-success to empty-tail-test handoff. Thin configuration
unfolding keeps both large machines opaque while matching retained banks. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewWhole
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding RecoveryRawViewLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem end_restart (x : Cursor) (total : Nat) :
    RecoveryCalls.restarted (programs 1)
      (RepeatMachine.cfg 3 (source x) total 1).heads (RepeatMachine.cfg 3 (source x) total 1).tapes=
      RecoveryRawViewEnd.cfg x.data total RecoveryRawViewEnd.machine.start := by
  simp only [RecoveryCalls.restarted,RepeatMachine.cfg,controlConfig,source,RecoveryRawViewEnd.cfg,
    TapeEmbedding.config,State.cfg,State.innerCfg,RecoveryBankPair.cfg,
    RecoveryRawLiteralBound.State.cfg,RecoveryRawLiteralStream.State.cfg,
    RecoveryRawLiteralStream.State.extraHeads]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawViewWhole
