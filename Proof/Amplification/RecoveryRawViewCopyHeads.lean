import Proof.Amplification.RecoveryRawViewCopyInstall

/-! The framed handoff changes tape contents and reset capacities only.
Every retained source and counter head stays at its real entry position. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copied_heads {s : Nat} (x : State) (bits : List Bool) (q : Fin s) :
    ((copied x bits).cfg q).heads=(x.cfg q).heads := by
  simp only [State.cfg,State.innerCfg,RecoveryBankPair.cfg,TapeEmbedding.config,
    RecoveryRawLiteralBound.State.cfg,RecoveryRawLiteralStream.State.cfg,
    RecoveryRawLiteralStream.State.extraHeads,copied]

end NearCubicWires.RepairOrdinary.RecoveryRawView
