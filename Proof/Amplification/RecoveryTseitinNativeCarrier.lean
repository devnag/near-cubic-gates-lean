import Proof.Amplification.RecoveryTseitinNativePrefixLayout

/-! Keep the physical capacity abstract through the ambient joins. The
actual cubic producer is substituted only after the generic endpoint proof. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workspaceData (cap n count output : Nat) (word : List Bool) (i : Fin 1370) : List Bool :=
  if i=1336 then List.replicate cap true else
  if i=1338 then CompareMachine.word count else input n count output word i
theorem workspace_actual (n count output : Nat) (word : List Bool) :
    workspaceData (Reuse.capacity n count) n count output word=preparedData n count output word := rfl

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
