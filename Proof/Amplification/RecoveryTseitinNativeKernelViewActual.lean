import Proof.Amplification.RecoveryTseitinNativeKernelViewCore

/-! The actual allocated tape bank has the original node-clause consumer view. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RecoveryTseitinNode RecoveryTseitinKernel
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem kernel_view {n z : Nat} (index : Nat) (node : BooleanNode n) (out : List Bool)
    (ambient : Configuration 1335 z)
    (href : ∀ j,ambient.tapes (generatedRef (referencePorts (kind node) j))=nodeWords index node j ∧
      ambient.heads (generatedRef (referencePorts (kind node) j))=0)
    (hd : ambient.tapes 17=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) true)
    (hl : ambient.tapes 18=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)+1) false)
    (hdh : ambient.heads 17=0) (hlh : ambient.heads 18=0)
    (hw : ∀ i,ambient.tapes (kernelWork i)=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) false ∧
      ambient.heads (kernelWork i)=0)
    (hout : ambient.tapes 1333=out) (houth : ambient.heads 1333=out.length) :
    ∀ i,ambient.tapes (kernelSlots (decide (kind node=2)) i)=
      RecoveryTseitinClauseAppend.input (readyData index node) out (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) i ∧
      ambient.heads (kernelSlots (decide (kind node=2)) i)=RecoveryTseitinClauseAppend.heads out.length i := by
  exact kernel_view_core (kind node) (nodeWords index node)
    (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) out ambient href hd hl hdh hlh hw hout houth

end NearCubicWires.RepairSource.RecoveryTseitinNative
