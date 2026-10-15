import Proof.Amplification.RecoveryTseitinNativeKernelViewActual

/-! Driver equalities are checked at an abstract capacity before the physical
large capacity is substituted. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem view_driver (refs : Fin 3→List Bool) (cap : Nat) : viewData refs cap 3=List.replicate cap true := rfl
theorem view_log (refs : Fin 3→List Bool) (cap : Nat) : viewData refs cap 4=List.replicate (cap+1) false := rfl
theorem ready_driver {n : Nat} (index : Nat) (node : BooleanNode n) :
    readyData index node 3=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) true :=
  view_driver (nodeWords index node) (RecoveryTseitinTautology.Cold.driverCapacity (n+index))
theorem ready_log {n : Nat} (index : Nat) (node : BooleanNode n) :
    readyData index node 4=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)+1) false :=
  view_log (nodeWords index node) (RecoveryTseitinTautology.Cold.driverCapacity (n+index))

end NearCubicWires.RepairSource.RecoveryTseitinNative
