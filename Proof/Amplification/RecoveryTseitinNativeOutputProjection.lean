import Proof.Amplification.RecoveryTseitinNativeNodeStep

/-! Project only the physical output port over an abstract receipt carrier;
the native controller's large fixed state cardinality stays opaque. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_head {s : Nat} (r : ExecutionReceipt 1338 s) (pos : Nat) (out : List Bool)
    (h : r.final.heads=heads pos out.length) : r.final.heads 1333=out.length := by
  have hh:=congrFun h 1333
  simpa [heads] using hh
theorem output_tape {s : Nat} (r : ExecutionReceipt 1338 s) (n index : Nat)
    (word out : List Bool) (cap : Nat) (h : r.final.tapes=data n index word out cap) :
    r.final.tapes 1333=out := by
  have ht:=congrFun h 1333
  simpa [data] using ht

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
