import Proof.Gates.GateRecovery.Bundle
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.Language
import Proof.Hierarchy.HierarchyProjectionPrefix

namespace GR

/-! The schedule's native width machine: the bundle's `WidthSource` (`sec:gadget-machine`, the exact native width
`q(N_s)` from `1^{2^s}`). -/
namespace NearCubicWires.RepairSource.CloseoutSchedule
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def nativeMachine (sources : GateEightSources) (_k : Nat)
    (_clock : OrdinaryClock (fun n=>n^(_k+2))) :=
  sources.width.machine

def nativeBudget (sources : GateEightSources) (_k : Nat)
    (_clock : OrdinaryClock (fun n=>n^(_k+2))) (s : Nat) :=
  sources.width.budget s

def nativeInput (sources : GateEightSources) (_k : Nat) (s : Nat) : Fin sources.width.tapes → List Bool :=
  fun i => if i = sources.width.inPort then frame (List.replicate (2 ^ s) true) else []

def nativeRaw (sources : GateEightSources) (_k : Nat) :=
  sources.width.outPort

theorem native_run (sources : GateEightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (s : Nat) : ∃ out,
    ClockJoin.ReadyRun (nativeMachine sources k clock) (nativeBudget sources k clock s)
      (nativeInput sources k s) out ∧
      out (nativeRaw sources k)=List.replicate (sources.width.width s) true :=
  sources.width.run s

end
end NearCubicWires.RepairSource.CloseoutSchedule

end GR
