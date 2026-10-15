import Proof.Gates.GateRecovery.Bundle
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleNative

namespace GR

/-! The native-width machine's budget is polynomial in `2^s` (the `WidthSource` bound). -/
namespace NearCubicWires.RepairSource.CloseoutSchedule
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem native_budget (sources : GateEightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) :
    ∃ coefficient degree : Nat, ∀ s,
      nativeBudget sources k clock s ≤ coefficient*(2^s+1)^degree :=
  ⟨sources.width.coefficient,sources.width.degree,sources.width.poly⟩

end
end NearCubicWires.RepairSource.CloseoutSchedule

end GR
