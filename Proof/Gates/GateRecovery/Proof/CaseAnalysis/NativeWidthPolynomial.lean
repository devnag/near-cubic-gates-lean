import Proof.Gates.GateRecovery.Bundle
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleBounds
import Proof.Foundations.PolynomialSchedule

namespace GR

/-! The dyadic native widths grow at most linearly: `q(N_s) ≤ q(N_0) + jump·s` (`sec:all-lengths`, "The native widths
q(N_ν) have bounded additive jumps"). -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairOrdinary PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem native_dyadic_bound (sources : GateEightSources) (k : Nat)
    (_clock : OrdinaryClock (fun n=>n^(k+2))) (s : Nat) :
    sources.width.width s ≤ sources.width.width 0+sources.width.jump*s := by
  induction s with
  | zero=>simp
  | succ s ih=>
    have h:=sources.width.step s
    nlinarith

theorem native_dyadic_polynomial (sources : GateEightSources) (k : Nat)
    (_clock : OrdinaryClock (fun n=>n^(k+2))) :
    PolynomiallyBounded (fun s=>sources.width.width s) :=
  polynomiallyBounded_mono (native_dyadic_bound sources k _clock)
    (polynomiallyBounded_add (polynomiallyBounded_constant (sources.width.width 0))
      (polynomiallyBounded_mul
        (polynomiallyBounded_constant sources.width.jump)
        polynomiallyBounded_id))

end
end NearCubicWires.RepairSource.CloseoutLanguage

end GR
