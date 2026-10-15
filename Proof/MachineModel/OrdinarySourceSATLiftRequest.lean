import Proof.MachineModel.OrdinarySourceSATLiftRequestBound
import Proof.MachineModel.OrdinaryOracleCompose

/-! Closed physical selected-refuter requests from actual unary N. The fixed
word and polynomial coefficients are explicit program parameters. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem runs (code : List Bool) (C D n : ℕ) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat (program code C D) (List.replicate n true)
      (value code C D n) (budget code C D n) := by
  obtain ⟨data,hprepare,ready⟩ := cold_prepare code C D n
  obtain ⟨used,final,hused,trace,halted,output⟩ := emit code C D n (fun _ => 0) data ready
  obtain ⟨before,hbefore,prefixTrace⟩ := hprepare
  refine ⟨before+used,final,?_,OrdinaryOracleCompose.trans prefixTrace trace,halted,output⟩
  exact (show before+used ≤ prepareBudget C D n+emitBudget code C D n by omega).trans
    (ledger_bound code C D n)

noncomputable def refuter (p : OrdinaryOracleProgram) (code : List Bool) (C D : ℕ) :
    OrdinaryOracleProgram := compose (program code C D) (lifted p)

theorem source_runs {p : OrdinaryOracleProgram} (code : List Bool) (C D n : ℕ) {output : List Bool}
    (h : OrdinaryOracleRuns RecoveryOracle.sourceSAT p (sourceInput code n) output (C*(n+1)^D)) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat (refuter p code C D) (List.replicate n true) output
      (16*(budget code C D n+1099511627776*(C*(n+1)^D+(sourceInput code n).length+1)^3+1)) := by
  exact compose_runs (runs code C D n) (lifted_runs h)

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
