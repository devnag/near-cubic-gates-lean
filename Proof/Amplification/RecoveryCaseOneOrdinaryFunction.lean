import Proof.Amplification.RecoveryCaseOneOrdinaryRun

/-! The Case-1 bit computation is one ordinary-oracle word function.
Its program is fixed before the hierarchy request and address are given. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneOrdinary
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
variable {c d k : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
  (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad)

def Request := Σ r : InputRequest,BitInput (RecoveryCaseOneBit.generated source amplifier H Cpad hpad r).arity

def function : OrdinaryOracleWordFunction RecoveryOracle.correctedSat
    (Request source amplifier H Cpad hpad)
    (fun request=>word H request.1 (List.ofFn request.2))
    (fun request=>((RecoveryCaseOneBit.generated source amplifier H Cpad hpad request.1).function request.2).toNat.bits)
    (fun request=>budget source amplifier H Cpad hpad request.1 request.2) where
  program := program source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)
  realizes request := ordinary_runs source amplifier H Cpad hpad request.1 request.2

end
end NearCubicWires.RepairSource.RecoveryCaseOneOrdinary
