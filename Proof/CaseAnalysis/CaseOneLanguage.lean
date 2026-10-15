import Proof.CaseAnalysis.CaseOneMeaning
import Proof.CaseAnalysis.Language

/-! The original-word ordinary Case-1 program computes the exact Case-1
branch of the same common language core. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem selected_case_one_runs (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (degree copies clauseBits : Nat)
    {n target : Nat} (input : BitInput n) (address : BitInput target) :
    let source:=fixedProjection sources
    let H:=(sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
    let amplifier:=selectedAmplifier sources.amplification degree
    let pcp:=(outer sources k clock).result.pcp
    ∀ (_hsmall : ¬RecoveryChoice.SmallOracle pcp degree input)
      (hfit : (amplifier.output (RecoveryCaseOneRequest.request pcp input).inputArity
        (RecoveryCaseOneRequest.request pcp input).function).arity ≤ target),
      OrdinaryOracleRuns RecoveryOracle.correctedSat
        (RecoveryCaseOnePaddedOrdinary.program source amplifier.constructor.program k H.coefficient
          (padding sources k clock) (VerifierEncoding.code H.verifier))
        (RecoveryCaseOnePaddedOrdinary.word H ⟨n,input⟩ (List.ofFn address))
        (core pcp (selectedPCPP sources) amplifier input copies clauseBits target address).toNat.bits
        (RecoveryCaseOnePaddedOrdinary.budget source amplifier H (padding sources k clock)
          (Nat.le_max_right _ _) ⟨n,input⟩ hfit address) := by
  intro source H amplifier pcp hsmall hfit
  rw [core_case_one pcp (selectedPCPP sources) amplifier input copies clauseBits target hsmall hfit]
  exact RecoveryCaseOnePaddedOrdinary.ordinary_runs source amplifier H (padding sources k clock)
    (Nat.le_max_right _ _) ⟨n,input⟩ hfit address

end
end NearCubicWires.RepairSource.CloseoutLanguage
