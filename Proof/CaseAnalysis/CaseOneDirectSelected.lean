import Proof.CaseAnalysis.CaseOneDirect
import Proof.CaseAnalysis.CaseOneLanguage

/-! The direct original-input worker computes the Case1 branch of the SAME
selected common core. This is the physical branch consumed by final assembly. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem selected_case_one_direct (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k + 2))) (degree copies clauseBits : Nat)
    {n target : Nat} (input : BitInput n) (address : BitInput target) :
    let source := fixedProjection sources
    let H := (sources.hierarchy (fun n => n^(k + 2)) clock).hierarchy
    let amplifier := selectedAmplifier sources.amplification degree
    let pcp := (outer sources k clock).result.pcp
    ∀ (_hsmall : ¬RecoveryChoice.SmallOracle pcp degree input)
      (hfit : (amplifier.output (RecoveryCaseOneRequest.request pcp input).inputArity
        (RecoveryCaseOneRequest.request pcp input).function).arity ≤ target),
      ∃ cost ≤ CloseoutCaseOneDirect.budget source amplifier H (padding sources k clock)
          (Nat.le_max_right _ _) ⟨n, input⟩ hfit address, ∃ out,
        Ready RecoveryOracle.correctedSat
          (CloseoutCaseOneDirect.program source amplifier.constructor.program k H.coefficient
            (padding sources k clock) (VerifierEncoding.code H.verifier)) cost
          (CloseoutCaseOneDirect.input source amplifier.constructor.program k
            (List.ofFn input) (List.ofFn address)) out ∧
        out (CloseoutCaseOneDirect.ports source amplifier.constructor.program k).outputTape =
          frame (core pcp (selectedPCPP sources) amplifier input copies clauseBits target address).toNat.bits := by
  intro source H amplifier pcp hsmall hfit
  rw [core_case_one pcp (selectedPCPP sources) amplifier input copies clauseBits target hsmall hfit]
  exact CloseoutCaseOneDirect.direct_ready source amplifier H (padding sources k clock)
    (Nat.le_max_right _ _) ⟨n, input⟩ hfit address

end
end NearCubicWires.RepairSource.CloseoutLanguage
