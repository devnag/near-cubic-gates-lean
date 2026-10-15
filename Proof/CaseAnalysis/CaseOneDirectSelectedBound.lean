import Proof.CaseAnalysis.CaseOneDirectBound
import Proof.CaseAnalysis.CaseOneDirectSelected

/-! The same selected Case1 core is computed by the complete direct worker
within its one source-fixed C.12 envelope at the actual final address. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem selected_case_one_bounded (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k + 2))) (degree copies clauseBits : Nat)
    {n target : Nat} (input : BitInput n) (address : BitInput target) :
    let source := fixedProjection sources
    let H := (sources.hierarchy (fun n => n^(k + 2)) clock).hierarchy
    let amplifier := selectedAmplifier sources.amplification degree
    let pcp := (outer sources k clock).result.pcp
    ∀ (_hsmall : ¬RecoveryChoice.SmallOracle pcp degree input)
      (_hfit : (amplifier.output (RecoveryCaseOneRequest.request pcp input).inputArity
        (RecoveryCaseOneRequest.request pcp input).function).arity ≤ target)
      (_hpos : 1 ≤ target) (_hN : n ≤ 2^target)
      (_hR : HierarchyProjection.width source H (padding sources k clock) n ≤ target),
      ∃ cost ≤ CloseoutCaseOne.directCoefficient source H (padding sources k clock)*
          (2^target+1)^CloseoutCaseOne.directExponent source k amplifier.constructionExponent,
        ∃ out, Ready RecoveryOracle.correctedSat
          (CloseoutCaseOneDirect.program source amplifier.constructor.program k H.coefficient
            (padding sources k clock) (VerifierEncoding.code H.verifier)) cost
          (CloseoutCaseOneDirect.input source amplifier.constructor.program k
            (List.ofFn input) (List.ofFn address)) out ∧
        out (CloseoutCaseOneDirect.ports source amplifier.constructor.program k).outputTape =
          frame (core pcp (selectedPCPP sources) amplifier input copies clauseBits target address).toNat.bits := by
  intro source H amplifier pcp hsmall hfit hpos hN hR
  obtain ⟨cost, hcost, out, hrun, hout⟩ :=
    selected_case_one_direct sources k clock degree copies clauseBits input address hsmall hfit
  refine ⟨cost, hcost.trans ?_, out, hrun, hout⟩
  exact CloseoutCaseOne.direct_budget_bound source amplifier H (padding sources k clock)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) ⟨n, input⟩ hpos hN hR hfit address

end
end NearCubicWires.RepairSource.CloseoutLanguage
