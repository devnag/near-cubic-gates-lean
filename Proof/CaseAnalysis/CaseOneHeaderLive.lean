import Proof.CaseAnalysis.CaseOneLive

/-! Consume the shared hierarchy request retained by the common SAT dispatch.
The existing Case1 worker uses that word directly; the live schedule supplies
all fits, and the already-paid direct envelope bounds its entire execution. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration OrdinaryOracleCompose
open RecoveryScheduleEnvelope ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem selected_case_one_header_live (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (degree copies clauseDegree : Nat)
    (hcopies : (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies)
    {n : Nat} (address : BitInput n) :
    let source := fixedProjection sources
    let H := (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy
    let amplifier := selectedAmplifier sources.amplification degree
    let pcp := (outer sources k clock).result.pcp
    let s := selectedIndex (widthAt sources k clock copies clauseDegree) n
    let cb := clauseWidth clauseDegree (pcp.nativeWidth (2^s))
    ∀ input : BitInput (2^s), 1 ≤ s →
      ¬RecoveryChoice.SmallOracle pcp degree input →
      ∃ cost ≤ CloseoutCaseOne.directCoefficient source H (padding sources k clock)*
          (2^n+1)^CloseoutCaseOne.directExponent source k amplifier.constructionExponent,
        ∃ out, Ready RecoveryOracle.correctedSat
          (RecoveryCaseOnePaddedBit.program source amplifier.constructor.program k H.coefficient
            (padding sources k clock) (VerifierEncoding.code H.verifier)) cost
          (RecoveryCaseOnePaddedBit.input source amplifier.constructor.program k
            (HierarchySourceInput.hierarchyInput H ⟨2^s, input⟩) (List.ofFn address)) out ∧
        out (RecoveryCaseOnePaddedBit.ports source amplifier.constructor.program k).outputTape =
          frame (core pcp (selectedPCPP sources) amplifier input copies cb n address).toNat.bits := by
  intro source H amplifier pcp s cb input hs hsmall
  obtain ⟨hn, hN, hR, hfit⟩ :=
    case_one_live_fits sources k clock degree copies clauseDegree n hcopies input hs
  obtain ⟨cost, hcost, out, hrun, hout⟩ := RecoveryCaseOnePaddedBit.bit_ready source amplifier H
    (padding sources k clock) (Nat.le_max_right _ _) ⟨2^s, input⟩ hfit address
  have hb := CloseoutCaseOne.direct_budget_bound source amplifier H (padding sources k clock)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) ⟨2^s, input⟩ hn hN hR hfit address
  have hle : RecoveryCaseOnePaddedBit.budget source amplifier H (padding sources k clock)
      (Nat.le_max_right _ _) ⟨2^s, input⟩ hfit address ≤
      CloseoutCaseOneDirect.budget source amplifier H (padding sources k clock)
        (Nat.le_max_right _ _) ⟨2^s, input⟩ hfit address := Nat.le_add_left _ _
  refine ⟨cost, hcost.trans (hle.trans hb), out, hrun, ?_⟩
  rw [core_case_one pcp (selectedPCPP sources) amplifier input copies cb n hsmall hfit]
  exact hout

end
end NearCubicWires.RepairSource.CloseoutLanguage
