import Proof.CaseAnalysis.CaseOneDirectSelectedBound
import Proof.CaseAnalysis.Parameters
import Proof.CaseAnalysis.NativeWidthStep

/-! The live schedule itself supplies every size premise of the complete
Case1 worker. No extra runtime arity test or independent resource choice is
needed at this branch of the common language. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration OrdinaryOracleCompose
open RecoveryScheduleEnvelope CloseoutNativeWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem case_one_live_fits (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (degree copies clauseDegree n : Nat)
    (hcopies : (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies) :
    let source := fixedProjection sources
    let H := (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy
    let amplifier := selectedAmplifier sources.amplification degree
    let pcp := (outer sources k clock).result.pcp
    let s := selectedIndex (widthAt sources k clock copies clauseDegree) n
    ∀ input : BitInput (2^s), 1 ≤ s →
      1 ≤ n ∧ 2^s ≤ 2^n ∧
      HierarchyProjection.width source H (padding sources k clock) (2^s) ≤ n ∧
      (amplifier.output (RecoveryCaseOneRequest.request pcp input).inputArity
        (RecoveryCaseOneRequest.request pcp input).function).arity ≤ n := by
  intro source H amplifier pcp s input hs
  let cb := clauseWidth clauseDegree (pcp.nativeWidth (2^s))
  have hc : 1 ≤ copies := amplifier.arityCoefficientPositive.trans hcopies
  have hsn : s ≤ n := selectedIndex_le _ _
  have hselected := selectedIndex_fits (widthAt sources k clock copies clauseDegree) n (by omega)
  have hwidth : copies*(pcp.nativeWidth (2^s)+cb+1) ≤ n :=
    hselected.2.trans (Nat.div_le_self n 2)
  have hq := native_dyadic_lower source H (padding sources k clock) s
  change s+1 ≤ pcp.nativeWidth (2^s) at hq
  have hR : HierarchyProjection.width source H (padding sources k clock) (2^s) ≤ n := by
    change pcp.nativeWidth (2^s) ≤ n
    have hm := Nat.mul_le_mul_right (pcp.nativeWidth (2^s)+cb+1) hc
    omega
  have hfit := CloseoutParameters.arity_envelope amplifier copies (pcp.nativeWidth (2^s))
    cb hcopies (by omega) (RecoveryCaseOneRequest.request pcp input).function
  exact ⟨by omega, Nat.pow_le_pow_right (by decide) hsn, hR, hfit.trans hwidth⟩

theorem selected_case_one_live (sources : EightSources) (k : Nat)
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
          (CloseoutCaseOneDirect.program source amplifier.constructor.program k H.coefficient
            (padding sources k clock) (VerifierEncoding.code H.verifier)) cost
          (CloseoutCaseOneDirect.input source amplifier.constructor.program k
            (List.ofFn input) (List.ofFn address)) out ∧
        out (CloseoutCaseOneDirect.ports source amplifier.constructor.program k).outputTape =
          frame (core pcp (selectedPCPP sources) amplifier input copies cb n address).toNat.bits := by
  intro source H amplifier pcp s cb input hs hsmall
  obtain ⟨hn, hN, hR, hfit⟩ :=
    case_one_live_fits sources k clock degree copies clauseDegree n hcopies input hs
  exact selected_case_one_bounded sources k clock degree copies cb input address hsmall
    hfit hn hN hR

end
end NearCubicWires.RepairSource.CloseoutLanguage
