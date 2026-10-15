import Proof.CaseAnalysis.CaseOneHardness

/-! Close Case 1 at the literal selected source, refuter output and length
schedule. All numeric/source onsets are chosen once, after fixed parameters. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairOrdinary SelectedRecoveryIntegration CloseoutCaseOne
open RecoveryScheduleEnvelope CloseoutNativeWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem case_one_eventual (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2)))
    (machine : OrdinaryWeakMachine) (littleO : OrdinaryLittleO machine (fun n=>n^(k+2)))
    (oneSided : ∀ n x, machine.accepts n x →
      (sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy.timedView.accepts n x=true)
    (degree copies clauseDegree sourceOnset : Nat)
    (hd : 17*sources.amplification.stvExponent ≤ degree)
    (hcopies : (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies)
    (gamma : ℝ) (hg : 0 < gamma)
    (symmetricCoefficient thresholdCoefficient : ℝ)
    (hs0 : 0 ≤ symmetricCoefficient) (hs1 : symmetricCoefficient ≤ 1)
    (ht0 : 0 ≤ thresholdCoefficient) (ht1 : thresholdCoefficient ≤ 1) :
    ∃ onset, ∀ n, onset ≤ n →
      let s:=selectedIndex (widthAt sources k clock copies clauseDegree) n
      let input:=(sources.hierarchy (fun n=>n^(k+2)) clock).output machine (2^s)
      ¬RecoveryChoice.SmallOracle (outer sources k clock).result.pcp degree input →
      (∀ circuit : SymmetricThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤ wireScale symmetricCoefficient 5 n →
        agreement circuit.eval (language sources k clock machine degree copies clauseDegree sourceOnset n) < 1/2+gamma) ∧
      (∀ circuit : ThresholdThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤ wireScale thresholdCoefficient 9 n →
        agreement circuit.eval (language sources k clock machine degree copies clauseDegree sourceOnset n) < 1/2+gamma) := by
  let H:=sources.hierarchy (fun n=>n^(k+2)) clock
  let pcp:=(outer sources k clock).result.pcp
  let amplifier:=selectedAmplifier sources.amplification degree
  let factor:=3*(copies*(2*clauseDegree+2))+2
  have hc:=sources.amplification.stvExponentPositive
  have hcopies1 : 1 ≤ copies := amplifier.arityCoefficientPositive.trans hcopies
  obtain ⟨refOnset,refReady⟩:=actualRefuterPCPRecoveryJoin H.joint _
    (outer sources k clock) machine littleO oneSided
  obtain ⟨advOnset,_,advReady⟩:=advantage_onset sources.amplification.stvExponent degree
    hc (by omega) gamma hg
  let s0:=max 1 (sourceOnset+refOnset+advOnset+factor^16)
  obtain ⟨scheduleOnset,scheduleReady⟩:=schedule_onset sources k clock copies clauseDegree s0
    hcopies1 (Nat.le_max_left _ _)
  refine ⟨max scheduleOnset 6,?_⟩
  intro n hn s input hsmall
  obtain ⟨hs,hlo,hhi⟩:=scheduleReady n ((Nat.le_max_left _ _).trans hn)
  have hsum : sourceOnset+refOnset+advOnset+factor^16 ≤ s :=
    (Nat.le_max_right _ _).trans hs
  have hsIndex : 1 ≤ s := (Nat.le_max_left _ _).trans hs
  have hsN : s ≤ 2^s := (Nat.lt_two_pow_self : s < 2^s).le
  have hq:=native_dyadic_lower (fixedProjection sources) H.hierarchy
    (padding sources k clock) s
  change s+1 ≤ pcp.nativeWidth (2^s) at hq
  have hcomplete:= (refReady (2^s) (by omega)).2
  have hfitCore:=CloseoutParameters.arity_envelope amplifier copies
    (pcp.nativeWidth (2^s)) (clauseWidth clauseDegree (pcp.nativeWidth (2^s))) hcopies (by omega)
    (RecoveryCaseOneRequest.request pcp input).function
  have hfit : (amplifier.output (RecoveryCaseOneRequest.request pcp input).inputArity
      (RecoveryCaseOneRequest.request pcp input).function).arity ≤ n :=
    hfitCore.trans (hhi.trans (Nat.div_le_self n 2))
  have hnq : n ≤ factor*pcp.nativeWidth (2^s) := length_native_factor copies clauseDegree _ n (by omega) hlo
  have hs50:=simulation_bound sources.amplification.stvExponent degree factor n (pcp.nativeWidth (2^s)) 5
    hc (by omega) ((Nat.le_max_right _ _).trans hn) hnq (by omega) hd hs0 hs1
  have ht50:=simulation_bound sources.amplification.stvExponent degree factor n (pcp.nativeWidth (2^s)) 9
    hc (by omega) ((Nat.le_max_right _ _).trans hn) hnq (by omega) hd ht0 ht1
  have hh:=core_hardness pcp (selectedPCPP sources) amplifier input copies
    (clauseWidth clauseDegree (pcp.nativeWidth (2^s))) n
    ⌊wireScale symmetricCoefficient 5 n⌋₊ ⌊wireScale thresholdCoefficient 9 n⌋₊
    sources.normalization (by omega) hcomplete hsmall hfit
    ((Nat.mul_le_mul_right _ (by decide : 40 ≤ 50)).trans hs50) ht50 gamma
    (advReady _ (by omega))
  have heq : language sources k clock machine degree copies clauseDegree sourceOnset n=
      core pcp (selectedPCPP sources) amplifier input copies
        (clauseWidth clauseDegree (pcp.nativeWidth (2^s))) n := by
    funext address
    change (if 1 ≤ s ∧ sourceOnset ≤ 2^s then _ else false)=_
    rw [if_pos ⟨hsIndex,by omega⟩]
  rw [heq]
  exact ⟨fun circuit hcap=>hh.1 circuit (Nat.le_floor hcap),
    fun circuit hcap=>hh.2 circuit (Nat.le_floor hcap)⟩

end
end NearCubicWires.RepairSource.CloseoutLanguage
