import Proof.CaseAnalysis.HardnessPremises

/-! One top-down binding closes both eventual circuit-class conclusions
from the SAME legal weak machine and its exact dyadic sampled completeness.
The physical machine, total runtime and little-o remain producer obligations. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation RepairOrdinary SelectedRecoveryIntegration
open RecoveryScheduleEnvelope CloseoutNativeWidth CloseoutCaseOne CircuitRestriction
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem hardness_pair (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2)))
    (M : OrdinaryWeakMachine) (littleO : OrdinaryLittleO M (fun n => n^(k+2)))
    (oneSided : ∀ n x, M.accepts n x →
      (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy.timedView.accepts n x = true)
    (degree copies clauseDegree sourceOnset : Nat)
    (hdegree : 17*sources.amplification.stvExponent ≤ degree)
    (hcopies : (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies)
    (clauses : ClauseReady sources degree clauseDegree)
    (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2)
    (gamma : ℝ) (hg : 0 < gamma) (heps : xorEpsilon (delta : ℝ) copies < gamma)
    (symCap thrCap : ℝ) (hsym : 0 < symCap) (hthr : 0 < thrCap)
    (completeSym : SampledCompleteness sources k clock M degree copies clauseDegree
      delta symmetricWireFamily 5 symCap)
    (completeThr : SampledCompleteness sources k clock M degree copies clauseDegree
      delta thresholdWireFamily 9 thrCap) :
    let factor := 3*(copies*(2*clauseDegree+2))+2
    let symC := headlineCoefficient symCap factor
    let thrC := headlineCoefficient thrCap factor
    0 < symC ∧ 0 < thrC ∧ ∃ onset, ∀ n, onset ≤ n →
      (∀ circuit : SymmetricThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤ wireScale symC 5 n →
        agreement circuit.eval (language sources k clock M degree copies clauseDegree sourceOnset n) < 1/2+gamma) ∧
      (∀ circuit : ThresholdThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤ wireScale thrC 9 n →
        agreement circuit.eval (language sources k clock M degree copies clauseDegree sourceOnset n) < 1/2+gamma) := by
  intro factor symC thrC
  let H := sources.hierarchy (fun n => n^(k+2)) clock
  let pcp := (outer sources k clock).result.pcp
  have hf : 0 < factor := by dsimp [factor]; omega
  have hsc : 0 < symC := headlineCoefficient_positive symCap factor hsym hf
  have htc : 0 < thrC := headlineCoefficient_positive thrCap factor hthr hf
  have hcopies1 : 1 ≤ copies :=
    (selectedAmplifier sources.amplification degree).arityCoefficientPositive.trans hcopies
  obtain ⟨oneOnset,oneReady⟩ := case_one_eventual sources k clock M littleO oneSided
    degree copies clauseDegree sourceOnset hdegree hcopies gamma hg symC thrC
    hsc.le (headlineCoefficient_le_one _ _) htc.le (headlineCoefficient_le_one _ _)
  obtain ⟨refOnset,refReady⟩ := actualRefuterPCPRecoveryJoin H.joint _
    (outer sources k clock) M littleO oneSided
  obtain ⟨clauseOnset,clauseReady⟩ := clauses
  obtain ⟨symOnset,symReady⟩ := completeSym
  obtain ⟨thrOnset,thrReady⟩ := completeThr
  let s0 := max 1 (sourceOnset+refOnset+clauseOnset+symOnset+thrOnset+
    (selectedPCPP sources).minimumArity)
  obtain ⟨scheduleOnset,scheduleReady⟩ := schedule_onset sources k clock copies clauseDegree s0
    hcopies1 (Nat.le_max_left _ _)
  refine ⟨hsc,htc,max oneOnset scheduleOnset,?_⟩
  intro n hn
  let s := selectedIndex (widthAt sources k clock copies clauseDegree) n
  let input := H.output M (2^s)
  by_cases hsmall : RecoveryChoice.SmallOracle pcp degree input
  · obtain ⟨hs,hlo,hhi⟩ := scheduleReady n ((Nat.le_max_right _ _).trans hn)
    have hsum : sourceOnset+refOnset+clauseOnset+symOnset+thrOnset+
        (selectedPCPP sources).minimumArity ≤ s := (Nat.le_max_right _ _).trans hs
    have hs1 : 1 ≤ s := (Nat.le_max_left _ _).trans hs
    have hsN : s ≤ 2^s := (Nat.lt_two_pow_self : s < 2^s).le
    let q := pcp.nativeWidth (2^s)
    have hq := native_dyadic_lower (fixedProjection sources) H.hierarchy (padding sources k clock) s
    change s+1 ≤ q at hq
    change n/3 ≤ coreWidth copies clauseDegree q at hlo
    change coreWidth copies clauseDegree q ≤ n/2 at hhi
    have hqn : q ≤ n := (core_lower copies clauseDegree q hcopies1).trans
      (hhi.trans (Nat.div_le_self n 2))
    have hnq : n ≤ factor*q := length_native_factor copies clauseDegree q n (by omega) hlo
    let oracle := (RecoveryChoice.oracleSelector pcp degree input hsmall).circuit
    let request := CloseoutWitnessPolicy.request sources k clock input oracle
    let pcpp := (selectedPCPP sources).output request
    have hc : pcpp.clauseBits ≤ clauseWidth clauseDegree q :=
      clauseReady k clock (2^s) input oracle
        (RecoveryChoice.oracleSelector pcp degree input hsmall).sizeBounded (by change clauseOnset ≤ q; omega)
    have harity : request.arity = q :=
      CloseoutWitnessPolicy.actual_arity_eq_native sources k clock input oracle (by change (selectedPCPP sources).minimumArity ≤ q; omega)
    have hfit : copies*(request.arity+clauseWidth clauseDegree q+1) ≤ n := by
      rw [harity]
      exact hhi.trans (Nat.div_le_self n 2)
    have hreject : ¬ M.accepts (2^s) input := (refReady (2^s) (by omega)).1
    have hsCap := headline_cap_transfer symCap factor 5 q n hsym.le hf hqn hnq
    have htCap := headline_cap_transfer thrCap factor 9 q n hthr.le hf hqn hnq
    have hhard := case_two_direct_hardness pcp (selectedPCPP sources)
      (selectedAmplifier sources.amplification degree) input copies (clauseWidth clauseDegree q) n
      ⌊wireScale symC 5 n⌋₊ ⌊wireScale thrC 9 n⌋₊ hcopies1
      sources.refuterXor.xor delta hd hh gamma heps hsmall hc hfit
      (fun w => hreject (symReady s (by omega) input hsmall hc (symmetric_sampled_weaken hsCap w)))
      (fun w => hreject (thrReady s (by omega) input hsmall hc (threshold_sampled_weaken htCap w)))
    have heq : language sources k clock M degree copies clauseDegree sourceOnset n =
        core pcp (selectedPCPP sources) (selectedAmplifier sources.amplification degree)
          input copies (clauseWidth clauseDegree q) n := by
      funext address
      change (if 1 ≤ s ∧ sourceOnset ≤ 2^s then _ else false) = _
      rw [if_pos ⟨hs1,by omega⟩]
    rw [heq]
    exact ⟨fun circuit hcap => hhard.1 circuit (Nat.le_floor hcap),
      fun circuit hcap => hhard.2 circuit (Nat.le_floor hcap)⟩
  · exact oneReady n ((Nat.le_max_left _ _).trans hn) hsmall

end
end NearCubicWires.RepairSource.CloseoutLanguage
