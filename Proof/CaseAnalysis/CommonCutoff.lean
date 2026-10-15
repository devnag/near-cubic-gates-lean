import Proof.CaseAnalysis.HardnessPremises

/-! A single source cutoff makes the recovery clause/arity/fit branches
redundant on every live scheduled input. Lift q-level cutoffs to N-level
powers before choosing the actual prefix onset; retain that SAME onset in
both the ordinary program and the language. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation RepairOrdinary SelectedRecoveryIntegration
open RecoveryScheduleEnvelope CloseoutNativeWidth ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem live_clause_fit (sources : EightSources) (degree copies clauseDegree : Nat)
    (clauses : ClauseReady sources degree clauseDegree) :
    ∃ cutoff, 1 ≤ cutoff ∧ ∀ (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
      (sourceOnset : Nat), cutoff ≤ sourceOnset → ∀ n,
      let s := selectedIndex (widthAt sources k clock copies clauseDegree) n
      ∀ input : BitInput (2^s),
      ∀ oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)),
      oracle.size ≤ oracleSizeBound degree ((outer sources k clock).result.pcp.nativeWidth (2^s)) →
      1 ≤ s ∧ sourceOnset ≤ 2^s →
      let q := (outer sources k clock).result.pcp.nativeWidth (2^s)
      let request := CloseoutWitnessPolicy.request sources k clock input oracle
      request.arity = q ∧
      ((selectedPCPP sources).output request).clauseBits ≤ clauseWidth clauseDegree q ∧
      copies*(request.arity+clauseWidth clauseDegree q+1) ≤ n := by
  obtain ⟨clauseOnset,hclause⟩ := clauses
  let q0 := max clauseOnset (selectedPCPP sources).minimumArity
  refine ⟨2^q0,Nat.one_le_pow _ _ (by decide),?_⟩
  intro k clock sourceOnset hcut n s input oracle hsize hlive q request
  let H := (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy
  have henv : 2^q0 ≤ Dimensions.envelope (fixedProjection sources)
      (HierarchyEncode.length H (padding sources k clock) (2^s)) :=
    (hcut.trans hlive.2).trans ((Nat.le_succ _).trans
      (input_le_envelope (fixedProjection sources) H (padding sources k clock) (2^s)))
  have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2) henv
  have hq0 : q0 ≤ q := hlog.trans (Nat.le_succ _)
  have hmin : (selectedPCPP sources).minimumArity ≤ q := (Nat.le_max_right _ _).trans hq0
  have harity : request.arity = q :=
    CloseoutWitnessPolicy.actual_arity_eq_native sources k clock input oracle hmin
  have hc : ((selectedPCPP sources).output request).clauseBits ≤ clauseWidth clauseDegree q :=
    hclause k clock (2^s) input oracle hsize ((Nat.le_max_left _ _).trans hq0)
  have hselected := selectedIndex_fits (widthAt sources k clock copies clauseDegree) n (by omega)
  have hfit : copies*(request.arity+clauseWidth clauseDegree q+1) ≤ n := by
    rw [harity]
    exact hselected.2.trans (Nat.div_le_self n 2)
  exact ⟨harity,hc,hfit⟩

end
end NearCubicWires.RepairSource.CloseoutLanguage
