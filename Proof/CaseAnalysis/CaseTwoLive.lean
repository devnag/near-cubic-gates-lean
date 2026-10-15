import Proof.CaseAnalysis.HardnessPremises
import Proof.CaseAnalysis.CaseOneLive

/-! One fixed source cutoff supplies all Case2 shape premises on every live
language input. The existing paid onset guard therefore also guards recovery
and the physical fixed-copy consumer at finite lengths. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation RepairOrdinary SelectedRecoveryIntegration
open RecoveryScheduleEnvelope CloseoutNativeWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem case_two_live_cutoff (sources:EightSources) (degree clauseDegree:ℕ)
    (clauses:ClauseReady sources degree clauseDegree):
    ∃ cutoff:ℕ,1 ≤ cutoff ∧
      ∀ (k:ℕ) (clock:OrdinaryClock (fun n=>n^(k+2))) (copies n:ℕ),
      let pcp:=(outer sources k clock).result.pcp
      let s:=selectedIndex (widthAt sources k clock copies clauseDegree) n
      let q:=pcp.nativeWidth (2^s)
      ∀ (input:BitInput (2^s)) (oracle:BooleanCircuit q),
        1 ≤ copies → cutoff ≤ 2^s → oracle.size ≤ oracleSizeBound degree q →
        1 ≤ s ∧ 2^s ≤ 2^n ∧ 1 ≤ q ∧
        (CloseoutWitnessPolicy.request sources k clock input oracle).arity=q ∧
        ((selectedPCPP sources).output (CloseoutWitnessPolicy.request sources k clock input oracle)).clauseBits ≤ 
          clauseWidth clauseDegree q ∧
        copies*((CloseoutWitnessPolicy.request sources k clock input oracle).arity+
          clauseWidth clauseDegree q+1) ≤ n:=by
  obtain ⟨clauseOnset,ready⟩:=clauses
  let s0:=max 1 (max clauseOnset (selectedPCPP sources).minimumArity)
  refine ⟨2^s0,Nat.one_le_pow _ _ (by decide),?_⟩
  intro k clock copies n pcp s q input oracle hc hcut ho
  have hs0:s0 ≤ s:=(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcut
  have hs1:1 ≤ s:=(Nat.le_max_left _ _).trans hs0
  have hsClause:clauseOnset ≤ s:=(Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hs0)
  have hsMinimum:(selectedPCPP sources).minimumArity ≤ s:=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hs0)
  have lower:=native_dyadic_lower (fixedProjection sources)
    (sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy (padding sources k clock) s
  change s+1 ≤ q at lower
  have arity: (CloseoutWitnessPolicy.request sources k clock input oracle).arity=q:=
    CloseoutWitnessPolicy.actual_arity_eq_native sources k clock input oracle
      (by change (selectedPCPP sources).minimumArity ≤ q;omega)
  have clausesReady:=ready k clock (2^s) input oracle ho (by change clauseOnset ≤ q;omega)
  have selected:=selectedIndex_fits (widthAt sources k clock copies clauseDegree) n (by change s≠0;omega)
  have fit:copies*(q+clauseWidth clauseDegree q+1) ≤ n:=
    selected.2.trans (Nat.div_le_self n 2)
  refine ⟨hs1,Nat.pow_le_pow_right (by decide : 0 < 2) (selectedIndex_le _ _),by omega,
    arity,clausesReady,?_⟩
  rw [arity]
  exact fit

end
end NearCubicWires.RepairSource.CloseoutLanguage
