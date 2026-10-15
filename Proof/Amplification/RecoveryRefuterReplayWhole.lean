import Proof.Amplification.RecoveryRefuterReplayPolynomial

/-! Whole selected-refuter ordinary polynomial replay. It consumes the
actual source and clock, with no local realization or budget-word premise. -/
namespace NearCubicWires.RepairSource.RecoveryRefuterReplay
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem polynomial_runs {T : Nat→Nat} (source : HierarchyRefuterAlgorithm T) (clock : OrdinaryClock T)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M T) :
    ∃ (K E onset : Nat) (p : OrdinaryOracleProgram),1≤K ∧ 1≤E ∧
      ∀ n,onset≤n →
        OrdinaryOracleRuns RecoveryOracle.correctedSat p (List.replicate n true)
          (List.ofFn (source.output M n)) (K*(n+2)^E) ∧
        (M.accepts n (source.output M n) ↔ source.hierarchy.timedView.accepts n (source.output M n)=false) := by
  obtain ⟨C,D,onset,p,_,hrun⟩ := eventual_runs source clock M hM
  let code := VerifierEncoding.code M.verifier
  refine ⟨polynomialCoefficient code C D,polynomialDegree D,onset,p,?_,?_,?_⟩
  · have hpow : 1≤(C+D+code.length+1)^6 := Nat.one_le_pow _ _ (by omega)
    unfold polynomialCoefficient
    omega
  · unfold polynomialDegree
    omega
  · intro n hn
    obtain ⟨h,hconflict⟩ := hrun n hn
    exact ⟨h.enlarge (budget_bound code C D n),hconflict⟩

end NearCubicWires.RepairSource.RecoveryRefuterReplay
