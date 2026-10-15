import Proof.Amplification.RecoveryRefuterReplayBounds

/-! Execute the selected hierarchy refuter from actual unary length,
including physical fixed-code/budget production and every translated query.
The same output is retained in its eventual hierarchy-conflict theorem. -/
namespace NearCubicWires.RepairSource.RecoveryRefuterReplay
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (code : List Bool) (C D n : Nat) :=
  16*(OrdinarySourceSATLift.Request.budget code C D n+
    1099511627776*(C*(n+1)^D+(OrdinarySourceSATLift.Request.sourceInput code n).length+1)^3+1)

theorem eventual_runs {T : Nat→Nat} (source : HierarchyRefuterAlgorithm T) (clock : OrdinaryClock T)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M T) :
    ∃ (C D onset : Nat) (p : OrdinaryOracleProgram),1≤C ∧
      ∀ n,onset≤n →
        OrdinaryOracleRuns RecoveryOracle.correctedSat p (List.replicate n true)
          (List.ofFn (source.output M n)) (budget (VerifierEncoding.code M.verifier) C D n) ∧
        (M.accepts n (source.output M n) ↔ source.hierarchy.timedView.accepts n (source.output M n)=false) := by
  obtain ⟨clockC,clockD,_,hclock⟩ := clock.polynomial
  let code := VerifierEncoding.code M.verifier
  let C := coefficient source.coefficient source.degree code.length clockC
  let D := degree source.degree clockD
  obtain ⟨onset,hsource⟩ := source.eventual M hM
  refine ⟨C,D,onset,OrdinarySourceSATLift.Request.refuter source.program code C D,?_,?_⟩
  · apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.ne_of_gt
    exact Nat.mul_pos (Nat.mul_pos source.coefficientPositive
      (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
  · intro n hn
    obtain ⟨hr,hconflict⟩ := hsource n hn
    have hb : source.coefficient*(T n+n+code.length+1)^source.degree≤C*(n+1)^D :=
      source_bound source.coefficient source.degree code.length clockC clockD (T n) n
        (clock.atLeastInput n) (hclock n)
    have hrun := OrdinarySourceSATLift.Request.source_runs code C D n (hr.enlarge hb)
    exact ⟨hrun,hconflict⟩

end NearCubicWires.RepairSource.RecoveryRefuterReplay
