import Proof.Hierarchy.HierarchyNormalizedRealization
import Proof.Amplification.RecoveryRefuterReplayWhole
import Proof.Foundations.SourceRegistry

/-! Early integration at the actual fixed-U source, normalized outer PCP and
selected ordinary refuter. The legal weak machine remains an explicit local
input; this theorem does not assert the repaired headline. -/
namespace NearCubicWires.RepairSource.SelectedRecoveryIntegration
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def fixedProjection (sources : EightSources) := UWhole.projectionSource sources.pcp.projection
def padding (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n => n^(k+2))) :=
  max (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy.coefficient (k+3)
def outer (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n => n^(k+2))) :=
  HierarchyNormalized.outer (fixedProjection sources)
    (sources.hierarchy (fun n => n^(k+2)) clock).joint (padding sources k clock)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem runs_and_cases (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2)))
    (M : OrdinaryWeakMachine) (littleO : OrdinaryLittleO M (fun n => n^(k+2)))
    (oneSided : ∀ n x, M.accepts n x →
      (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy.timedView.accepts n x=true)
    (d : ℕ) :
    ∃ (K E onset : ℕ) (p : OrdinaryOracleProgram), 1 ≤ K ∧ 1 ≤ E ∧
      ∀ n, onset ≤ n →
        OrdinaryOracleRuns RecoveryOracle.correctedSat p (List.replicate n true)
          (List.ofFn ((sources.hierarchy (fun n => n^(k+2)) clock).output M n))
          (K*(n+2)^E) ∧
        ¬M.accepts n ((sources.hierarchy (fun n => n^(k+2)) clock).output M n) ∧
        (1 ≤ (outer sources k clock).result.pcp.nativeWidth n →
          Nonempty (ScheduledOuterCase (outer sources k clock).result.pcp
            (selectedAmplifier sources.amplification d).toScheduleAmplifier
            ((sources.hierarchy (fun n => n^(k+2)) clock).output M n))) := by
  obtain ⟨K,E,runOnset,p,hK,hE,hrun⟩ := RecoveryRefuterReplay.polynomial_runs
    (sources.hierarchy (fun n => n^(k+2)) clock) clock M littleO
  obtain ⟨caseOnset,hcase⟩ := registered_scheduled_recovery sources
    (fun n => n^(k+2)) clock _ (outer sources k clock) M littleO oneSided d
  refine ⟨K,E,max runOnset caseOnset,p,hK,hE,?_⟩
  intro n hn
  obtain ⟨hr,hconflict⟩ := hrun n ((Nat.le_max_left _ _).trans hn)
  refine ⟨hr,?_,fun hq => hcase n ((Nat.le_max_right _ _).trans hn) hq⟩
  intro hm
  have ht := oneSided n _ hm
  have hf := hconflict.mp hm
  rw [ht] at hf
  contradiction

end
end NearCubicWires.RepairSource.SelectedRecoveryIntegration
