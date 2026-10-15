import Proof.Foundations.VerifierEncoding
import Proof.Foundations.RecoverySourceSAT
import Proof.Foundations.RecoveryOracleContracts
import Proof.Foundations.RecoveryCaseOne

/-! CLW4.6 at the ordinary hierarchy and its actual promised refuter domain.
The algorithm is retained, including the literal finite verifier description
and all query costs. Its guarantee is eventual for each fixed legal weak
machine. Clocking/totalization and finite exceptions in recovery are local.
This source does not promise a runner on arbitrary unbounded raw requests. -/
namespace NearCubicWires.RepairSource
open SourceInterfaces ExecutableInterfaces LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def refuterInput (M : OrdinaryWeakMachine) (n : ℕ) : List Bool :=
  frame (VerifierEncoding.code M.verifier) ++ frame (List.replicate n true)

structure HierarchyRefuterAlgorithm (T : ℕ → ℕ) where
  hierarchy : OrdinaryHierarchy T
  output : OrdinaryWeakMachine → (n : ℕ) → BitInput n
  program : OrdinaryOracleProgram
  coefficient : ℕ
  degree : ℕ
  coefficientPositive : 0 < coefficient
  eventual : ∀ M, OrdinaryLittleO M T → ∃ onset, ∀ n, onset ≤ n →
    OrdinaryOracleRuns RecoveryOracle.sourceSAT program (refuterInput M n)
      (List.ofFn (output M n))
      (coefficient * (T n + n + (VerifierEncoding.code M.verifier).length + 1) ^ degree) ∧
    (M.accepts n (output M n) ↔ hierarchy.timedView.accepts n (output M n) = false)

/-- A sufficient restriction of CLW's printed time-constructible domain:
the paper ultimately selects an explicit polynomial power clock. The
ordinary clock computer is a hypothesis, never a semantic step annotation. -/
def HierarchyRefuterSource : Prop :=
  ∀ T : ℕ → ℕ, OrdinaryClock T → Nonempty (HierarchyRefuterAlgorithm T)

def HierarchyRefuterAlgorithm.joint {T : ℕ → ℕ}
    (source : HierarchyRefuterAlgorithm T) : JointOrdinarySource T where
  hierarchy := source.hierarchy
  refuter :=
    { output := source.output
      separates := by
        intro M hM
        obtain ⟨onset, result⟩ := source.eventual M hM
        exact ⟨onset, fun n hn => (result n hn).2⟩ }

/-- Exact fixed-machine specialization: description length belongs to the
coefficient once M is frozen. The degree and actual program do not change. -/
theorem refuter_fixed_machine_budget (C d degree t n : ℕ) (hn : n ≤ t) :
    C * (t + n + d + 1) ^ degree ≤
      (C * (d + 3) ^ degree) * (t + 1) ^ degree := by
  have h : t + n + d + 1 ≤ (d + 3) * (t + 1) := by nlinarith
  calc
    _ ≤ C * ((d + 3) * (t + 1)) ^ degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h degree)
    _ = _ := by rw [mul_pow]; ring

/-- Both the semantic contradiction and the oracle receipt refer to the same
output of the same selected source program, after one common eventual onset. -/
theorem hierarchy_refuter_call {T : ℕ → ℕ}
    (source : HierarchyRefuterAlgorithm T) (clock : OrdinaryClock T)
    (M : OrdinaryWeakMachine) (littleO : OrdinaryLittleO M T) :
    ∃ onset, ∀ n, onset ≤ n →
      OrdinaryOracleRuns RecoveryOracle.sourceSAT source.program (refuterInput M n)
        (List.ofFn (source.output M n))
        ((source.coefficient * ((VerifierEncoding.code M.verifier).length + 3) ^ source.degree) *
          (T n + 1) ^ source.degree) ∧
      (M.accepts n (source.output M n) ↔
        source.hierarchy.timedView.accepts n (source.output M n) = false) := by
  obtain ⟨onset, result⟩ := source.eventual M littleO
  refine ⟨onset, ?_⟩
  intro n hn
  obtain ⟨hrun, conflict⟩ := result n hn
  exact ⟨hrun.enlarge (refuter_fixed_machine_budget _ _ _ _ _ (clock.atLeastInput n)), conflict⟩

/-- Enclosing source application. Only the actual selected hierarchy's local
PCP realization and the eventual ordinary competitor remain as suppliers. -/
theorem hierarchy_source_scheduled_recovery {T : ℕ → ℕ}
    (source : HierarchyRefuterAlgorithm T) (degrees : PCPDegrees)
    (outer : ChangedHierarchyOuterPCP source.joint degrees)
    (M : OrdinaryWeakMachine) (littleO : OrdinaryLittleO M T)
    (oneSided : ∀ n x, M.accepts n x → source.hierarchy.timedView.accepts n x = true)
    (amplifier : SourceAmplifierFactory) (d : ℕ) :
    ∃ onset, ∀ n, onset ≤ n → 1 ≤ outer.result.pcp.nativeWidth n →
      Nonempty (ScheduledOuterCase outer.result.pcp
        (selectedAmplifier amplifier d).toScheduleAmplifier (source.output M n)) :=
  ordinaryRefuterScheduledRecovery source.joint degrees outer M littleO oneSided amplifier d

end NearCubicWires.RepairSource
