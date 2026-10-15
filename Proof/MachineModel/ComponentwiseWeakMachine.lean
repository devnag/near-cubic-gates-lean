import Proof.Foundations.ComponentwiseValidity
import Proof.Foundations.ComponentwiseVerifierParameters

/-!
# One-sided componentwise weak-machine ledger

This module is the last source-independent step in Appendix C.10.  An
accepting verifier branch on a hierarchy-NO input must expose the three
quantities it actually checked: rounded clause mean, real clause mean, and
decoded supplier estimate.  The local validity and gap lemmas make that trace
empty, hence every branch rejects.
-/

namespace NearCubicWires.ComponentwiseWeakMachine

open NearCubicWires
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RecoveryPipeline

/-- Evidence extracted from one purported accepting branch on a NO instance.
Each inequality has one owner: PCP/PCPP soundness, componentwise validity, the
supplier error guarantee, or the verifier's final comparison. -/
structure NoInstanceBranchLedger (parameters : SoundnessParameters) where
  roundedMean : ℝ
  realMean : ℝ
  estimate : ℝ
  roundedSound :
    roundedMean ≤ parameters.soundness + parameters.outerError
  validityClose :
    |realMean - roundedMean| ≤
      6 * Real.sqrt (12 * parameters.zeta)
  estimateClose :
    |estimate - realMean| ≤ parameters.estimationError
  accepted : parameters.acceptanceThreshold ≤ estimate

theorem noInstanceBranchLedger_empty
    (parameters : SoundnessParameters) :
    IsEmpty (NoInstanceBranchLedger parameters) := by
  refine ⟨?_⟩
  intro ledger
  exact
    (rejects_at_acceptanceThreshold parameters
      ledger.roundedMean ledger.realMean ledger.estimate
      ledger.roundedSound ledger.validityClose ledger.estimateClose)
      ledger.accepted

/-- The actual verifier compares against a finite rational code selected
strictly on the completeness side of the semantic midpoint.  This ledger is
the executable boundary: its final inequality is exactly the comparison
proved by the register program. -/
structure ExecutableNoInstanceBranchLedger
    {completeness soundness : ℝ}
    (parameters :
      ExecutableSoundnessParameters completeness soundness) where
  roundedMean : ℝ
  realMean : ℝ
  estimate : ℝ
  roundedSound :
    roundedMean ≤ soundness + (parameters.outerError : ℝ)
  validityClose :
    |realMean - roundedMean| ≤
      6 * Real.sqrt (12 * (parameters.zeta : ℝ))
  estimateClose :
    |estimate - realMean| ≤ (parameters.estimationError : ℝ)
  accepted : (parameters.threshold : ℝ) ≤ estimate

theorem executableNoInstanceBranchLedger_empty
    {completeness soundness : ℝ}
    (parameters :
      ExecutableSoundnessParameters completeness soundness) :
    IsEmpty (ExecutableNoInstanceBranchLedger parameters) := by
  refine ⟨?_⟩
  intro ledger
  apply (noInstanceBranchLedger_empty parameters.semantic).false
  exact
    { roundedMean := ledger.roundedMean
      realMean := ledger.realMean
      estimate := ledger.estimate
      roundedSound := ledger.roundedSound
      validityClose := ledger.validityClose
      estimateClose := ledger.estimateClose
      accepted :=
        parameters.semanticThreshold_le_executable.trans ledger.accepted }

/-- Once the concrete verifier proves that every accepting NO-instance branch
decodes to the ledger above, one-sidedness follows without a semantic machine
surrogate. -/
theorem eventuallyOneSided_of_branchLedger
    {hierarchy : Language}
    (machine : ExecutableWeakNondeterministicMachine)
    (parameters : SoundnessParameters)
    (onset : ℕ)
    (ledgerOfAcceptedBranch :
      ∀ n, onset ≤ n → ∀ input : BitInput n,
        hierarchy n input = false →
        ∀ witness : BitInput (machine.witnessBits n),
          machine.run n input witness →
            Nonempty (NoInstanceBranchLedger parameters)) :
    EventuallyOneSided hierarchy machine := by
  refine ⟨onset, ?_⟩
  intro n hn input hno haccepts
  rcases haccepts with ⟨witness, haccepts⟩
  rcases ledgerOfAcceptedBranch n hn input hno witness haccepts with
    ⟨ledger⟩
  exact noInstanceBranchLedger_empty parameters |>.false ledger

theorem eventuallyOneSided_of_executableBranchLedger
    {hierarchy : Language} {completeness soundness : ℝ}
    (machine : ExecutableWeakNondeterministicMachine)
    (parameters :
      ExecutableSoundnessParameters completeness soundness)
    (onset : ℕ)
    (ledgerOfAcceptedBranch :
      ∀ n, onset ≤ n → ∀ input : BitInput n,
        hierarchy n input = false →
        ∀ witness : BitInput (machine.witnessBits n),
          machine.run n input witness →
            Nonempty (ExecutableNoInstanceBranchLedger parameters)) :
    EventuallyOneSided hierarchy machine := by
  refine ⟨onset, ?_⟩
  intro n hn input hno haccepts
  rcases haccepts with ⟨witness, haccepts⟩
  rcases ledgerOfAcceptedBranch n hn input hno witness haccepts with
    ⟨ledger⟩
  exact executableNoInstanceBranchLedger_empty parameters |>.false ledger

end NearCubicWires.ComponentwiseWeakMachine
