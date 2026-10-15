import Proof.MachineModel.BankDiagonalBodyClosure
import Proof.MachineModel.BankProjectionTableStage
import Proof.MachineModel.BankRegisterCaseTwoChain

/-!
# The bank/diagonal cluster's three residuals, discharged together

`BankDiagonalBodyClosure.inverse_bodyRun_ofDiagonalCluster` consumes exactly
three cluster-specific premises beside the six width budgets and the compiler's
run:

* `BankAtomContextRegisters.InverseAtomTableRuns`,
* `BankFramedTargetChains.InverseCaseOnePointRuns`,
* `BankFramedTargetChains.InverseCaseTwoPointRuns`.

`BankProjectionTableStage`, `BankRegisterCaseOneChain` and
`BankRegisterCaseTwoChain` each discharge one of them.  The consumer shares a
*single* pair of envelopes between the two chains, so the three cannot simply be
quoted side by side: this module supplies the two monotonicity lemmas that let
one shared envelope cover both branches, and states the triple at that shared
envelope.

After it, the cluster's remaining obligations are

* `InverseScheduledRowRuns` — one decision-row stage, target uniform;
* `InverseScheduledOccurrenceRuns` — the Case-2 per-block occurrence callee;
* `InverseCaseTwoBankEnvelopes` — a resource domination statement;

together with the two hypotheses the cluster already threads, the executable
presentation and the onset-restricted schedule diagonal.
-/

namespace NearCubicWires.BankResidualClusterClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

private theorem run_fuel_mono {program : NPOracleProgram}
    {maximumBits fuel target : ℕ} {state : NPOracleState} {output : ℕ}
    (hexec : runNPOracleProgram program maximumBits fuel state = some output)
    (hfuel : fuel ≤ target) :
    runNPOracleProgram program maximumBits target state = some output := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  exact run_fuel_add hexec extra

/-! ## 1. Both chain premises are monotone in their envelopes -/

/-- Widening the Case-1 chain's envelopes preserves its run. -/
theorem inverseCaseOnePointRuns_mono
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (caseOne : NPOracleProgram)
    (chainBits chainFuel wideBits wideFuel : LanguageEvaluationRequest → ℕ)
    (hchain :
      InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
        caseOne chainBits chainFuel)
    (hbits : ∀ request, chainBits request ≤ wideBits request)
    (hfuel : ∀ request, chainFuel request ≤ wideFuel request) :
    InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
      caseOne wideBits wideFuel := by
  intro target hlarge hyes hrejects haccepts data hbranch input
  exact run_fuel_mono
    (run_bits_mono
      (hchain target hlarge hyes hrejects haccepts data hbranch input)
      (hbits ⟨target, input⟩))
    (hfuel ⟨target, input⟩)

/-- Widening the Case-2 chain's envelopes preserves its run. -/
theorem inverseCaseTwoPointRuns_mono
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (caseTwo : NPOracleProgram)
    (chainBits chainFuel wideBits wideFuel : LanguageEvaluationRequest → ℕ)
    (hchain :
      InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
        caseTwo chainBits chainFuel)
    (hbits : ∀ request, chainBits request ≤ wideBits request)
    (hfuel : ∀ request, chainFuel request ≤ wideFuel request) :
    InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
      caseTwo wideBits wideFuel := by
  intro target hlarge hyes hrejects haccepts branchTwo hbranch input
  exact run_fuel_mono
    (run_bits_mono
      (hchain target hlarge hyes hrejects haccepts branchTwo hbranch input)
      (hbits ⟨target, input⟩))
    (hfuel ⟨target, input⟩)

/-! ## 2. The shared chain envelope -/

/-- The width the dispatcher charges both chains. -/
noncomputable def residualChainBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (rowBits : ℕ → ℕ → ℕ) (bodyBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  max
    (inverseChainOneBits contracts clockDepth machine advantageExponent rowBits
      request)
    (inverseChainTwoBits contracts clockDepth advantageExponent bodyBits
      request)

/-- The fuel the dispatcher charges both chains. -/
noncomputable def residualChainFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (row occurrence : NPOracleProgram) (rowFuel : ℕ → ℕ → ℕ)
    (bodyFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  max
    (inverseChainOneFuel contracts clockDepth machine advantageExponent row
      rowFuel request)
    (inverseChainTwoFuel contracts clockDepth advantageExponent occurrence
      bodyFuel request)

/-! ## 3. The three residuals, at the shared envelope -/

/-- **The cluster's three residuals, discharged.**  Each of the three premises
`inverse_bodyRun_ofDiagonalCluster` still carries about the bank and the two
chains is produced here, at one shared chain envelope, from the executable
presentation, the onset-restricted schedule diagonal, and the three residual
statements of the three producing modules. -/
theorem inverse_clusterResiduals_discharged
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (row occurrence : NPOracleProgram)
    (rowBits rowFuel occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (hrow :
      InverseScheduledRowRuns contracts clockDepth machine advantageExponent row
        rowBits rowFuel)
    (hoccurrence :
      InverseScheduledOccurrenceRuns contracts clockDepth machine
        advantageExponent occurrence occurrenceBits occurrenceFuel)
    (henvelopes :
      InverseCaseTwoBankEnvelopes contracts clockDepth machine advantageExponent
        occurrence occurrenceBits occurrenceFuel bodyBits bodyFuel) :
    InverseAtomTableRuns contracts clockDepth machine advantageExponent pcp
        (inverseBankTableProgram contracts clockDepth machine pcp)
        (inverseBankTableBits contracts clockDepth machine advantageExponent
          pcp)
        (inverseBankTableFuel contracts clockDepth machine advantageExponent
          pcp) ∧
      InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
        (inverseChainOneProgram contracts clockDepth machine advantageExponent
          row)
        (residualChainBits contracts clockDepth machine advantageExponent
          rowBits bodyBits)
        (residualChainFuel contracts clockDepth machine advantageExponent row
          occurrence rowFuel bodyFuel) ∧
      InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
        (inverseChainTwoProgram contracts clockDepth advantageExponent
          occurrence)
        (residualChainBits contracts clockDepth machine advantageExponent
          rowBits bodyBits)
        (residualChainFuel contracts clockDepth machine advantageExponent row
          occurrence rowFuel bodyFuel) := by
  refine ⟨inverseAtomTableRuns_ofDiagonal contracts clockDepth machine
      advantageExponent pcp hpresentation hdiagonal, ?_, ?_⟩
  · exact inverseCaseOnePointRuns_mono contracts clockDepth machine
      advantageExponent _ _ _ _ _
      (inverseCaseOnePointRuns_ofRow contracts clockDepth machine
        advantageExponent row rowBits rowFuel hrow hdiagonal)
      (fun _ => Nat.le_max_left _ _) (fun _ => Nat.le_max_left _ _)
  · exact inverseCaseTwoPointRuns_mono contracts clockDepth machine
      advantageExponent _ _ _ _ _
      (inverseCaseTwoPointRuns_ofOccurrence contracts clockDepth machine
        advantageExponent occurrence occurrenceBits occurrenceFuel bodyBits
        bodyFuel hoccurrence henvelopes hdiagonal)
      (fun _ => Nat.le_max_right _ _) (fun _ => Nat.le_max_right _ _)

end NearCubicWires.BankResidualClusterClosure
