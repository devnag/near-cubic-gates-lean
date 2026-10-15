import Proof.Circuits.FixedScheduledRowStageClosure
import Proof.CaseAnalysis.FixedSelectorCaseOnePointRunsOfRow
import Proof.MachineModel.TotalOuterProofRowGuardedProgram

/-!
# The fixed scheduled row without query-count positivity

The generic guarded row emitter is interpreted at the published fixed schedule.
At zero query count the semantic decision row is empty; at nonzero count the
generic module already proves equality with the original row program.  This
module exposes only the unconditional fixed row contract and its immediate
Case-one point-run consumer.
-/

namespace NearCubicWires.FixedTotalScheduledRowStageClosure

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedRegisterCaseOneChain
open NearCubicWires.FixedScheduleDiagonalClosure
open NearCubicWires.FixedSelectorCaseOnePointRunsOfRow
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.OuterProofRowProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TotalOuterProofRowGuardedProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The semantic seam at zero -/

private theorem outerProofRowStream_eq_nil_of_queryCount_zero
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (code : ℕ) (hzero : pcp.queryCount n = 0) :
    outerProofRowStream pcp input code = [] := by
  have hclauses :
      (pcp.decision input (bitInputOfCode (pcp.nativeWidth n) code)).clauses =
        [] := by
    cases hlist :
        (pcp.decision input
          (bitInputOfCode (pcp.nativeWidth n) code)).clauses with
    | nil => rfl
    | cons clause clauses =>
        have literal := clause (0 : Fin 3)
        cases literal with
        | positive query =>
            have hquery := query.isLt
            exact False.elim (by omega)
        | negative query =>
            have hquery := query.isLt
            exact False.elim (by omega)
  simp [outerProofRowStream, outerProofRowFormula, hclauses]

theorem totalOuterProofRowOutput_eq_scheduled
    {clockDepth : ℕ} {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) (code : ℕ) :
    totalOuterProofRowOutput outer.pcp input code =
      encodeTaggedList
        (outerProofRowStream (paddedOuterPCP outer) input code) := by
  by_cases hzero : outer.pcp.queryCount (sourceLength sourceIndex) = 0
  · have hnil := outerProofRowStream_eq_nil_of_queryCount_zero
      (paddedOuterPCP outer) input code hzero
    simp [totalOuterProofRowOutput, hzero, hnil, encodeTaggedList]
  · rw [totalOuterProofRowOutput, if_neg hzero]
    rw [rowRawStream_eq_scheduledOuterProofRowStream outer sourceIndex input
      code (Nat.pos_of_ne_zero hzero)]

/-! ## 2. Fixed scheduled wrappers -/

noncomputable def fixedTotalScheduledRowProgram (contracts : PublishedContracts)
    (clockDepth : ℕ) : NPOracleProgram :=
  totalOuterProofRowProgram
    (publishedHierarchyOuterPCP contracts clockDepth).pcp

noncomputable def fixedTotalScheduledRowBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (target code : ℕ) : ℕ :=
  totalOuterProofRowGuardBits
    (publishedHierarchyOuterPCP contracts clockDepth).pcp
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      target)
    (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
      (fixedChainSourceIndex contracts clockDepth requestedRate target))
    code

noncomputable def fixedTotalScheduledRowFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (target code : ℕ) : ℕ :=
  totalOuterProofRowFuel
    (publishedHierarchyOuterPCP contracts clockDepth).pcp
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      target)
    code

set_option maxHeartbeats 800000 in
-- The fixed source index occurs dependently in the input word and output row.
theorem run_fixedTotalScheduledRowProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target code : ℕ) :
    runNPOracleProgram (fixedTotalScheduledRowProgram contracts clockDepth)
        (fixedTotalScheduledRowBits contracts clockDepth machine requestedRate
          target code)
        (fixedTotalScheduledRowFuel contracts clockDepth machine requestedRate
          target code)
        (initialNPOracleState
          (sourceLength
            (fixedChainSourceIndex contracts clockDepth requestedRate target))
          (Nat.pair code
            (Nat.pair
              (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
                (fixedChainSourceIndex contracts clockDepth requestedRate
                  target))
              (encodeBitInput
                (fixedRefuterInput contracts
                  (publishedHierarchyOuterPCP contracts clockDepth) machine
                  requestedRate target))))) =
      some
        (encodeTaggedList
          (outerProofRowStream
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target)
            code)) := by
  have hrun := run_totalOuterProofRowProgram
    (publishedHierarchyOuterPCP contracts clockDepth).pcp
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      target)
    (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
      (fixedChainSourceIndex contracts clockDepth requestedRate target))
    code
  have hout := totalOuterProofRowOutput_eq_scheduled
    (publishedHierarchyOuterPCP contracts clockDepth)
    (fixedChainSourceIndex contracts clockDepth requestedRate target)
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      target)
    code
  unfold fixedTotalScheduledRowProgram fixedTotalScheduledRowBits
    fixedTotalScheduledRowFuel
  exact hrun.trans (congrArg some hout)

theorem run_fixedTotalScheduledRowProgram_zero
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target code : ℕ)
    (hzero :
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
        (sourceLength
          (fixedChainSourceIndex contracts clockDepth requestedRate target)) =
        0) :
    runNPOracleProgram (fixedTotalScheduledRowProgram contracts clockDepth)
        (fixedTotalScheduledRowBits contracts clockDepth machine requestedRate
          target code)
        (fixedTotalScheduledRowFuel contracts clockDepth machine requestedRate
          target code)
        (initialNPOracleState
          (sourceLength
            (fixedChainSourceIndex contracts clockDepth requestedRate target))
          (Nat.pair code
            (Nat.pair
              (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
                (fixedChainSourceIndex contracts clockDepth requestedRate
                  target))
              (encodeBitInput
                (fixedRefuterInput contracts
                  (publishedHierarchyOuterPCP contracts clockDepth) machine
                  requestedRate target))))) =
      some 0 := by
  have hrun := run_totalOuterProofRowProgram_zero
    (publishedHierarchyOuterPCP contracts clockDepth).pcp
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      target)
    (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
      (fixedChainSourceIndex contracts clockDepth requestedRate target))
    code hzero
  unfold fixedTotalScheduledRowProgram fixedTotalScheduledRowBits
    fixedTotalScheduledRowFuel
  exact hrun

/-! ## 3. Unconditional row and immediate point run -/

theorem fixedTotalScheduledRowRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ) :
    FixedScheduledRowRuns contracts clockDepth machine requestedRate
      (fixedTotalScheduledRowProgram contracts clockDepth)
      (fixedTotalScheduledRowBits contracts clockDepth machine requestedRate)
      (fixedTotalScheduledRowFuel contracts clockDepth machine requestedRate) := by
  intro target _hlarge code _hcode
  exact run_fixedTotalScheduledRowProgram contracts clockDepth machine
    requestedRate target code

set_option maxHeartbeats 1600000 in
-- The selector-prefixed point contract carries the total row envelopes twice.
/-- The immediate Case-one point-run consumer no longer needs query-count
positivity. -/
theorem fixedCaseOnePointRuns_ofTotalRow
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ) :
    FixedCaseOnePointRuns contracts clockDepth machine requestedRate
      (fixedSelectorChainOneProgram contracts clockDepth machine requestedRate
        (fixedTotalScheduledRowProgram contracts clockDepth))
      (fixedSelectorChainOneBits contracts clockDepth machine requestedRate
        (fixedTotalScheduledRowBits contracts clockDepth machine requestedRate))
      (fixedSelectorChainOneFuel contracts clockDepth machine requestedRate
        (fixedTotalScheduledRowProgram contracts clockDepth)
        (fixedTotalScheduledRowFuel contracts clockDepth machine
          requestedRate)) :=
  fixedCaseOnePointRuns_ofSelectorRow contracts clockDepth machine requestedRate
    (fixedTotalScheduledRowProgram contracts clockDepth)
    (fixedTotalScheduledRowBits contracts clockDepth machine requestedRate)
    (fixedTotalScheduledRowFuel contracts clockDepth machine requestedRate)
    (fixedTotalScheduledRowRuns contracts clockDepth machine requestedRate)

end NearCubicWires.FixedTotalScheduledRowStageClosure
