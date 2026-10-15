import Proof.MachineModel.BankCaseTwoSeedBlockListProgram
import Proof.MachineModel.BankRegisterCaseOneChain

/-!
# The Case-2 chain at the requested point code

`BankFramedTargetChains.inverse_chainTwo_ofPointRuns` reduces the dispatcher's
Case-2 premise to `InverseCaseTwoPointRuns`: one **fixed** instruction stream
returning the canonical target bit from the requested point code.

`BankCaseTwoSeedBlockListProgram.run_bankCaseTwoTargetBitProgram_inverse`
already runs the whole Case-2 branch from the numeral bank's frame with the XOR
copy count read out of a register rather than baked, so on that side the chain
is target uniform outright — mirroring
`EmittedBranchTargetProgram.fixedCaseTwoChainProgram_target_independent`, which
records the same for the fixed schedule.  §1 puts the published numeral bank in
front of it, so the stream starts at the bare point code, and §3 discharges
`InverseCaseTwoPointRuns`.

## What is left, exactly

One correctness premise, `InverseScheduledOccurrenceRuns`: the per-block
occurrence callee of `CaseTwoSeedBlockListProgram`, at every block below the
scheduled copy count.  That callee is the one stage that still bakes
`CanonicalTargetLanguageProgram.caseTwoSubstitutedCircuit caseTwo`, an object
recovered from the accepting oracle and therefore genuinely request-dependent;
removing it means computing the substituted circuit at run time from the
compiled substitution substrate
(`CanonicalStructuralGF2SubstituteProgram`,
`CanonicalStructuralGF2TruthTableProgram.structuralGF2BitMajority_eq_substitute`),
which is not attempted here.

Beside it, one resource premise `InverseCaseTwoBankEnvelopes`: the shared chain
envelopes of the dispatcher must dominate the register-driven Case-2 envelopes.
The dispatcher shares one width and one fuel function between both branches, so
a domination statement is the only way to state the Case-2 side without letting
the branch's own accepting oracle leak into a public resource function.
-/

namespace NearCubicWires.BankRegisterCaseTwoChain

open NearCubicWires
open NearCubicWires.BankCaseTwoSeedBlockListProgram
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

private theorem run_fuel_mono {program : NPOracleProgram}
    {maximumBits fuel target : ℕ} {state : NPOracleState} {output : ℕ}
    (hexec : runNPOracleProgram program maximumBits fuel state = some output)
    (hfuel : fuel ≤ target) :
    runNPOracleProgram program maximumBits target state = some output := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  exact run_fuel_add hexec extra

/-! ## 1. The chain from the requested point code -/

/-- The register-driven Case-2 body at the numeral bank's frame. -/
noncomputable def inverseChainTwoBodyProgram
    (contracts : PublishedContracts) (occurrence : NPOracleProgram) :
    NPOracleProgram :=
  bankCaseTwoTargetBitProgram (publishedAmplifier contracts).algorithm
    occurrence

/-- **The register-driven Case-2 chain at the requested point code.** -/
noncomputable def inverseChainTwoProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (occurrence : NPOracleProgram) : NPOracleProgram :=
  uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (inverseChainTwoBodyProgram contracts occurrence)

/-- Width of the whole chain at one request. -/
noncomputable def inverseChainTwoBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (bodyBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent) bodyBits request

/-- Fuel of the whole chain at one request. -/
noncomputable def inverseChainTwoFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (occurrence : NPOracleProgram)
    (bodyFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (inverseChainTwoBodyProgram contracts occurrence) bodyFuel request

/-- The schedule's XOR copy count at one target. -/
noncomputable def inverseChainTwoCopies
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (inverseChainSourceIndex contracts clockDepth advantageExponent target)

/-! ## 2. The two residual premises -/

/-- **The Case-2 chain's correctness residual.**  The per-block occurrence
callee at every block below the scheduled copy count.  This is the one stage of
the branch that still reads the substituted circuit recovered from the
accepting oracle. -/
def InverseScheduledOccurrenceRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (occurrence : NPOracleProgram)
    (occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)),
    inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes = .caseTwo caseTwo →
    ∀ (point : BitInput target) (block : ℕ),
      block < inverseChainTwoCopies contracts clockDepth advantageExponent
        target →
      runNPOracleProgram occurrence (occurrenceBits target block)
          (occurrenceFuel target block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point) block).toNat

/-- **The Case-2 chain's resource residual.**  The dispatcher's shared chain
envelopes dominate the register-driven Case-2 envelopes at every request. -/
def InverseCaseTwoBankEnvelopes
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (occurrence : NPOracleProgram)
    (occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)),
    inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes = .caseTwo caseTwo →
    ∀ point : BitInput target,
      bankCaseTwoTargetBitBits target
          (sourceLength
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))
          (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
            (sourceLength
              (inverseChainSourceIndex contracts clockDepth advantageExponent
                target)))
          (inverseChainTwoCopies contracts clockDepth advantageExponent target)
          (encodeBitInput point) (occurrenceBits target)
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point))
          ((List.range
            (inverseChainTwoCopies contracts clockDepth advantageExponent
              target)).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))) ≤
        bodyBits ⟨target, point⟩ ∧
      bankCaseTwoTargetBitFuel (publishedAmplifier contracts).algorithm
          occurrence target
          (inverseChainTwoCopies contracts clockDepth advantageExponent target)
          (encodeBitInput point) (occurrenceFuel target)
          ((List.range
            (inverseChainTwoCopies contracts clockDepth advantageExponent
              target)).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))) ≤
        bodyFuel ⟨target, point⟩

/-! ## 3. `InverseCaseTwoPointRuns`, discharged -/

/-- **`InverseCaseTwoPointRuns` from the occurrence callee alone.**  Every
schedule numeral of the Case-2 branch — the XOR copy count included — is read
from the numeral bank's registers, and the bank itself is the chain's first
stage, so the stream is one fixed program.  The onset-restricted schedule
diagonal is threaded, never asserted. -/
theorem inverseCaseTwoPointRuns_ofOccurrence
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (occurrence : NPOracleProgram)
    (occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (hoccurrence :
      InverseScheduledOccurrenceRuns contracts clockDepth machine
        advantageExponent occurrence occurrenceBits occurrenceFuel)
    (henvelopes :
      InverseCaseTwoBankEnvelopes contracts clockDepth machine advantageExponent
        occurrence occurrenceBits occurrenceFuel bodyBits bodyFuel)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target =
        sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target)) :
    InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
      (inverseChainTwoProgram contracts clockDepth advantageExponent occurrence)
      (inverseChainTwoBits contracts clockDepth advantageExponent bodyBits)
      (inverseChainTwoFuel contracts clockDepth advantageExponent occurrence
        bodyFuel) := by
  intro target hlarge hyes hrejects haccepts caseTwo hbranch input
  refine run_uniformTargetProgram
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent) _ bodyBits bodyFuel target
    input _ ?_
  obtain ⟨hbits, hfuel⟩ := henvelopes target hyes caseTwo hbranch input
  exact run_fuel_mono
    (run_bits_mono
      (run_bankCaseTwoTargetBitProgram_inverse occurrence contracts clockDepth
        machine advantageExponent target hlarge hyes hrejects haccepts caseTwo
        hbranch (hdiagonal target hlarge) input (occurrenceBits target)
        (occurrenceFuel target)
        (hoccurrence target hlarge hyes caseTwo hbranch input))
      hbits)
    hfuel

end NearCubicWires.BankRegisterCaseTwoChain
