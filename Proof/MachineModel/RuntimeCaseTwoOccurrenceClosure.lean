import Proof.MachineModel.BankCaseTwoEnvelopeClosure
import Proof.Amplification.CanonicalRecoveryRequest
import Proof.MachineModel.RuntimeCaseTwoBlockOccurrenceProgram

namespace NearCubicWires.RuntimeCaseTwoOccurrenceClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.BankCaseTwoSeedBlockListProgram
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.BankResidualClusterClosure
open NearCubicWires.BankScheduledRowStageClosure
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram
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

/-! ## 1. The scheduled Case-2 packet -/

/-- The seven numerals of the scheduled Case-2 occurrence callee at one target
and one accepting oracle. -/
noncomputable def inverseCaseTwoOccurrencePacket
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target : ℕ)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)) : ℕ :=
  occurrencePacket
    (seedArity (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseChainSourceIndex contracts clockDepth advantageExponent target))
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
      (sourceLength
        (inverseChainSourceIndex contracts clockDepth advantageExponent
          target)))
    (widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth)
      (sourceLength
        (inverseChainSourceIndex contracts clockDepth advantageExponent
          target)))
    (clauseBitsEnvelope (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (sourceLength
        (inverseChainSourceIndex contracts clockDepth advantageExponent
          target)))
    (caseTwoFactoryPCPP (publishedPointwisePCPP contracts) caseTwo).clauseBits
    (caseTwoSubstitutedCircuit caseTwo).size
    (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo))

/-! ## 2. The numeral residual -/

/-- **The Case-2 occurrence residual, as numerals.**  One fixed program that,
from the requested public length alone, emits the seven numerals of the
schedule's Case-2 occurrence callee at the oracle the branch carries. -/
def InverseScheduledOccurrencePacket
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (packetProgram : NPOracleProgram) (packetBits packetFuel : ℕ → ℕ) : Prop :=
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
    runNPOracleProgram packetProgram (packetBits target) (packetFuel target)
        (initialNPOracleState target target) =
      some
        (inverseCaseTwoOccurrencePacket contracts clockDepth machine
          advantageExponent target caseTwo)

/-! ## 3. `InverseScheduledOccurrenceRuns`, discharged -/

/-- The callee's width at one target, block, oracle and point code. -/
noncomputable def inverseOccurrenceCaseTwoBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (packetBits : ℕ → ℕ) (target : ℕ)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target))
    (block pointCode : ℕ) : ℕ :=
  occurrenceCalleeBits (publishedPointwisePCPP contracts).factory target
    (inverseCaseTwoOccurrencePacket contracts clockDepth machine
      advantageExponent target caseTwo)
    (packetBits target) (caseTwoSubstitutedCircuit caseTwo) block pointCode
    (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
      pointCode block).toNat

/-- The callee's fuel at one target, block, oracle and point code. -/
noncomputable def inverseOccurrenceCaseTwoFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (packetProgram : NPOracleProgram) (packetFuel : ℕ → ℕ) (target : ℕ)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target))
    (block pointCode : ℕ) : ℕ :=
  occurrenceCalleeFuel (publishedPointwisePCPP contracts).factory packetProgram
    (inverseCaseTwoOccurrencePacket contracts clockDepth machine
      advantageExponent target caseTwo)
    (packetFuel target) (caseTwoSubstitutedCircuit caseTwo) block pointCode

open Classical in
/-- The callee's width at one target and block, quoted at the oracle the
schedule's own branch carries and taken uniformly over the point codes of that
target. -/
noncomputable def inverseOccurrenceBranchBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (packetBits : ℕ → ℕ) (target block : ℕ) : ℕ :=
  if hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target) then
    match
      inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes with
    | .caseOne _ => 0
    | .caseTwo caseTwo =>
        (Finset.range (2 ^ target)).sup
          (inverseOccurrenceCaseTwoBits contracts clockDepth machine
            advantageExponent packetBits target caseTwo block)
  else 0

open Classical in
/-- The callee's fuel at one target and block, quoted at the branch's oracle and
taken uniformly over the point codes of that target. -/
noncomputable def inverseOccurrenceBranchFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (packetProgram : NPOracleProgram) (packetFuel : ℕ → ℕ)
    (target block : ℕ) : ℕ :=
  if hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target) then
    match
      inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes with
    | .caseOne _ => 0
    | .caseTwo caseTwo =>
        (Finset.range (2 ^ target)).sup
          (inverseOccurrenceCaseTwoFuel contracts clockDepth machine
            advantageExponent packetProgram packetFuel target caseTwo block)
  else 0

set_option maxHeartbeats 1600000 in
-- The statement carries the packet, the substituted circuit and both branch
-- envelopes at one target, so elaborating it alone exceeds the default budget.
/-- **The Case-2 chain's correctness residual, discharged from its numerals.**
With the seven immediates of the per-block occurrence callee replaced by reads
of a packet in the public length register, the callee is one fixed program and
`InverseScheduledOccurrenceRuns` follows from the numeral residual alone. -/
theorem inverseScheduledOccurrenceRuns_ofPacket
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (packetProgram : NPOracleProgram) (packetBits packetFuel : ℕ → ℕ)
    (hpackets :
      InverseScheduledOccurrencePacket contracts clockDepth machine
        advantageExponent packetProgram packetBits packetFuel) :
    InverseScheduledOccurrenceRuns contracts clockDepth machine
      advantageExponent
      (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
        packetProgram)
      (inverseOccurrenceBranchBits contracts clockDepth machine
        advantageExponent packetBits)
      (inverseOccurrenceBranchFuel contracts clockDepth machine
        advantageExponent packetProgram packetFuel) := by
  intro target hlarge hyes caseTwo hbranch point block _hblock
  have hpacket := hpackets target hlarge hyes caseTwo hbranch
  have hrun :=
    run_occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
      packetProgram target
      (inverseCaseTwoOccurrencePacket contracts clockDepth machine
        advantageExponent target caseTwo)
      (packetBits target) (packetFuel target)
      (caseTwoSubstitutedCircuit caseTwo) block (encodeBitInput point) hpacket
      (by simp [inverseCaseTwoOccurrencePacket, inverseChainSourceIndex])
      (by simp [inverseCaseTwoOccurrencePacket])
      (by simp [inverseCaseTwoOccurrencePacket])
  have hvalue :
      (caseTwoBlockValue (publishedPointwisePCPP contracts).factory
          (caseTwoSubstitutedCircuit caseTwo)
          (packetInputArity
            (inverseCaseTwoOccurrencePacket contracts clockDepth machine
              advantageExponent target caseTwo))
          (packetPaddedInputBits
            (inverseCaseTwoOccurrencePacket contracts clockDepth machine
              advantageExponent target caseTwo))
          (packetNativeClauseBits
            (inverseCaseTwoOccurrencePacket contracts clockDepth machine
              advantageExponent target caseTwo))
          (packetPaddedClauseBits
            (inverseCaseTwoOccurrencePacket contracts clockDepth machine
              advantageExponent target caseTwo))
          (packetArity
            (inverseCaseTwoOccurrencePacket contracts clockDepth machine
              advantageExponent target caseTwo))
          (encodeBitInput point) block) =
        caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
          (encodeBitInput point) block := by
    simp [inverseCaseTwoOccurrencePacket, caseTwoScheduledBlockValue,
      inverseChainSourceIndex]
  rw [hvalue] at hrun
  have hmember :
      encodeBitInput point ∈ Finset.range (2 ^ target) :=
    Finset.mem_range.mpr
      (encodeBitInput_lt_pow point)
  have hbitsEq :
      inverseOccurrenceBranchBits contracts clockDepth machine advantageExponent
          packetBits target block =
        (Finset.range (2 ^ target)).sup
          (inverseOccurrenceCaseTwoBits contracts clockDepth machine
            advantageExponent packetBits target caseTwo block) := by
    simp only [inverseOccurrenceBranchBits]
    rw [dif_pos hyes, hbranch]
  have hfuelEq :
      inverseOccurrenceBranchFuel contracts clockDepth machine advantageExponent
          packetProgram packetFuel target block =
        (Finset.range (2 ^ target)).sup
          (inverseOccurrenceCaseTwoFuel contracts clockDepth machine
            advantageExponent packetProgram packetFuel target caseTwo block) := by
    simp only [inverseOccurrenceBranchFuel]
    rw [dif_pos hyes, hbranch]
  have hbitsLe :=
    Finset.le_sup
      (f :=
        inverseOccurrenceCaseTwoBits contracts clockDepth machine
          advantageExponent packetBits target caseTwo block)
      hmember
  have hfuelLe :=
    Finset.le_sup
      (f :=
        inverseOccurrenceCaseTwoFuel contracts clockDepth machine
          advantageExponent packetProgram packetFuel target caseTwo block)
      hmember
  rw [inverseOccurrenceCaseTwoBits] at hbitsLe
  rw [inverseOccurrenceCaseTwoFuel] at hfuelLe
  exact run_fuel_mono (run_bits_mono hrun (hbitsEq ▸ hbitsLe)) (hfuelEq ▸ hfuelLe)

/-! ## 4. What the cluster closure still needs -/

set_option maxHeartbeats 1600000 in
-- The statement is the cluster's whole three-way conjunction at one shared
-- envelope, so elaborating it alone exceeds the default budget.
/-- **The bank/diagonal cluster's three residuals, from the occurrence numerals
alone.**  `BankCaseTwoEnvelopeClosure.inverse_clusterResiduals_ofOccurrence`
carried the per-block occurrence callee; §3 replaces it by the numeral
residual, so the cluster now needs only the padded presentation, the
onset-restricted schedule diagonal, the scheduled query-count positivity, and
one program emitting the seven Case-2 numerals from the public length. -/
theorem inverse_clusterResiduals_ofPacket
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
    (packetProgram : NPOracleProgram) (packetBits packetFuel : ℕ → ℕ)
    (hcounts :
      InverseScheduledQueryCounts contracts clockDepth advantageExponent)
    (hpackets :
      InverseScheduledOccurrencePacket contracts clockDepth machine
        advantageExponent packetProgram packetBits packetFuel) :
    InverseAtomTableRuns contracts clockDepth machine advantageExponent pcp
        (inverseBankTableProgram contracts clockDepth machine pcp)
        (inverseBankTableBits contracts clockDepth machine advantageExponent
          pcp)
        (inverseBankTableFuel contracts clockDepth machine advantageExponent
          pcp) ∧
      InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
        (inverseChainOneProgram contracts clockDepth machine advantageExponent
          (inverseScheduledRowProgram contracts clockDepth))
        (residualChainBits contracts clockDepth machine advantageExponent
          (inverseScheduledRowBits contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyBits contracts clockDepth machine
            advantageExponent
            (inverseOccurrenceBranchBits contracts clockDepth machine
              advantageExponent packetBits)))
        (residualChainFuel contracts clockDepth machine advantageExponent
          (inverseScheduledRowProgram contracts clockDepth)
          (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
            packetProgram)
          (inverseScheduledRowFuel contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyFuel contracts clockDepth machine
            advantageExponent
            (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
              packetProgram)
            (inverseOccurrenceBranchFuel contracts clockDepth machine
              advantageExponent packetProgram packetFuel))) ∧
      InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
        (inverseChainTwoProgram contracts clockDepth advantageExponent
          (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
            packetProgram))
        (residualChainBits contracts clockDepth machine advantageExponent
          (inverseScheduledRowBits contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyBits contracts clockDepth machine
            advantageExponent
            (inverseOccurrenceBranchBits contracts clockDepth machine
              advantageExponent packetBits)))
        (residualChainFuel contracts clockDepth machine advantageExponent
          (inverseScheduledRowProgram contracts clockDepth)
          (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
            packetProgram)
          (inverseScheduledRowFuel contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyFuel contracts clockDepth machine
            advantageExponent
            (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
              packetProgram)
            (inverseOccurrenceBranchFuel contracts clockDepth machine
              advantageExponent packetProgram packetFuel))) :=
  inverse_clusterResiduals_ofOccurrence contracts clockDepth machine
    advantageExponent pcp hpresentation hdiagonal
    (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
      packetProgram)
    (inverseOccurrenceBranchBits contracts clockDepth machine advantageExponent
      packetBits)
    (inverseOccurrenceBranchFuel contracts clockDepth machine advantageExponent
      packetProgram packetFuel)
    hcounts
    (inverseScheduledOccurrenceRuns_ofPacket contracts clockDepth machine
      advantageExponent packetProgram packetBits packetFuel hpackets)

end NearCubicWires.RuntimeCaseTwoOccurrenceClosure
