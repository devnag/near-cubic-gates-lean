import Proof.MachineModel.RuntimeCaseTwoOccurrenceClosure
import Proof.MachineModel.RuntimeScheduleQuadNumeralProgram

/-!
# The occurrence packet, split into its schedule and oracle halves

`RuntimeCaseTwoOccurrenceClosure` reduced the Case-2 occurrence residual to
`InverseScheduledOccurrencePacket`: one fixed program emitting the seven
numerals of the per-block callee from the target's public length.  The premise
was all-or-nothing, yet its two halves are of completely different character.

`RuntimeCaseTwoBlockOccurrenceProgram.occurrencePacket` is *literally*
`Nat.pair (quad) (triple)`:

* the **schedule quad** — `seedArity`, the outer native width, the width
  envelope and the clause-address envelope — is arithmetic in the scheduled
  source length alone.  `RuntimeScheduleQuadNumeralProgram` builds it, and §2
  instantiates that stream at the published contracts, leaving *no* premise:
  the only hypothesis is the schedule diagonal the cluster already carries.
* the **oracle triple** — the published factory's clause width at the
  substituted circuit, that circuit's size, and its encoding — is recovered
  from the accepting oracle rather than computed from the request.

§1 records the split.  §2 discharges the quad.  §3 states the oracle triple as
the residual premise.  §4 pairs the two streams and re-proves
`InverseScheduledOccurrencePacket` from the triple alone, and §5 restates the
cluster closure at the smaller premise.

## What the oracle triple still needs

The encoder is
`recovered description bits ↦ encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)`,
and §6 reduces it to three named pieces by proving the two codec identities the
tree lacked.  `caseTwoSubstitutedCircuit caseTwo` is
`(outer.substitution.circuit ⟨n, input, restrictPaddedOracle caseTwo.circuit _⟩).padToArity`,
so:

* `encodeBooleanCircuit_padSize` turns the outer `padToArity` into one
  `encodeBalancedList` **append** of a constant list — and
  `CanonicalBalancedFlattenProgram.balancedAppendProgram` is that append;
* `encodeBooleanCircuit_restrictBooleanCircuit` turns the inner
  `restrictPaddedOracle` into one **map** of a per-node transform over the
  encoded node list — and `CanonicalBalancedCall.balancedCallProgram` is that
  map;
* the substitution runner's own `ExecutableProjectionSubstitution.computes`
  then supplies the encoding of the substituted circuit itself.

What is left open is exactly: the per-node callee for `restrictBooleanNode`,
the constant-node generator for the padding suffix, and the assembler that
turns the recovered bounded-circuit description into `encodeBooleanCircuit` of
the oracle it describes.
-/

namespace NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit

open NearCubicWires
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.CanonicalBinary
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.BankResidualClusterClosure
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BankScheduledRowStageClosure
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOnePadding
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram
open NearCubicWires.RuntimeCaseTwoOccurrenceClosure
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.RuntimeScheduleQuadNumeralProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The packet is one pair of its two halves -/

/-- The oracle half of the occurrence packet: the published factory's clause
width at the substituted circuit, that circuit's size, and its encoding. -/
def occurrenceTripleWord (nativeClauseBits circuitSize encoded : ℕ) : ℕ :=
  Nat.pair nativeClauseBits (Nat.pair circuitSize encoded)

/-- **The split.**  The seven-numeral packet is the pair of its schedule quad
and its oracle triple, with no rearrangement at all. -/
theorem occurrencePacket_eq_pair
    (arity inputArity paddedInputBits paddedClauseBits nativeClauseBits
      circuitSize encoded : ℕ) :
    occurrencePacket arity inputArity paddedInputBits paddedClauseBits
        nativeClauseBits circuitSize encoded =
      Nat.pair
        (occurrenceQuadWord arity inputArity paddedInputBits paddedClauseBits)
        (occurrenceTripleWord nativeClauseBits circuitSize encoded) :=
  rfl

/-! ## 2. The schedule quad at the published contracts -/

private theorem inverseScheduleLength_eq_sourceLength
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) :
    inverseScheduleLength contracts clockDepth advantageExponent target =
      sourceLength
        (inverseChainSourceIndex contracts clockDepth advantageExponent
          target) :=
  rfl

/-- The published quad stream: the schedule numeral bank's arithmetic at the
published outer shape, substitution and pointwise source. -/
noncomputable def inverseOccurrenceQuadProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) : NPOracleProgram :=
  occurrenceQuadProgram
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program
    clockDepth
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
    (publishedHierarchyOuterPCP contracts clockDepth).proofExponent
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (publishedHierarchyOuterPCP contracts clockDepth).substitution.sizeCoefficient
    (publishedHierarchyOuterPCP contracts clockDepth).substitutionExponent
    (publishedPointwisePCPP contracts).coefficient
    (publishedPointwisePCPP contracts).degree

theorem inverseOccurrenceQuadProgram_oracleFree
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) :
    OracleFree (inverseOccurrenceQuadProgram contracts clockDepth
      advantageExponent) :=
  occurrenceQuadProgram_oracleFree _ _ _ _ _ _ _ _
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shapeOracleFree

noncomputable def inverseOccurrenceQuadBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrenceQuadBits target clockDepth
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
    (publishedHierarchyOuterPCP contracts clockDepth).proofExponent
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (publishedHierarchyOuterPCP contracts clockDepth).substitution.sizeCoefficient
    (publishedHierarchyOuterPCP contracts clockDepth).substitutionExponent
    (publishedPointwisePCPP contracts).coefficient
    (publishedPointwisePCPP contracts).degree target
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget target)
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.execute target)

noncomputable def inverseOccurrenceQuadFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrenceQuadFuel
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program
    clockDepth
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
    (publishedHierarchyOuterPCP contracts clockDepth).proofExponent
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (publishedHierarchyOuterPCP contracts clockDepth).substitution.sizeCoefficient
    (publishedHierarchyOuterPCP contracts clockDepth).substitutionExponent
    (publishedPointwisePCPP contracts).coefficient
    (publishedPointwisePCPP contracts).degree target
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget target)

/-- The schedule quad of the occurrence packet at one target. -/
noncomputable def inverseOccurrenceQuadWord
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrenceQuadWord
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

set_option maxHeartbeats 800000 in
-- The statement carries the published quad stream and all four envelopes at
-- one target, so elaborating it alone exceeds the default budget.
/-- **The schedule quad, discharged.**  On the schedule's diagonal the public
length register *is* the scheduled source length, so the published stream of
`RuntimeScheduleQuadNumeralProgram` emits the quad word with no premise beyond
the diagonal the cluster already carries. -/
theorem run_inverseOccurrenceQuadProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ)
    (hdiagonal :
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target) :
    runNPOracleProgram
        (inverseOccurrenceQuadProgram contracts clockDepth advantageExponent)
        (inverseOccurrenceQuadBits contracts clockDepth advantageExponent target)
        (inverseOccurrenceQuadFuel contracts clockDepth advantageExponent target)
        (initialNPOracleState target target) =
      some
        (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
          target) := by
  have hlength :
      sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target) =
        target :=
    (inverseScheduleLength_eq_sourceLength contracts clockDepth
      advantageExponent target).symm.trans hdiagonal.symm
  rw [inverseOccurrenceQuadWord,
    seedArity_eq_sum (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseChainSourceIndex contracts clockDepth advantageExponent target),
    hlength]
  exact run_occurrenceQuadProgram
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program target
    clockDepth
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
    (publishedHierarchyOuterPCP contracts clockDepth).proofExponent
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (publishedHierarchyOuterPCP contracts clockDepth).substitution.sizeCoefficient
    (publishedHierarchyOuterPCP contracts clockDepth).substitutionExponent
    (publishedPointwisePCPP contracts).coefficient
    (publishedPointwisePCPP contracts).degree
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget target)
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget target)
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.execute target)
    (publishedWidthBudget_positive
      (publishedHierarchyOuterPCP contracts clockDepth) target)
    (publishedPointwisePCPP contracts).coefficientPositive
    (run_publishedShapeProgram (publishedHierarchyOuterPCP contracts clockDepth)
      target)

/-! ## 3. The oracle triple -/

/-- The oracle half of the occurrence packet at one target and one accepting
oracle. -/
noncomputable def inverseOccurrenceTripleWord
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
  occurrenceTripleWord
    (caseTwoFactoryPCPP (publishedPointwisePCPP contracts) caseTwo).clauseBits
    (caseTwoSubstitutedCircuit caseTwo).size
    (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo))

/-- **The Case-2 occurrence residual, as oracle numerals only.**  One fixed
program that, from the requested public length alone, emits the three
oracle-derived numerals of the schedule's Case-2 occurrence callee at the
oracle the branch carries. -/
def InverseScheduledOccurrenceTriple
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (tripleProgram : NPOracleProgram) (tripleBits tripleFuel : ℕ → ℕ) : Prop :=
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
    runNPOracleProgram tripleProgram (tripleBits target) (tripleFuel target)
        (initialNPOracleState target target) =
      some
        (inverseOccurrenceTripleWord contracts clockDepth machine
          advantageExponent target caseTwo)

/-! ## 4. Pairing the two halves -/

/-- Run both halves on the public length and pair their outputs. -/
def occurrencePacketPairProgram
    (quadProgram tripleProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms duplicateProgram <|
    linkPrograms (preserveRightProgram quadProgram) <|
      linkPrograms swapPairProgram <|
        linkPrograms (preserveRightProgram tripleProgram) swapPairProgram

theorem occurrencePacketPairProgram_oracleFree
    {quadProgram tripleProgram : NPOracleProgram}
    (hquad : OracleFree quadProgram) (htriple : OracleFree tripleProgram) :
    OracleFree (occurrencePacketPairProgram quadProgram tripleProgram) :=
  oracleFree_linkPrograms duplicateProgram_oracleFree
    (oracleFree_linkPrograms (preserveRightProgram_oracleFree _ hquad)
      (oracleFree_linkPrograms swapPairProgram_oracleFree
        (oracleFree_linkPrograms (preserveRightProgram_oracleFree _ htriple)
          swapPairProgram_oracleFree)))

def occurrencePacketPairFuel (quadProgram tripleProgram : NPOracleProgram)
    (quadFuel tripleFuel : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram quadProgram)
      (linkPrograms swapPairProgram
        (linkPrograms (preserveRightProgram tripleProgram) swapPairProgram)))
    2 <|
    linkFuel
      (linkPrograms swapPairProgram
        (linkPrograms (preserveRightProgram tripleProgram) swapPairProgram))
      (preserveRightFuel quadFuel) <|
      linkFuel
        (linkPrograms (preserveRightProgram tripleProgram) swapPairProgram)
        4 <|
        linkFuel swapPairProgram (preserveRightFuel tripleFuel) 4

def occurrencePacketPairBits
    (inputLength quadBits tripleBits quad triple : ℕ) : ℕ :=
  occurrenceStageBits inputLength (duplicateBits inputLength) <|
    occurrenceStageBits inputLength
      (preserveRightBits quadBits inputLength inputLength quad) <|
      occurrenceStageBits inputLength (swapPairBits quad inputLength) <|
        occurrenceStageBits inputLength
          (preserveRightBits tripleBits inputLength quad triple)
          (swapPairBits triple quad)

/-- **The two halves, paired.** -/
theorem run_occurrencePacketPairProgram
    (quadProgram tripleProgram : NPOracleProgram)
    (inputLength quadBits quadFuel tripleBits tripleFuel quad triple : ℕ)
    (hquad :
      runNPOracleProgram quadProgram quadBits quadFuel
          (initialNPOracleState inputLength inputLength) = some quad)
    (htriple :
      runNPOracleProgram tripleProgram tripleBits tripleFuel
          (initialNPOracleState inputLength inputLength) = some triple) :
    runNPOracleProgram (occurrencePacketPairProgram quadProgram tripleProgram)
        (occurrencePacketPairBits inputLength quadBits tripleBits quad triple)
        (occurrencePacketPairFuel quadProgram tripleProgram quadFuel tripleFuel)
        (initialNPOracleState inputLength inputLength) =
      some (Nat.pair quad triple) :=
  run_occurrenceStage (run_duplicateProgram inputLength inputLength)
    (run_occurrenceStage
      (run_preserveRightProgram quadProgram inputLength quadBits quadFuel
        inputLength inputLength quad hquad)
      (run_occurrenceStage (run_swapPairProgram inputLength quad inputLength)
        (run_occurrenceStage
          (run_preserveRightProgram tripleProgram inputLength tripleBits
            tripleFuel inputLength quad triple htriple)
          (run_swapPairProgram inputLength triple quad))))

/-- The published packet stream: the schedule quad of §2 beside the oracle
triple. -/
noncomputable def inverseOccurrencePacketProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (tripleProgram : NPOracleProgram) :
    NPOracleProgram :=
  occurrencePacketPairProgram
    (inverseOccurrenceQuadProgram contracts clockDepth advantageExponent)
    tripleProgram

theorem inverseOccurrencePacketProgram_oracleFree
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) {tripleProgram : NPOracleProgram}
    (htriple : OracleFree tripleProgram) :
    OracleFree
      (inverseOccurrencePacketProgram contracts clockDepth advantageExponent
        tripleProgram) :=
  occurrencePacketPairProgram_oracleFree
    (inverseOccurrenceQuadProgram_oracleFree contracts clockDepth
      advantageExponent)
    htriple

noncomputable def inverseOccurrencePacketFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (tripleProgram : NPOracleProgram)
    (tripleFuel : ℕ → ℕ) (target : ℕ) : ℕ :=
  occurrencePacketPairFuel
    (inverseOccurrenceQuadProgram contracts clockDepth advantageExponent)
    tripleProgram
    (inverseOccurrenceQuadFuel contracts clockDepth advantageExponent target)
    (tripleFuel target)

open Classical in
/-- The packet stream's width at one target, quoted at the oracle the
schedule's own branch carries.  Only the triple's output width is
oracle-derived, so this is the one branch read the pairing needs. -/
noncomputable def inverseOccurrencePacketBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (tripleBits : ℕ → ℕ) (target : ℕ) : ℕ :=
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
        occurrencePacketPairBits target
          (inverseOccurrenceQuadBits contracts clockDepth advantageExponent
            target)
          (tripleBits target)
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target)
          (inverseOccurrenceTripleWord contracts clockDepth machine
            advantageExponent target caseTwo)
  else 0

set_option maxHeartbeats 1600000 in
-- The statement carries the paired stream, both branch envelopes and the whole
-- seven-numeral packet at one target, so elaborating it alone exceeds the
-- default budget.
/-- **The seven-numeral premise, from the oracle triple alone.**  The schedule
quad is discharged outright by §2, so the only correctness datum left in
`InverseScheduledOccurrencePacket` is the three oracle numerals. -/
theorem inverseScheduledOccurrencePacket_ofTriple
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (tripleProgram : NPOracleProgram) (tripleBits tripleFuel : ℕ → ℕ)
    (htriples :
      InverseScheduledOccurrenceTriple contracts clockDepth machine
        advantageExponent tripleProgram tripleBits tripleFuel) :
    InverseScheduledOccurrencePacket contracts clockDepth machine
      advantageExponent
      (inverseOccurrencePacketProgram contracts clockDepth advantageExponent
        tripleProgram)
      (inverseOccurrencePacketBits contracts clockDepth machine
        advantageExponent tripleBits)
      (inverseOccurrencePacketFuel contracts clockDepth advantageExponent
        tripleProgram tripleFuel) := by
  intro target hlarge hyes caseTwo hbranch
  have hquad :=
    run_inverseOccurrenceQuadProgram contracts clockDepth advantageExponent
      target (hdiagonal target hlarge)
  have htriple := htriples target hlarge hyes caseTwo hbranch
  have hbits :
      inverseOccurrencePacketBits contracts clockDepth machine advantageExponent
          tripleBits target =
        occurrencePacketPairBits target
          (inverseOccurrenceQuadBits contracts clockDepth advantageExponent
            target)
          (tripleBits target)
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target)
          (inverseOccurrenceTripleWord contracts clockDepth machine
            advantageExponent target caseTwo) := by
    simp only [inverseOccurrencePacketBits]
    rw [dif_pos hyes, hbranch]
  have hpacket :
      inverseCaseTwoOccurrencePacket contracts clockDepth machine
          advantageExponent target caseTwo =
        Nat.pair
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target)
          (inverseOccurrenceTripleWord contracts clockDepth machine
            advantageExponent target caseTwo) :=
    rfl
  rw [hbits, hpacket, inverseOccurrencePacketProgram,
    inverseOccurrencePacketFuel]
  exact run_occurrencePacketPairProgram
    (inverseOccurrenceQuadProgram contracts clockDepth advantageExponent)
    tripleProgram target
    (inverseOccurrenceQuadBits contracts clockDepth advantageExponent target)
    (inverseOccurrenceQuadFuel contracts clockDepth advantageExponent target)
    (tripleBits target) (tripleFuel target)
    (inverseOccurrenceQuadWord contracts clockDepth advantageExponent target)
    (inverseOccurrenceTripleWord contracts clockDepth machine advantageExponent
      target caseTwo)
    hquad htriple

/-! ## 5. What the cluster closure still needs -/

set_option maxHeartbeats 1600000 in
-- The statement is the cluster's whole three-way conjunction at the paired
-- packet stream, so elaborating it alone exceeds the default budget.
/-- **The bank/diagonal cluster's three residuals, from the oracle numerals
alone.**  `RuntimeCaseTwoOccurrenceClosure.inverse_clusterResiduals_ofPacket`
carried all seven occurrence numerals; §2 discharges four of them, so the
cluster now needs only the padded presentation, the onset-restricted schedule
diagonal, the scheduled query-count positivity, and one program emitting the
*three oracle* numerals from the public length. -/
theorem inverse_clusterResiduals_ofTriple
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
    (tripleProgram : NPOracleProgram) (tripleBits tripleFuel : ℕ → ℕ)
    (hcounts :
      InverseScheduledQueryCounts contracts clockDepth advantageExponent)
    (htriples :
      InverseScheduledOccurrenceTriple contracts clockDepth machine
        advantageExponent tripleProgram tripleBits tripleFuel) :
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
              advantageExponent
              (inverseOccurrencePacketBits contracts clockDepth machine
                advantageExponent tripleBits))))
        (residualChainFuel contracts clockDepth machine advantageExponent
          (inverseScheduledRowProgram contracts clockDepth)
          (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
            (inverseOccurrencePacketProgram contracts clockDepth
              advantageExponent tripleProgram))
          (inverseScheduledRowFuel contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyFuel contracts clockDepth machine
            advantageExponent
            (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
              (inverseOccurrencePacketProgram contracts clockDepth
                advantageExponent tripleProgram))
            (inverseOccurrenceBranchFuel contracts clockDepth machine
              advantageExponent
              (inverseOccurrencePacketProgram contracts clockDepth
                advantageExponent tripleProgram)
              (inverseOccurrencePacketFuel contracts clockDepth
                advantageExponent tripleProgram tripleFuel)))) ∧
      InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
        (inverseChainTwoProgram contracts clockDepth advantageExponent
          (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
            (inverseOccurrencePacketProgram contracts clockDepth
              advantageExponent tripleProgram)))
        (residualChainBits contracts clockDepth machine advantageExponent
          (inverseScheduledRowBits contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyBits contracts clockDepth machine
            advantageExponent
            (inverseOccurrenceBranchBits contracts clockDepth machine
              advantageExponent
              (inverseOccurrencePacketBits contracts clockDepth machine
                advantageExponent tripleBits))))
        (residualChainFuel contracts clockDepth machine advantageExponent
          (inverseScheduledRowProgram contracts clockDepth)
          (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
            (inverseOccurrencePacketProgram contracts clockDepth
              advantageExponent tripleProgram))
          (inverseScheduledRowFuel contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyFuel contracts clockDepth machine
            advantageExponent
            (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
              (inverseOccurrencePacketProgram contracts clockDepth
                advantageExponent tripleProgram))
            (inverseOccurrenceBranchFuel contracts clockDepth machine
              advantageExponent
              (inverseOccurrencePacketProgram contracts clockDepth
                advantageExponent tripleProgram)
              (inverseOccurrencePacketFuel contracts clockDepth
                advantageExponent tripleProgram tripleFuel)))) :=
  inverse_clusterResiduals_ofPacket contracts clockDepth machine
    advantageExponent pcp hpresentation hdiagonal
    (inverseOccurrencePacketProgram contracts clockDepth advantageExponent
      tripleProgram)
    (inverseOccurrencePacketBits contracts clockDepth machine advantageExponent
      tripleBits)
    (inverseOccurrencePacketFuel contracts clockDepth advantageExponent
      tripleProgram tripleFuel)
    hcounts
    (inverseScheduledOccurrencePacket_ofTriple contracts clockDepth machine
      advantageExponent hdiagonal tripleProgram tripleBits tripleFuel htriples)

/-! ## 6. The two codec identities the oracle triple needs

`caseTwoSubstitutedCircuit caseTwo` is the substitution runner's own circuit
wrapped in two syntactic transforms — an inner restriction of the recovered
oracle to the native face, and an outer arity padding.  Neither had an
encoding-level lemma anywhere in the tree, so the encoder could not even be
decomposed.  The two lemmas below supply them, and each lands on a canonical
balanced-list operation that already has a fixed program. -/

/-- **Padding, at the encoding.**  Appending unreachable constants appends the
same constant *code* to the encoded node list and leaves the output address
alone: the outer `padToArity` is one `encodeBalancedList` append. -/
theorem encodeBooleanCircuit_padSize {n : ℕ}
    (circuit : BooleanCircuit n) (count : ℕ) :
    encodeBooleanCircuit (circuit.padSize count) =
      encodeTaggedList
        [encodeBalancedList
            (circuit.nodes.map encodeBooleanNode ++
              List.replicate count
                (encodeBooleanNode (BooleanNode.const false : BooleanNode n))),
          encodeNat circuit.output.val] := by
  have hnodes :
      (circuit.padSize count).nodes =
        circuit.nodes ++
          List.replicate count (BooleanNode.const false : BooleanNode n) := by
    change (circuit.toBuilder.appendFalse count).nodes = _
    rw [BooleanDAGBuilder.appendFalse_nodes]
    rfl
  have houtput : (circuit.padSize count).output.val = circuit.output.val := rfl
  simp only [encodeBooleanCircuit, hnodes, houtput, List.map_append,
    List.map_replicate]

/-- The same identity at the minimal padding the pointwise-PCPP precondition
forces. -/
theorem encodeBooleanCircuit_padToArity {n : ℕ} (circuit : BooleanCircuit n) :
    encodeBooleanCircuit circuit.padToArity =
      encodeTaggedList
        [encodeBalancedList
            (circuit.nodes.map encodeBooleanNode ++
              List.replicate (n - circuit.size)
                (encodeBooleanNode (BooleanNode.const false : BooleanNode n))),
          encodeNat circuit.output.val] :=
  encodeBooleanCircuit_padSize circuit (n - circuit.size)

/-- **Restriction, at the encoding.**  Restricting to a face rewrites every
node in place and leaves the output address alone: the inner
`restrictPaddedOracle` is one `encodeBalancedList` map of a per-node
transform. -/
theorem encodeBooleanCircuit_restrictBooleanCircuit {core target : ℕ}
    (circuit : BooleanCircuit target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    encodeBooleanCircuit (restrictBooleanCircuit circuit hcore padding) =
      encodeTaggedList
        [encodeBalancedList
            (circuit.nodes.map fun node =>
              encodeBooleanNode (restrictBooleanNode hcore padding node)),
          encodeNat circuit.output.val] := by
  simp only [encodeBooleanCircuit, restrictBooleanCircuit, List.map_map,
    Function.comp_def]

/-- The same identity at the zero-suffix face the padded verifier queries. -/
theorem encodeBooleanCircuit_restrictPaddedOracle {native padded : ℕ}
    (circuit : BooleanCircuit padded) (hwidth : native ≤ padded) :
    encodeBooleanCircuit (restrictPaddedOracle circuit hwidth) =
      encodeTaggedList
        [encodeBalancedList
            (circuit.nodes.map fun node =>
              encodeBooleanNode
                (restrictBooleanNode hwidth
                  (zeroPadding (native := native) (padded := padded)) node)),
          encodeNat circuit.output.val] :=
  encodeBooleanCircuit_restrictBooleanCircuit circuit hwidth zeroPadding

/-- **The oracle triple's encoder, decomposed.**  The substituted circuit's
encoding is one balanced append over the substitution runner's own output, and
the runner's request carries one balanced map over the recovered oracle. -/
theorem encodeBooleanCircuit_caseTwoSubstitutedCircuit
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo) =
      encodeTaggedList
        [encodeBalancedList
            ((outer.substitutedCircuit input
                  (restrictPaddedOracle caseTwo.circuit
                    (nativeWidth_le_widthEnvelope outer
                      (sourceLength sourceIndex)))).nodes.map
                encodeBooleanNode ++
              List.replicate
                (outer.pcp.nativeWidth (sourceLength sourceIndex) -
                  (outer.substitutedCircuit input
                    (restrictPaddedOracle caseTwo.circuit
                      (nativeWidth_le_widthEnvelope outer
                        (sourceLength sourceIndex)))).size)
                (encodeBooleanNode
                  (BooleanNode.const false :
                    BooleanNode (outer.pcp.nativeWidth
                      (sourceLength sourceIndex))))),
          encodeNat
            (outer.substitutedCircuit input
              (restrictPaddedOracle caseTwo.circuit
                (nativeWidth_le_widthEnvelope outer
                  (sourceLength sourceIndex)))).output.val] :=
  encodeBooleanCircuit_padToArity
    (outer.substitutedCircuit input
      (restrictPaddedOracle caseTwo.circuit
        (nativeWidth_le_widthEnvelope outer (sourceLength sourceIndex))))

/-- The triple's second numeral, in the substitution runner's own size. -/
theorem caseTwoSubstitutedCircuit_size
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    (caseTwoSubstitutedCircuit caseTwo).size =
      (outer.substitutedCircuit input
          (restrictPaddedOracle caseTwo.circuit
            (nativeWidth_le_widthEnvelope outer (sourceLength sourceIndex)))).size +
        (outer.pcp.nativeWidth (sourceLength sourceIndex) -
          (outer.substitutedCircuit input
            (restrictPaddedOracle caseTwo.circuit
              (nativeWidth_le_widthEnvelope outer
                (sourceLength sourceIndex)))).size) :=
  BooleanCircuit.padSize_size _ _

end NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
