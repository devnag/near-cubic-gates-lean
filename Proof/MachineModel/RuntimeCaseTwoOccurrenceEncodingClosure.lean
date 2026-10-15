import Proof.MachineModel.RuntimeCaseTwoOccurrencePacketSplit
import Proof.MachineModel.RuntimeCaseTwoOracleTripleProgram

/-!
# The Case-2 occurrence residual, reduced to one numeral

`RuntimeCaseTwoOccurrencePacketSplit` cut the seven-numeral premise down to the
oracle triple: the published factory's clause width at the Case-2 substituted
circuit, that circuit's size, and its encoding.  `RuntimeCaseTwoOracleTripleProgram`
shows the first two are fixed-program functions of the third together with the
circuit's arity — and the arity is the schedule quad's second numeral, which §2
of the split module already emits.

So the whole oracle half collapses to the **single** encoder

> `InverseScheduledOccurrenceEncoding` — one fixed program that, from the
> requested public length alone, emits
> `encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)` at the oracle the
> branch carries.

§1 states it.  §2 assembles the arity stream beside it and re-proves the oracle
triple.  §3 restates the bank/diagonal cluster's three residuals at that single
premise.  This is the residue the prose of `RuntimeCaseTwoOccurrenceClosure`
predicted, now as a theorem rather than a remark.

## Where the register discipline goes

The arity is read from the published shape runner at the target's own public
length, which the schedule diagonal identifies with the scheduled source
length; the encoder is entered at the same length; and the assembled pair is
handed to the frozen triple stream through the ordinary
`CanonicalNativeCallProgram` frame inside it.  Both envelopes are branch reads
for the reason `BankCaseTwoEnvelopeClosure` records — the Case-2 oracle is
bound inside the premise — and here the *fuel* is a branch read too, since the
factory's own runner budgets are stated at the substituted circuit.
-/

namespace NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.BankResidualClusterClosure
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BankScheduledRowStageClosure
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram
open NearCubicWires.RuntimeCaseTwoOccurrenceClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeCaseTwoOracleTripleProgram
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.RuntimeScheduleQuadNumeralProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The single encoder -/

/-- **The Case-2 occurrence residual, as one numeral.**  One fixed program
that, from the requested public length alone, emits the encoding of the
substituted circuit of the oracle the branch carries. -/
def InverseScheduledOccurrenceEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (encodingProgram : NPOracleProgram)
    (encodingBits encodingFuel : ℕ → ℕ) : Prop :=
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
    runNPOracleProgram encodingProgram (encodingBits target)
        (encodingFuel target) (initialNPOracleState target target) =
      some (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo))

/-! ## 2. The oracle triple from the encoder -/

/-- The published arity stream: the outer native width at the target's own
public length. -/
noncomputable def inverseNativeWidthProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) : NPOracleProgram :=
  nativeWidthProgram
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program

noncomputable def inverseNativeWidthBits
    (contracts : PublishedContracts) (clockDepth : ℕ) (target : ℕ) : ℕ :=
  nativeWidthBits target
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget target)
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.execute target)

noncomputable def inverseNativeWidthFuel
    (contracts : PublishedContracts) (clockDepth : ℕ) (target : ℕ) : ℕ :=
  nativeWidthFuel
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget target)

/-- **The published triple stream.**  Arity beside encoding, then the frozen
oracle-triple assembler of `RuntimeCaseTwoOracleTripleProgram`. -/
noncomputable def inverseEncodedTripleProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (encodingProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (occurrencePacketPairProgram (inverseNativeWidthProgram contracts clockDepth)
      encodingProgram)
    (oracleTripleProgram (publishedPointwisePCPP contracts).factory)

theorem inverseEncodedTripleProgram_oracleFree
    (contracts : PublishedContracts) (clockDepth : ℕ)
    {encodingProgram : NPOracleProgram} (hencoding : OracleFree encodingProgram) :
    OracleFree
      (inverseEncodedTripleProgram contracts clockDepth encodingProgram) :=
  oracleFree_linkPrograms
    (occurrencePacketPairProgram_oracleFree
      (nativeWidthProgram_oracleFree
        (publishedHierarchyOuterPCP contracts clockDepth).pcp.shapeOracleFree)
      hencoding)
    (oracleTripleProgram_oracleFree (publishedPointwisePCPP contracts).factory)

open Classical in
/-- The triple stream's width at one target, quoted at the oracle the
schedule's own branch carries. -/
noncomputable def inverseEncodedTripleBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (encodingBits : ℕ → ℕ) (target : ℕ) : ℕ :=
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
        occurrenceStageBits target
          (occurrencePacketPairBits target
            (inverseNativeWidthBits contracts clockDepth target)
            (encodingBits target)
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
              (sourceLength
                (inverseChainSourceIndex contracts clockDepth advantageExponent
                  target)))
            (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)))
          (oracleTripleBits (publishedPointwisePCPP contracts).factory target
            (caseTwoSubstitutedCircuit caseTwo))
  else 0

open Classical in
/-- The triple stream's clock at one target, quoted at the branch's oracle: the
factory's own runner budgets are stated at the substituted circuit, so the
clock is a branch read as well. -/
noncomputable def inverseEncodedTripleFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (encodingProgram : NPOracleProgram) (encodingFuel : ℕ → ℕ)
    (target : ℕ) : ℕ :=
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
        linkFuel (oracleTripleProgram (publishedPointwisePCPP contracts).factory)
          (occurrencePacketPairFuel
            (inverseNativeWidthProgram contracts clockDepth) encodingProgram
            (inverseNativeWidthFuel contracts clockDepth target)
            (encodingFuel target))
          (oracleTripleFuel (publishedPointwisePCPP contracts).factory
            (caseTwoSubstitutedCircuit caseTwo))
  else 0

private theorem occurrenceTripleWord_eq_oracleTripleWord
    (nativeClauseBits circuitSize encoded : ℕ) :
    occurrenceTripleWord nativeClauseBits circuitSize encoded =
      oracleTripleWord nativeClauseBits circuitSize encoded :=
  rfl

set_option maxHeartbeats 1600000 in
-- The statement carries the published triple stream and both branch envelopes
-- at one target, so elaborating it alone exceeds the default budget.
/-- **The oracle triple, from the encoder alone.**  The factory's clause width
and the circuit's size are fixed-program functions of the encoding and the
schedule's own arity, so `InverseScheduledOccurrenceTriple` follows from the
single encoder and the schedule diagonal. -/
theorem inverseScheduledOccurrenceTriple_ofEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (encodingProgram : NPOracleProgram) (encodingBits encodingFuel : ℕ → ℕ)
    (hencodings :
      InverseScheduledOccurrenceEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingBits encodingFuel) :
    InverseScheduledOccurrenceTriple contracts clockDepth machine
      advantageExponent
      (inverseEncodedTripleProgram contracts clockDepth encodingProgram)
      (inverseEncodedTripleBits contracts clockDepth machine advantageExponent
        encodingBits)
      (inverseEncodedTripleFuel contracts clockDepth machine advantageExponent
        encodingProgram encodingFuel) := by
  intro target hlarge hyes caseTwo hbranch
  have hlength :
      sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target) =
        target := (hdiagonal target hlarge).symm
  have harity :
      runNPOracleProgram (inverseNativeWidthProgram contracts clockDepth)
          (inverseNativeWidthBits contracts clockDepth target)
          (inverseNativeWidthFuel contracts clockDepth target)
          (initialNPOracleState target target) =
        some
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
            (sourceLength
              (inverseChainSourceIndex contracts clockDepth advantageExponent
                target))) := by
    rw [hlength]
    exact run_nativeWidthProgram
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program target
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget target)
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget target)
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.execute
        target)
      (run_publishedShapeProgram
        (publishedHierarchyOuterPCP contracts clockDepth) target)
  have hencoding := hencodings target hlarge hyes caseTwo hbranch
  have hbits :
      inverseEncodedTripleBits contracts clockDepth machine advantageExponent
          encodingBits target =
        occurrenceStageBits target
          (occurrencePacketPairBits target
            (inverseNativeWidthBits contracts clockDepth target)
            (encodingBits target)
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
              (sourceLength
                (inverseChainSourceIndex contracts clockDepth advantageExponent
                  target)))
            (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)))
          (oracleTripleBits (publishedPointwisePCPP contracts).factory target
            (caseTwoSubstitutedCircuit caseTwo)) := by
    simp only [inverseEncodedTripleBits]
    rw [dif_pos hyes, hbranch]
  have hfuel :
      inverseEncodedTripleFuel contracts clockDepth machine advantageExponent
          encodingProgram encodingFuel target =
        linkFuel (oracleTripleProgram (publishedPointwisePCPP contracts).factory)
          (occurrencePacketPairFuel
            (inverseNativeWidthProgram contracts clockDepth) encodingProgram
            (inverseNativeWidthFuel contracts clockDepth target)
            (encodingFuel target))
          (oracleTripleFuel (publishedPointwisePCPP contracts).factory
            (caseTwoSubstitutedCircuit caseTwo)) := by
    simp only [inverseEncodedTripleFuel]
    rw [dif_pos hyes, hbranch]
  have hword :
      inverseOccurrenceTripleWord contracts clockDepth machine advantageExponent
          target caseTwo =
        oracleTripleWord
          ((publishedPointwisePCPP contracts).factory.forCircuit
            (caseTwoSubstitutedCircuit caseTwo)).clauseBits
          (caseTwoSubstitutedCircuit caseTwo).size
          (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)) :=
    rfl
  rw [hbits, hfuel, hword, inverseEncodedTripleProgram]
  exact run_occurrenceStage
    (run_occurrencePacketPairProgram
      (inverseNativeWidthProgram contracts clockDepth) encodingProgram target
      (inverseNativeWidthBits contracts clockDepth target)
      (inverseNativeWidthFuel contracts clockDepth target) (encodingBits target)
      (encodingFuel target)
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target)))
      (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)) harity
      hencoding)
    (run_oracleTripleProgram (publishedPointwisePCPP contracts).factory target
      (caseTwoSubstitutedCircuit caseTwo))

/-! ## 3. What the cluster closure still needs -/

set_option maxHeartbeats 1600000 in
-- The statement is the cluster's whole three-way conjunction at the encoder's
-- packet stream, so elaborating it alone exceeds the default budget.
/-- **The bank/diagonal cluster's three residuals, from the single encoder.**
Six of the seven occurrence numerals are now discharged outright — four by the
schedule quad, two by the factory's own runners — so the cluster needs the
padded presentation, the onset-restricted schedule diagonal, the scheduled
query-count positivity, and *one program emitting the substituted circuit's
encoding* from the public length. -/
theorem inverse_clusterResiduals_ofEncoding
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
    (encodingProgram : NPOracleProgram) (encodingBits encodingFuel : ℕ → ℕ)
    (hcounts :
      InverseScheduledQueryCounts contracts clockDepth advantageExponent)
    (hencodings :
      InverseScheduledOccurrenceEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingBits encodingFuel) :
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
                advantageExponent
                (inverseEncodedTripleBits contracts clockDepth machine
                  advantageExponent encodingBits)))))
        (residualChainFuel contracts clockDepth machine advantageExponent
          (inverseScheduledRowProgram contracts clockDepth)
          (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
            (inverseOccurrencePacketProgram contracts clockDepth
              advantageExponent
              (inverseEncodedTripleProgram contracts clockDepth
                encodingProgram)))
          (inverseScheduledRowFuel contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyFuel contracts clockDepth machine
            advantageExponent
            (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
              (inverseOccurrencePacketProgram contracts clockDepth
                advantageExponent
                (inverseEncodedTripleProgram contracts clockDepth
                  encodingProgram)))
            (inverseOccurrenceBranchFuel contracts clockDepth machine
              advantageExponent
              (inverseOccurrencePacketProgram contracts clockDepth
                advantageExponent
                (inverseEncodedTripleProgram contracts clockDepth
                  encodingProgram))
              (inverseOccurrencePacketFuel contracts clockDepth
                advantageExponent
                (inverseEncodedTripleProgram contracts clockDepth
                  encodingProgram)
                (inverseEncodedTripleFuel contracts clockDepth machine
                  advantageExponent encodingProgram encodingFuel))))) ∧
      InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
        (inverseChainTwoProgram contracts clockDepth advantageExponent
          (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
            (inverseOccurrencePacketProgram contracts clockDepth
              advantageExponent
              (inverseEncodedTripleProgram contracts clockDepth
                encodingProgram))))
        (residualChainBits contracts clockDepth machine advantageExponent
          (inverseScheduledRowBits contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyBits contracts clockDepth machine
            advantageExponent
            (inverseOccurrenceBranchBits contracts clockDepth machine
              advantageExponent
              (inverseOccurrencePacketBits contracts clockDepth machine
                advantageExponent
                (inverseEncodedTripleBits contracts clockDepth machine
                  advantageExponent encodingBits)))))
        (residualChainFuel contracts clockDepth machine advantageExponent
          (inverseScheduledRowProgram contracts clockDepth)
          (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
            (inverseOccurrencePacketProgram contracts clockDepth
              advantageExponent
              (inverseEncodedTripleProgram contracts clockDepth
                encodingProgram)))
          (inverseScheduledRowFuel contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyFuel contracts clockDepth machine
            advantageExponent
            (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
              (inverseOccurrencePacketProgram contracts clockDepth
                advantageExponent
                (inverseEncodedTripleProgram contracts clockDepth
                  encodingProgram)))
            (inverseOccurrenceBranchFuel contracts clockDepth machine
              advantageExponent
              (inverseOccurrencePacketProgram contracts clockDepth
                advantageExponent
                (inverseEncodedTripleProgram contracts clockDepth
                  encodingProgram))
              (inverseOccurrencePacketFuel contracts clockDepth
                advantageExponent
                (inverseEncodedTripleProgram contracts clockDepth
                  encodingProgram)
                (inverseEncodedTripleFuel contracts clockDepth machine
                  advantageExponent encodingProgram encodingFuel))))) :=
  inverse_clusterResiduals_ofTriple contracts clockDepth machine
    advantageExponent pcp hpresentation hdiagonal
    (inverseEncodedTripleProgram contracts clockDepth encodingProgram)
    (inverseEncodedTripleBits contracts clockDepth machine advantageExponent
      encodingBits)
    (inverseEncodedTripleFuel contracts clockDepth machine advantageExponent
      encodingProgram encodingFuel)
    hcounts
    (inverseScheduledOccurrenceTriple_ofEncoding contracts clockDepth machine
      advantageExponent hdiagonal encodingProgram encodingBits encodingFuel
      hencodings)

end NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
