import Proof.MachineModel.CanonicalFourfoldRowProducerDispatchProgram
import Proof.MachineModel.CanonicalSignedGateEvaluationProgram

/-!
# The symmetric row table producer, linked to its front end

`CanonicalSignedGateEvaluationProgram` §10 compiles the residual assignment
table of an arbitrary occurrence pool from one host-shaped input,

```text
    residualAssignmentTableInput occurrences inputMask liveMask
```

and `CanonicalFourfoldRowProducerDispatchProgram` §4 consumes the resulting
context as the `htable` premise of the fork row evaluator.  Between them sits
exactly one front end: the program turning a row-tail handoff into that input.

This module is the seam.  It fixes the linked producer

```text
    symmetricRowTableProgram requestProgram :=
      linkPrograms requestProgram residualAssignmentTableProgram
```

and discharges `htable` from a single interpreter premise on
`requestProgram`, with the greedy live-set selector entering only through the
abstract mask equation `hlive`.  The same premise then instantiates the
symmetric fork row evaluator, so the whole symmetric row evaluator is a fixed
program over exactly two link-time producers with one exact contract each.
-/

namespace NearCubicWires.CanonicalSymmetricRowTableProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalFourfoldRowProducerDispatchProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalFourfoldRowTailProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.CanonicalStructuralGF2EvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 The linked table producer

The front end is a link-time parameter with one exact contract.  Nothing below
inspects it, so the same theorem serves the symmetric family however that
front end is eventually compiled. -/

/-- **The symmetric row table producer.**  A front end emitting the pool's
request list, then the fixed residual assignment table machine. -/
def symmetricRowTableProgram (requestProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms requestProgram residualAssignmentTableProgram

theorem symmetricRowTableProgram_oracleFree
    (requestProgram : NPOracleProgram) (hrequest : OracleFree requestProgram) :
    OracleFree (symmetricRowTableProgram requestProgram) :=
  oracleFree_linkPrograms hrequest residualAssignmentTableProgram_oracleFree

/-- The row's occurrence pool, named once. -/
def symmetricRowOccurrences
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List (SupportedNormalizedGate request.q) :=
  symmetricFourfoldOccurrences request

/-- The row's live set, named once. -/
def symmetricRowLiveSet
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) : Finset (Fin request.q) :=
  normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale

def symmetricRowTableFuel
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (requestFuel inputMask liveMask : ℕ) : ℕ :=
  linkFuel residualAssignmentTableProgram requestFuel
    (residualAssignmentTableFuel (symmetricRowOccurrences request) inputMask
      liveMask)

def symmetricRowTableStageBits
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (input : BitInput request.q) (inputMask liveMask : ℕ) :
    ℕ :=
  max 1 <| max (natBitLength request.q) <|
    residualAssignmentTableBits (symmetricRowOccurrences request)
      (symmetricRowLiveSet request liveScale) input inputMask liveMask

/-- **The symmetric row's residual assignment context, executed from the
handoff.**  This is exactly the `htable` premise of
`run_structuralForkRowEvaluatorProgram_symmetricRow`, reduced to one contract
on the front end. -/
theorem run_symmetricRowTableProgram
    (requestProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale rowIndex : ℕ) (input : BitInput request.q)
    (liveMask maximumBits requestFuel : ℕ)
    (hlive : liveMask = coordinateMask (symmetricRowLiveSet request liveScale))
    (hbits :
      symmetricRowTableStageBits request liveScale input
          (encodeBitInput input) liveMask ≤
        maximumBits)
    (hrequest :
      runNPOracleProgram requestProgram maximumBits requestFuel
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (residualAssignmentTableInput (symmetricRowOccurrences request)
            (encodeBitInput input) liveMask)) :
    runNPOracleProgram (symmetricRowTableProgram requestProgram) maximumBits
        (symmetricRowTableFuel request requestFuel (encodeBitInput input)
          liveMask)
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
      some
        (finiteAssignmentContext
          (symmetricRowResidualAssignment request liveScale input)) := by
  have hpositive : 1 ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [symmetricRowTableStageBits]
  have hlength : natBitLength request.q ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [symmetricRowTableStageBits]
  have htableBits :
      residualAssignmentTableBits (symmetricRowOccurrences request)
          (symmetricRowLiveSet request liveScale) input (encodeBitInput input)
          liveMask ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [symmetricRowTableStageBits]
  have htable :=
    run_symmetricRowResidualAssignmentTableProgram request liveScale input
      (encodeBitInput input) liveMask maximumBits rfl hlive htableBits
  exact run_linkPrograms hpositive hlength hrequest htable

/-! ## §2 The symmetric fork row evaluator over the front end

Substituting §1 into the dispatcher's row theorem replaces the `htable`
premise by the front end's own contract.  The remaining producer premise is
the polynomial side, stated on every row index through the total row
polynomial of the dispatch module. -/

def symmetricRowForkEvaluatorProgram
    (requestProgram polynomialProgram : NPOracleProgram) : NPOracleProgram :=
  structuralForkRowEvaluatorProgram (symmetricRowTableProgram requestProgram)
    polynomialProgram

theorem symmetricRowForkEvaluatorProgram_oracleFree
    (requestProgram polynomialProgram : NPOracleProgram)
    (hrequest : OracleFree requestProgram)
    (hpolynomial : OracleFree polynomialProgram) :
    OracleFree (symmetricRowForkEvaluatorProgram requestProgram
      polynomialProgram) :=
  structuralForkRowEvaluatorProgram_oracleFree
    (symmetricRowTableProgram requestProgram) polynomialProgram
    (symmetricRowTableProgram_oracleFree requestProgram hrequest) hpolynomial

noncomputable def symmetricRowForkEvaluatorFuel
    (requestProgram polynomialProgram : NPOracleProgram)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (requestFuel polynomialFuel liveMask : ℕ) : ℕ :=
  structuralForkRowEvaluatorFuel (symmetricRowTableProgram requestProgram)
    polynomialProgram
    (symmetricRowTableFuel request requestFuel (encodeBitInput input) liveMask)
    polynomialFuel (symmetricRowResidualAssignment request liveScale input)
    (symmetricRowPolynomial request liveScale accuracyExponent rowIndex input)

/-- **The symmetric fork row evaluator over its front end.**  The table half is
now one interpreter premise about the request producer; the polynomial half is
unchanged. -/
theorem run_symmetricRowForkEvaluatorProgram
    (requestProgram polynomialProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (liveMask maximumBits tableBits polynomialBits requestFuel
      polynomialFuel : ℕ)
    (hlive : liveMask = coordinateMask (symmetricRowLiveSet request liveScale))
    (htableBits :
      symmetricRowTableStageBits request liveScale input
          (encodeBitInput input) liveMask ≤
        tableBits)
    (hbits :
      structuralForkRowEvaluatorBits request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
          tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
            input) ≤
        maximumBits)
    (hrequest :
      runNPOracleProgram requestProgram tableBits requestFuel
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (residualAssignmentTableInput (symmetricRowOccurrences request)
            (encodeBitInput input) liveMask))
    (hpolynomial :
      runNPOracleProgram polynomialProgram polynomialBits polynomialFuel
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (encodedStructuralGF2
            (symmetricRowPolynomial request liveScale accuracyExponent
              rowIndex input))) :
    runNPOracleProgram
        (symmetricRowForkEvaluatorProgram requestProgram polynomialProgram)
        maximumBits
        (symmetricRowForkEvaluatorFuel requestProgram polynomialProgram
          request liveScale accuracyExponent rowIndex input requestFuel
          polynomialFuel liveMask)
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) :=
  run_structuralForkRowEvaluatorProgram_symmetricRow
    (symmetricRowTableProgram requestProgram) polynomialProgram algorithm
    request liveScale accuracyExponent rowIndex input maximumBits tableBits
    polynomialBits
    (symmetricRowTableFuel request requestFuel (encodeBitInput input) liveMask)
    polynomialFuel hbits
    (run_symmetricRowTableProgram requestProgram algorithm request liveScale
      rowIndex input liveMask tableBits requestFuel hlive htableBits hrequest)
    hpolynomial

end NearCubicWires.CanonicalSymmetricRowTableProgram
