import Proof.PCP.PaddedProjectionRunnerAssembly
import Proof.MachineModel.RuntimeScheduleNumeralBank

/-!
# The padded shape runner

The first of the three runners `PaddedProjectionRunnerAssembly` asks for: one
fixed instruction stream emitting

`Nat.pair (widthEnvelope outer n) (outer.pcp.queryCount n)`

from the public length alone.  Neither component is recomputed here.  The
width envelope is `RuntimeScheduleNumeralBank.widthEnvelopeProgram`, whose
floor logarithm is already derived from the published ceiling-logarithm loop;
the query count is read at run time out of the published shape runner's own
output, so the padded runner bakes no shape numeral as an immediate.

Only two framing streams are new, and both are straight-line: one self-pairing
duplicator and one four-register reframer.  Everything else is
`PreserveRightProgram.preserveRightProgram` and one verified link per stage.
-/

namespace NearCubicWires.PaddedProjectionShapeRunner

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The two straight-line framing streams -/

private theorem bits_of_le_pair_left {value left right : ℕ}
    (hvalue : value ≤ left) :
    natBitLength value ≤ natBitLength (Nat.pair left right) :=
  natBitLength_mono (hvalue.trans (Nat.left_le_pair left right))

private theorem bits_of_le_pair_right {value left right : ℕ}
    (hvalue : value ≤ right) :
    natBitLength value ≤ natBitLength (Nat.pair left right) :=
  natBitLength_mono (hvalue.trans (Nat.right_le_pair left right))

/-- Present the request code beside itself. -/
private def duplicateProgram : NPOracleProgram :=
  [ .pair 0 0 0 1
  , .halt 0
  ]

@[simp] private theorem duplicateProgram_oracleFree :
    OracleFree duplicateProgram := by
  rfl

private theorem run_duplicateProgram (inputLength value : ℕ) :
    runNPOracleProgram duplicateProgram (natBitLength (Nat.pair value value)) 2
        (initialNPOracleState inputLength value) =
      some (Nat.pair value value) := by
  have hbits :
      natBitLength (Nat.pair value value) ≤
        natBitLength (Nat.pair value value) := le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair value value) (by rfl) rfl
    (by simp [initialNPOracleState]) hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

/-- Replace the published shape code by its query-count component and hand the
retained public length back to the width stage. -/
private def reframeProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 2 4 3
  , .pair 3 4 0 4
  , .halt 0
  ]

@[simp] private theorem reframeProgram_oracleFree :
    OracleFree reframeProgram := by
  rfl

def reframeBits (shapeCode sourceLen : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair shapeCode sourceLen)
      (Nat.pair sourceLen (Nat.unpair shapeCode).2))

private theorem run_reframeProgram (inputLength shapeCode sourceLen : ℕ) :
    runNPOracleProgram reframeProgram (reframeBits shapeCode sourceLen) 5
        (initialNPOracleState inputLength (Nat.pair shapeCode sourceLen)) =
      some (Nat.pair sourceLen (Nat.unpair shapeCode).2) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair shapeCode sourceLen →
      natBitLength value ≤ reframeBits shapeCode sourceLen :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ Nat.pair sourceLen (Nat.unpair shapeCode).2 →
      natBitLength value ≤ reframeBits shapeCode sourceLen :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hshapeCode := hrequest shapeCode (Nat.left_le_pair shapeCode sourceLen)
  have hsourceLen := hrequest sourceLen (Nat.right_le_pair shapeCode sourceLen)
  have hcount :=
    hrequest (Nat.unpair shapeCode).2
      ((Nat.unpair_right_le shapeCode).trans (Nat.left_le_pair _ _))
  have houtput := hresult _ (le_refl _)
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := shapeCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hshapeCode]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := sourceLen) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hsourceLen]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair shapeCode).2) (by rfl)
    rfl (by simp [NPOracleState.write, NPOracleState.jump]) hcount]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair sourceLen (Nat.unpair shapeCode).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 2. The padded shape runner -/

/-- **The padded shape stream.**  The published shape runner supplies the query
count; the numeral bank's width envelope supplies the padded width. -/
def paddedShapeProgram (outerShape : NPOracleProgram)
    (clockDepth coefficient exponent : ℕ) : NPOracleProgram :=
  linkPrograms duplicateProgram <|
    linkPrograms (preserveRightProgram outerShape) <|
      linkPrograms reframeProgram
        (preserveRightProgram
          (widthEnvelopeProgram clockDepth coefficient exponent))

theorem paddedShapeProgram_oracleFree {outerShape : NPOracleProgram}
    (houterShape : OracleFree outerShape)
    (clockDepth coefficient exponent : ℕ) :
    OracleFree (paddedShapeProgram outerShape clockDepth coefficient exponent) :=
  oracleFree_linkPrograms duplicateProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree outerShape houterShape)
      (oracleFree_linkPrograms reframeProgram_oracleFree
        (preserveRightProgram_oracleFree _
          (widthEnvelopeProgram_oracleFree clockDepth coefficient exponent))))

/-- The padded shape stream's fuel: the two framing streams, the published
shape runner's own charge and the width envelope's own charge. -/
def paddedShapeFuel (outerShape : NPOracleProgram)
    (clockDepth coefficient exponent outerShapeFuel sourceLen : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram outerShape)
      (linkPrograms reframeProgram
        (preserveRightProgram
          (widthEnvelopeProgram clockDepth coefficient exponent))))
    2 <|
    linkFuel
      (linkPrograms reframeProgram
        (preserveRightProgram
          (widthEnvelopeProgram clockDepth coefficient exponent)))
      (preserveRightFuel outerShapeFuel) <|
      linkFuel
        (preserveRightProgram
          (widthEnvelopeProgram clockDepth coefficient exponent))
        5
        (preserveRightFuel
          (widthEnvelopeFuel clockDepth coefficient exponent sourceLen))

/-- The padded shape stream's register width. -/
def paddedShapeBits (clockDepth coefficient exponent outerShapeBits sourceLen
    shapeCode : ℕ) : ℕ :=
  occurrenceStageBits sourceLen (natBitLength (Nat.pair sourceLen sourceLen)) <|
    occurrenceStageBits sourceLen
      (preserveRightBits outerShapeBits sourceLen sourceLen shapeCode) <|
      occurrenceStageBits sourceLen (reframeBits shapeCode sourceLen)
        (preserveRightBits
          (widthEnvelopeBits sourceLen clockDepth coefficient exponent sourceLen)
          sourceLen (Nat.unpair shapeCode).2
          (widthValue clockDepth coefficient exponent sourceLen))

/-- **The padded shape stream, executed.**  The published shape runner's own
exact run is the only imported execution; the published width budget's
positivity is the only side condition. -/
theorem run_paddedShapeProgram (outerShape : NPOracleProgram)
    (clockDepth coefficient exponent outerShapeBits outerShapeFuel sourceLen
      shapeCode : ℕ)
    (hbudget :
      1 ≤ widthBudgetValue clockDepth coefficient exponent sourceLen)
    (houterShape :
      runNPOracleProgram outerShape outerShapeBits outerShapeFuel
          (initialNPOracleState sourceLen sourceLen) =
        some shapeCode) :
    runNPOracleProgram
        (paddedShapeProgram outerShape clockDepth coefficient exponent)
        (paddedShapeBits clockDepth coefficient exponent outerShapeBits
          sourceLen shapeCode)
        (paddedShapeFuel outerShape clockDepth coefficient exponent
          outerShapeFuel sourceLen)
        (initialNPOracleState sourceLen sourceLen) =
      some
        (Nat.pair (widthValue clockDepth coefficient exponent sourceLen)
          (Nat.unpair shapeCode).2) :=
  run_occurrenceStage (run_duplicateProgram sourceLen sourceLen)
    (run_occurrenceStage
      (run_preserveRightProgram outerShape sourceLen outerShapeBits
        outerShapeFuel sourceLen sourceLen shapeCode houterShape)
      (run_occurrenceStage (run_reframeProgram sourceLen shapeCode sourceLen)
        (run_preserveRightProgram
          (widthEnvelopeProgram clockDepth coefficient exponent) sourceLen
          (widthEnvelopeBits sourceLen clockDepth coefficient exponent sourceLen)
          (widthEnvelopeFuel clockDepth coefficient exponent sourceLen) sourceLen
          (Nat.unpair shapeCode).2
          (widthValue clockDepth coefficient exponent sourceLen)
          (run_widthEnvelopeProgram sourceLen clockDepth coefficient exponent
            sourceLen hbudget))))

/-! ## 3. The published instance -/

/-- The published padded shape stream. -/
def publishedPaddedShapeProgram {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) : NPOracleProgram :=
  paddedShapeProgram outer.pcp.shape.program clockDepth
    outer.pcp.shape.coefficient outer.proofExponent

theorem publishedPaddedShapeProgram_oracleFree {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    OracleFree (publishedPaddedShapeProgram outer) :=
  paddedShapeProgram_oracleFree outer.pcp.shapeOracleFree clockDepth
    outer.pcp.shape.coefficient outer.proofExponent

/-- The published padded shape stream's fuel. -/
def publishedPaddedShapeFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceLen : ℕ) : ℕ :=
  paddedShapeFuel outer.pcp.shape.program clockDepth
    outer.pcp.shape.coefficient outer.proofExponent
    (outer.pcp.shape.budget sourceLen) sourceLen

/-- The published padded shape stream's register width. -/
def publishedPaddedShapeBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceLen : ℕ) : ℕ :=
  paddedShapeBits clockDepth outer.pcp.shape.coefficient outer.proofExponent
    (outer.pcp.shape.budget sourceLen) sourceLen
    (outer.pcp.shape.execute sourceLen)

/-- **The padded shape runner, executed.**  No hypothesis remains: the emitted
pair is exactly the padded shape output of
`PaddedProjectionRunnerOutputs.paddedShapeOutput`. -/
theorem run_publishedPaddedShapeProgram {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceLen : ℕ) :
    runNPOracleProgram (publishedPaddedShapeProgram outer)
        (publishedPaddedShapeBits outer sourceLen)
        (publishedPaddedShapeFuel outer sourceLen)
        (initialNPOracleState sourceLen sourceLen) =
      some (paddedShapeOutput outer sourceLen) :=
  run_paddedShapeProgram outer.pcp.shape.program clockDepth
    outer.pcp.shape.coefficient outer.proofExponent
    (outer.pcp.shape.budget sourceLen) (outer.pcp.shape.budget sourceLen)
    sourceLen (outer.pcp.shape.execute sourceLen)
    (publishedWidthBudget_positive outer sourceLen)
    (run_publishedShapeProgram outer sourceLen)

end NearCubicWires.PaddedProjectionShapeRunner
