import Proof.PCP.PaddedProjectionShapeRunner

/-!
# The padded decision runner

The padded verifier's decision is the source verifier's decision on the
*native prefix* of the padded random string: the padding coordinates are never
read.  On canonical codes that is one modular reduction,

`encodeBitInput (prefixBits hwidth randomness) =
  encodeBitInput randomness % 2 ^ nativeWidth`,

which is `BitInputPrefixProgram.bitInputPrefix_encodeBitInput`; the reduction
itself is the published `bitInputPrefixProgram`, so no new bit loop is written.

The stream therefore has four stages: read the native width out of the
published shape runner's output, reduce the padded random code modulo that
width, rebuild the source decision runner's own request code, and delegate.
§2 packages the delegation as one reusable callee lemma so that the source
runner's `halts` field is consumed exactly once.
-/

namespace NearCubicWires.PaddedProjectionDecisionRunner

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The two straight-line framing streams -/

/-- Split the retained request beside the published shape code and present the
prefix reducer's own call frame `pair (pair width value) context`. -/
private def prefixFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairLeft 3 5 4
  , .unpairRight 3 6 5
  , .pair 4 6 7 6
  , .pair 7 5 0 7
  , .halt 0
  ]

@[simp] private theorem prefixFrameProgram_oracleFree :
    OracleFree prefixFrameProgram := by
  rfl

def prefixFrameBits (shapeCode encodedInput encodedRandomness : ℕ) :
    ℕ :=
  natBitLength
    (max (Nat.pair shapeCode (Nat.pair encodedInput encodedRandomness))
      (Nat.pair
        (bitInputPrefixInput (Nat.unpair shapeCode).1 encodedRandomness)
        encodedInput))

private theorem run_prefixFrameProgram
    (inputLength shapeCode encodedInput encodedRandomness : ℕ) :
    runNPOracleProgram prefixFrameProgram
        (prefixFrameBits shapeCode encodedInput encodedRandomness) 8
        (initialNPOracleState inputLength
          (Nat.pair shapeCode (Nat.pair encodedInput encodedRandomness))) =
      some
        (Nat.pair
          (bitInputPrefixInput (Nat.unpair shapeCode).1 encodedRandomness)
          encodedInput) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair shapeCode (Nat.pair encodedInput encodedRandomness) →
      natBitLength value ≤
        prefixFrameBits shapeCode encodedInput encodedRandomness :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        Nat.pair
          (bitInputPrefixInput (Nat.unpair shapeCode).1 encodedRandomness)
          encodedInput →
      natBitLength value ≤
        prefixFrameBits shapeCode encodedInput encodedRandomness :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hshapeCode := hrequest shapeCode (Nat.left_le_pair _ _)
  have hretained :=
    hrequest (Nat.pair encodedInput encodedRandomness) (Nat.right_le_pair _ _)
  have hwidth :=
    hrequest (Nat.unpair shapeCode).1
      ((Nat.unpair_left_le shapeCode).trans (Nat.left_le_pair _ _))
  have hinput :=
    hrequest encodedInput
      ((Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _))
  have hrandomness :=
    hrequest encodedRandomness
      ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _))
  have hcall :=
    hresult (bitInputPrefixInput (Nat.unpair shapeCode).1 encodedRandomness)
      (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := shapeCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hshapeCode]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair encodedInput encodedRandomness) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hretained]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair shapeCode).1) (by rfl)
    rfl (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := encodedInput) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hinput]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := encodedRandomness) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrandomness]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := bitInputPrefixInput (Nat.unpair shapeCode).1 encodedRandomness)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitInputPrefixInput])
    hcall]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair
      (bitInputPrefixInput (Nat.unpair shapeCode).1 encodedRandomness)
      encodedInput) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Rebuild the source decision runner's own request code from the reduced
random code, the retained input code and the retained public length. -/
private def callFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .copy 1 4 3
  , .pair 3 2 5 4
  , .pair 4 5 0 5
  , .halt 0
  ]

@[simp] private theorem callFrameProgram_oracleFree :
    OracleFree callFrameProgram := by
  rfl

def callFrameBits (inputLength reduced encodedInput : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair reduced encodedInput)
      (decisionCode inputLength encodedInput reduced))

private theorem run_callFrameProgram
    (inputLength reduced encodedInput : ℕ) :
    runNPOracleProgram callFrameProgram
        (callFrameBits inputLength reduced encodedInput) 6
        (initialNPOracleState inputLength
          (Nat.pair reduced encodedInput)) =
      some (decisionCode inputLength encodedInput reduced) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair reduced encodedInput →
      natBitLength value ≤ callFrameBits inputLength reduced encodedInput :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ decisionCode inputLength encodedInput reduced →
      natBitLength value ≤ callFrameBits inputLength reduced encodedInput :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hreduced := hrequest reduced (Nat.left_le_pair _ _)
  have hinput := hrequest encodedInput (Nat.right_le_pair _ _)
  have hlength := hresult inputLength (Nat.left_le_pair _ _)
  have hinner :=
    hresult (Nat.pair encodedInput reduced) (Nat.right_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := reduced) (by rfl) rfl
    (by simp [initialNPOracleState]) hreduced]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := encodedInput) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hinput]
  rw [show 4 = 3 + 1 by omega]
  rw [run_copy_instruction (value := inputLength) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hlength]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair encodedInput reduced) (by rfl)
    rfl (by simp [NPOracleState.write, NPOracleState.jump]) hinner]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := decisionCode inputLength encodedInput reduced) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, decisionCode]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 2. The one delegation lemma -/

private theorem run_bitInputPrefix (inputLength width value : ℕ) :
    runNPOracleProgram bitInputPrefixProgram (bitInputPrefixBits width value)
        (bitInputPrefixFuel width value)
        (initialNPOracleState inputLength
          (bitInputPrefixInput width value)) =
      some (bitInputPrefix width value) := by
  have hrun :=
    run_bitInputPrefixProgram inputLength width value
      (bitInputPrefixBits width value) 0 (le_refl _)
  rwa [Nat.add_zero] at hrun

/-- **The source decision runner, called on the reduced random code.**  The
reduced code is by construction the canonical code of a native random string,
so the source runner's own `halts` field applies verbatim; this is the only
place the source decision runner is executed. -/
theorem run_nativeDecision {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) {n : ℕ} (input : BitInput n)
    (encodedRandomness : ℕ) :
    runNPOracleProgram outer.pcp.decisionRunner.program
        (decisionBudget outer.pcp n) (decisionBudget outer.pcp n)
        (initialNPOracleState n
          (decisionCode n (encodeBitInput input)
            (bitInputPrefix (outer.pcp.nativeWidth n) encodedRandomness))) =
      some
        (paddedDecisionOutput outer n (encodeBitInput input)
          encodedRandomness) := by
  have hview :
      bitInputPrefix (outer.pcp.nativeWidth n) encodedRandomness =
        encodeBitInput
          (bitInputPrefixView (outer.pcp.nativeWidth n) encodedRandomness) :=
    bitInputPrefix_eq_encodeView _ _
  have hrun :=
    outer.pcp.decisionRunner.run_eq_execute
      (outer.pcp.decisionRequest input
        (bitInputPrefixView (outer.pcp.nativeWidth n) encodedRandomness))
  have houtput :
      paddedDecisionOutput outer n (encodeBitInput input) encodedRandomness =
        outer.pcp.decisionRunner.execute
          (outer.pcp.decisionRequest input
            (bitInputPrefixView (outer.pcp.nativeWidth n)
              encodedRandomness)) := by
    rw [paddedDecisionOutput, hview]
    exact decisionExecuteAt_eq outer.pcp input _
  rw [houtput, hview]
  exact hrun

/-! ## 3. The padded decision runner -/

/-- **The padded decision stream.** -/
def paddedDecisionProgram (outerShape outerDecision : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (preserveRightProgram outerShape) <|
    linkPrograms prefixFrameProgram <|
      linkPrograms (preserveRightProgram bitInputPrefixProgram)
        (linkPrograms callFrameProgram outerDecision)

theorem paddedDecisionProgram_oracleFree
    {outerShape outerDecision : NPOracleProgram}
    (houterShape : OracleFree outerShape)
    (houterDecision : OracleFree outerDecision) :
    OracleFree (paddedDecisionProgram outerShape outerDecision) :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree outerShape houterShape)
    (oracleFree_linkPrograms prefixFrameProgram_oracleFree
      (oracleFree_linkPrograms
        (preserveRightProgram_oracleFree bitInputPrefixProgram
          bitInputPrefixProgram_oracleFree)
        (oracleFree_linkPrograms callFrameProgram_oracleFree
          houterDecision)))

/-- The padded decision stream's fuel. -/
def paddedDecisionFuel (outerDecision : NPOracleProgram)
    (outerShapeFuel outerDecisionFuel width encodedRandomness : ℕ) : ℕ :=
  linkFuel
    (linkPrograms prefixFrameProgram
      (linkPrograms (preserveRightProgram bitInputPrefixProgram)
        (linkPrograms callFrameProgram outerDecision)))
    (preserveRightFuel outerShapeFuel) <|
    linkFuel
      (linkPrograms (preserveRightProgram bitInputPrefixProgram)
        (linkPrograms callFrameProgram outerDecision))
      8 <|
      linkFuel (linkPrograms callFrameProgram outerDecision)
        (preserveRightFuel (bitInputPrefixFuel width encodedRandomness)) <|
        linkFuel outerDecision 6 outerDecisionFuel

/-- The padded decision stream's register width. -/
def paddedDecisionBits (inputLength outerShapeBits outerDecisionBits shapeCode
    encodedInput encodedRandomness : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (preserveRightBits outerShapeBits inputLength
      (Nat.pair encodedInput encodedRandomness) shapeCode) <|
    occurrenceStageBits inputLength
      (prefixFrameBits shapeCode encodedInput encodedRandomness) <|
      occurrenceStageBits inputLength
        (preserveRightBits
          (bitInputPrefixBits (Nat.unpair shapeCode).1 encodedRandomness)
          (bitInputPrefixInput (Nat.unpair shapeCode).1 encodedRandomness)
          encodedInput
          (bitInputPrefix (Nat.unpair shapeCode).1 encodedRandomness)) <|
        occurrenceStageBits inputLength
          (callFrameBits inputLength
            (bitInputPrefix (Nat.unpair shapeCode).1 encodedRandomness)
            encodedInput)
          outerDecisionBits

/-- **The padded decision stream, executed.**  The published shape runner and
the published decision runner supply the two imported executions. -/
theorem run_paddedDecisionProgram (outerShape outerDecision : NPOracleProgram)
    (inputLength outerShapeBits outerShapeFuel outerDecisionBits
      outerDecisionFuel shapeCode encodedInput encodedRandomness output : ℕ)
    (houterShape :
      runNPOracleProgram outerShape outerShapeBits outerShapeFuel
          (initialNPOracleState inputLength inputLength) =
        some shapeCode)
    (houterDecision :
      runNPOracleProgram outerDecision outerDecisionBits outerDecisionFuel
          (initialNPOracleState inputLength
            (decisionCode inputLength encodedInput
              (bitInputPrefix (Nat.unpair shapeCode).1 encodedRandomness))) =
        some output) :
    runNPOracleProgram (paddedDecisionProgram outerShape outerDecision)
        (paddedDecisionBits inputLength outerShapeBits outerDecisionBits
          shapeCode encodedInput encodedRandomness)
        (paddedDecisionFuel outerDecision outerShapeFuel
          outerDecisionFuel (Nat.unpair shapeCode).1 encodedRandomness)
        (initialNPOracleState inputLength
          (decisionCode inputLength encodedInput encodedRandomness)) =
      some output :=
  run_occurrenceStage
    (run_preserveRightProgram outerShape inputLength outerShapeBits
      outerShapeFuel inputLength (Nat.pair encodedInput encodedRandomness)
      shapeCode houterShape)
    (run_occurrenceStage
      (run_prefixFrameProgram inputLength shapeCode encodedInput
        encodedRandomness)
      (run_occurrenceStage
        (run_preserveRightProgram bitInputPrefixProgram inputLength
          (bitInputPrefixBits (Nat.unpair shapeCode).1 encodedRandomness)
          (bitInputPrefixFuel (Nat.unpair shapeCode).1 encodedRandomness)
          (bitInputPrefixInput (Nat.unpair shapeCode).1 encodedRandomness)
          encodedInput
          (bitInputPrefix (Nat.unpair shapeCode).1 encodedRandomness)
          (run_bitInputPrefix inputLength (Nat.unpair shapeCode).1
            encodedRandomness))
        (run_occurrenceStage
          (run_callFrameProgram inputLength
            (bitInputPrefix (Nat.unpair shapeCode).1 encodedRandomness)
            encodedInput)
          houterDecision)))

/-! ## 4. The published instance -/

/-- The published padded decision stream. -/
def publishedPaddedDecisionProgram {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) : NPOracleProgram :=
  paddedDecisionProgram outer.pcp.shape.program
    outer.pcp.decisionRunner.program

theorem publishedPaddedDecisionProgram_oracleFree {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    OracleFree (publishedPaddedDecisionProgram outer) :=
  paddedDecisionProgram_oracleFree outer.pcp.shapeOracleFree
    outer.pcp.decisionOracleFree

/-- The published padded decision stream's fuel. -/
def publishedPaddedDecisionFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (request : ProjectionDecisionRequest) : ℕ :=
  paddedDecisionFuel outer.pcp.decisionRunner.program
    (outer.pcp.shape.budget request.inputArity)
    (decisionBudget outer.pcp request.inputArity)
    (outer.pcp.nativeWidth request.inputArity)
    (encodeBitInput request.randomness)

/-- The published padded decision stream's register width. -/
def publishedPaddedDecisionBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (request : ProjectionDecisionRequest) : ℕ :=
  paddedDecisionBits request.inputArity
    (outer.pcp.shape.budget request.inputArity)
    (decisionBudget outer.pcp request.inputArity)
    (outer.pcp.shape.execute request.inputArity)
    (encodeBitInput request.input) (encodeBitInput request.randomness)

/-- **The padded decision runner, executed.**  No hypothesis remains: the
emitted numeral is the padded decision output of
`PaddedProjectionRunnerAssembly.paddedDecisionRequestOutput`. -/
theorem run_publishedPaddedDecisionProgram {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (request : ProjectionDecisionRequest) :
    runNPOracleProgram (publishedPaddedDecisionProgram outer)
        (publishedPaddedDecisionBits outer request)
        (publishedPaddedDecisionFuel outer request)
        (initialNPOracleState (ProjectionDecisionRequest.length request)
          (ProjectionDecisionRequest.code request)) =
      some (paddedDecisionRequestOutput outer request) :=
  run_paddedDecisionProgram outer.pcp.shape.program
    outer.pcp.decisionRunner.program request.inputArity
    (outer.pcp.shape.budget request.inputArity)
    (outer.pcp.shape.budget request.inputArity)
    (decisionBudget outer.pcp request.inputArity)
    (decisionBudget outer.pcp request.inputArity)
    (outer.pcp.shape.execute request.inputArity)
    (encodeBitInput request.input) (encodeBitInput request.randomness)
    (paddedDecisionRequestOutput outer request)
    (outer.pcp.shape.run_eq_execute request.inputArity)
    (run_nativeDecision outer request.input
      (encodeBitInput request.randomness))

end NearCubicWires.PaddedProjectionDecisionRunner
