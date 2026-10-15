import Proof.MachineModel.CanonicalBitSerialModProgram
import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalNativeModProgram
import Proof.PCP.PaddedProjectionDecisionRunner
import Proof.MachineModel.TaggedProgramChoice

/-!
# The padded query runner

The padded query runner cannot forward the source runner's answer verbatim.
`ExecutableInterfaces.decodeProjectedRandomBit` reduces the returned index
*modulo the width it is applied at*, so a native code read at the padded width
names a different address.  `PaddedProjectionRunnerOutputs.paddedQueryOutput`
therefore re-tags: the emitted index is the native index reduced modulo a
tag-dependent modulus — the native width on an address tag, two on a constant
tag — which the padded decode then reproduces exactly.

Two facts shape the stream.

* The source query runner is only obliged to halt on its *own* requests, so
  the padded runner must not call it outside the published shape.  The guard is
  the saturating product `(queryCount - query) * (nativeWidth - bit)`, which
  vanishes exactly off that shape; `TaggedProgramChoice.taggedProgramChoice`
  dispatches on it, and the vanishing branch emits the canonical false
  constant.

* Only one modular reduction is needed per side because the modulus itself is
  selected by a second `taggedProgramChoice` on the saturating difference
  `2 - tag`.  Every framing stream in this module is therefore straight-line;
  no instruction trace in the file contains a branch.
-/

namespace NearCubicWires.PaddedProjectionQueryRunner

open NearCubicWires
open NearCubicWires.CanonicalBitSerialModProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeModProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## 1. Two reusable dispatch wrappers -/

private theorem run_at_larger_fuel {program : NPOracleProgram}
    {bits fuel larger : ℕ} {state : NPOracleState} {output : ℕ}
    (hrun : runNPOracleProgram program bits fuel state = some output)
    (hfuel : fuel ≤ larger) :
    runNPOracleProgram program bits larger state = some output := by
  have hmore := run_fuel_add hrun (larger - fuel)
  rwa [Nat.add_sub_cancel' hfuel] at hmore

/-- Dispatch on a vanishing tag at a caller-chosen width and clock.  This is
the single wrapper every branch in the module goes through. -/
private theorem run_choiceZero (first second : NPOracleProgram)
    (inputLength payload branchBits branchFuel bits choiceFuel output : ℕ)
    (hinput :
      natBitLength (Nat.pair inputLength (Nat.pair 0 payload)) ≤ bits)
    (hbranchBits : branchBits ≤ bits)
    (houtput : natBitLength output ≤ bits)
    (hfuel : branchFuel ≤ choiceFuel)
    (hbranch :
      runNPOracleProgram first branchBits branchFuel
          (initialNPOracleState inputLength payload) =
        some output) :
    runNPOracleProgram (taggedProgramChoice first second) bits
        (taggedProgramChoiceFuel choiceFuel)
        (initialNPOracleState inputLength (Nat.pair 0 payload)) =
      some output :=
  run_taggedProgramChoice_zero first second inputLength payload bits choiceFuel
    output hinput
    (run_bits_mono (run_at_larger_fuel hbranch hfuel) hbranchBits) houtput

private theorem run_choiceNonzero (first second : NPOracleProgram)
    (inputLength tag payload branchBits branchFuel bits choiceFuel output : ℕ)
    (htag : tag ≠ 0)
    (hinput :
      natBitLength (Nat.pair inputLength (Nat.pair tag payload)) ≤ bits)
    (hbranchBits : branchBits ≤ bits)
    (houtput : natBitLength output ≤ bits)
    (hfuel : branchFuel ≤ choiceFuel)
    (hbranch :
      runNPOracleProgram second branchBits branchFuel
          (initialNPOracleState inputLength payload) =
        some output) :
    runNPOracleProgram (taggedProgramChoice first second) bits
        (taggedProgramChoiceFuel choiceFuel)
        (initialNPOracleState inputLength (Nat.pair tag payload)) =
      some output :=
  run_taggedProgramChoice_nonzero first second inputLength tag payload bits
    choiceFuel output htag hinput
    (run_bits_mono (run_at_larger_fuel hbranch hfuel) hbranchBits) houtput

/-! ## 2. The straight-line framing streams -/

/-- The retained request tail of one query request code. -/
def queryTail (encodedInput queryIndex bitIndex : ℕ) : ℕ :=
  Nat.pair encodedInput (Nat.pair queryIndex bitIndex)

/-- The dispatch guard: it vanishes exactly off the published shape. -/
def queryGuard (shapeCode queryIndex bitIndex : ℕ) : ℕ :=
  ((Nat.unpair shapeCode).2 - queryIndex) *
    ((Nat.unpair shapeCode).1 - bitIndex)

/-- The modulus selected by the emitted tag. -/
def selectedModulus (tag width : ℕ) : ℕ :=
  if 2 - tag = 0 then 2 else width

/-- Present the guard's two saturating factors beside the native width and the
retained request tail. -/
private def guardFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairRight 3 6 5
  , .unpairLeft 6 7 6
  , .unpairRight 6 8 7
  , .subtract 5 7 9 8
  , .subtract 4 8 10 9
  , .pair 9 10 11 10
  , .pair 4 3 12 11
  , .pair 11 12 0 12
  , .halt 0
  ]

@[simp] private theorem guardFrameProgram_oracleFree :
    OracleFree guardFrameProgram := by
  rfl

def guardFrameOutput (shapeCode encodedInput queryIndex bitIndex : ℕ) :
    ℕ :=
  Nat.pair
    (bitSerialMulInput ((Nat.unpair shapeCode).2 - queryIndex)
      ((Nat.unpair shapeCode).1 - bitIndex))
    (Nat.pair (Nat.unpair shapeCode).1
      (queryTail encodedInput queryIndex bitIndex))

def guardFrameBits (shapeCode encodedInput queryIndex bitIndex : ℕ) :
    ℕ :=
  natBitLength
    (max (Nat.pair shapeCode (queryTail encodedInput queryIndex bitIndex))
      (guardFrameOutput shapeCode encodedInput queryIndex bitIndex))

private theorem run_guardFrameProgram
    (inputLength shapeCode encodedInput queryIndex bitIndex : ℕ) :
    runNPOracleProgram guardFrameProgram
        (guardFrameBits shapeCode encodedInput queryIndex bitIndex) 13
        (initialNPOracleState inputLength
          (Nat.pair shapeCode (queryTail encodedInput queryIndex bitIndex))) =
      some (guardFrameOutput shapeCode encodedInput queryIndex bitIndex) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair shapeCode (queryTail encodedInput queryIndex bitIndex) →
      natBitLength value ≤
        guardFrameBits shapeCode encodedInput queryIndex bitIndex :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ guardFrameOutput shapeCode encodedInput queryIndex bitIndex →
      natBitLength value ≤
        guardFrameBits shapeCode encodedInput queryIndex bitIndex :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hshapeCode := hrequest shapeCode (Nat.left_le_pair _ _)
  have htail :=
    hrequest (queryTail encodedInput queryIndex bitIndex)
      (Nat.right_le_pair _ _)
  have hwidth :=
    hrequest (Nat.unpair shapeCode).1
      ((Nat.unpair_left_le shapeCode).trans (Nat.left_le_pair _ _))
  have hcount :=
    hrequest (Nat.unpair shapeCode).2
      ((Nat.unpair_right_le shapeCode).trans (Nat.left_le_pair _ _))
  have hindices :=
    hrequest (Nat.pair queryIndex bitIndex)
      ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _))
  have hquery :=
    hrequest queryIndex
      ((Nat.left_le_pair _ _).trans
        ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _)))
  have hbit :=
    hrequest bitIndex
      ((Nat.right_le_pair _ _).trans
        ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _)))
  have hcountDiff :=
    hrequest ((Nat.unpair shapeCode).2 - queryIndex)
      ((Nat.sub_le _ _).trans
        ((Nat.unpair_right_le shapeCode).trans (Nat.left_le_pair _ _)))
  have hwidthDiff :=
    hrequest ((Nat.unpair shapeCode).1 - bitIndex)
      ((Nat.sub_le _ _).trans
        ((Nat.unpair_left_le shapeCode).trans (Nat.left_le_pair _ _)))
  have hfactors :=
    hresult
      (bitSerialMulInput ((Nat.unpair shapeCode).2 - queryIndex)
        ((Nat.unpair shapeCode).1 - bitIndex))
      (Nat.left_le_pair _ _)
  have hcontext :=
    hresult
      (Nat.pair (Nat.unpair shapeCode).1
        (queryTail encodedInput queryIndex bitIndex))
      (Nat.right_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := shapeCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hshapeCode]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := queryTail encodedInput queryIndex bitIndex) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htail]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair shapeCode).1) (by rfl)
    rfl (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair shapeCode).2) (by rfl)
    rfl (by simp [NPOracleState.write, NPOracleState.jump]) hcount]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair queryIndex bitIndex)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, queryTail]) hindices]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := queryIndex) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hquery]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := bitIndex) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbit]
  rw [show 6 = 5 + 1 by omega]
  rw [run_subtract_instruction
    (value := (Nat.unpair shapeCode).2 - queryIndex) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountDiff]
  rw [show 5 = 4 + 1 by omega]
  rw [run_subtract_instruction
    (value := (Nat.unpair shapeCode).1 - bitIndex) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthDiff]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := bitSerialMulInput ((Nat.unpair shapeCode).2 - queryIndex)
      ((Nat.unpair shapeCode).1 - bitIndex)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSerialMulInput])
    hfactors]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.unpair shapeCode).1
      (queryTail encodedInput queryIndex bitIndex)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcontext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := guardFrameOutput shapeCode encodedInput queryIndex bitIndex)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, guardFrameOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- The vanishing-guard branch: the canonical false constant. -/
private def constantFalseProgram : NPOracleProgram :=
  [ .set 2 2 1
  , .set 3 0 2
  , .pair 2 3 0 3
  , .halt 0
  ]

@[simp] private theorem constantFalseProgram_oracleFree :
    OracleFree constantFalseProgram := by
  rfl

def constantFalseBits : ℕ := natBitLength (Nat.pair 2 0)

private theorem run_constantFalseProgram (inputLength code : ℕ) :
    runNPOracleProgram constantFalseProgram constantFalseBits 4
        (initialNPOracleState inputLength code) =
      some (Nat.pair 2 0) := by
  have houtput : natBitLength (Nat.pair 2 0) ≤ constantFalseBits := le_refl _
  have htag : natBitLength 2 ≤ constantFalseBits :=
    natBitLength_mono (Nat.left_le_pair 2 0)
  have hzero : natBitLength 0 ≤ constantFalseBits :=
    natBitLength_mono (Nat.right_le_pair 2 0)
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (register := 2) (value := 2) (by rfl) rfl htag]
  rw [show 3 = 2 + 1 by omega]
  rw [run_set_instruction (register := 3) (value := 0) (by rfl) rfl hzero]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 2 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Rebuild the source query runner's own request code and retain the native
width. -/
private def callFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .copy 1 4 3
  , .pair 4 3 5 4
  , .pair 5 2 0 5
  , .halt 0
  ]

@[simp] private theorem callFrameProgram_oracleFree :
    OracleFree callFrameProgram := by
  rfl

def callFrameBits (inputLength width tail : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair width tail) (Nat.pair (Nat.pair inputLength tail) width))

private theorem run_callFrameProgram (inputLength width tail : ℕ) :
    runNPOracleProgram callFrameProgram
        (callFrameBits inputLength width tail) 6
        (initialNPOracleState inputLength (Nat.pair width tail)) =
      some (Nat.pair (Nat.pair inputLength tail) width) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair width tail →
      natBitLength value ≤ callFrameBits inputLength width tail :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ Nat.pair (Nat.pair inputLength tail) width →
      natBitLength value ≤ callFrameBits inputLength width tail :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hwidth := hrequest width (Nat.left_le_pair _ _)
  have htail := hrequest tail (Nat.right_le_pair _ _)
  have hlength :=
    hresult inputLength ((Nat.left_le_pair _ _).trans (Nat.left_le_pair _ _))
  have hcode :=
    hresult (Nat.pair inputLength tail) (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [initialNPOracleState]) hwidth]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := tail) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htail]
  rw [show 4 = 3 + 1 by omega]
  rw [run_copy_instruction (value := inputLength) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hlength]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputLength tail) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcode]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair inputLength tail) width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Present the tag reducer's call frame beside the decoded index and the
retained native width. -/
private def tagFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .set 6 3 5
  , .pair 4 6 7 6
  , .pair 5 3 8 7
  , .pair 7 8 0 8
  , .halt 0
  ]

@[simp] private theorem tagFrameProgram_oracleFree :
    OracleFree tagFrameProgram := by
  rfl

def tagFrameOutput (code width : ℕ) : ℕ :=
  Nat.pair (nativeModInput (Nat.unpair code).1 3)
    (Nat.pair (Nat.unpair code).2 width)

def tagFrameBits (code width : ℕ) : ℕ :=
  natBitLength (max (Nat.pair code width) (tagFrameOutput code width))

private theorem run_tagFrameProgram (inputLength code width : ℕ) :
    runNPOracleProgram tagFrameProgram (tagFrameBits code width) 9
        (initialNPOracleState inputLength (Nat.pair code width)) =
      some (tagFrameOutput code width) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair code width →
      natBitLength value ≤ tagFrameBits code width :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ tagFrameOutput code width →
      natBitLength value ≤ tagFrameBits code width :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hcode := hrequest code (Nat.left_le_pair _ _)
  have hwidth := hrequest width (Nat.right_le_pair _ _)
  have htag :=
    hrequest (Nat.unpair code).1
      ((Nat.unpair_left_le code).trans (Nat.left_le_pair _ _))
  have hindex :=
    hrequest (Nat.unpair code).2
      ((Nat.unpair_right_le code).trans (Nat.left_le_pair _ _))
  have hthree :=
    hresult 3 ((Nat.right_le_pair _ _).trans (Nat.left_le_pair _ _))
  have hcall :=
    hresult (nativeModInput (Nat.unpair code).1 3) (Nat.left_le_pair _ _)
  have hcontext :=
    hresult (Nat.pair (Nat.unpair code).2 width) (Nat.right_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := code) (by rfl) rfl
    (by simp [initialNPOracleState]) hcode]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := width) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hwidth]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair code).1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htag]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair code).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hindex]
  rw [show 5 = 4 + 1 by omega]
  rw [run_set_instruction (register := 6) (value := 3) (by rfl) rfl hthree]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := nativeModInput (Nat.unpair code).1 3)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, nativeModInput]) hcall]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (Nat.unpair code).2 width)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcontext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := tagFrameOutput code width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tagFrameOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Present the modulus dispatch tag `2 - tag` in front of the retained
frame. -/
private def modulusTagProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .set 3 2 2
  , .subtract 3 2 4 3
  , .pair 4 0 0 4
  , .halt 0
  ]

@[simp] private theorem modulusTagProgram_oracleFree :
    OracleFree modulusTagProgram := by
  rfl

def modulusTagBits (tag payload : ℕ) : ℕ :=
  natBitLength
    (max 2
      (max (Nat.pair tag payload)
        (Nat.pair (2 - tag) (Nat.pair tag payload))))

private theorem run_modulusTagProgram (inputLength tag payload : ℕ) :
    runNPOracleProgram modulusTagProgram (modulusTagBits tag payload) 5
        (initialNPOracleState inputLength (Nat.pair tag payload)) =
      some (Nat.pair (2 - tag) (Nat.pair tag payload)) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair tag payload →
      natBitLength value ≤ modulusTagBits tag payload :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
  have hresult : ∀ value : ℕ,
      value ≤ Nat.pair (2 - tag) (Nat.pair tag payload) →
      natBitLength value ≤ modulusTagBits tag payload :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have htag := hrequest tag (Nat.left_le_pair _ _)
  have htwo : natBitLength 2 ≤ modulusTagBits tag payload :=
    natBitLength_mono (Nat.le_max_left _ _)
  have hdiff :=
    hresult (2 - tag) (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag) (by rfl) rfl
    (by simp [initialNPOracleState]) htag]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (register := 3) (value := 2) (by rfl) rfl htwo]
  rw [show 3 = 2 + 1 by omega]
  rw [run_subtract_instruction (value := 2 - tag) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdiff]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (2 - tag) (Nat.pair tag payload))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Constant-tag branch: reduce the decoded index modulo two. -/
private def modTwoProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .set 5 2 4
  , .pair 4 5 6 5
  , .pair 6 2 0 6
  , .halt 0
  ]

@[simp] private theorem modTwoProgram_oracleFree :
    OracleFree modTwoProgram := by
  rfl

def modBranchBits (tag index width modulus : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair tag (Nat.pair index width))
      (Nat.pair (nativeModInput index modulus) tag))

private theorem run_modTwoProgram (inputLength tag index width : ℕ) :
    runNPOracleProgram modTwoProgram (modBranchBits tag index width 2) 7
        (initialNPOracleState inputLength
          (Nat.pair tag (Nat.pair index width))) =
      some (Nat.pair (nativeModInput index 2) tag) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair tag (Nat.pair index width) →
      natBitLength value ≤ modBranchBits tag index width 2 :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ Nat.pair (nativeModInput index 2) tag →
      natBitLength value ≤ modBranchBits tag index width 2 :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have htag := hrequest tag (Nat.left_le_pair _ _)
  have hpayload :=
    hrequest (Nat.pair index width) (Nat.right_le_pair _ _)
  have hindex :=
    hrequest index ((Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _))
  have htwo :=
    hresult 2
      ((Nat.right_le_pair index 2).trans (Nat.left_le_pair _ _))
  have hcall :=
    hresult (nativeModInput index 2) (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag) (by rfl) rfl
    (by simp [initialNPOracleState]) htag]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair index width) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpayload]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hindex]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (register := 5) (value := 2) (by rfl) rfl htwo]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := nativeModInput index 2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, nativeModInput]) hcall]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (nativeModInput index 2) tag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Address-tag branch: reduce the decoded index modulo the native width. -/
private def modWidthProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 2 0 3
  , .halt 0
  ]

@[simp] private theorem modWidthProgram_oracleFree :
    OracleFree modWidthProgram := by
  rfl

private theorem run_modWidthProgram (inputLength tag index width : ℕ) :
    runNPOracleProgram modWidthProgram (modBranchBits tag index width width) 4
        (initialNPOracleState inputLength
          (Nat.pair tag (Nat.pair index width))) =
      some (Nat.pair (nativeModInput index width) tag) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair tag (Nat.pair index width) →
      natBitLength value ≤ modBranchBits tag index width width :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ Nat.pair (nativeModInput index width) tag →
      natBitLength value ≤ modBranchBits tag index width width :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have htag := hrequest tag (Nat.left_le_pair _ _)
  have hpayload :=
    hrequest (Nat.pair index width) (Nat.right_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag) (by rfl) rfl
    (by simp [initialNPOracleState]) htag]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair index width) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpayload]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (nativeModInput index width) tag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, nativeModInput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Present the emitted tag in front of the reduced index. -/
private def swapFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 2 0 3
  , .halt 0
  ]

@[simp] private theorem swapFrameProgram_oracleFree :
    OracleFree swapFrameProgram := by
  rfl

def swapFrameBits (left right : ℕ) : ℕ :=
  natBitLength (max (Nat.pair left right) (Nat.pair right left))

private theorem run_swapFrameProgram (inputLength left right : ℕ) :
    runNPOracleProgram swapFrameProgram (swapFrameBits left right) 4
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.pair right left) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair left right →
      natBitLength value ≤ swapFrameBits left right :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have houtput : natBitLength (Nat.pair right left) ≤ swapFrameBits left right :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hleft := hrequest left (Nat.left_le_pair _ _)
  have hright := hrequest right (Nat.right_le_pair _ _)
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair right left) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 3. The in-range chain -/

private def queryStage7 : NPOracleProgram := swapFrameProgram

private def queryStage6 : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSerialModProgram) queryStage7

private def queryStage5 : NPOracleProgram :=
  linkPrograms (taggedProgramChoice modTwoProgram modWidthProgram) queryStage6

private def queryStage4 : NPOracleProgram :=
  linkPrograms modulusTagProgram queryStage5

private def queryStage3 : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSerialModProgram) queryStage4

private def queryStage2 : NPOracleProgram :=
  linkPrograms tagFrameProgram queryStage3

private def queryStage1 (outerQuery : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (preserveRightProgram outerQuery) queryStage2

/-- The in-range branch: call the source query runner, then re-tag. -/
def inRangeProgram (outerQuery : NPOracleProgram) : NPOracleProgram :=
  linkPrograms callFrameProgram (queryStage1 outerQuery)

/-- The re-tagged emission at one native width and one source answer. -/
def emittedValue (width queryOutput : ℕ) : ℕ :=
  Nat.pair ((Nat.unpair queryOutput).1 % 3)
    ((Nat.unpair queryOutput).2 %
      selectedModulus ((Nat.unpair queryOutput).1 % 3) width)

def modulusChoiceBits (inputLength width queryOutput : ℕ) : ℕ :=
  max
    (natBitLength
      (Nat.pair inputLength
        (Nat.pair (2 - (Nat.unpair queryOutput).1 % 3)
          (Nat.pair ((Nat.unpair queryOutput).1 % 3)
            (Nat.pair (Nat.unpair queryOutput).2 width)))))
    (max
      (modBranchBits ((Nat.unpair queryOutput).1 % 3)
        (Nat.unpair queryOutput).2 width
        (selectedModulus ((Nat.unpair queryOutput).1 % 3) width))
      (natBitLength
        (Nat.pair
          (nativeModInput (Nat.unpair queryOutput).2
            (selectedModulus ((Nat.unpair queryOutput).1 % 3) width))
          ((Nat.unpair queryOutput).1 % 3))))

private theorem run_modulusChoice (inputLength width queryOutput : ℕ) :
    runNPOracleProgram (taggedProgramChoice modTwoProgram modWidthProgram)
        (modulusChoiceBits inputLength width queryOutput)
        (taggedProgramChoiceFuel 7)
        (initialNPOracleState inputLength
          (Nat.pair (2 - (Nat.unpair queryOutput).1 % 3)
            (Nat.pair ((Nat.unpair queryOutput).1 % 3)
              (Nat.pair (Nat.unpair queryOutput).2 width)))) =
      some
        (Nat.pair
          (nativeModInput (Nat.unpair queryOutput).2
            (selectedModulus ((Nat.unpair queryOutput).1 % 3) width))
          ((Nat.unpair queryOutput).1 % 3)) := by
  have hbranchBits :
      modBranchBits ((Nat.unpair queryOutput).1 % 3) (Nat.unpair queryOutput).2
          width (selectedModulus ((Nat.unpair queryOutput).1 % 3) width) ≤
        modulusChoiceBits inputLength width queryOutput :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have houtput :
      natBitLength
          (Nat.pair
            (nativeModInput (Nat.unpair queryOutput).2
              (selectedModulus ((Nat.unpair queryOutput).1 % 3) width))
            ((Nat.unpair queryOutput).1 % 3)) ≤
        modulusChoiceBits inputLength width queryOutput :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hinput :
      natBitLength
          (Nat.pair inputLength
            (Nat.pair (2 - (Nat.unpair queryOutput).1 % 3)
              (Nat.pair ((Nat.unpair queryOutput).1 % 3)
                (Nat.pair (Nat.unpair queryOutput).2 width)))) ≤
        modulusChoiceBits inputLength width queryOutput :=
    Nat.le_max_left _ _
  by_cases hconstant : 2 - (Nat.unpair queryOutput).1 % 3 = 0
  · have hmodulus :
        selectedModulus ((Nat.unpair queryOutput).1 % 3) width = 2 := by
      unfold selectedModulus
      rw [if_pos hconstant]
    rw [hmodulus] at hbranchBits houtput ⊢
    rw [hconstant] at hinput ⊢
    exact run_choiceZero modTwoProgram modWidthProgram inputLength _
      (modBranchBits ((Nat.unpair queryOutput).1 % 3)
        (Nat.unpair queryOutput).2 width 2)
      7 (modulusChoiceBits inputLength width queryOutput) 7 _ hinput
      hbranchBits houtput (le_refl 7)
      (run_modTwoProgram inputLength ((Nat.unpair queryOutput).1 % 3)
        (Nat.unpair queryOutput).2 width)
  · have hmodulus :
        selectedModulus ((Nat.unpair queryOutput).1 % 3) width = width := by
      unfold selectedModulus
      rw [if_neg hconstant]
    rw [hmodulus] at hbranchBits houtput ⊢
    exact run_choiceNonzero modTwoProgram modWidthProgram inputLength _ _
      (modBranchBits ((Nat.unpair queryOutput).1 % 3)
        (Nat.unpair queryOutput).2 width width)
      4 (modulusChoiceBits inputLength width queryOutput) 7 _ hconstant
      hinput hbranchBits houtput (by omega)
      (run_modWidthProgram inputLength ((Nat.unpair queryOutput).1 % 3)
        (Nat.unpair queryOutput).2 width)

def inRangeFuel (outerQuery : NPOracleProgram)
    (outerQueryFuel width queryOutput : ℕ) : ℕ :=
  linkFuel (queryStage1 outerQuery) 6 <|
    linkFuel queryStage2 (preserveRightFuel outerQueryFuel) <|
      linkFuel queryStage3 9 <|
        linkFuel queryStage4
          (preserveRightFuel (bitSerialModFuel (Nat.unpair queryOutput).1 3)) <|
          linkFuel queryStage5 5 <|
            linkFuel queryStage6 (taggedProgramChoiceFuel 7) <|
              linkFuel queryStage7
                (preserveRightFuel
                  (bitSerialModFuel (Nat.unpair queryOutput).2
                    (selectedModulus ((Nat.unpair queryOutput).1 % 3) width)))
                4

def inRangeBits (inputLength width tail outerQueryBits
    queryOutput : ℕ) : ℕ :=
  occurrenceStageBits inputLength (callFrameBits inputLength width tail) <|
    occurrenceStageBits inputLength
      (preserveRightBits outerQueryBits (Nat.pair inputLength tail) width
        queryOutput) <|
      occurrenceStageBits inputLength (tagFrameBits queryOutput width) <|
        occurrenceStageBits inputLength
          (preserveRightBits (bitSerialModBits (Nat.unpair queryOutput).1 3)
            (nativeModInput (Nat.unpair queryOutput).1 3)
            (Nat.pair (Nat.unpair queryOutput).2 width)
            ((Nat.unpair queryOutput).1 % 3)) <|
          occurrenceStageBits inputLength
            (modulusTagBits ((Nat.unpair queryOutput).1 % 3)
              (Nat.pair (Nat.unpair queryOutput).2 width)) <|
            occurrenceStageBits inputLength
              (modulusChoiceBits inputLength width queryOutput) <|
              occurrenceStageBits inputLength
                (preserveRightBits
                  (bitSerialModBits (Nat.unpair queryOutput).2
                    (selectedModulus ((Nat.unpair queryOutput).1 % 3) width))
                  (nativeModInput (Nat.unpair queryOutput).2
                    (selectedModulus ((Nat.unpair queryOutput).1 % 3) width))
                  ((Nat.unpair queryOutput).1 % 3)
                  ((Nat.unpair queryOutput).2 %
                    selectedModulus ((Nat.unpair queryOutput).1 % 3) width))
                (swapFrameBits
                  ((Nat.unpair queryOutput).2 %
                    selectedModulus ((Nat.unpair queryOutput).1 % 3) width)
                  ((Nat.unpair queryOutput).1 % 3))

private theorem run_inRangeProgram (outerQuery : NPOracleProgram)
    (inputLength outerQueryBits outerQueryFuel width tail queryOutput : ℕ)
    (hwidth : 0 < width)
    (houterQuery :
      runNPOracleProgram outerQuery outerQueryBits outerQueryFuel
          (initialNPOracleState inputLength (Nat.pair inputLength tail)) =
        some queryOutput) :
    runNPOracleProgram (inRangeProgram outerQuery)
        (inRangeBits inputLength width tail outerQueryBits queryOutput)
        (inRangeFuel outerQuery outerQueryFuel width queryOutput)
        (initialNPOracleState inputLength (Nat.pair width tail)) =
      some (emittedValue width queryOutput) := by
  have hmodulus :
      0 < selectedModulus ((Nat.unpair queryOutput).1 % 3) width := by
    simp only [selectedModulus]
    split <;> omega
  exact run_occurrenceStage (run_callFrameProgram inputLength width tail)
    (run_occurrenceStage
      (run_preserveRightProgram outerQuery inputLength outerQueryBits
        outerQueryFuel (Nat.pair inputLength tail) width queryOutput
        houterQuery)
      (run_occurrenceStage (run_tagFrameProgram inputLength queryOutput width)
        (run_occurrenceStage
          (run_preserveRightProgram bitSerialModProgram inputLength
            (bitSerialModBits (Nat.unpair queryOutput).1 3)
            (bitSerialModFuel (Nat.unpair queryOutput).1 3)
            (nativeModInput (Nat.unpair queryOutput).1 3)
            (Nat.pair (Nat.unpair queryOutput).2 width)
            ((Nat.unpair queryOutput).1 % 3)
            (run_bitSerialModProgram inputLength (Nat.unpair queryOutput).1 3
              (by omega)))
          (run_occurrenceStage
            (run_modulusTagProgram inputLength ((Nat.unpair queryOutput).1 % 3)
              (Nat.pair (Nat.unpair queryOutput).2 width))
            (run_occurrenceStage
              (run_modulusChoice inputLength width queryOutput)
              (run_occurrenceStage
                (run_preserveRightProgram bitSerialModProgram inputLength
                  (bitSerialModBits (Nat.unpair queryOutput).2
                    (selectedModulus ((Nat.unpair queryOutput).1 % 3) width))
                  (bitSerialModFuel (Nat.unpair queryOutput).2
                    (selectedModulus ((Nat.unpair queryOutput).1 % 3) width))
                  (nativeModInput (Nat.unpair queryOutput).2
                    (selectedModulus ((Nat.unpair queryOutput).1 % 3) width))
                  ((Nat.unpair queryOutput).1 % 3)
                  ((Nat.unpair queryOutput).2 %
                    selectedModulus ((Nat.unpair queryOutput).1 % 3) width)
                  (run_bitSerialModProgram inputLength (Nat.unpair queryOutput).2
                    (selectedModulus ((Nat.unpair queryOutput).1 % 3) width)
                    hmodulus))
                (run_swapFrameProgram inputLength
                  ((Nat.unpair queryOutput).2 %
                    selectedModulus ((Nat.unpair queryOutput).1 % 3) width)
                  ((Nat.unpair queryOutput).1 % 3))))))))

/-! ## 4. The padded query runner -/

/-- **The padded query stream.** -/
def paddedQueryProgram (outerShape outerQuery : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (preserveRightProgram outerShape) <|
    linkPrograms guardFrameProgram <|
      linkPrograms (preserveRightProgram bitSerialMulProgram)
        (taggedProgramChoice constantFalseProgram (inRangeProgram outerQuery))

theorem inRangeProgram_oracleFree {outerQuery : NPOracleProgram}
    (houterQuery : OracleFree outerQuery) :
    OracleFree (inRangeProgram outerQuery) :=
  oracleFree_linkPrograms callFrameProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree outerQuery houterQuery)
      (oracleFree_linkPrograms tagFrameProgram_oracleFree
        (oracleFree_linkPrograms
          (preserveRightProgram_oracleFree bitSerialModProgram
            bitSerialModProgram_oracleFree)
          (oracleFree_linkPrograms modulusTagProgram_oracleFree
            (oracleFree_linkPrograms
              (taggedProgramChoice_oracleFree modTwoProgram modWidthProgram
                modTwoProgram_oracleFree modWidthProgram_oracleFree)
              (oracleFree_linkPrograms
                (preserveRightProgram_oracleFree bitSerialModProgram
                  bitSerialModProgram_oracleFree)
                swapFrameProgram_oracleFree))))))

theorem paddedQueryProgram_oracleFree
    {outerShape outerQuery : NPOracleProgram}
    (houterShape : OracleFree outerShape)
    (houterQuery : OracleFree outerQuery) :
    OracleFree (paddedQueryProgram outerShape outerQuery) :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree outerShape houterShape)
    (oracleFree_linkPrograms guardFrameProgram_oracleFree
      (oracleFree_linkPrograms
        (preserveRightProgram_oracleFree bitSerialMulProgram
          bitSerialMulProgram_oracleFree)
        (taggedProgramChoice_oracleFree constantFalseProgram
          (inRangeProgram outerQuery) constantFalseProgram_oracleFree
          (inRangeProgram_oracleFree houterQuery))))

/-- The value the padded query stream emits. -/
def paddedQueryValue (shapeCode queryIndex bitIndex queryOutput : ℕ) : ℕ :=
  if queryGuard shapeCode queryIndex bitIndex = 0 then
    Nat.pair 2 0
  else
    emittedValue (Nat.unpair shapeCode).1 queryOutput

def queryChoiceBits (inputLength shapeCode encodedInput queryIndex
    bitIndex outerQueryBits queryOutput : ℕ) : ℕ :=
  max
    (natBitLength
      (Nat.pair inputLength
        (Nat.pair (queryGuard shapeCode queryIndex bitIndex)
          (Nat.pair (Nat.unpair shapeCode).1
            (queryTail encodedInput queryIndex bitIndex)))))
    (max
      (max constantFalseBits
        (inRangeBits inputLength (Nat.unpair shapeCode).1
          (queryTail encodedInput queryIndex bitIndex) outerQueryBits
          queryOutput))
      (natBitLength
        (paddedQueryValue shapeCode queryIndex bitIndex queryOutput)))

/-- The padded query stream's fuel. -/
def paddedQueryFuel (outerQuery : NPOracleProgram)
    (outerShapeFuel outerQueryFuel shapeCode bitIndex queryOutput : ℕ) : ℕ :=
  linkFuel
    (linkPrograms guardFrameProgram
      (linkPrograms (preserveRightProgram bitSerialMulProgram)
        (taggedProgramChoice constantFalseProgram (inRangeProgram outerQuery))))
    (preserveRightFuel outerShapeFuel) <|
    linkFuel
      (linkPrograms (preserveRightProgram bitSerialMulProgram)
        (taggedProgramChoice constantFalseProgram (inRangeProgram outerQuery)))
      13 <|
      linkFuel
        (taggedProgramChoice constantFalseProgram (inRangeProgram outerQuery))
        (preserveRightFuel
          (bitSerialMulFuel ((Nat.unpair shapeCode).1 - bitIndex)))
        (taggedProgramChoiceFuel
          (max 4
            (inRangeFuel outerQuery outerQueryFuel (Nat.unpair shapeCode).1
              queryOutput)))

/-- The padded query stream's register width. -/
def paddedQueryBits (inputLength shapeCode encodedInput queryIndex bitIndex
    outerShapeBits outerQueryBits queryOutput : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (preserveRightBits outerShapeBits inputLength
      (queryTail encodedInput queryIndex bitIndex) shapeCode) <|
    occurrenceStageBits inputLength
      (guardFrameBits shapeCode encodedInput queryIndex bitIndex) <|
      occurrenceStageBits inputLength
        (preserveRightBits
          (bitSerialMulBits inputLength
            ((Nat.unpair shapeCode).2 - queryIndex)
            ((Nat.unpair shapeCode).1 - bitIndex))
          (bitSerialMulInput ((Nat.unpair shapeCode).2 - queryIndex)
            ((Nat.unpair shapeCode).1 - bitIndex))
          (Nat.pair (Nat.unpair shapeCode).1
            (queryTail encodedInput queryIndex bitIndex))
          (queryGuard shapeCode queryIndex bitIndex))
        (queryChoiceBits inputLength shapeCode encodedInput queryIndex bitIndex
          outerQueryBits queryOutput)

/-- **The padded query stream, executed.**  The source query runner is called
only where the guard is positive, which is exactly where the source PCP's own
`halts` field applies. -/
theorem run_paddedQueryProgram (outerShape outerQuery : NPOracleProgram)
    (inputLength outerShapeBits outerShapeFuel outerQueryBits outerQueryFuel
      shapeCode encodedInput queryIndex bitIndex queryOutput : ℕ)
    (houterShape :
      runNPOracleProgram outerShape outerShapeBits outerShapeFuel
          (initialNPOracleState inputLength inputLength) =
        some shapeCode)
    (houterQuery : queryGuard shapeCode queryIndex bitIndex ≠ 0 →
      runNPOracleProgram outerQuery outerQueryBits outerQueryFuel
          (initialNPOracleState inputLength
            (queryCode inputLength encodedInput queryIndex bitIndex)) =
        some queryOutput) :
    runNPOracleProgram (paddedQueryProgram outerShape outerQuery)
        (paddedQueryBits inputLength shapeCode encodedInput queryIndex bitIndex
          outerShapeBits outerQueryBits queryOutput)
        (paddedQueryFuel outerQuery outerShapeFuel outerQueryFuel shapeCode
          bitIndex queryOutput)
        (initialNPOracleState inputLength
          (queryCode inputLength encodedInput queryIndex bitIndex)) =
      some (paddedQueryValue shapeCode queryIndex bitIndex queryOutput) := by
  have hchoice :
      runNPOracleProgram
          (taggedProgramChoice constantFalseProgram (inRangeProgram outerQuery))
          (queryChoiceBits inputLength shapeCode encodedInput queryIndex
            bitIndex outerQueryBits queryOutput)
          (taggedProgramChoiceFuel
            (max 4
              (inRangeFuel outerQuery outerQueryFuel (Nat.unpair shapeCode).1
                queryOutput)))
          (initialNPOracleState inputLength
            (Nat.pair (queryGuard shapeCode queryIndex bitIndex)
              (Nat.pair (Nat.unpair shapeCode).1
                (queryTail encodedInput queryIndex bitIndex)))) =
        some (paddedQueryValue shapeCode queryIndex bitIndex queryOutput) := by
    have hinput :
        natBitLength
            (Nat.pair inputLength
              (Nat.pair (queryGuard shapeCode queryIndex bitIndex)
                (Nat.pair (Nat.unpair shapeCode).1
                  (queryTail encodedInput queryIndex bitIndex)))) ≤
          queryChoiceBits inputLength shapeCode encodedInput queryIndex bitIndex
            outerQueryBits queryOutput :=
      Nat.le_max_left _ _
    have houtput :
        natBitLength
            (paddedQueryValue shapeCode queryIndex bitIndex queryOutput) ≤
          queryChoiceBits inputLength shapeCode encodedInput queryIndex bitIndex
            outerQueryBits queryOutput :=
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    by_cases hguard : queryGuard shapeCode queryIndex bitIndex = 0
    · have hvalue :
          paddedQueryValue shapeCode queryIndex bitIndex queryOutput =
            Nat.pair 2 0 := by
        unfold paddedQueryValue
        rw [if_pos hguard]
      rw [hvalue] at houtput ⊢
      rw [hguard] at hinput ⊢
      exact run_choiceZero constantFalseProgram (inRangeProgram outerQuery)
        inputLength _ constantFalseBits 4
        (queryChoiceBits inputLength shapeCode encodedInput queryIndex bitIndex
          outerQueryBits queryOutput)
        (max 4
          (inRangeFuel outerQuery outerQueryFuel (Nat.unpair shapeCode).1
            queryOutput))
        (Nat.pair 2 0) hinput
        ((Nat.le_max_left _ _).trans
          ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
        houtput (Nat.le_max_left _ _)
        (run_constantFalseProgram inputLength
          (Nat.pair (Nat.unpair shapeCode).1
            (queryTail encodedInput queryIndex bitIndex)))
    · have hpositive : 0 < (Nat.unpair shapeCode).1 - bitIndex := by
        rcases Nat.eq_zero_or_pos ((Nat.unpair shapeCode).1 - bitIndex) with
          hzero | hpos
        · exact absurd (by simp [queryGuard, hzero]) hguard
        · exact hpos
      have hvalue :
          paddedQueryValue shapeCode queryIndex bitIndex queryOutput =
            emittedValue (Nat.unpair shapeCode).1 queryOutput := by
        unfold paddedQueryValue
        rw [if_neg hguard]
      rw [hvalue] at houtput ⊢
      exact run_choiceNonzero constantFalseProgram (inRangeProgram outerQuery)
        inputLength _ _
        (inRangeBits inputLength (Nat.unpair shapeCode).1
          (queryTail encodedInput queryIndex bitIndex) outerQueryBits
          queryOutput)
        (inRangeFuel outerQuery outerQueryFuel (Nat.unpair shapeCode).1
          queryOutput)
        (queryChoiceBits inputLength shapeCode encodedInput queryIndex bitIndex
          outerQueryBits queryOutput)
        (max 4
          (inRangeFuel outerQuery outerQueryFuel (Nat.unpair shapeCode).1
            queryOutput))
        (emittedValue (Nat.unpair shapeCode).1 queryOutput) hguard hinput
        ((Nat.le_max_right _ _).trans
          ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
        houtput (Nat.le_max_right _ _)
        (run_inRangeProgram outerQuery inputLength outerQueryBits outerQueryFuel
          (Nat.unpair shapeCode).1 (queryTail encodedInput queryIndex bitIndex)
          queryOutput (by omega) (houterQuery hguard))
  have hproduct :
      runNPOracleProgram
          (linkPrograms (preserveRightProgram bitSerialMulProgram)
            (taggedProgramChoice constantFalseProgram
              (inRangeProgram outerQuery)))
          (occurrenceStageBits inputLength
            (preserveRightBits
              (bitSerialMulBits inputLength
                ((Nat.unpair shapeCode).2 - queryIndex)
                ((Nat.unpair shapeCode).1 - bitIndex))
              (bitSerialMulInput ((Nat.unpair shapeCode).2 - queryIndex)
                ((Nat.unpair shapeCode).1 - bitIndex))
              (Nat.pair (Nat.unpair shapeCode).1
                (queryTail encodedInput queryIndex bitIndex))
              (queryGuard shapeCode queryIndex bitIndex))
            (queryChoiceBits inputLength shapeCode encodedInput queryIndex
              bitIndex outerQueryBits queryOutput))
          (linkFuel
            (taggedProgramChoice constantFalseProgram
              (inRangeProgram outerQuery))
            (preserveRightFuel
              (bitSerialMulFuel ((Nat.unpair shapeCode).1 - bitIndex)))
            (taggedProgramChoiceFuel
              (max 4
                (inRangeFuel outerQuery outerQueryFuel (Nat.unpair shapeCode).1
                  queryOutput))))
          (initialNPOracleState inputLength
            (guardFrameOutput shapeCode encodedInput queryIndex bitIndex)) =
        some (paddedQueryValue shapeCode queryIndex bitIndex queryOutput) :=
    run_occurrenceStage
      (first := preserveRightProgram bitSerialMulProgram)
      (second :=
        taggedProgramChoice constantFalseProgram (inRangeProgram outerQuery))
      (run_preserveRightProgram bitSerialMulProgram inputLength
        (bitSerialMulBits inputLength
          ((Nat.unpair shapeCode).2 - queryIndex)
          ((Nat.unpair shapeCode).1 - bitIndex))
        (bitSerialMulFuel ((Nat.unpair shapeCode).1 - bitIndex))
        (bitSerialMulInput ((Nat.unpair shapeCode).2 - queryIndex)
          ((Nat.unpair shapeCode).1 - bitIndex))
        (Nat.pair (Nat.unpair shapeCode).1
          (queryTail encodedInput queryIndex bitIndex))
        (queryGuard shapeCode queryIndex bitIndex)
        (run_bitSerialMulProgram inputLength
          ((Nat.unpair shapeCode).2 - queryIndex)
          ((Nat.unpair shapeCode).1 - bitIndex)))
      hchoice
  have hguardStage :=
    run_occurrenceStage (first := guardFrameProgram)
      (second :=
        linkPrograms (preserveRightProgram bitSerialMulProgram)
          (taggedProgramChoice constantFalseProgram
            (inRangeProgram outerQuery)))
      (run_guardFrameProgram inputLength shapeCode encodedInput queryIndex
        bitIndex)
      hproduct
  exact run_occurrenceStage (first := preserveRightProgram outerShape)
    (second :=
      linkPrograms guardFrameProgram
        (linkPrograms (preserveRightProgram bitSerialMulProgram)
          (taggedProgramChoice constantFalseProgram
            (inRangeProgram outerQuery))))
    (run_preserveRightProgram outerShape inputLength outerShapeBits
      outerShapeFuel inputLength (queryTail encodedInput queryIndex bitIndex)
      shapeCode houterShape)
    hguardStage

/-! ## 5. The published instance -/

/-- The published padded query stream. -/
def publishedPaddedQueryProgram {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) : NPOracleProgram :=
  paddedQueryProgram outer.pcp.shape.program outer.pcp.query.program

theorem publishedPaddedQueryProgram_oracleFree {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    OracleFree (publishedPaddedQueryProgram outer) :=
  paddedQueryProgram_oracleFree outer.pcp.shapeOracleFree
    outer.pcp.queryOracleFree

/-- The published padded query stream's fuel. -/
def publishedPaddedQueryFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (request : ProjectionQueryRequest) :
    ℕ :=
  paddedQueryFuel outer.pcp.query.program
    (outer.pcp.shape.budget request.inputArity)
    (queryBudget outer.pcp request.inputArity)
    (outer.pcp.shape.execute request.inputArity) request.bit.val
    (queryExecuteAt outer.pcp request.inputArity
      (encodeBitInput request.input) request.query.val request.bit.val)

/-- The published padded query stream's register width. -/
def publishedPaddedQueryBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (request : ProjectionQueryRequest) :
    ℕ :=
  paddedQueryBits request.inputArity
    (outer.pcp.shape.execute request.inputArity)
    (encodeBitInput request.input) request.query.val request.bit.val
    (outer.pcp.shape.budget request.inputArity)
    (queryBudget outer.pcp request.inputArity)
    (queryExecuteAt outer.pcp request.inputArity
      (encodeBitInput request.input) request.query.val request.bit.val)

/-- **The padded query runner, executed.**  No hypothesis remains: the emitted
numeral is the padded query output of
`PaddedProjectionRunnerAssembly.paddedQueryRequestOutput`. -/
theorem run_publishedPaddedQueryProgram {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (request : ProjectionQueryRequest) :
    runNPOracleProgram (publishedPaddedQueryProgram outer)
        (publishedPaddedQueryBits outer request)
        (publishedPaddedQueryFuel outer request)
        (initialNPOracleState (ProjectionQueryRequest.length request)
          (ProjectionQueryRequest.code request)) =
      some (paddedQueryRequestOutput outer request) := by
  have hcond :
      (outer.pcp.queryCount request.inputArity - request.query.val) *
          (outer.pcp.nativeWidth request.inputArity - request.bit.val) =
        queryGuard (outer.pcp.shape.execute request.inputArity)
          request.query.val request.bit.val := rfl
  have hmodulus : ∀ tag : ℕ,
      selectedModulus (tag % 3)
          (Nat.unpair (outer.pcp.shape.execute request.inputArity)).1 =
        paddedQueryModulus outer request.inputArity tag := by
    intro tag
    unfold selectedModulus paddedQueryModulus
    by_cases htag : tag % 3 = 2
    · rw [if_pos (by omega), if_pos htag]
    · rw [if_neg (by omega), if_neg htag]
      rfl
  have hvalue :
      paddedQueryValue (outer.pcp.shape.execute request.inputArity)
          request.query.val request.bit.val
          (queryExecuteAt outer.pcp request.inputArity
            (encodeBitInput request.input) request.query.val
            request.bit.val) =
        paddedQueryRequestOutput outer request := by
    unfold paddedQueryValue paddedQueryRequestOutput paddedQueryOutput
      emittedValue
    rw [hcond, hmodulus]
  rw [← hvalue]
  refine run_paddedQueryProgram outer.pcp.shape.program outer.pcp.query.program
    request.inputArity (outer.pcp.shape.budget request.inputArity)
    (outer.pcp.shape.budget request.inputArity)
    (queryBudget outer.pcp request.inputArity)
    (queryBudget outer.pcp request.inputArity)
    (outer.pcp.shape.execute request.inputArity)
    (encodeBitInput request.input) request.query.val request.bit.val
    (queryExecuteAt outer.pcp request.inputArity
      (encodeBitInput request.input) request.query.val request.bit.val)
    (outer.pcp.shape.run_eq_execute request.inputArity) ?_
  intro hguard
  have hcountValue :
      (Nat.unpair (outer.pcp.shape.execute request.inputArity)).2 =
        outer.pcp.queryCount request.inputArity := rfl
  have hwidthValue :
      (Nat.unpair (outer.pcp.shape.execute request.inputArity)).1 =
        outer.pcp.nativeWidth request.inputArity := rfl
  have hqueryLt :
      request.query.val < outer.pcp.queryCount request.inputArity := by
    have hfactor :
        (Nat.unpair (outer.pcp.shape.execute request.inputArity)).2 -
            request.query.val ≠ 0 := by
      intro hzero
      exact hguard (by unfold queryGuard; rw [hzero, Nat.zero_mul])
    omega
  have hbitLt :
      request.bit.val < outer.pcp.nativeWidth request.inputArity := by
    have hfactor :
        (Nat.unpair (outer.pcp.shape.execute request.inputArity)).1 -
            request.bit.val ≠ 0 := by
      intro hzero
      exact hguard (by unfold queryGuard; rw [hzero, Nat.mul_zero])
    omega
  exact outer.pcp.query.run_eq_execute
    (outer.pcp.queryRequest request.input ⟨request.query.val, hqueryLt⟩
      ⟨request.bit.val, hbitLt⟩)

end NearCubicWires.PaddedProjectionQueryRunner
