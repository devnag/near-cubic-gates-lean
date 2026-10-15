import Proof.MachineModel.CanonicalBranchSelectorProgram

/-!
# The length-driven schedule decoder

`CanonicalTargetLanguageProgram.executableLanguageProgramOfRun` demands *one*
instruction stream for every `LanguageEvaluationRequest`, whereas the two
chains of `BranchTargetLanguageProgram` still carry the scheduled numerals as
immediates chosen from the request's own target length.  Every such numeral is
a function of `LanguageEvaluationRequest.length` through the sole source
enumeration: `RecoveryScheduleEnvelope.sourceIndexOfLength` decodes the index,
`RecoveryScheduleEnvelope.sourceLength` is `2 ^ (index + 1)`, and the widths,
caps, and copy counts are arithmetic in that length and the published
constants.

This module supplies the first, length-only stage of that decoder: from the
request alone it emits the scheduled source index and the scheduled source
length beside the retained request code, in the framed shape

`pair sourceIndex (pair sourceLength code)`.

Two already verified programs do the work — `sourceIndexProgram`, whose only
input is the public length register, and `binaryTwoPowProgram` — bracketed by
three straight-line framing adapters and the count-preserving wrapper.  The
decoder is oracle-free, and its width and fuel are closed in the public
length alone.

## What the decoder cannot supply

Two of the numerals the chains bake are *not* arithmetic in the public length:

* `outer.pcp.queryCount` at the scheduled length is an opaque field of the
  projection PCP, bounded only from above by the published contract, exactly
  the datum whose positivity `BranchTargetLanguageProgram` already carries as
  an explicit Case-1 hypothesis;
* the Case-2 substituted circuit's encoding depends on the recovered oracle,
  not on the request, and is produced by the bounded-oracle description
  recovery rather than by schedule arithmetic.

Both are recorded at the packaging seam rather than hidden here.
-/

namespace NearCubicWires.LanguageScheduleDecoderProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping -/

private theorem le_pair_of_le_left {value left right : ℕ}
    (hvalue : value ≤ left) : value ≤ Nat.pair left right :=
  hvalue.trans (Nat.left_le_pair left right)

private theorem le_pair_of_le_right {value left right : ℕ}
    (hvalue : value ≤ right) : value ≤ Nat.pair left right :=
  hvalue.trans (Nat.right_le_pair left right)

/-! ## 2. The three framing adapters -/

/-- Duplicate the request so that the length decoder may overwrite one copy. -/
def scheduleRequestPrepProgram : NPOracleProgram :=
  [ .pair 0 0 2 1
  , .copy 2 0 2
  , .halt 0
  ]

@[simp] theorem scheduleRequestPrepProgram_oracleFree :
    OracleFree scheduleRequestPrepProgram := by
  rfl

def scheduleRequestPrepBits (code : ℕ) : ℕ :=
  natBitLength (Nat.pair code code)

theorem run_scheduleRequestPrepProgram (inputLength code : ℕ) :
    runNPOracleProgram scheduleRequestPrepProgram
        (scheduleRequestPrepBits code) 3
        (initialNPOracleState inputLength code) =
      some (Nat.pair code code) := by
  have houtput :
      natBitLength (Nat.pair code code) ≤ scheduleRequestPrepBits code :=
    le_refl _
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair code code) (by rfl) rfl
    (by simp [initialNPOracleState]) houtput]
  rw [show 2 = 1 + 1 by omega]
  rw [run_copy_instruction (value := Nat.pair code code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Frame the decoded source index as the exponent request of the scheduled
source length, retaining the index and the request code. -/
def scheduleExponentPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .set 3 1 2
  , .add 2 3 4 3
  , .pair 4 0 0 4
  , .halt 0
  ]

@[simp] theorem scheduleExponentPrepProgram_oracleFree :
    OracleFree scheduleExponentPrepProgram := by
  rfl

def scheduleExponentPrepBits (sourceIndex code : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair sourceIndex code)
      (Nat.pair (sourceIndex + 1) (Nat.pair sourceIndex code)))

theorem run_scheduleExponentPrepProgram (inputLength sourceIndex code : ℕ) :
    runNPOracleProgram scheduleExponentPrepProgram
        (scheduleExponentPrepBits sourceIndex code) 5
        (initialNPOracleState inputLength (Nat.pair sourceIndex code)) =
      some (Nat.pair (sourceIndex + 1) (Nat.pair sourceIndex code)) := by
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair sourceIndex code →
      natBitLength value ≤ scheduleExponentPrepBits sourceIndex code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ Nat.pair (sourceIndex + 1) (Nat.pair sourceIndex code) →
      natBitLength value ≤ scheduleExponentPrepBits sourceIndex code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hindex := hrequest sourceIndex (Nat.left_le_pair sourceIndex code)
  have hone :=
    hresult 1
      (le_pair_of_le_left (by omega : (1 : ℕ) ≤ sourceIndex + 1))
  have hsuccessor :=
    hresult (sourceIndex + 1) (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceIndex) (by rfl) rfl
    (by simp [initialNPOracleState]) hindex]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl hone]
  rw [show 3 = 2 + 1 by omega]
  rw [run_add_instruction (value := sourceIndex + 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsuccessor]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (sourceIndex + 1) (Nat.pair sourceIndex code))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Reorder the decoded schedule into the public decoder ABI. -/
def scheduleFramePrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 5 6 5
  , .pair 4 6 0 6
  , .halt 0
  ]

@[simp] theorem scheduleFramePrepProgram_oracleFree :
    OracleFree scheduleFramePrepProgram := by
  rfl

/-- Public output of the decoder: the scheduled source index, the scheduled
source length, and the retained request code. -/
def scheduleDecoderOutput (sourceIndex scheduledLength code : ℕ) : ℕ :=
  Nat.pair sourceIndex (Nat.pair scheduledLength code)

def scheduleFramePrepBits (sourceIndex scheduledLength code : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair scheduledLength (Nat.pair sourceIndex code))
      (scheduleDecoderOutput sourceIndex scheduledLength code))

theorem run_scheduleFramePrepProgram
    (inputLength sourceIndex scheduledLength code : ℕ) :
    runNPOracleProgram scheduleFramePrepProgram
        (scheduleFramePrepBits sourceIndex scheduledLength code) 7
        (initialNPOracleState inputLength
          (Nat.pair scheduledLength (Nat.pair sourceIndex code))) =
      some (scheduleDecoderOutput sourceIndex scheduledLength code) := by
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair scheduledLength (Nat.pair sourceIndex code) →
      natBitLength value ≤
        scheduleFramePrepBits sourceIndex scheduledLength code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ scheduleDecoderOutput sourceIndex scheduledLength code →
      natBitLength value ≤
        scheduleFramePrepBits sourceIndex scheduledLength code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hlength := hrequest scheduledLength (Nat.left_le_pair _ _)
  have htail := hrequest (Nat.pair sourceIndex code) (Nat.right_le_pair _ _)
  have hindex :=
    hrequest sourceIndex
      (le_pair_of_le_right (Nat.left_le_pair sourceIndex code))
  have hcode :=
    hrequest code (le_pair_of_le_right (Nat.right_le_pair sourceIndex code))
  have hframed :=
    hresult (Nat.pair scheduledLength code) (Nat.right_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := scheduledLength) (by rfl) rfl
    (by simp [initialNPOracleState]) hlength]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair sourceIndex code)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htail]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceIndex) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hindex]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcode]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair scheduledLength code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hframed]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := scheduleDecoderOutput sourceIndex scheduledLength code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, scheduleDecoderOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 3. The decoder -/

private def scheduleDecoderTailThree : NPOracleProgram :=
  linkPrograms (preserveRightProgram binaryTwoPowProgram)
    scheduleFramePrepProgram

private def scheduleDecoderTailTwo : NPOracleProgram :=
  linkPrograms scheduleExponentPrepProgram scheduleDecoderTailThree

private def scheduleDecoderTailOne : NPOracleProgram :=
  linkPrograms (preserveRightProgram sourceIndexProgram)
    scheduleDecoderTailTwo

/-- **The length-driven schedule decoder.**  One fixed oracle-free program
emitting the scheduled source index and the scheduled source length of the
requested public length, beside the retained request code. -/
def scheduleDecoderProgram : NPOracleProgram :=
  linkPrograms scheduleRequestPrepProgram scheduleDecoderTailOne

theorem scheduleDecoderProgram_oracleFree : OracleFree scheduleDecoderProgram := by
  apply oracleFree_linkPrograms scheduleRequestPrepProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree sourceIndexProgram
      sourceIndexProgram_oracleFree
  apply oracleFree_linkPrograms scheduleExponentPrepProgram_oracleFree
  exact oracleFree_linkPrograms
    (preserveRightProgram_oracleFree binaryTwoPowProgram
      binaryTwoPowProgram_oracleFree)
    scheduleFramePrepProgram_oracleFree

def scheduleDecoderFuel (inputLength : ℕ) : ℕ :=
  linkFuel scheduleDecoderTailOne 3 <|
    linkFuel scheduleDecoderTailTwo
      (preserveRightFuel (sourceIndexProgramFuel inputLength)) <|
      linkFuel scheduleDecoderTailThree 5 <|
        linkFuel scheduleFramePrepProgram
          (preserveRightFuel
            (binaryTwoPowFuel (sourceIndexOfLength inputLength + 1)))
          7

def scheduleDecoderBits (inputLength code : ℕ) : ℕ :=
  occurrenceStageBits inputLength (scheduleRequestPrepBits code) <|
    occurrenceStageBits inputLength
      (preserveRightBits (sourceIndexProgramMaximumBits inputLength) code code
        (sourceIndexOfLength inputLength)) <|
      occurrenceStageBits inputLength
        (scheduleExponentPrepBits (sourceIndexOfLength inputLength) code) <|
        occurrenceStageBits inputLength
          (preserveRightBits
            (binaryTwoPowBits (sourceIndexOfLength inputLength + 1))
            (sourceIndexOfLength inputLength + 1)
            (Nat.pair (sourceIndexOfLength inputLength) code)
            (sourceLength (sourceIndexOfLength inputLength)))
          (scheduleFramePrepBits (sourceIndexOfLength inputLength)
            (sourceLength (sourceIndexOfLength inputLength)) code)

/-- **Exact execution of the schedule decoder.**  From the public length alone
the fixed program emits the scheduled source index and the scheduled source
length; the request code is carried through untouched. -/
theorem run_scheduleDecoderProgram (inputLength code : ℕ) :
    runNPOracleProgram scheduleDecoderProgram
        (scheduleDecoderBits inputLength code)
        (scheduleDecoderFuel inputLength)
        (initialNPOracleState inputLength code) =
      some
        (scheduleDecoderOutput (sourceIndexOfLength inputLength)
          (sourceLength (sourceIndexOfLength inputLength)) code) := by
  have hindex :
      runNPOracleProgram (preserveRightProgram sourceIndexProgram)
          (preserveRightBits (sourceIndexProgramMaximumBits inputLength) code
            code (sourceIndexOfLength inputLength))
          (preserveRightFuel (sourceIndexProgramFuel inputLength))
          (initialNPOracleState inputLength (Nat.pair code code)) =
        some (Nat.pair (sourceIndexOfLength inputLength) code) :=
    run_preserveRightProgram sourceIndexProgram inputLength
      (sourceIndexProgramMaximumBits inputLength)
      (sourceIndexProgramFuel inputLength) code code
      (sourceIndexOfLength inputLength)
      (run_sourceIndexProgram_atLength inputLength code)
  have hlength :
      runNPOracleProgram (preserveRightProgram binaryTwoPowProgram)
          (preserveRightBits
            (binaryTwoPowBits (sourceIndexOfLength inputLength + 1))
            (sourceIndexOfLength inputLength + 1)
            (Nat.pair (sourceIndexOfLength inputLength) code)
            (sourceLength (sourceIndexOfLength inputLength)))
          (preserveRightFuel
            (binaryTwoPowFuel (sourceIndexOfLength inputLength + 1)))
          (initialNPOracleState inputLength
            (Nat.pair (sourceIndexOfLength inputLength + 1)
              (Nat.pair (sourceIndexOfLength inputLength) code))) =
        some
          (Nat.pair (sourceLength (sourceIndexOfLength inputLength))
            (Nat.pair (sourceIndexOfLength inputLength) code)) :=
    run_preserveRightProgram binaryTwoPowProgram inputLength
      (binaryTwoPowBits (sourceIndexOfLength inputLength + 1))
      (binaryTwoPowFuel (sourceIndexOfLength inputLength + 1))
      (sourceIndexOfLength inputLength + 1)
      (Nat.pair (sourceIndexOfLength inputLength) code)
      (sourceLength (sourceIndexOfLength inputLength))
      (run_binaryTwoPowProgram inputLength (sourceIndexOfLength inputLength + 1)
        (binaryTwoPowBits (sourceIndexOfLength inputLength + 1)) (le_refl _))
  exact run_occurrenceStage
    (run_scheduleRequestPrepProgram inputLength code)
    (run_occurrenceStage hindex
      (run_occurrenceStage
        (run_scheduleExponentPrepProgram inputLength
          (sourceIndexOfLength inputLength) code)
        (run_occurrenceStage hlength
          (run_scheduleFramePrepProgram inputLength
            (sourceIndexOfLength inputLength)
            (sourceLength (sourceIndexOfLength inputLength)) code))))

/-! ## 4. The decoder at one language request -/

/-- The decoder, read off a `LanguageEvaluationRequest` directly. -/
theorem run_scheduleDecoderProgram_request (request : LanguageEvaluationRequest) :
    runNPOracleProgram scheduleDecoderProgram
        (scheduleDecoderBits (LanguageEvaluationRequest.length request)
          (LanguageEvaluationRequest.code request))
        (scheduleDecoderFuel (LanguageEvaluationRequest.length request))
        (initialNPOracleState (LanguageEvaluationRequest.length request)
          (LanguageEvaluationRequest.code request)) =
      some
        (scheduleDecoderOutput
          (sourceIndexOfLength (LanguageEvaluationRequest.length request))
          (sourceLength
            (sourceIndexOfLength (LanguageEvaluationRequest.length request)))
          (LanguageEvaluationRequest.code request)) :=
  run_scheduleDecoderProgram (LanguageEvaluationRequest.length request)
    (LanguageEvaluationRequest.code request)

/-- The decoder is exact on the scheduled lengths: at a public length that is
itself a source length, the emitted index is that source's own. -/
@[simp] theorem scheduleDecoderOutput_at_sourceLength
    (sourceIndex code : ℕ) :
    scheduleDecoderOutput (sourceIndexOfLength (sourceLength sourceIndex))
        (sourceLength (sourceIndexOfLength (sourceLength sourceIndex))) code =
      scheduleDecoderOutput sourceIndex (sourceLength sourceIndex) code := by
  rw [sourceIndexOfLength_sourceLength]

end NearCubicWires.LanguageScheduleDecoderProgram
