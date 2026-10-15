import Proof.MachineModel.RuntimeScheduleNumeralBank

/-!
# The refuter-word frame, read from the numeral bank

`RefuterWordFrameProgram.refuterWordFrameProgram` builds the frame

`pair (encodeBitInput word) (pair sourceLength pointCode)`

that every scheduled recovery stage consumes, but it takes the scheduled source
length as an *immediate* of its request prelude, so its instruction stream
depends on the request.  This module rebuilds exactly that frame from the
numeral bank's output instead: the scheduled source length is read out of a
register, and the only immediate left is
`ExecutableWeakNondeterministicMachine.description`, which the machine-dependence
analysis of `ExecutableTargetLanguagePackaging` already licenses as frozen.

Only the request prelude and the reframing adapter are rebuilt; the published
refuter call and the canonical low-bit normalizer are reused verbatim through
`CanonicalNativeCallProgram.nativeContextCallProgram` and
`BitInputPrefixProgram.bitInputPrefixProgram`, and the identification of the
truncated output code with the refuter's own word is
`RefuterWordFrameProgram.encodeBitInput_refuterOutput`.

This is the first of the four immediates listed at the packaging seam; the
remaining three — the recovery seed's width, the decision row stage's query
count, and the Case-2 copy count — are the same rewrite applied to their own
stages, and the bank already supplies each numeral in the same frame.
-/

namespace NearCubicWires.BankRefuterWordFrameProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CaseOneTargetLanguageClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RefuterWordFrameProgram
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping -/

private theorem le_pair_left {value left right : ℕ} (hvalue : value ≤ left) :
    value ≤ Nat.pair left right :=
  hvalue.trans (Nat.left_le_pair left right)

private theorem le_pair_right {value left right : ℕ} (hvalue : value ≤ right) :
    value ≤ Nat.pair left right :=
  hvalue.trans (Nat.right_le_pair left right)

/-! ## 2. The register-driven request prelude

Input the bank's frame
`pair sourceLength (pair width (pair queryCount (pair copies pointCode)))`,
output the published refuter's call frame
`pair (pair description sourceLength) (pair sourceLength pointCode)`.  The
scheduled source length is now a register read; the description is the only
immediate. -/

private def bankRefuterRequestProgram (description : ℕ) : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 3 3
  , .unpairRight 3 3 4
  , .unpairRight 3 3 5
  , .set 4 description 6
  , .pair 4 2 5 7
  , .pair 2 3 6 8
  , .pair 5 6 0 9
  , .halt 0
  ]

@[simp] private theorem bankRefuterRequestProgram_oracleFree
    (description : ℕ) :
    OracleFree (bankRefuterRequestProgram description) := by
  rfl

/-- The published refuter's call frame at one scheduled source length. -/
def bankRefuterRequestOutput
    (description sourceLen pointCode : ℕ) : ℕ :=
  Nat.pair (Nat.pair description sourceLen) (Nat.pair sourceLen pointCode)

private def bankRefuterRequestBits
    (description sourceLen width queryCount copies pointCode : ℕ) : ℕ :=
  natBitLength
    (max
      (scheduleNumeralBankOutput sourceLen width queryCount copies pointCode)
      (bankRefuterRequestOutput description sourceLen pointCode))

private theorem run_bankRefuterRequestProgram
    (inputLength description sourceLen width queryCount copies
      pointCode : ℕ) :
    runNPOracleProgram (bankRefuterRequestProgram description)
        (bankRefuterRequestBits description sourceLen width queryCount copies
          pointCode)
        10
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies
            pointCode)) =
      some (bankRefuterRequestOutput description sourceLen pointCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        scheduleNumeralBankOutput sourceLen width queryCount copies pointCode →
      natBitLength value ≤
        bankRefuterRequestBits description sourceLen width queryCount copies
          pointCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ bankRefuterRequestOutput description sourceLen pointCode →
      natBitLength value ≤
        bankRefuterRequestBits description sourceLen width queryCount copies
          pointCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hlength := hrequest sourceLen (le_pair_left (le_refl sourceLen))
  have hwidthTail :=
    hrequest (Nat.pair width (Nat.pair queryCount (Nat.pair copies pointCode)))
      (le_pair_right (le_refl _))
  have hcountTail :=
    hrequest (Nat.pair queryCount (Nat.pair copies pointCode))
      (le_pair_right (le_pair_right (le_refl _)))
  have hcopyTail :=
    hrequest (Nat.pair copies pointCode)
      (le_pair_right (le_pair_right (le_pair_right (le_refl _))))
  have hpoint :=
    hrequest pointCode
      (le_pair_right
        (le_pair_right (le_pair_right (le_pair_right (le_refl pointCode)))))
  have hdescription :=
    hresult description (le_pair_left (le_pair_left (le_refl description)))
  have hcall :=
    hresult (Nat.pair description sourceLen) (le_pair_left (le_refl _))
  have hcontext :=
    hresult (Nat.pair sourceLen pointCode) (le_pair_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceLen) (by rfl) rfl
    (by simp [initialNPOracleState, scheduleNumeralBankOutput]) hlength]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair queryCount (Nat.pair copies pointCode)))
    (by rfl) rfl
    (by
      simp [initialNPOracleState, scheduleNumeralBankOutput,
        NPOracleState.write, NPOracleState.jump])
    hwidthTail]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair queryCount (Nat.pair copies pointCode)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountTail]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair copies pointCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcopyTail]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := pointCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpoint]
  rw [show 5 = 4 + 1 by omega]
  rw [run_set_instruction (value := description) (by rfl) rfl hdescription]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair description sourceLen)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcall]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair sourceLen pointCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcontext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := bankRefuterRequestOutput description sourceLen pointCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        bankRefuterRequestOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 3. The truncation adapter

Input `pair outputCode (pair sourceLength pointCode)`, output
`pair (bitInputPrefixInput sourceLength outputCode) (pair sourceLength
pointCode)`. -/

private def bankPrefixFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .pair 4 2 5 4
  , .pair 5 3 0 5
  , .halt 0
  ]

@[simp] private theorem bankPrefixFrameProgram_oracleFree :
    OracleFree bankPrefixFrameProgram := by
  rfl

private def bankPrefixFrameInput (sourceLen pointCode outputCode : ℕ) : ℕ :=
  Nat.pair outputCode (Nat.pair sourceLen pointCode)

private def bankPrefixFrameOutput (sourceLen pointCode outputCode : ℕ) : ℕ :=
  Nat.pair (bitInputPrefixInput sourceLen outputCode)
    (Nat.pair sourceLen pointCode)

private def bankPrefixFrameBits (sourceLen pointCode outputCode : ℕ) : ℕ :=
  natBitLength
    (max (bankPrefixFrameInput sourceLen pointCode outputCode)
      (bankPrefixFrameOutput sourceLen pointCode outputCode))

private theorem run_bankPrefixFrameProgram
    (inputLength sourceLen pointCode outputCode : ℕ) :
    runNPOracleProgram bankPrefixFrameProgram
        (bankPrefixFrameBits sourceLen pointCode outputCode) 6
        (initialNPOracleState inputLength
          (bankPrefixFrameInput sourceLen pointCode outputCode)) =
      some (bankPrefixFrameOutput sourceLen pointCode outputCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤ bankPrefixFrameInput sourceLen pointCode outputCode →
      natBitLength value ≤ bankPrefixFrameBits sourceLen pointCode outputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ bankPrefixFrameOutput sourceLen pointCode outputCode →
      natBitLength value ≤ bankPrefixFrameBits sourceLen pointCode outputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hcode := hrequest outputCode (le_pair_left (le_refl outputCode))
  have hcontext :=
    hrequest (Nat.pair sourceLen pointCode) (le_pair_right (le_refl _))
  have hlength :=
    hrequest sourceLen (le_pair_right (le_pair_left (le_refl sourceLen)))
  have hprefix :=
    hresult (bitInputPrefixInput sourceLen outputCode)
      (le_pair_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := outputCode) (by rfl) rfl
    (by simp [initialNPOracleState, bankPrefixFrameInput]) hcode]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair sourceLen pointCode)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, bankPrefixFrameInput, NPOracleState.write,
        NPOracleState.jump])
    hcontext]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceLen) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlength]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := bitInputPrefixInput sourceLen outputCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, bitInputPrefixInput])
    hprefix]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := bankPrefixFrameOutput sourceLen pointCode outputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bankPrefixFrameOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 4. The published refuter call -/

private def bankRefuterCallProgram
    (refuterProgram : NPOracleProgram) (description : ℕ) : NPOracleProgram :=
  linkPrograms (bankRefuterRequestProgram description)
    (nativeContextCallProgram refuterProgram)

private def bankRefuterCallFuel
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (sourceLen : ℕ) : ℕ :=
  linkFuel (nativeContextCallProgram refuter.runner.program) 10
    (nativeContextCallFuel refuter.runner.program
      (refuter.runner.budget (refuter.request machine sourceLen)) sourceLen
      (Nat.pair machine.description sourceLen))

private def bankRefuterCallBits
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (inputLength sourceLen width queryCount copies pointCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (bankRefuterRequestBits machine.description sourceLen width queryCount
      copies pointCode)
    (nativeContextCallBits inputLength sourceLen
      (Nat.pair machine.description sourceLen) pointCode
      (refuter.outputCode machine sourceLen)
      (refuter.runner.budget (refuter.request machine sourceLen)))

private theorem run_bankRefuterCallProgram
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (inputLength sourceLen width queryCount copies pointCode : ℕ) :
    runNPOracleProgram
        (bankRefuterCallProgram refuter.runner.program machine.description)
        (bankRefuterCallBits refuter machine inputLength sourceLen width
          queryCount copies pointCode)
        (bankRefuterCallFuel refuter machine sourceLen)
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies
            pointCode)) =
      some
        (Nat.pair (refuter.outputCode machine sourceLen)
          (Nat.pair sourceLen pointCode)) :=
  run_occurrenceStage
    (run_bankRefuterRequestProgram inputLength machine.description sourceLen
      width queryCount copies pointCode)
    (run_nativeContextCallProgram refuter.runner.program inputLength sourceLen
      (Nat.pair machine.description sourceLen) pointCode
      (refuter.outputCode machine sourceLen)
      (refuter.runner.budget (refuter.request machine sourceLen))
      (refuter.runner.budget (refuter.request machine sourceLen))
      (refuter.runner.run_eq_execute (refuter.request machine sourceLen)))

/-! ## 5. The frame -/

private def bankRefuterPrefixProgram
    (refuterProgram : NPOracleProgram) (description : ℕ) : NPOracleProgram :=
  linkPrograms (bankRefuterCallProgram refuterProgram description)
    bankPrefixFrameProgram

private def bankRefuterPrefixFuel
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (sourceLen : ℕ) : ℕ :=
  linkFuel bankPrefixFrameProgram
    (bankRefuterCallFuel refuter machine sourceLen) 6

private def bankRefuterPrefixBits
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (inputLength sourceLen width queryCount copies pointCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (bankRefuterCallBits refuter machine inputLength sourceLen width queryCount
      copies pointCode)
    (bankPrefixFrameBits sourceLen pointCode
      (refuter.outputCode machine sourceLen))

private theorem run_bankRefuterPrefixProgram
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (inputLength sourceLen width queryCount copies pointCode : ℕ) :
    runNPOracleProgram
        (bankRefuterPrefixProgram refuter.runner.program machine.description)
        (bankRefuterPrefixBits refuter machine inputLength sourceLen width
          queryCount copies pointCode)
        (bankRefuterPrefixFuel refuter machine sourceLen)
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies
            pointCode)) =
      some
        (bankPrefixFrameOutput sourceLen pointCode
          (refuter.outputCode machine sourceLen)) :=
  run_occurrenceStage
    (run_bankRefuterCallProgram refuter machine inputLength sourceLen width
      queryCount copies pointCode)
    (run_bankPrefixFrameProgram inputLength sourceLen pointCode
      (refuter.outputCode machine sourceLen))

/-- **The refuter-word frame, read from the numeral bank.**  One fixed
instruction stream whose only immediate is the machine description. -/
def bankRefuterWordFrameProgram
    (refuterProgram : NPOracleProgram) (description : ℕ) : NPOracleProgram :=
  linkPrograms (bankRefuterPrefixProgram refuterProgram description)
    (preserveRightProgram bitInputPrefixProgram)

theorem bankRefuterWordFrameProgram_oracleFree
    {refuterProgram : NPOracleProgram} (hrefuter : OracleFree refuterProgram)
    (description : ℕ) :
    OracleFree (bankRefuterWordFrameProgram refuterProgram description) :=
  oracleFree_linkPrograms
    (oracleFree_linkPrograms
      (oracleFree_linkPrograms (bankRefuterRequestProgram_oracleFree description)
        (nativeContextCallProgram_oracleFree hrefuter))
      bankPrefixFrameProgram_oracleFree)
    (preserveRightProgram_oracleFree bitInputPrefixProgram
      bitInputPrefixProgram_oracleFree)

def bankRefuterWordFrameFuel
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (sourceLen : ℕ) : ℕ :=
  linkFuel (preserveRightProgram bitInputPrefixProgram)
    (bankRefuterPrefixFuel refuter machine sourceLen)
    (preserveRightFuel
      (bitInputPrefixFuel sourceLen (refuter.outputCode machine sourceLen)))

def bankRefuterWordFrameBits
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (inputLength sourceLen width queryCount copies pointCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (bankRefuterPrefixBits refuter machine inputLength sourceLen width
      queryCount copies pointCode)
    (preserveRightBits
      (bitInputPrefixBits sourceLen (refuter.outputCode machine sourceLen))
      (bitInputPrefixInput sourceLen (refuter.outputCode machine sourceLen))
      (Nat.pair sourceLen pointCode)
      (bitInputPrefix sourceLen (refuter.outputCode machine sourceLen)))

/-- **The refuter-word frame, executed from the bank's registers.**  The frame
`pair (encodeBitInput word) (pair sourceLength pointCode)` consumed by every
scheduled recovery stage is produced from the numeral bank's output with no
target-derived immediate: the scheduled source length is read from a register
and the published refuter call is the only imported execution. -/
theorem run_bankRefuterWordFrameProgram
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (inputLength sourceLen width queryCount copies pointCode : ℕ) :
    runNPOracleProgram
        (bankRefuterWordFrameProgram refuter.runner.program machine.description)
        (bankRefuterWordFrameBits refuter machine inputLength sourceLen width
          queryCount copies pointCode)
        (bankRefuterWordFrameFuel refuter machine sourceLen)
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies
            pointCode)) =
      some
        (Nat.pair (encodeBitInput (refuter.output machine sourceLen))
          (Nat.pair sourceLen pointCode)) := by
  have hrun :
      runNPOracleProgram
          (bankRefuterWordFrameProgram refuter.runner.program
            machine.description)
          (bankRefuterWordFrameBits refuter machine inputLength sourceLen width
            queryCount copies pointCode)
          (bankRefuterWordFrameFuel refuter machine sourceLen)
          (initialNPOracleState inputLength
            (scheduleNumeralBankOutput sourceLen width queryCount copies
              pointCode)) =
        some
          (Nat.pair
            (bitInputPrefix sourceLen (refuter.outputCode machine sourceLen))
            (Nat.pair sourceLen pointCode)) :=
    run_occurrenceStage
      (run_bankRefuterPrefixProgram refuter machine inputLength sourceLen width
        queryCount copies pointCode)
      (run_preserveRightProgram bitInputPrefixProgram inputLength
        (bitInputPrefixBits sourceLen (refuter.outputCode machine sourceLen))
        (bitInputPrefixFuel sourceLen (refuter.outputCode machine sourceLen))
        (bitInputPrefixInput sourceLen (refuter.outputCode machine sourceLen))
        (Nat.pair sourceLen pointCode)
        (bitInputPrefix sourceLen (refuter.outputCode machine sourceLen))
        (run_bitInputPrefixProgram inputLength sourceLen
          (refuter.outputCode machine sourceLen)
          (bitInputPrefixBits sourceLen (refuter.outputCode machine sourceLen))
          0 (Nat.le_refl _)))
  rw [encodeBitInput_refuterOutput refuter machine sourceLen]
  exact hrun

/-! ## 6. The Case-1 chain from the bank's frame

Linking the register-driven frame onto the published Case-1 compiler closes the
first of the four baked numerals: `CaseOneTargetLanguageClosure`'s scheduled
source length is now a register read.  The recovery seed's width remains the
one numeral this chain still takes as an immediate, and the decision row stage
`row` is unchanged.
-/

/-- The Case-1 chain from the numeral bank's frame. -/
def bankCaseOneTargetBitProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (refuterProgram row : NPOracleProgram) (description width : ℕ) :
    NPOracleProgram :=
  linkPrograms (bankRefuterWordFrameProgram refuterProgram description)
    (caseOneTargetBitProgram algorithm (outerProofFormulaSeedProgram row width))

def bankCaseOneTargetBitFuel
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (row : NPOracleProgram) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceIndex : ℕ) (rowFuel : ℕ → ℕ) (targetFuel : ℕ) : ℕ :=
  linkFuel
    (caseOneTargetBitProgram algorithm
      (outerProofFormulaSeedProgram row (scheduledWidth outer sourceIndex)))
    (bankRefuterWordFrameFuel source.refuter machine (sourceLength sourceIndex))
    (caseOneTargetBitFuel algorithm
      (outerProofFormulaSeedProgram row (scheduledWidth outer sourceIndex))
      outer sourceIndex (scheduledRefuterWord source machine sourceIndex)
      (outerProofFormulaSeedFuel row (paddedOuterPCP outer)
        (scheduledRefuterWord source machine sourceIndex) rowFuel)
      targetFuel)

def bankCaseOneTargetBitBits
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceIndex target width queryCount copies pointCode targetBits : ℕ)
    (rowBits : ℕ → ℕ) : ℕ :=
  occurrenceStageBits target
    (bankRefuterWordFrameBits source.refuter machine target
      (sourceLength sourceIndex) width queryCount copies pointCode)
    (caseOneTargetBitBits algorithm outer sourceIndex
      (scheduledRefuterWord source machine sourceIndex)
      (outerProofFormulaSeedBits (paddedOuterPCP outer)
        (scheduledRefuterWord source machine sourceIndex) rowBits)
      target pointCode targetBits)

/-- **The Case-1 chain, executed from the numeral bank's frame.**  The two
hypotheses are the ones `CaseOneTargetLanguageClosure` already carries — the
named decision row stage and the published target-bit run — and the scheduled
source length is no longer an immediate of the stream. -/
theorem run_bankCaseOneTargetBitProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (row : NPOracleProgram) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceIndex target width queryCount copies pointCode targetBits targetFuel
      value : ℕ)
    (rowBits rowFuel : ℕ → ℕ)
    (hrow : ∀ code, code < 2 ^ scheduledWidth outer sourceIndex →
      runNPOracleProgram row (rowBits code) (rowFuel code)
          (initialNPOracleState (sourceLength sourceIndex)
            (Nat.pair code
              (Nat.pair (scheduledWidth outer sourceIndex)
                (encodeBitInput
                  (scheduledRefuterWord source machine sourceIndex))))) =
        some
          (encodeTaggedList
            (outerProofRowStream (paddedOuterPCP outer)
              (scheduledRefuterWord source machine sourceIndex) code)))
    (htarget :
      runNPOracleProgram (targetBitProgram algorithm) targetBits targetFuel
          (initialNPOracleState target
            (targetBitCaseOneInput
              (algorithm.outputArity
                (scheduledAmplifierRequest outer sourceIndex
                  (scheduledRefuterWord source machine sourceIndex)))
              (algorithm.descriptor
                (scheduledAmplifierRequest outer sourceIndex
                  (scheduledRefuterWord source machine sourceIndex)))
              pointCode)) =
        some value) :
    runNPOracleProgram
        (bankCaseOneTargetBitProgram algorithm source.refuter.runner.program row
          machine.description (scheduledWidth outer sourceIndex))
        (bankCaseOneTargetBitBits algorithm outer machine sourceIndex target
          width queryCount copies pointCode targetBits rowBits)
        (bankCaseOneTargetBitFuel algorithm row outer machine sourceIndex
          rowFuel targetFuel)
        (initialNPOracleState target
          (scheduleNumeralBankOutput (sourceLength sourceIndex) width queryCount
            copies pointCode)) =
      some value :=
  run_occurrenceStage
    (run_bankRefuterWordFrameProgram source.refuter machine target
      (sourceLength sourceIndex) width queryCount copies pointCode)
    (run_caseOneTargetBitProgram algorithm
      (outerProofFormulaSeedProgram row (scheduledWidth outer sourceIndex))
      outer sourceIndex (scheduledRefuterWord source machine sourceIndex)
      (outerProofFormulaSeedBits (paddedOuterPCP outer)
        (scheduledRefuterWord source machine sourceIndex) rowBits)
      (outerProofFormulaSeedFuel row (paddedOuterPCP outer)
        (scheduledRefuterWord source machine sourceIndex) rowFuel)
      target pointCode targetBits targetFuel value
      (run_outerProofRecoveryFormulaSeedProgram row outer sourceIndex
        (scheduledRefuterWord source machine sourceIndex) rowBits rowFuel hrow)
      htarget)

end NearCubicWires.BankRefuterWordFrameProgram
