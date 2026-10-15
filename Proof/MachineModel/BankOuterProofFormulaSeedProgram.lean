import Proof.MachineModel.BankRefuterWordFrameProgram

/-!
# The Case-1 recovery seed, with the scheduled width read rather than baked

`BankRefuterWordFrameProgram.run_bankCaseOneTargetBitProgram` reads the
scheduled *source length* from the numeral bank's registers, but the Case-1
chain still carries one target-derived immediate: the scheduled width, frozen
by the `set` instruction of
`OuterProofRecoveryFormulaSeedProgram.outerProofSeedPreludeProgram`.

That immediate cannot be replaced by a read of the numeral bank's width
register, because the seed runs inside a native context call and sees only the
refuter word.  It does, however, see the *public length* — and on the Case-1
chain that public length is precisely the scheduled source length the bank
itself decodes the width from.  `RuntimeScheduleNumeralBank.widthEnvelopeProgram`
is the bank's width stage as a standalone stream, so the seed can recompute the
width from its own length register.

This module performs that swap.  §1 lifts the public length beside the retained
refuter word, §2 runs the width stage on it and reassembles the exact frame
`outerProofSeedPreludeOutput` produced, and §3 re-derives the composed seed run
with the published tail of `OuterProofRecoveryFormulaSeedProgram` unchanged.
The resulting program's only parameters are the named decision row stage and
the three *frozen* published shape numerals `(clockDepth, coefficient,
exponent)`; no request-derived numeral appears anywhere in the stream.
-/

namespace NearCubicWires.BankOuterProofFormulaSeedProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The public length beside the retained request -/

/-- Copy the public length register in front of the request code. -/
def bankSeedLengthLiftProgram : NPOracleProgram :=
  [ .copy 1 2 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] theorem bankSeedLengthLiftProgram_oracleFree :
    OracleFree bankSeedLengthLiftProgram := by
  rfl

def bankSeedLengthLiftBits (inputLength inputCode : ℕ) : ℕ :=
  natBitLength (Nat.pair inputLength inputCode)

theorem run_bankSeedLengthLiftProgram (inputLength inputCode : ℕ) :
    runNPOracleProgram bankSeedLengthLiftProgram
        (bankSeedLengthLiftBits inputLength inputCode) 3
        (initialNPOracleState inputLength inputCode) =
      some (Nat.pair inputLength inputCode) := by
  have houtput :
      natBitLength (Nat.pair inputLength inputCode) ≤
        bankSeedLengthLiftBits inputLength inputCode :=
    Nat.le_refl _
  have hlength :
      natBitLength inputLength ≤ bankSeedLengthLiftBits inputLength inputCode :=
    natBitLength_mono (Nat.left_le_pair inputLength inputCode)
  rw [show 3 = 2 + 1 by omega]
  rw [run_copy_instruction (value := inputLength) (by rfl) rfl
    (by simp [initialNPOracleState]) hlength]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputLength inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 2. The prelude frame with the computed width -/

/-- Rebuild the seed's prelude frame `pair width (pair width request)` from
`pair width request`. -/
def bankSeedWidthFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] theorem bankSeedWidthFrameProgram_oracleFree :
    OracleFree bankSeedWidthFrameProgram := by
  rfl

def bankSeedWidthFrameBits (width inputCode : ℕ) : ℕ :=
  natBitLength (outerProofSeedPreludeOutput width inputCode)

theorem run_bankSeedWidthFrameProgram
    (inputLength width inputCode : ℕ) :
    runNPOracleProgram bankSeedWidthFrameProgram
        (bankSeedWidthFrameBits width inputCode) 3
        (initialNPOracleState inputLength (Nat.pair width inputCode)) =
      some (outerProofSeedPreludeOutput width inputCode) := by
  have houtput :
      natBitLength (outerProofSeedPreludeOutput width inputCode) ≤
        bankSeedWidthFrameBits width inputCode :=
    Nat.le_refl _
  have hframe :
      natBitLength (Nat.pair width inputCode) ≤
        bankSeedWidthFrameBits width inputCode :=
    natBitLength_mono
      (Nat.right_le_pair width (Nat.pair width inputCode))
  have hwidth :
      natBitLength width ≤ bankSeedWidthFrameBits width inputCode :=
    natBitLength_mono
      (Nat.left_le_pair width (Nat.pair width inputCode))
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [initialNPOracleState]) hwidth]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := outerProofSeedPreludeOutput width inputCode) (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        outerProofSeedPreludeOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- **The register-driven seed prelude.**  The width the seed used to freeze is
recomputed from the public length by the numeral bank's own width stage. -/
def bankOuterProofSeedPreludeProgram
    (clockDepth coefficient exponent : ℕ) : NPOracleProgram :=
  linkPrograms bankSeedLengthLiftProgram
    (linkPrograms
      (preserveRightProgram (widthEnvelopeProgram clockDepth coefficient
        exponent))
      bankSeedWidthFrameProgram)

theorem bankOuterProofSeedPreludeProgram_oracleFree
    (clockDepth coefficient exponent : ℕ) :
    OracleFree (bankOuterProofSeedPreludeProgram clockDepth coefficient
      exponent) :=
  oracleFree_linkPrograms bankSeedLengthLiftProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _
        (widthEnvelopeProgram_oracleFree clockDepth coefficient exponent))
      bankSeedWidthFrameProgram_oracleFree)

def bankOuterProofSeedPreludeFuel
    (clockDepth coefficient exponent inputLength : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram (widthEnvelopeProgram clockDepth coefficient
        exponent))
      bankSeedWidthFrameProgram)
    3
    (linkFuel bankSeedWidthFrameProgram
      (preserveRightFuel
        (widthEnvelopeFuel clockDepth coefficient exponent inputLength))
      3)

def bankOuterProofSeedPreludeBits
    (clockDepth coefficient exponent inputLength inputCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (bankSeedLengthLiftBits inputLength inputCode)
    (occurrenceStageBits inputLength
      (preserveRightBits
        (widthEnvelopeBits inputLength clockDepth coefficient exponent
          inputLength)
        inputLength inputCode
        (widthValue clockDepth coefficient exponent inputLength))
      (bankSeedWidthFrameBits
        (widthValue clockDepth coefficient exponent inputLength) inputCode))

/-- **The register-driven prelude, executed.**  The published width budget's
positivity — `RuntimeScheduleNumeralBank.publishedWidthBudget_positive` at the
scheduled length — is the only side condition. -/
theorem run_bankOuterProofSeedPreludeProgram
    (clockDepth coefficient exponent inputLength inputCode : ℕ)
    (hbudget :
      1 ≤ widthBudgetValue clockDepth coefficient exponent inputLength) :
    runNPOracleProgram
        (bankOuterProofSeedPreludeProgram clockDepth coefficient exponent)
        (bankOuterProofSeedPreludeBits clockDepth coefficient exponent
          inputLength inputCode)
        (bankOuterProofSeedPreludeFuel clockDepth coefficient exponent
          inputLength)
        (initialNPOracleState inputLength inputCode) =
      some
        (outerProofSeedPreludeOutput
          (widthValue clockDepth coefficient exponent inputLength)
          inputCode) :=
  run_occurrenceStage
    (run_bankSeedLengthLiftProgram inputLength inputCode)
    (run_occurrenceStage
      (run_preserveRightProgram
        (widthEnvelopeProgram clockDepth coefficient exponent) inputLength
        (widthEnvelopeBits inputLength clockDepth coefficient exponent
          inputLength)
        (widthEnvelopeFuel clockDepth coefficient exponent inputLength)
        inputLength inputCode
        (widthValue clockDepth coefficient exponent inputLength)
        (run_widthEnvelopeProgram inputLength clockDepth coefficient exponent
          inputLength hbudget))
      (run_bankSeedWidthFrameProgram inputLength
        (widthValue clockDepth coefficient exponent inputLength) inputCode))

/-! ## 3. The composed seed, with no width immediate -/

/-- **The register-driven Case-1 recovery seed.**  Its parameters are the named
decision row stage and the three frozen published shape numerals. -/
def bankOuterProofFormulaSeedProgram
    (row : NPOracleProgram) (clockDepth coefficient exponent : ℕ) :
    NPOracleProgram :=
  linkPrograms (bankOuterProofSeedPreludeProgram clockDepth coefficient
      exponent)
    (linkPrograms (preserveRightProgram binaryTwoPowProgram)
      (linkPrograms outerProofSeedRangeFrameProgram
        (linkPrograms
          (preserveRightProgram (outerProofFormulaStreamProgram row))
          outerProofSeedResultFrameProgram)))

theorem bankOuterProofFormulaSeedProgram_oracleFree
    {row : NPOracleProgram} (hrow : OracleFree row)
    (clockDepth coefficient exponent : ℕ) :
    OracleFree
      (bankOuterProofFormulaSeedProgram row clockDepth coefficient exponent) := by
  apply oracleFree_linkPrograms
  · exact bankOuterProofSeedPreludeProgram_oracleFree clockDepth coefficient
      exponent
  · apply oracleFree_linkPrograms
    · exact preserveRightProgram_oracleFree binaryTwoPowProgram
        binaryTwoPowProgram_oracleFree
    · apply oracleFree_linkPrograms
      · exact outerProofSeedRangeFrameProgram_oracleFree
      · apply oracleFree_linkPrograms
        · exact preserveRightProgram_oracleFree _
            (outerProofFormulaStreamProgram_oracleFree hrow)
        · exact outerProofSeedResultFrameProgram_oracleFree

def bankOuterProofFormulaSeedFuel
    (row : NPOracleProgram) (clockDepth coefficient exponent : ℕ)
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (rowFuel : ℕ → ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram binaryTwoPowProgram)
      (linkPrograms outerProofSeedRangeFrameProgram
        (linkPrograms
          (preserveRightProgram (outerProofFormulaStreamProgram row))
          outerProofSeedResultFrameProgram)))
    (bankOuterProofSeedPreludeFuel clockDepth coefficient exponent n)
    (linkFuel
      (linkPrograms outerProofSeedRangeFrameProgram
        (linkPrograms
          (preserveRightProgram (outerProofFormulaStreamProgram row))
          outerProofSeedResultFrameProgram))
      (preserveRightFuel (binaryTwoPowFuel (pcp.nativeWidth n)))
      (linkFuel
        (linkPrograms
          (preserveRightProgram (outerProofFormulaStreamProgram row))
          outerProofSeedResultFrameProgram)
        9
        (linkFuel outerProofSeedResultFrameProgram
          (preserveRightFuel
            (outerProofFormulaStreamFuel row pcp input rowFuel))
          7)))

def bankOuterProofFormulaSeedBits
    (clockDepth coefficient exponent : ℕ)
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (rowBits : ℕ → ℕ) : ℕ :=
  max
    (bankOuterProofSeedPreludeBits clockDepth coefficient exponent n
      (encodeBitInput input))
    (outerProofFormulaSeedBits pcp input rowBits)

set_option maxHeartbeats 2000000 in
-- Five nested link terms; the seed's resource envelope is elaborated in full.
/-- **The register-driven seed, executed.**  Given the schedule identification
`widthValue … n = pcp.nativeWidth n` — which
`RuntimeScheduleNumeralBank.bankWidth_at_sourceLength` supplies at every
scheduled source length — the composed stream produces exactly the frame
`OuterProofRecoveryFormulaSeedProgram.run_outerProofFormulaSeedProgram`
produces, with the width immediate removed. -/
theorem run_bankOuterProofFormulaSeedProgram
    (row : NPOracleProgram) (clockDepth coefficient exponent : ℕ)
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (rowBits rowFuel : ℕ → ℕ)
    (hbudget : 1 ≤ widthBudgetValue clockDepth coefficient exponent n)
    (hwidth : widthValue clockDepth coefficient exponent n = pcp.nativeWidth n)
    (hrow : ∀ code, code < 2 ^ pcp.nativeWidth n →
      runNPOracleProgram row (rowBits code) (rowFuel code)
          (initialNPOracleState n
            (Nat.pair code
              (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))) =
        some (encodeTaggedList (outerProofRowStream pcp input code))) :
    runNPOracleProgram
        (bankOuterProofFormulaSeedProgram row clockDepth coefficient exponent)
        (bankOuterProofFormulaSeedBits clockDepth coefficient exponent pcp input
          rowBits)
        (bankOuterProofFormulaSeedFuel row clockDepth coefficient exponent pcp
          input rowFuel)
        (initialNPOracleState n (encodeBitInput input)) =
      some
        (Nat.pair
          (Nat.pair (2 ^ pcp.nativeWidth n)
            (rawClauseStream (outerProofRecoveryFormula pcp input)))
          (Nat.pair n
            (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))) := by
  set maximumBits :=
    bankOuterProofFormulaSeedBits clockDepth coefficient exponent pcp input
      rowBits with hmaximumBits
  have htail : outerProofFormulaSeedBits pcp input rowBits ≤ maximumBits :=
    Nat.le_max_right _ _
  have hpositive : 1 ≤ maximumBits :=
    (Nat.le_max_left _ _ : (1 : ℕ) ≤ _).trans htail
  have hlengthBits : natBitLength n ≤ maximumBits :=
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans htail
  have hpreludeBits :
      bankOuterProofSeedPreludeBits clockDepth coefficient exponent n
          (encodeBitInput input) ≤
        maximumBits :=
    Nat.le_max_left _ _
  have htwoPowBits :
      preserveRightBits (binaryTwoPowBits (pcp.nativeWidth n))
          (pcp.nativeWidth n)
          (Nat.pair (pcp.nativeWidth n) (encodeBitInput input))
          (2 ^ pcp.nativeWidth n) ≤
        maximumBits :=
    ((Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans htail
  have hrangeFrameBits :
      outerProofSeedRangeFrameBits n (pcp.nativeWidth n)
          (encodeBitInput input) ≤
        maximumBits :=
    ((Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans htail
  have hstreamBits :
      preserveRightBits (outerProofFormulaStreamBits pcp input rowBits)
          (generatedBalancedRangeInput (2 ^ (pcp.nativeWidth n + 1))
            (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))
          (outerProofSeedRetainedFrame n (pcp.nativeWidth n)
            (encodeBitInput input))
          (rawClauseStream (outerProofRecoveryFormula pcp input)) ≤
        maximumBits :=
    ((Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans htail
  have hresultBits :
      outerProofSeedResultFrameBits n (pcp.nativeWidth n)
          (encodeBitInput input)
          (rawClauseStream (outerProofRecoveryFormula pcp input)) ≤
        maximumBits :=
    ((Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans htail
  have hprelude :
      runNPOracleProgram
          (bankOuterProofSeedPreludeProgram clockDepth coefficient exponent)
          maximumBits
          (bankOuterProofSeedPreludeFuel clockDepth coefficient exponent n)
          (initialNPOracleState n (encodeBitInput input)) =
        some
          (outerProofSeedPreludeOutput (pcp.nativeWidth n)
            (encodeBitInput input)) := by
    have hrun :=
      run_bits_mono
        (run_bankOuterProofSeedPreludeProgram clockDepth coefficient exponent n
          (encodeBitInput input) hbudget)
        hpreludeBits
    rwa [hwidth] at hrun
  have htwoPow :=
    run_bits_mono
      (run_preserveRightProgram binaryTwoPowProgram n
        (binaryTwoPowBits (pcp.nativeWidth n))
        (binaryTwoPowFuel (pcp.nativeWidth n)) (pcp.nativeWidth n)
        (Nat.pair (pcp.nativeWidth n) (encodeBitInput input))
        (2 ^ pcp.nativeWidth n)
        (run_binaryTwoPowProgram n (pcp.nativeWidth n)
          (binaryTwoPowBits (pcp.nativeWidth n)) (Nat.le_refl _)))
      htwoPowBits
  have hrangeFrame :=
    run_bits_mono
      (run_outerProofSeedRangeFrameProgram n (pcp.nativeWidth n)
        (encodeBitInput input))
      hrangeFrameBits
  have hstream :=
    run_bits_mono
      (run_preserveRightProgram (outerProofFormulaStreamProgram row) n
        (outerProofFormulaStreamBits pcp input rowBits)
        (outerProofFormulaStreamFuel row pcp input rowFuel)
        (generatedBalancedRangeInput (2 ^ (pcp.nativeWidth n + 1))
          (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))
        (outerProofSeedRetainedFrame n (pcp.nativeWidth n)
          (encodeBitInput input))
        (rawClauseStream (outerProofRecoveryFormula pcp input))
        (run_outerProofFormulaStreamProgram row pcp input rowBits rowFuel hrow))
      hstreamBits
  have hresult :=
    run_bits_mono
      (run_outerProofSeedResultFrameProgram n (pcp.nativeWidth n)
        (encodeBitInput input)
        (rawClauseStream (outerProofRecoveryFormula pcp input)))
      hresultBits
  have hfourth := run_linkPrograms hpositive hlengthBits hstream hresult
  have hthird := run_linkPrograms hpositive hlengthBits hrangeFrame hfourth
  have hsecond := run_linkPrograms hpositive hlengthBits htwoPow hthird
  exact run_linkPrograms hpositive hlengthBits hprelude hsecond

/-! ## 4. The scheduled instance

At a request whose public length is the scheduled source length, the recomputed
width is the chain's own scheduled width: this is
`RuntimeScheduleNumeralBank.bankWidth_at_sourceLength`, and the budget's
positivity is `publishedWidthBudget_positive`.
-/

/-- **The scheduled Case-1 seed with no numeral immediate.**  Both side
conditions of §3 are discharged by the published schedule, so the seed of the
Case-1 chain is register-driven outright. -/
theorem run_bankOuterProofRecoveryFormulaSeedProgram
    (row : NPOracleProgram) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex))
    (rowBits rowFuel : ℕ → ℕ)
    (hrow : ∀ code, code < 2 ^ scheduledWidth outer sourceIndex →
      runNPOracleProgram row (rowBits code) (rowFuel code)
          (initialNPOracleState (sourceLength sourceIndex)
            (Nat.pair code
              (Nat.pair (scheduledWidth outer sourceIndex)
                (encodeBitInput input)))) =
        some
          (encodeTaggedList
            (outerProofRowStream (paddedOuterPCP outer) input code))) :
    runNPOracleProgram
        (bankOuterProofFormulaSeedProgram row clockDepth
          outer.pcp.shape.coefficient outer.proofExponent)
        (bankOuterProofFormulaSeedBits clockDepth outer.pcp.shape.coefficient
          outer.proofExponent (paddedOuterPCP outer) input rowBits)
        (bankOuterProofFormulaSeedFuel row clockDepth
          outer.pcp.shape.coefficient outer.proofExponent
          (paddedOuterPCP outer) input rowFuel)
        (initialNPOracleState (sourceLength sourceIndex)
          (encodeBitInput input)) =
      some
        (Nat.pair
          (Nat.pair (2 ^ scheduledWidth outer sourceIndex)
            (rawClauseStream
              (outerProofRecoveryFormula (paddedOuterPCP outer) input)))
          (Nat.pair (sourceLength sourceIndex)
            (Nat.pair (scheduledWidth outer sourceIndex)
              (encodeBitInput input)))) := by
  have hwidth :
      widthValue clockDepth outer.pcp.shape.coefficient outer.proofExponent
          (sourceLength sourceIndex) =
        (paddedOuterPCP outer).nativeWidth (sourceLength sourceIndex) := by
    have hbank := bankWidth_at_sourceLength outer sourceIndex
    rw [bankWidth, bankSourceLength_sourceLength] at hbank
    exact hbank
  have hpadded :
      (paddedOuterPCP outer).nativeWidth (sourceLength sourceIndex) =
        scheduledWidth outer sourceIndex := rfl
  have hrun :=
    run_bankOuterProofFormulaSeedProgram row clockDepth
      outer.pcp.shape.coefficient outer.proofExponent (paddedOuterPCP outer)
      input rowBits rowFuel
      (publishedWidthBudget_positive outer (sourceLength sourceIndex)) hwidth
      (by simpa only [hpadded] using hrow)
  simpa only [hpadded] using hrun

end NearCubicWires.BankOuterProofFormulaSeedProgram
