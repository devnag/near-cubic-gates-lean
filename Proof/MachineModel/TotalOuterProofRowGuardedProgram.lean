import Proof.MachineModel.OuterProofRowStageProgram
import Proof.Circuits.TotalRowCountGuard

/-!
# The total outer-proof row stream

`rowSeedProgram` emits `pair tableCode (pair queryCount decisionCode)`.  This
module replaces only the following `rowStreamProgram` call by
`TotalRowCountGuard.countGuardProgram rowStreamProgram`.  The zero branch emits
the canonical empty-row code; the nonzero branch reuses the existing stream
execution unchanged.
-/

namespace NearCubicWires.TotalOuterProofRowGuardedProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterProofRowProgram
open NearCubicWires.OuterProofRowStageProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.TotalRowCountGuard
open NearCubicWires.VerifiedLinker

def totalOuterProofRowProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) : NPOracleProgram :=
  linkPrograms
    (rowSeedProgram pcp.query.program pcp.decisionRunner.program
      pcp.shape.program)
    (countGuardProgram rowStreamProgram)

theorem totalOuterProofRowProgram_oracleFree
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) :
    OracleFree (totalOuterProofRowProgram pcp) :=
  oracleFree_linkPrograms
    (rowSeedProgram_oracleFree pcp.queryOracleFree pcp.decisionOracleFree
      pcp.shapeOracleFree)
    (countGuardProgram_oracleFree rowStreamProgram rowStreamProgram_oracleFree)

def totalOuterProofRowOutput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) : ℕ :=
  if pcp.queryCount n = 0 then 0
  else
    encodeTaggedList
      (rowRawStream (pcp.queryCount n) (rowDecisionCode pcp input code)
        (rowAddressOf pcp input code))

def totalOuterProofRowGuardBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (width code : ℕ) : ℕ :=
  max 1 <| max (natBitLength n) <|
    max (rowSeedBits pcp input width code) <|
      max
        (countGuardFrameBits n
          (encodeBalancedList (rowSeedTable pcp input code))
          (pcp.queryCount n) (rowDecisionCode pcp input code)) <|
        max
          (natBitLength
            (Nat.pair n
              (countGuardFrameOutput
                (encodeBalancedList (rowSeedTable pcp input code))
                (pcp.queryCount n) (rowDecisionCode pcp input code)))) <|
          max
            (rowStreamBits n (pcp.queryCount n)
              (rowDecisionCode pcp input code) (rowSeedTable pcp input code)
              (rowAddressOf pcp input code))
            (natBitLength (totalOuterProofRowOutput pcp input code))

def totalOuterProofRowGuardFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) : ℕ :=
  linkFuel (taggedProgramChoice emptyGuardProgram rowStreamProgram) 6
    (taggedProgramChoiceFuel
      (if pcp.queryCount n = 0 then 2
      else
        rowStreamFuel n (pcp.queryCount n) (rowDecisionCode pcp input code)
          (rowSeedTable pcp input code) (rowAddressOf pcp input code)))

def totalOuterProofRowFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) : ℕ :=
  linkFuel (countGuardProgram rowStreamProgram) (rowSeedFuel pcp input code)
    (totalOuterProofRowGuardFuel pcp input code)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
-- Both guard branches retain the seed's dependent table and decision code.
/-- The guarded row emitter is total in the query count. -/
theorem run_totalOuterProofRowProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (width code : ℕ) :
    runNPOracleProgram (totalOuterProofRowProgram pcp)
        (totalOuterProofRowGuardBits pcp input width code)
        (totalOuterProofRowFuel pcp input code)
        (initialNPOracleState n
          (Nat.pair code (Nat.pair width (encodeBitInput input)))) =
      some (totalOuterProofRowOutput pcp input code) := by
  let maximumBits := totalOuterProofRowGuardBits pcp input width code
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlength : natBitLength n ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hseedBits : rowSeedBits pcp input width code ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hframeBits :
      countGuardFrameBits n
          (encodeBalancedList (rowSeedTable pcp input code))
          (pcp.queryCount n) (rowDecisionCode pcp input code) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have htaggedBits :
      natBitLength
          (Nat.pair n
            (countGuardFrameOutput
              (encodeBalancedList (rowSeedTable pcp input code))
              (pcp.queryCount n) (rowDecisionCode pcp input code))) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hstreamBits :
      rowStreamBits n (pcp.queryCount n) (rowDecisionCode pcp input code)
          (rowSeedTable pcp input code) (rowAddressOf pcp input code) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have houtputBits :
      natBitLength (totalOuterProofRowOutput pcp input code) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hseed :
      runNPOracleProgram
          (rowSeedProgram pcp.query.program pcp.decisionRunner.program
            pcp.shape.program)
          maximumBits (rowSeedFuel pcp input code)
          (initialNPOracleState n
            (Nat.pair code (Nat.pair width (encodeBitInput input)))) =
        some
          (Nat.pair (encodeBalancedList (rowSeedTable pcp input code))
            (Nat.pair (pcp.queryCount n) (rowDecisionCode pcp input code))) :=
    run_bits_mono (run_rowSeedProgram pcp input width code) hseedBits
  by_cases hzero : pcp.queryCount n = 0
  · have hframeBits0 :
        countGuardFrameBits n
            (encodeBalancedList (rowSeedTable pcp input code)) 0
            (rowDecisionCode pcp input code) ≤ maximumBits := by
      simpa only [hzero] using hframeBits
    have htaggedBits0 :
        natBitLength
            (Nat.pair n
              (countGuardFrameOutput
                (encodeBalancedList (rowSeedTable pcp input code)) 0
                (rowDecisionCode pcp input code))) ≤ maximumBits := by
      simpa only [hzero] using htaggedBits
    have hseed0 :
        runNPOracleProgram
            (rowSeedProgram pcp.query.program pcp.decisionRunner.program
              pcp.shape.program)
            maximumBits (rowSeedFuel pcp input code)
            (initialNPOracleState n
              (Nat.pair code (Nat.pair width (encodeBitInput input)))) =
          some
            (Nat.pair (encodeBalancedList (rowSeedTable pcp input code))
              (Nat.pair 0 (rowDecisionCode pcp input code))) := by
      simpa only [hzero] using hseed
    have hguard := run_countGuardProgram_zero rowStreamProgram n
      (encodeBalancedList (rowSeedTable pcp input code))
      (rowDecisionCode pcp input code) maximumBits hpositive hlength
      hframeBits0 htaggedBits0
    have hlinked :
        runNPOracleProgram
            (linkPrograms
              (rowSeedProgram pcp.query.program pcp.decisionRunner.program
                pcp.shape.program)
              (countGuardProgram rowStreamProgram))
            maximumBits
            (linkFuel (countGuardProgram rowStreamProgram)
              (rowSeedFuel pcp input code)
              (linkFuel
                (taggedProgramChoice emptyGuardProgram rowStreamProgram) 6
                (taggedProgramChoiceFuel 2)))
            (initialNPOracleState n
              (Nat.pair code (Nat.pair width (encodeBitInput input)))) =
          some 0 :=
      run_linkPrograms hpositive hlength hseed0 hguard
    rw [totalOuterProofRowProgram, totalOuterProofRowFuel,
      totalOuterProofRowGuardFuel, if_pos hzero, totalOuterProofRowOutput,
      if_pos hzero]
    exact hlinked
  · have hsource :
        runNPOracleProgram rowStreamProgram maximumBits
            (rowStreamFuel n (pcp.queryCount n)
              (rowDecisionCode pcp input code) (rowSeedTable pcp input code)
              (rowAddressOf pcp input code))
            (initialNPOracleState n
              (Nat.pair (encodeBalancedList (rowSeedTable pcp input code))
                (Nat.pair (pcp.queryCount n)
                  (rowDecisionCode pcp input code)))) =
          some
            (encodeTaggedList
              (rowRawStream (pcp.queryCount n)
                (rowDecisionCode pcp input code)
                (rowAddressOf pcp input code))) :=
      run_bits_mono
        (run_rowStreamProgram n (pcp.queryCount n)
          (rowDecisionCode pcp input code) (rowSeedTable pcp input code)
          (rowAddressOf pcp input code) (Nat.pos_of_ne_zero hzero)
          (rowSeedTable_length pcp input code)
          (fun index hindex =>
            rowSeedTable_getElem pcp input code index hindex))
        hstreamBits
    have hencodedOutputBits :
        natBitLength
            (encodeTaggedList
              (rowRawStream (pcp.queryCount n)
                (rowDecisionCode pcp input code)
                (rowAddressOf pcp input code))) ≤ maximumBits := by
      simpa only [totalOuterProofRowOutput, if_neg hzero] using houtputBits
    have hguard := run_countGuardProgram_nonzero rowStreamProgram n
      (encodeBalancedList (rowSeedTable pcp input code)) (pcp.queryCount n)
      (rowDecisionCode pcp input code) maximumBits
      (rowStreamFuel n (pcp.queryCount n) (rowDecisionCode pcp input code)
        (rowSeedTable pcp input code) (rowAddressOf pcp input code))
      (encodeTaggedList
        (rowRawStream (pcp.queryCount n) (rowDecisionCode pcp input code)
          (rowAddressOf pcp input code)))
      hzero hpositive hlength hframeBits htaggedBits hsource
      hencodedOutputBits
    have hlinked :
        runNPOracleProgram
            (linkPrograms
              (rowSeedProgram pcp.query.program pcp.decisionRunner.program
                pcp.shape.program)
              (countGuardProgram rowStreamProgram))
            maximumBits
            (linkFuel (countGuardProgram rowStreamProgram)
              (rowSeedFuel pcp input code)
              (linkFuel
                (taggedProgramChoice emptyGuardProgram rowStreamProgram) 6
                (taggedProgramChoiceFuel
                  (rowStreamFuel n (pcp.queryCount n)
                    (rowDecisionCode pcp input code)
                    (rowSeedTable pcp input code)
                    (rowAddressOf pcp input code)))))
            (initialNPOracleState n
              (Nat.pair code (Nat.pair width (encodeBitInput input)))) =
          some
            (encodeTaggedList
              (rowRawStream (pcp.queryCount n)
                (rowDecisionCode pcp input code)
                (rowAddressOf pcp input code))) :=
      run_linkPrograms hpositive hlength hseed hguard
    rw [totalOuterProofRowProgram, totalOuterProofRowFuel,
      totalOuterProofRowGuardFuel, if_neg hzero, totalOuterProofRowOutput,
      if_neg hzero]
    exact hlinked

/-! ## 2. Hostile zero and positive-count compatibility -/

theorem run_totalOuterProofRowProgram_zero
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (width code : ℕ) (hzero : pcp.queryCount n = 0) :
    runNPOracleProgram (totalOuterProofRowProgram pcp)
        (totalOuterProofRowGuardBits pcp input width code)
        (totalOuterProofRowFuel pcp input code)
        (initialNPOracleState n
          (Nat.pair code (Nat.pair width (encodeBitInput input)))) =
      some 0 := by
  have hrun := run_totalOuterProofRowProgram pcp input width code
  simpa only [totalOuterProofRowOutput, if_pos hzero] using hrun

theorem run_totalOuterProofRowProgram_positive_eq_original
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (width code : ℕ)
    (hpositive : 0 < pcp.queryCount n) :
    runNPOracleProgram (totalOuterProofRowProgram pcp)
        (totalOuterProofRowGuardBits pcp input width code)
        (totalOuterProofRowFuel pcp input code)
        (initialNPOracleState n
          (Nat.pair code (Nat.pair width (encodeBitInput input)))) =
      runNPOracleProgram
        (outerProofRowProgram pcp.query.program pcp.decisionRunner.program
          pcp.shape.program)
        (outerProofRowBits pcp input width code)
        (outerProofRowFuel pcp input code)
        (initialNPOracleState n
          (Nat.pair code (Nat.pair width (encodeBitInput input)))) := by
  have htotal := run_totalOuterProofRowProgram pcp input width code
  have horiginal := run_outerProofRowProgram pcp input width code hpositive
  rw [htotal, horiginal]
  simp only [totalOuterProofRowOutput, if_neg (Nat.ne_of_gt hpositive)]

end NearCubicWires.TotalOuterProofRowGuardedProgram
