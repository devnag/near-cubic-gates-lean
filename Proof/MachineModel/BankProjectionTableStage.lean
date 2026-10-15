import Proof.MachineModel.BankAtomContextRegisters
import Proof.MachineModel.BankRefuterWordFrameProgram
import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalTwoPowProgram

/-!
# The projection-runner table, executed from the numeral bank's frame

`BankAtomContextRegisters.inverseAtomContextRuns_ofTable` leaves one residual,
`InverseAtomTableRuns`: from the numeral bank's frame produce

`encodeBalancedList (projectionRunnerCallOutputs pcp scheduledInput)`.

`ProjectionRunnerBalancedProgram.run_projectionRunnerBalancedProgram` already
executes that list — but from the runner's *own* request frame

`pair (queryCount * width + 2 ^ width) (pair (encodeBitInput input) (pair width
queryCount))`,

which mentions the scheduled refuter word, the scheduled width and the
scheduled query count.  Every one of those three is available from the bank
with no schedule immediate:

* the refuter word is `BankRefuterWordFrameProgram.run_bankRefuterWordFrameProgram`,
  whose only immediate is the machine description;
* `2 ^ width` is `CanonicalTwoPowProgram.run_binaryTwoPowProgram` on the width
  register;
* `queryCount * width` is `CanonicalBitSerialMulProgram.run_bitSerialMulProgram`
  on the two registers.

§2–§5 are the three straight-line frames that thread those four values into the
runner's request, §6 links the whole stage, and §7 discharges
`InverseAtomTableRuns` on the schedule's diagonal.

## The diagonal, again

The runner's run is stated at the *PCP input's* public length while the stage
runs at the request's public length, exactly as `BankFrameLoweringAdapter` §4
records.  §6 takes the identification as an equation between the two lengths
and §7 supplies it from the onset-restricted diagonal hypothesis the consumer
already threads.  Nothing is asserted.
-/

namespace NearCubicWires.BankProjectionTableStage

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BankRefuterWordFrameProgram
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerAtomProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping -/

private theorem natBitLength_mono' {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right :=
  Nat.add_le_add_right (Nat.log_mono_right hle) 1

private theorem le_pair_left {value left right : ℕ} (hvalue : value ≤ left) :
    value ≤ Nat.pair left right :=
  hvalue.trans (Nat.left_le_pair left right)

private theorem le_pair_right {value left right : ℕ} (hvalue : value ≤ right) :
    value ≤ Nat.pair left right :=
  hvalue.trans (Nat.right_le_pair left right)

/-! ## 2. Frame duplication -/

private def tableFrameDuplicateProgram : NPOracleProgram :=
  [ .pair 0 0 0 1
  , .halt 0
  ]

@[simp] private theorem tableFrameDuplicateProgram_oracleFree :
    OracleFree tableFrameDuplicateProgram := by
  rfl

private def tableFrameDuplicateBits (frame : ℕ) : ℕ :=
  natBitLength (Nat.pair frame frame)

private theorem run_tableFrameDuplicateProgram (inputLength frame : ℕ) :
    runNPOracleProgram tableFrameDuplicateProgram
        (tableFrameDuplicateBits frame) 2
        (initialNPOracleState inputLength frame) =
      some (Nat.pair frame frame) := by
  have hbits : natBitLength (Nat.pair frame frame) ≤
      tableFrameDuplicateBits frame := le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair frame frame) (by rfl) rfl
    (by simp [initialNPOracleState]) hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

/-! ## 3. The multiplier's request, read off the bank -/

/-- The word stage's output: the refuter-word frame beside the retained bank
frame. -/
private def tableShapeInput
    (sourceLen width queryCount copies code wordCode : ℕ) : ℕ :=
  Nat.pair (Nat.pair wordCode (Nat.pair sourceLen code))
    (scheduleNumeralBankOutput sourceLen width queryCount copies code)

/-- The bit-serial multiplier's request beside the three numerals still
needed. -/
private def tableShapeOutput (width queryCount wordCode : ℕ) : ℕ :=
  Nat.pair (Nat.pair queryCount width)
    (Nat.pair width (Nat.pair queryCount wordCode))

private def tableShapeProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairLeft 2 2 2
  , .unpairRight 0 3 3
  , .unpairRight 3 3 4
  , .unpairLeft 3 4 5
  , .unpairRight 3 3 6
  , .unpairLeft 3 5 7
  , .pair 5 2 6 8
  , .pair 4 6 6 9
  , .pair 5 4 7 10
  , .pair 7 6 0 11
  , .halt 0
  ]

@[simp] private theorem tableShapeProgram_oracleFree :
    OracleFree tableShapeProgram := by
  rfl

private def tableShapeBits
    (sourceLen width queryCount copies code wordCode : ℕ) : ℕ :=
  natBitLength
    (max (tableShapeInput sourceLen width queryCount copies code wordCode)
      (tableShapeOutput width queryCount wordCode))

private theorem run_tableShapeProgram
    (inputLength sourceLen width queryCount copies code wordCode : ℕ) :
    runNPOracleProgram tableShapeProgram
        (tableShapeBits sourceLen width queryCount copies code wordCode) 12
        (initialNPOracleState inputLength
          (tableShapeInput sourceLen width queryCount copies code wordCode)) =
      some (tableShapeOutput width queryCount wordCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤ tableShapeInput sourceLen width queryCount copies code wordCode →
      natBitLength value ≤
        tableShapeBits sourceLen width queryCount copies code wordCode :=
    fun _ hvalue => natBitLength_mono' (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ tableShapeOutput width queryCount wordCode →
      natBitLength value ≤
        tableShapeBits sourceLen width queryCount copies code wordCode :=
    fun _ hvalue => natBitLength_mono' (hvalue.trans (Nat.le_max_right _ _))
  have hword := hrequest (Nat.pair wordCode (Nat.pair sourceLen code))
    (le_pair_left (le_refl _))
  have hcode := hrequest wordCode (le_pair_left (le_pair_left (le_refl _)))
  have hframe :=
    hrequest (scheduleNumeralBankOutput sourceLen width queryCount copies code)
      (le_pair_right (le_refl _))
  have htail :=
    hrequest (Nat.pair width (Nat.pair queryCount (Nat.pair copies code)))
      (le_pair_right (le_pair_right (le_refl _)))
  have hwidth :=
    hrequest width
      (le_pair_right (le_pair_right (le_pair_left (le_refl _))))
  have hqueryTail :=
    hrequest (Nat.pair queryCount (Nat.pair copies code))
      (le_pair_right (le_pair_right (le_pair_right (le_refl _))))
  have hquery :=
    hrequest queryCount
      (le_pair_right
        (le_pair_right (le_pair_right (le_pair_left (le_refl _)))))
  have hinner :=
    hresult (Nat.pair queryCount wordCode)
      (le_pair_right (le_pair_right (le_refl _)))
  have hcontext :=
    hresult (Nat.pair width (Nat.pair queryCount wordCode))
      (le_pair_right (le_refl _))
  have hmul :=
    hresult (Nat.pair queryCount width) (le_pair_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := Nat.pair wordCode (Nat.pair sourceLen code)) (by rfl) rfl
    (by simp [initialNPOracleState, tableShapeInput]) hword]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := wordCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcode]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := scheduleNumeralBankOutput sourceLen width queryCount copies code)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, tableShapeInput, NPOracleState.write,
        NPOracleState.jump])
    hframe]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair queryCount (Nat.pair copies code)))
    (by
      rfl)
    rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        scheduleNumeralBankOutput])
    htail]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair queryCount (Nat.pair copies code)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hqueryTail]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := queryCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hquery]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair queryCount wordCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hinner]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair width (Nat.pair queryCount wordCode)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcontext]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair queryCount width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmul]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := tableShapeOutput width queryCount wordCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tableShapeOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 4. The exponent's request, re-read off the frame -/

/-- The multiplier's result beside the three numerals. -/
private def tableProductFrame (width queryCount wordCode : ℕ) : ℕ :=
  Nat.pair (queryCount * width)
    (Nat.pair width (Nat.pair queryCount wordCode))

private def tableExponentProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 3 2
  , .pair 3 0 0 3
  , .halt 0
  ]

@[simp] private theorem tableExponentProgram_oracleFree :
    OracleFree tableExponentProgram := by
  rfl

private def tableExponentBits (width queryCount wordCode : ℕ) : ℕ :=
  natBitLength
    (Nat.pair width (tableProductFrame width queryCount wordCode))

private theorem run_tableExponentProgram
    (inputLength width queryCount wordCode : ℕ) :
    runNPOracleProgram tableExponentProgram
        (tableExponentBits width queryCount wordCode) 4
        (initialNPOracleState inputLength
          (tableProductFrame width queryCount wordCode)) =
      some
        (Nat.pair width (tableProductFrame width queryCount wordCode)) := by
  have houtput :
      natBitLength (Nat.pair width (tableProductFrame width queryCount wordCode))
        ≤ tableExponentBits width queryCount wordCode := le_refl _
  have hframe :
      natBitLength (tableProductFrame width queryCount wordCode) ≤
        tableExponentBits width queryCount wordCode :=
    natBitLength_mono' (le_pair_right (le_refl _))
  have hcontext :
      natBitLength (Nat.pair width (Nat.pair queryCount wordCode)) ≤
        tableExponentBits width queryCount wordCode :=
    natBitLength_mono' (le_pair_right (le_pair_right (le_refl _)))
  have hwidth :
      natBitLength width ≤ tableExponentBits width queryCount wordCode :=
    natBitLength_mono' (le_pair_left (le_refl _))
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair queryCount wordCode)) (by rfl) rfl
    (by simp [initialNPOracleState, tableProductFrame]) hcontext]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair width (tableProductFrame width queryCount wordCode))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 5. The runner's own request -/

/-- The exponent's result beside the three numerals. -/
private def tablePowerFrame (width queryCount wordCode : ℕ) : ℕ :=
  Nat.pair (2 ^ width) (tableProductFrame width queryCount wordCode)

/-- The balanced projection runner's request frame. -/
private def tableRunnerRequest (width queryCount wordCode : ℕ) : ℕ :=
  Nat.pair (queryCount * width + 2 ^ width)
    (Nat.pair wordCode (Nat.pair width queryCount))

private def tableRunnerProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 3 4
  , .unpairLeft 3 5 5
  , .unpairRight 3 3 6
  , .unpairLeft 3 6 7
  , .unpairRight 3 7 8
  , .add 4 2 8 9
  , .pair 5 6 9 10
  , .pair 7 9 9 11
  , .pair 8 9 0 12
  , .halt 0
  ]

@[simp] private theorem tableRunnerProgram_oracleFree :
    OracleFree tableRunnerProgram := by
  rfl

private def tableRunnerBits (width queryCount wordCode : ℕ) : ℕ :=
  natBitLength
    (max (tablePowerFrame width queryCount wordCode)
      (tableRunnerRequest width queryCount wordCode))

private theorem run_tableRunnerProgram
    (inputLength width queryCount wordCode : ℕ) :
    runNPOracleProgram tableRunnerProgram
        (tableRunnerBits width queryCount wordCode) 13
        (initialNPOracleState inputLength
          (tablePowerFrame width queryCount wordCode)) =
      some (tableRunnerRequest width queryCount wordCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤ tablePowerFrame width queryCount wordCode →
      natBitLength value ≤ tableRunnerBits width queryCount wordCode :=
    fun _ hvalue => natBitLength_mono' (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ tableRunnerRequest width queryCount wordCode →
      natBitLength value ≤ tableRunnerBits width queryCount wordCode :=
    fun _ hvalue => natBitLength_mono' (hvalue.trans (Nat.le_max_right _ _))
  have hpower := hrequest (2 ^ width) (le_pair_left (le_refl _))
  have hproduct :=
    hrequest (tableProductFrame width queryCount wordCode)
      (le_pair_right (le_refl _))
  have hmul :=
    hrequest (queryCount * width)
      (le_pair_right (le_pair_left (le_refl _)))
  have hcontext :=
    hrequest (Nat.pair width (Nat.pair queryCount wordCode))
      (le_pair_right (le_pair_right (le_refl _)))
  have hwidth :=
    hrequest width
      (le_pair_right (le_pair_right (le_pair_left (le_refl _))))
  have hinner :=
    hrequest (Nat.pair queryCount wordCode)
      (le_pair_right (le_pair_right (le_pair_right (le_refl _))))
  have hquery :=
    hrequest queryCount
      (le_pair_right
        (le_pair_right (le_pair_right (le_pair_left (le_refl _)))))
  have hword :=
    hrequest wordCode
      (le_pair_right
        (le_pair_right (le_pair_right (le_pair_right (le_refl _)))))
  have hcount :=
    hresult (queryCount * width + 2 ^ width) (le_pair_left (le_refl _))
  have hshape :=
    hresult (Nat.pair width queryCount)
      (le_pair_right (le_pair_right (le_refl _)))
  have hatom :=
    hresult (Nat.pair wordCode (Nat.pair width queryCount))
      (le_pair_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := 2 ^ width) (by rfl) rfl
    (by simp [initialNPOracleState, tablePowerFrame]) hpower]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := tableProductFrame width queryCount wordCode) (by rfl) rfl
    (by
      simp [initialNPOracleState, tablePowerFrame, NPOracleState.write,
        NPOracleState.jump])
    hproduct]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := queryCount * width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tableProductFrame])
    hmul]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair queryCount wordCode)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tableProductFrame])
    hcontext]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair queryCount wordCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hinner]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := queryCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hquery]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := wordCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hword]
  rw [show 5 = 4 + 1 by omega]
  rw [run_add_instruction (value := queryCount * width + 2 ^ width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcount]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair width queryCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hshape]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair wordCode (Nat.pair width queryCount)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hatom]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := tableRunnerRequest width queryCount wordCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tableRunnerRequest])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 6. The stage, linked -/

private def tableTakeStageProgram
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) : NPOracleProgram :=
  linkPrograms (projectionRunnerBalancedProgram pcp)
    structuralAtomTakeLeftProgram

private def tableRunnerStageProgram
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) : NPOracleProgram :=
  linkPrograms tableRunnerProgram (tableTakeStageProgram pcp)

private def tablePowerStageProgram
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) : NPOracleProgram :=
  linkPrograms (preserveRightProgram binaryTwoPowProgram)
    (tableRunnerStageProgram pcp)

private def tableExponentStageProgram
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) : NPOracleProgram :=
  linkPrograms tableExponentProgram (tablePowerStageProgram pcp)

private def tableProductStageProgram
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSerialMulProgram)
    (tableExponentStageProgram pcp)

private def tableShapeStageProgram
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) : NPOracleProgram :=
  linkPrograms tableShapeProgram (tableProductStageProgram pcp)

private def tableWordStageProgram
    (refuterProgram : NPOracleProgram) (description : ℕ) : NPOracleProgram :=
  linkPrograms tableFrameDuplicateProgram
    (preserveRightProgram (bankRefuterWordFrameProgram refuterProgram
      description))

/-- **The projection-runner table stage.**  One fixed instruction stream from
the numeral bank's frame to the balanced runner table.  Its only immediates are
the machine description and the executable PCP itself; no schedule numeral and
no target-derived constant appears. -/
def bankProjectionTableProgram
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound)
    (refuterProgram : NPOracleProgram) (description : ℕ) : NPOracleProgram :=
  linkPrograms (tableWordStageProgram refuterProgram description)
    (tableShapeStageProgram pcp)

theorem bankProjectionTableProgram_oracleFree
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound)
    {refuterProgram : NPOracleProgram} (hrefuter : OracleFree refuterProgram)
    (description : ℕ) :
    OracleFree (bankProjectionTableProgram pcp refuterProgram description) :=
  oracleFree_linkPrograms
    (oracleFree_linkPrograms tableFrameDuplicateProgram_oracleFree
      (preserveRightProgram_oracleFree _
        (bankRefuterWordFrameProgram_oracleFree hrefuter description)))
    (oracleFree_linkPrograms tableShapeProgram_oracleFree
      (oracleFree_linkPrograms
        (preserveRightProgram_oracleFree bitSerialMulProgram
          bitSerialMulProgram_oracleFree)
        (oracleFree_linkPrograms tableExponentProgram_oracleFree
          (oracleFree_linkPrograms
            (preserveRightProgram_oracleFree binaryTwoPowProgram
              binaryTwoPowProgram_oracleFree)
            (oracleFree_linkPrograms tableRunnerProgram_oracleFree
              (oracleFree_linkPrograms
                (projectionRunnerBalancedProgram_oracleFree pcp)
                structuralAtomTakeLeftProgram_oracleFree))))))

/-! ### Resource envelopes, one named function per stage -/

private def tableTakeStageBits
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength : ℕ) : ℕ :=
  occurrenceStageBits inputLength (projectionRunnerBalancedBits pcp input)
    (natBitLength (projectionRunnerBalancedOutput pcp input))

private def tableRunnerStageBits
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength width queryCount wordCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength (tableRunnerBits width queryCount wordCode)
    (tableTakeStageBits pcp input inputLength)

private def tablePowerStageBits
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength width queryCount wordCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (preserveRightBits (binaryTwoPowBits width) width
      (tableProductFrame width queryCount wordCode) (2 ^ width))
    (tableRunnerStageBits pcp input inputLength width queryCount wordCode)

private def tableExponentStageBits
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength width queryCount wordCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength (tableExponentBits width queryCount wordCode)
    (tablePowerStageBits pcp input inputLength width queryCount wordCode)

private def tableProductStageBits
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength width queryCount wordCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (preserveRightBits (bitSerialMulBits inputLength queryCount width)
      (Nat.pair queryCount width)
      (Nat.pair width (Nat.pair queryCount wordCode)) (queryCount * width))
    (tableExponentStageBits pcp input inputLength width queryCount wordCode)

private def tableShapeStageBits
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n)
    (inputLength sourceLen width queryCount copies code wordCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (tableShapeBits sourceLen width queryCount copies code wordCode)
    (tableProductStageBits pcp input inputLength width queryCount wordCode)

private def tableWordStageBits
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (inputLength sourceLen width queryCount copies code wordCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (tableFrameDuplicateBits
      (scheduleNumeralBankOutput sourceLen width queryCount copies code))
    (preserveRightBits
      (bankRefuterWordFrameBits refuter machine inputLength sourceLen width
        queryCount copies code)
      (scheduleNumeralBankOutput sourceLen width queryCount copies code)
      (scheduleNumeralBankOutput sourceLen width queryCount copies code)
      (Nat.pair wordCode (Nat.pair sourceLen code)))

/-- The stage's width envelope at one request. -/
def bankProjectionTableBits
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound)
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (inputLength sourceLen copies code : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (tableWordStageBits refuter machine inputLength sourceLen
      (pcp.nativeWidth sourceLen) (pcp.queryCount sourceLen) copies code
      (encodeBitInput (refuter.output machine sourceLen)))
    (tableShapeStageBits pcp (refuter.output machine sourceLen) inputLength
      sourceLen (pcp.nativeWidth sourceLen) (pcp.queryCount sourceLen) copies
      code (encodeBitInput (refuter.output machine sourceLen)))

private def tableTakeStageFuel
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  linkFuel structuralAtomTakeLeftProgram
    (projectionRunnerBalancedFuel pcp input) 2

private def tableRunnerStageFuel
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  linkFuel (tableTakeStageProgram pcp) 13 (tableTakeStageFuel pcp input)

private def tablePowerStageFuel
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) (width : ℕ) : ℕ :=
  linkFuel (tableRunnerStageProgram pcp)
    (preserveRightFuel (binaryTwoPowFuel width))
    (tableRunnerStageFuel pcp input)

private def tableExponentStageFuel
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) (width : ℕ) : ℕ :=
  linkFuel (tablePowerStageProgram pcp) 4 (tablePowerStageFuel pcp input width)

private def tableProductStageFuel
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) (width : ℕ) : ℕ :=
  linkFuel (tableExponentStageProgram pcp)
    (preserveRightFuel (bitSerialMulFuel width))
    (tableExponentStageFuel pcp input width)

private def tableShapeStageFuel
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) (width : ℕ) : ℕ :=
  linkFuel (tableProductStageProgram pcp) 12
    (tableProductStageFuel pcp input width)

private def tableWordStageFuel
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (refuterProgram : NPOracleProgram) (description sourceLen : ℕ) : ℕ :=
  linkFuel
    (preserveRightProgram (bankRefuterWordFrameProgram refuterProgram
      description)) 2
    (preserveRightFuel (bankRefuterWordFrameFuel refuter machine sourceLen))

/-- The stage's fuel envelope at one request. -/
def bankProjectionTableFuel
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound)
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (sourceLen : ℕ) : ℕ :=
  linkFuel (tableShapeStageProgram pcp)
    (tableWordStageFuel refuter machine refuter.runner.program
      machine.description sourceLen)
    (tableShapeStageFuel pcp (refuter.output machine sourceLen)
      (pcp.nativeWidth sourceLen))

/-- The runner's request frame is exactly what the three straight-line frames
assemble. -/
private theorem tableRunnerRequest_eq
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound) {n : ℕ}
    (input : BitInput n) :
    tableRunnerRequest (pcp.nativeWidth n) (pcp.queryCount n)
        (encodeBitInput input) =
      projectionRunnerBalancedInput pcp input := by
  simp only [tableRunnerRequest, projectionRunnerBalancedInput,
    generatedBalancedRangeInput, projectionRunnerRangeCount,
    projectionRunnerRangeContext, projectionRunnerAtomContext]

/-- **The projection-runner table, executed from the numeral bank's frame.**
The four values the runner's request needs — the refuter word, the width, the
query count and their two arithmetic combinations — are all read or computed
from the bank's registers, so the only hypothesis is the identification of the
request's public length with the scheduled source length. -/
theorem run_bankProjectionTableProgram
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound)
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (inputLength sourceLen copies code : ℕ)
    (hlength : inputLength = sourceLen) :
    runNPOracleProgram
        (bankProjectionTableProgram pcp refuter.runner.program
          machine.description)
        (bankProjectionTableBits pcp refuter machine inputLength sourceLen
          copies code)
        (bankProjectionTableFuel pcp refuter machine sourceLen)
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
            (pcp.queryCount sourceLen) copies code)) =
      some
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (refuter.output machine sourceLen))) := by
  subst hlength
  set width := pcp.nativeWidth inputLength with hwidth
  set queryCount := pcp.queryCount inputLength with hqueryCount
  set input := refuter.output machine inputLength with hinput
  set wordCode := encodeBitInput input with hwordCode
  have htake :
      runNPOracleProgram (tableTakeStageProgram pcp)
          (tableTakeStageBits pcp input inputLength)
          (tableTakeStageFuel pcp input)
          (initialNPOracleState inputLength
            (projectionRunnerBalancedInput pcp input)) =
        some
          (encodeBalancedList (projectionRunnerCallOutputs pcp input)) := by
    refine run_occurrenceStage (run_projectionRunnerBalancedProgram pcp input)
      ?_
    exact run_structuralAtomTakeLeftProgram inputLength
      (encodeBalancedList (projectionRunnerCallOutputs pcp input))
      (projectionRunnerRangeContext pcp input)
      (natBitLength_mono' (Nat.left_le_pair _ _))
  have hrunner :
      runNPOracleProgram (tableRunnerStageProgram pcp)
          (tableRunnerStageBits pcp input inputLength width queryCount wordCode)
          (tableRunnerStageFuel pcp input)
          (initialNPOracleState inputLength
            (tablePowerFrame width queryCount wordCode)) =
        some
          (encodeBalancedList (projectionRunnerCallOutputs pcp input)) := by
    refine run_occurrenceStage
      (run_tableRunnerProgram inputLength width queryCount wordCode) ?_
    rw [hwidth, hqueryCount, hwordCode, tableRunnerRequest_eq]
    exact htake
  have hpower :
      runNPOracleProgram (tablePowerStageProgram pcp)
          (tablePowerStageBits pcp input inputLength width queryCount wordCode)
          (tablePowerStageFuel pcp input width)
          (initialNPOracleState inputLength
            (Nat.pair width (tableProductFrame width queryCount wordCode))) =
        some
          (encodeBalancedList (projectionRunnerCallOutputs pcp input)) :=
    run_occurrenceStage
      (run_preserveRightProgram binaryTwoPowProgram inputLength
        (binaryTwoPowBits width) (binaryTwoPowFuel width) width
        (tableProductFrame width queryCount wordCode) (2 ^ width)
        (run_binaryTwoPowProgram inputLength width (binaryTwoPowBits width)
          (le_refl _)))
      hrunner
  have hexponent :
      runNPOracleProgram (tableExponentStageProgram pcp)
          (tableExponentStageBits pcp input inputLength width queryCount
            wordCode)
          (tableExponentStageFuel pcp input width)
          (initialNPOracleState inputLength
            (tableProductFrame width queryCount wordCode)) =
        some
          (encodeBalancedList (projectionRunnerCallOutputs pcp input)) :=
    run_occurrenceStage
      (run_tableExponentProgram inputLength width queryCount wordCode) hpower
  have hproduct :
      runNPOracleProgram (tableProductStageProgram pcp)
          (tableProductStageBits pcp input inputLength width queryCount
            wordCode)
          (tableProductStageFuel pcp input width)
          (initialNPOracleState inputLength
            (tableShapeOutput width queryCount wordCode)) =
        some
          (encodeBalancedList (projectionRunnerCallOutputs pcp input)) :=
    run_occurrenceStage
      (run_preserveRightProgram bitSerialMulProgram inputLength
        (bitSerialMulBits inputLength queryCount width)
        (bitSerialMulFuel width) (Nat.pair queryCount width)
        (Nat.pair width (Nat.pair queryCount wordCode)) (queryCount * width)
        (run_bitSerialMulProgram inputLength queryCount width))
      hexponent
  have hshape :
      runNPOracleProgram (tableShapeStageProgram pcp)
          (tableShapeStageBits pcp input inputLength inputLength width
            queryCount copies code wordCode)
          (tableShapeStageFuel pcp input width)
          (initialNPOracleState inputLength
            (tableShapeInput inputLength width queryCount copies code
              wordCode)) =
        some
          (encodeBalancedList (projectionRunnerCallOutputs pcp input)) :=
    run_occurrenceStage
      (run_tableShapeProgram inputLength inputLength width queryCount copies
        code wordCode)
      hproduct
  exact run_occurrenceStage
    (run_occurrenceStage
      (run_tableFrameDuplicateProgram inputLength
        (scheduleNumeralBankOutput inputLength width queryCount copies code))
      (run_preserveRightProgram
        (bankRefuterWordFrameProgram refuter.runner.program machine.description)
        inputLength
        (bankRefuterWordFrameBits refuter machine inputLength inputLength width
          queryCount copies code)
        (bankRefuterWordFrameFuel refuter machine inputLength)
        (scheduleNumeralBankOutput inputLength width queryCount copies code)
        (scheduleNumeralBankOutput inputLength width queryCount copies code)
        (Nat.pair wordCode (Nat.pair inputLength code))
        (run_bankRefuterWordFrameProgram refuter machine inputLength inputLength
          width queryCount copies code)))
    hshape

/-! ## 7. `InverseAtomTableRuns`, discharged on the diagonal -/

/-- The stage at the published inverse schedule. -/
noncomputable def inverseBankTableProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  bankProjectionTableProgram pcp
    (publishedRefuterSource contracts clockDepth).refuter.runner.program
    machine.description

theorem inverseBankTableProgram_oracleFree
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hrefuter :
      OracleFree
        (publishedRefuterSource contracts clockDepth).refuter.runner.program) :
    OracleFree (inverseBankTableProgram contracts clockDepth machine pcp) :=
  bankProjectionTableProgram_oracleFree pcp hrefuter machine.description

/-- The bank's copy-count register at the schedule's own index. -/
noncomputable def inverseBankTableCopies
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (inverseSourceIndex
      (inverseSelectedSource contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseCoreAdvantagePower advantageExponent) target))

/-- Width of the stage at one request. -/
noncomputable def inverseBankTableBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (request : LanguageEvaluationRequest) : ℕ :=
  bankProjectionTableBits pcp
    (publishedRefuterSource contracts clockDepth).refuter machine
    (LanguageEvaluationRequest.length request)
    (inverseScheduleLength contracts clockDepth advantageExponent
      (LanguageEvaluationRequest.length request))
    (inverseBankTableCopies contracts clockDepth advantageExponent
      (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.code request)

/-- Fuel of the stage at one request. -/
noncomputable def inverseBankTableFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (request : LanguageEvaluationRequest) : ℕ :=
  bankProjectionTableFuel pcp
    (publishedRefuterSource contracts clockDepth).refuter machine
    (inverseScheduleLength contracts clockDepth advantageExponent
      (LanguageEvaluationRequest.length request))

/-- **The join fact.**  On the schedule's diagonal, and for a presented PCP,
the numeral bank's frame is the schedule's own five registers at the scheduled
source length, with the PCP's own width and query count in the two shape
positions. -/
theorem inverseAdapterFrame_ofRegisters
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    {target : ℕ} (input : BitInput target)
    (hdiagonal :
      target =
        sourceLength (inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent) target))) :
    inverseAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩ =
      scheduleNumeralBankOutput
        (sourceLength (inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent) target)))
        (pcp.nativeWidth
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target))))
        (pcp.queryCount
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target))))
        (inverseBankTableCopies contracts clockDepth advantageExponent target)
        (encodeBitInput input) := by
  have hwidth :=
    presentsPaddedOuterPCP_scheduledWidth hpresentation
      (inverseSourceIndex
        (inverseSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseCoreAdvantagePower advantageExponent) target))
  have hquery :=
    congrFun (presentsPaddedOuterPCP_queryCount hpresentation)
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseCoreAdvantagePower advantageExponent) target)))
  simp only [inverseAdapterFrame, inverseBankTableCopies]
  rw [hwidth, hquery]
  exact publishedBankFrame_at_inverseDiagonal contracts clockDepth
    advantageExponent target (encodeBitInput input) hdiagonal

/-- **The adapter's last residual, discharged.**  From the numeral bank's frame
the linked stage returns the balanced encoding of the projection runner's call
outputs at the scheduled PCP input.  The two hypotheses are exactly the two
`BankAtomContextRegisters` already threads — the executable presentation and the
onset-restricted schedule diagonal — and nothing else about the bank, the
schedule or the target is used. -/
theorem inverseAtomTableRuns_ofDiagonal
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
        target) :
    InverseAtomTableRuns contracts clockDepth machine advantageExponent pcp
      (inverseBankTableProgram contracts clockDepth machine pcp)
      (inverseBankTableBits contracts clockDepth machine advantageExponent pcp)
      (inverseBankTableFuel contracts clockDepth machine advantageExponent
        pcp) := by
  intro target hlarge input
  rw [inverseAdapterFrame_ofRegisters contracts clockDepth advantageExponent pcp
    hpresentation input (hdiagonal target hlarge)]
  exact run_bankProjectionTableProgram pcp
    (publishedRefuterSource contracts clockDepth).refuter machine target
    (sourceLength (inverseSourceIndex
      (inverseSelectedSource contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseCoreAdvantagePower advantageExponent) target)))
    (inverseBankTableCopies contracts clockDepth advantageExponent target)
    (encodeBitInput input) (hdiagonal target hlarge)

end NearCubicWires.BankProjectionTableStage
