import Proof.MachineModel.BankRecoveryCodeProgram

/-!
# The small-oracle size cap, read from the numeral bank

The branch query of `CanonicalBranchSelectorProgram` is the canonical
bounded-oracle recovery code of the scheduled refuter word *at the scheduled
size cap*

`RecoveryScheduleEnvelope.oracleSizeBound requiredDegree
  (scheduledWidth outer sourceIndex)`,

and `oracleSizeBound requiredDegree` is by definition the pairing clock
`pairClock (oracleDepth requiredDegree)`.  The numeral bank already leaves the
scheduled width in a register and `RuntimeScheduleNumeralBank.pairIterProgram`
is that clock as a fixed instruction stream, so the cap is a register
computation rather than an immediate.

This module performs it.  §2 lifts the bank's width register in front of the
retained frame, §3 runs the clock on it, §4 installs the resulting cap beside
the retained point code inside the frame, and §5 links the published
refuter-word frame of `BankRefuterWordFrameProgram` on top, producing

`pair (encodeBitInput word) (pair sourceLength (pair sizeBound pointCode))`,

the exact context the structural atom emitter of
`BankRecoveryCodeProgram` consumes.  Only the machine description remains an
immediate, and the machine-dependence analysis of
`ExecutableTargetLanguagePackaging` already licenses that one as frozen.
-/

namespace NearCubicWires.BankOracleSizeBoundProgram

open NearCubicWires
open NearCubicWires.BankRefuterWordFrameProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping -/

private theorem le_pair_left {value left right : ℕ} (hvalue : value ≤ left) :
    value ≤ Nat.pair left right :=
  hvalue.trans (Nat.left_le_pair left right)

private theorem le_pair_right {value left right : ℕ} (hvalue : value ≤ right) :
    value ≤ Nat.pair left right :=
  hvalue.trans (Nat.right_le_pair left right)

/-! ## 2. Lifting the bank's width register -/

/-- Input the bank's frame, output the scheduled width in front of it. -/
private def bankWidthLiftProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 3 2
  , .pair 3 0 0 3
  , .halt 0
  ]

@[simp] private theorem bankWidthLiftProgram_oracleFree :
    OracleFree bankWidthLiftProgram := by
  rfl

private def bankWidthLiftOutput
    (sourceLen width queryCount copies code : ℕ) : ℕ :=
  Nat.pair width
    (scheduleNumeralBankOutput sourceLen width queryCount copies code)

private def bankWidthLiftBits
    (sourceLen width queryCount copies code : ℕ) : ℕ :=
  natBitLength (bankWidthLiftOutput sourceLen width queryCount copies code)

private theorem run_bankWidthLiftProgram
    (inputLength sourceLen width queryCount copies code : ℕ) :
    runNPOracleProgram bankWidthLiftProgram
        (bankWidthLiftBits sourceLen width queryCount copies code) 4
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies code)) =
      some (bankWidthLiftOutput sourceLen width queryCount copies code) := by
  have hbits : ∀ value : ℕ,
      value ≤ bankWidthLiftOutput sourceLen width queryCount copies code →
      natBitLength value ≤
        bankWidthLiftBits sourceLen width queryCount copies code :=
    fun _ hvalue => natBitLength_mono hvalue
  have hframe :=
    hbits (scheduleNumeralBankOutput sourceLen width queryCount copies code)
      (le_pair_right (le_refl _))
  have htail :=
    hbits (Nat.pair width (Nat.pair queryCount (Nat.pair copies code)))
      (le_pair_right (le_pair_right (le_refl _)))
  have hwidth := hbits width (le_pair_left (le_refl width))
  have houtput := hbits _ (le_refl _)
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair queryCount (Nat.pair copies code)))
    (by rfl) rfl
    (by simp [initialNPOracleState, scheduleNumeralBankOutput]) htail]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := bankWidthLiftOutput sourceLen width queryCount copies code)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        bankWidthLiftOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 3. Installing the computed cap beside the point code -/

/-- Input `pair sizeBound frame`, output the same frame with the size bound
paired in front of the retained point code. -/
private def bankBoundInstallProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .unpairLeft 9 10 9
  , .unpairRight 9 11 10
  , .pair 2 11 12 11
  , .pair 10 12 13 12
  , .pair 8 13 14 13
  , .pair 6 14 15 14
  , .pair 4 15 0 15
  , .halt 0
  ]

@[simp] private theorem bankBoundInstallProgram_oracleFree :
    OracleFree bankBoundInstallProgram := by
  rfl

private def bankBoundInstallInput
    (sizeBound sourceLen width queryCount copies code : ℕ) : ℕ :=
  Nat.pair sizeBound
    (scheduleNumeralBankOutput sourceLen width queryCount copies code)

/-- The bank's frame with the computed size cap installed in front of the
retained point code. -/
def bankBoundFrame
    (sizeBound sourceLen width queryCount copies code : ℕ) : ℕ :=
  scheduleNumeralBankOutput sourceLen width queryCount copies
    (Nat.pair sizeBound code)

private def bankBoundInstallBits
    (sizeBound sourceLen width queryCount copies code : ℕ) : ℕ :=
  natBitLength
    (max (bankBoundInstallInput sizeBound sourceLen width queryCount copies code)
      (bankBoundFrame sizeBound sourceLen width queryCount copies code))

private theorem run_bankBoundInstallProgram
    (inputLength sizeBound sourceLen width queryCount copies code : ℕ) :
    runNPOracleProgram bankBoundInstallProgram
        (bankBoundInstallBits sizeBound sourceLen width queryCount copies code)
        16
        (initialNPOracleState inputLength
          (bankBoundInstallInput sizeBound sourceLen width queryCount copies
            code)) =
      some (bankBoundFrame sizeBound sourceLen width queryCount copies code) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        bankBoundInstallInput sizeBound sourceLen width queryCount copies code →
      natBitLength value ≤
        bankBoundInstallBits sizeBound sourceLen width queryCount copies code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ bankBoundFrame sizeBound sourceLen width queryCount copies code →
      natBitLength value ≤
        bankBoundInstallBits sizeBound sourceLen width queryCount copies code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hbound := hrequest sizeBound (le_pair_left (le_refl sizeBound))
  have hframe :=
    hrequest (scheduleNumeralBankOutput sourceLen width queryCount copies code)
      (le_pair_right (le_refl _))
  have hlength :=
    hrequest sourceLen (le_pair_right (le_pair_left (le_refl sourceLen)))
  have hwidthTail :=
    hrequest (Nat.pair width (Nat.pair queryCount (Nat.pair copies code)))
      (le_pair_right (le_pair_right (le_refl _)))
  have hwidth :=
    hrequest width
      (le_pair_right (le_pair_right (le_pair_left (le_refl width))))
  have hcountTail :=
    hrequest (Nat.pair queryCount (Nat.pair copies code))
      (le_pair_right (le_pair_right (le_pair_right (le_refl _))))
  have hcount :=
    hrequest queryCount
      (le_pair_right
        (le_pair_right (le_pair_right (le_pair_left (le_refl queryCount)))))
  have hcopyTail :=
    hrequest (Nat.pair copies code)
      (le_pair_right
        (le_pair_right (le_pair_right (le_pair_right (le_refl _)))))
  have hcopies :=
    hrequest copies
      (le_pair_right
        (le_pair_right
          (le_pair_right (le_pair_right (le_pair_left (le_refl copies))))))
  have hcode :=
    hrequest code
      (le_pair_right
        (le_pair_right
          (le_pair_right (le_pair_right (le_pair_right (le_refl code))))))
  have hpoint :=
    hresult (Nat.pair sizeBound code)
      (le_pair_right (le_pair_right (le_pair_right (le_pair_right (le_refl _)))))
  have hcopyOut :=
    hresult (Nat.pair copies (Nat.pair sizeBound code))
      (le_pair_right (le_pair_right (le_pair_right (le_refl _))))
  have hcountOut :=
    hresult
      (Nat.pair queryCount (Nat.pair copies (Nat.pair sizeBound code)))
      (le_pair_right (le_pair_right (le_refl _)))
  have hwidthOut :=
    hresult
      (Nat.pair width
        (Nat.pair queryCount (Nat.pair copies (Nat.pair sizeBound code))))
      (le_pair_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sizeBound) (by rfl) rfl
    (by simp [initialNPOracleState, bankBoundInstallInput]) hbound]
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := scheduleNumeralBankOutput sourceLen width queryCount copies code)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, bankBoundInstallInput, NPOracleState.write,
        NPOracleState.jump])
    hframe]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceLen) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        scheduleNumeralBankOutput])
    hlength]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair queryCount (Nat.pair copies code)))
    (by
      rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        scheduleNumeralBankOutput])
    hwidthTail]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair queryCount (Nat.pair copies code)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountTail]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := queryCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcount]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair copies code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcopyTail]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := copies) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcopies]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcode]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair sizeBound code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpoint]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair copies (Nat.pair sizeBound code)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcopyOut]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair queryCount (Nat.pair copies (Nat.pair sizeBound code)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountOut]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair width
        (Nat.pair queryCount (Nat.pair copies (Nat.pair sizeBound code))))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthOut]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := bankBoundFrame sizeBound sourceLen width queryCount copies code)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, bankBoundFrame,
        scheduleNumeralBankOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 4. The bank's frame with the scheduled size cap -/

/-- **The size-cap stage.**  The bank's frame in, the same frame with the
scheduled small-oracle cap installed beside the retained point code out.  The
only parameter is the requested polynomial degree, which is frozen. -/
def bankSizeBoundProgram (requiredDegree : ℕ) : NPOracleProgram :=
  linkPrograms bankWidthLiftProgram
    (linkPrograms (preserveRightProgram (pairIterProgram
        (oracleDepth requiredDegree)))
      bankBoundInstallProgram)

theorem bankSizeBoundProgram_oracleFree (requiredDegree : ℕ) :
    OracleFree (bankSizeBoundProgram requiredDegree) :=
  oracleFree_linkPrograms bankWidthLiftProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _
        (pairIterProgram_oracleFree (oracleDepth requiredDegree)))
      bankBoundInstallProgram_oracleFree)

def bankSizeBoundFuel (requiredDegree : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram (pairIterProgram (oracleDepth requiredDegree)))
      bankBoundInstallProgram)
    4
    (linkFuel bankBoundInstallProgram
      (preserveRightFuel (pairIterFuel (oracleDepth requiredDegree))) 16)

def bankSizeBoundBits
    (requiredDegree inputLength sourceLen width queryCount copies code : ℕ) :
    ℕ :=
  occurrenceStageBits inputLength
    (bankWidthLiftBits sourceLen width queryCount copies code)
    (occurrenceStageBits inputLength
      (preserveRightBits
        (pairIterBits inputLength (oracleDepth requiredDegree) width) width
        (scheduleNumeralBankOutput sourceLen width queryCount copies code)
        (oracleSizeBound requiredDegree width))
      (bankBoundInstallBits (oracleSizeBound requiredDegree width) sourceLen
        width queryCount copies code))

/-- **The size cap, executed from the bank's registers.**  The scheduled
small-oracle cap `oracleSizeBound requiredDegree width` is computed from the
bank's width register by the pairing clock and installed beside the retained
point code; no target-derived immediate appears. -/
theorem run_bankSizeBoundProgram
    (requiredDegree inputLength sourceLen width queryCount copies code : ℕ) :
    runNPOracleProgram (bankSizeBoundProgram requiredDegree)
        (bankSizeBoundBits requiredDegree inputLength sourceLen width queryCount
          copies code)
        (bankSizeBoundFuel requiredDegree)
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies code)) =
      some
        (bankBoundFrame (oracleSizeBound requiredDegree width) sourceLen width
          queryCount copies code) :=
  run_occurrenceStage
    (run_bankWidthLiftProgram inputLength sourceLen width queryCount copies code)
    (run_occurrenceStage
      (run_preserveRightProgram (pairIterProgram (oracleDepth requiredDegree))
        inputLength (pairIterBits inputLength (oracleDepth requiredDegree) width)
        (pairIterFuel (oracleDepth requiredDegree)) width
        (scheduleNumeralBankOutput sourceLen width queryCount copies code)
        (oracleSizeBound requiredDegree width)
        (run_pairIterProgram_pairClock inputLength
          (oracleDepth requiredDegree) width))
      (run_bankBoundInstallProgram inputLength
        (oracleSizeBound requiredDegree width) sourceLen width queryCount copies
        code))

/-! ## 5. The emitter's context: refuter word, scheduled length, size cap -/

/-- **The recovery frame.**  The numeral bank's frame in; the scheduled refuter
word, the scheduled source length, the scheduled small-oracle cap and the
retained point code out.  The machine description is the only immediate. -/
def bankRecoveryFrameProgram
    (refuterProgram : NPOracleProgram) (description requiredDegree : ℕ) :
    NPOracleProgram :=
  linkPrograms (bankSizeBoundProgram requiredDegree)
    (bankRefuterWordFrameProgram refuterProgram description)

theorem bankRecoveryFrameProgram_oracleFree
    {refuterProgram : NPOracleProgram} (hrefuter : OracleFree refuterProgram)
    (description requiredDegree : ℕ) :
    OracleFree
      (bankRecoveryFrameProgram refuterProgram description requiredDegree) :=
  oracleFree_linkPrograms (bankSizeBoundProgram_oracleFree requiredDegree)
    (bankRefuterWordFrameProgram_oracleFree hrefuter description)

def bankRecoveryFrameFuel
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (requiredDegree sourceLen : ℕ) : ℕ :=
  linkFuel (bankRefuterWordFrameProgram refuter.runner.program
      machine.description)
    (bankSizeBoundFuel requiredDegree)
    (bankRefuterWordFrameFuel refuter machine sourceLen)

def bankRecoveryFrameBits
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (requiredDegree inputLength sourceLen width queryCount copies code : ℕ) :
    ℕ :=
  occurrenceStageBits inputLength
    (bankSizeBoundBits requiredDegree inputLength sourceLen width queryCount
      copies code)
    (bankRefuterWordFrameBits refuter machine inputLength sourceLen width
      queryCount copies (Nat.pair (oracleSizeBound requiredDegree width) code))

/-- **The recovery frame, executed.**  Everything the structural atom emitter
needs — the scheduled refuter word, the scheduled source length, the scheduled
small-oracle cap and the request's own point code — is produced from the
numeral bank's frame by one fixed stream. -/
theorem run_bankRecoveryFrameProgram
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (requiredDegree inputLength sourceLen width queryCount copies code : ℕ) :
    runNPOracleProgram
        (bankRecoveryFrameProgram refuter.runner.program machine.description
          requiredDegree)
        (bankRecoveryFrameBits refuter machine requiredDegree inputLength
          sourceLen width queryCount copies code)
        (bankRecoveryFrameFuel refuter machine requiredDegree sourceLen)
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies code)) =
      some
        (Nat.pair (encodeBitInput (refuter.output machine sourceLen))
          (Nat.pair sourceLen
            (Nat.pair (oracleSizeBound requiredDegree width) code))) :=
  run_occurrenceStage
    (run_bankSizeBoundProgram requiredDegree inputLength sourceLen width
      queryCount copies code)
    (run_bankRefuterWordFrameProgram refuter machine inputLength sourceLen width
      queryCount copies (Nat.pair (oracleSizeBound requiredDegree width) code))

end NearCubicWires.BankOracleSizeBoundProgram
