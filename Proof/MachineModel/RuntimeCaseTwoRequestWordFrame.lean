import Proof.MachineModel.BankRefuterWordFrameProgram
import Proof.MachineModel.BankScheduleDiagonal
import Proof.MachineModel.RuntimeCaseTwoSubstitutedEncodingClosure

/-!
# The Case-2 request word's three numerals

`RuntimeCaseTwoSubstitutedEncodingClosure.InverseSubstitutionRequestWord` asks
for one program emitting

> `pair (encodeBooleanCircuit caseTwo.circuit)
>   (pair nativeWidth (pair sourceLength (encodeBitInput refuterWord)))`

from the requested public length.  Three of those four fields are already
published streams, and this module links them.

* The **native width** is `RuntimeScheduleQuadNumeralProgram.nativeWidthProgram`
  at the published shape runner, entered at the target's own public length; the
  schedule diagonal turns that length into the scheduled source length.
* The **scheduled source length** and the **refuter word** are the numeral
  bank's own registers: `UniformTargetLanguageBank.publishedBankProgram` emits
  the frame and `BankRefuterWordFrameProgram.bankRefuterWordFrameProgram`
  turns it into `pair (encodeBitInput word) (pair sourceLength pointCode)`, so
  one three-instruction adapter reshapes it into the pair the request word
  wants.  The diagonal is *threaded*, never asserted: it enters as the same
  hypothesis `RuntimeCaseTwoOccurrenceEncodingClosure` already carries.

§1 is the adapter, §2 the two bank numerals, §3 the frame, and §4 discharges
`InverseSubstitutionRequestWord` from one premise: a program emitting the
recovered oracle's *own* circuit code from the public length.  Nothing about
the substitution, the restriction, the arity padding or the three numerals is
left open.
-/

namespace NearCubicWires.RuntimeCaseTwoRequestWordFrame

open NearCubicWires
open NearCubicWires.BankRefuterWordFrameProgram
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.RuntimeScheduleQuadNumeralProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The refuter-word adapter

Input the refuter frame `pair word (pair sourceLength pointCode)`, output the
request word's tail `pair sourceLength word`. -/

def sourceWordAdapterProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .pair 4 2 0 4
  , .halt 0
  ]

@[simp] theorem sourceWordAdapterProgram_oracleFree :
    OracleFree sourceWordAdapterProgram := by
  rfl

def sourceWordAdapterFuel : ℕ := 5

def sourceWordAdapterBits (word sourceLen pointCode : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair word (Nat.pair sourceLen pointCode))
      (Nat.pair sourceLen word))

theorem run_sourceWordAdapterProgram
    (inputLength word sourceLen pointCode : ℕ) :
    runNPOracleProgram sourceWordAdapterProgram
        (sourceWordAdapterBits word sourceLen pointCode) sourceWordAdapterFuel
        (initialNPOracleState inputLength
          (Nat.pair word (Nat.pair sourceLen pointCode))) =
      some (Nat.pair sourceLen word) := by
  have hrequest :
      natBitLength (Nat.pair word (Nat.pair sourceLen pointCode)) ≤
        sourceWordAdapterBits word sourceLen pointCode :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtput :
      natBitLength (Nat.pair sourceLen word) ≤
        sourceWordAdapterBits word sourceLen pointCode :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hword :
      natBitLength word ≤ sourceWordAdapterBits word sourceLen pointCode :=
    (natBitLength_mono
      (Nat.left_le_pair word (Nat.pair sourceLen pointCode))).trans hrequest
  have htail :
      natBitLength (Nat.pair sourceLen pointCode) ≤
        sourceWordAdapterBits word sourceLen pointCode :=
    (natBitLength_mono
      (Nat.right_le_pair word (Nat.pair sourceLen pointCode))).trans hrequest
  have hlength :
      natBitLength sourceLen ≤ sourceWordAdapterBits word sourceLen pointCode :=
    (natBitLength_mono (Nat.left_le_pair sourceLen pointCode)).trans htail
  rw [show sourceWordAdapterFuel = 4 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := word) (by rfl) rfl
    (by simp [initialNPOracleState]) hword]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair sourceLen pointCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htail]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceLen) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlength]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair sourceLen word) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 2. The two bank numerals -/

/-- **The scheduled length beside the refuter word.**  The published numeral
bank, the register-driven refuter frame and the adapter of §1. -/
noncomputable def inverseSourceWordProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) : NPOracleProgram :=
  linkPrograms
    (publishedBankProgram (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent))
    (linkPrograms
      (bankRefuterWordFrameProgram
        (publishedRefuterSource contracts clockDepth).refuter.runner.program
        machine.description)
      sourceWordAdapterProgram)

noncomputable def inverseSourceWordFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (bankRefuterWordFrameProgram
        (publishedRefuterSource contracts clockDepth).refuter.runner.program
        machine.description)
      sourceWordAdapterProgram)
    (publishedBankFuel (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent) target)
    (linkFuel sourceWordAdapterProgram
      (bankRefuterWordFrameFuel
        (publishedRefuterSource contracts clockDepth).refuter machine
        (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
          target)))
      sourceWordAdapterFuel)

noncomputable def inverseSourceWordBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrenceStageBits target
    (publishedBankBits (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent) target target)
    (occurrenceStageBits target
      (bankRefuterWordFrameBits
        (publishedRefuterSource contracts clockDepth).refuter machine target
        (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
          target))
        (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseChainSourceIndex contracts clockDepth advantageExponent target))
        ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
          (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
            target)))
        (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent)
          (inverseChainSourceIndex contracts clockDepth advantageExponent target))
        target)
      (sourceWordAdapterBits
        (encodeBitInput
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target))
        (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
          target))
        target))

set_option maxHeartbeats 400000 in
-- The statement carries the bank's frame, the refuter call's envelope and the
-- adapter at one target, so elaborating it alone exceeds the default budget.
/-- **The two bank numerals, executed.**  On the schedule diagonal the fixed
stream returns the scheduled source length beside the published refuter's own
word, from the requested public length alone. -/
theorem run_inverseSourceWordProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target : ℕ)
    (hdiagonal :
      target =
        sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
          target)) :
    runNPOracleProgram
        (inverseSourceWordProgram contracts clockDepth machine
          advantageExponent)
        (inverseSourceWordBits contracts clockDepth machine advantageExponent
          target)
        (inverseSourceWordFuel contracts clockDepth machine advantageExponent
          target)
        (initialNPOracleState target target) =
      some
        (Nat.pair
          (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
          (encodeBitInput
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target))) := by
  have hbank :
      runNPOracleProgram
          (publishedBankProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent))
          (publishedBankBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target target)
          (publishedBankFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target)
          (initialNPOracleState target target) =
        some
          (scheduleNumeralBankOutput
            (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))
            (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseChainSourceIndex contracts clockDepth advantageExponent target))
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
              (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
                target)))
            (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (inverseBankRate contracts advantageExponent)
              (inverseChainSourceIndex contracts clockDepth advantageExponent target))
            target) := by
    have hrun :=
      run_publishedScheduleNumeralBankProgram
        (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target target
    simp only [inverseChainSourceIndex]
    rw [← publishedBankFrame_at_inverseDiagonal contracts clockDepth
      advantageExponent target target hdiagonal]
    exact hrun
  have hframe :=
    run_bankRefuterWordFrameProgram
      (publishedRefuterSource contracts clockDepth).refuter machine target
      (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent target))
      (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseChainSourceIndex contracts clockDepth advantageExponent target))
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
        (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
          target)))
      (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (inverseChainSourceIndex contracts clockDepth advantageExponent target))
      target
  exact run_occurrenceStage hbank
    (run_occurrenceStage hframe
      (run_sourceWordAdapterProgram target
        (encodeBitInput
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target))
        (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
          target))
        target))

/-! ## 3. The three-numeral frame -/

/-- **The request word's numeral tail.**  The native width beside the scheduled
length and the refuter word. -/
noncomputable def inverseRequestFrameProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) : NPOracleProgram :=
  occurrencePacketPairProgram (inverseNativeWidthProgram contracts clockDepth)
    (inverseSourceWordProgram contracts clockDepth machine advantageExponent)

noncomputable def inverseRequestFrameFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrencePacketPairFuel (inverseNativeWidthProgram contracts clockDepth)
    (inverseSourceWordProgram contracts clockDepth machine advantageExponent)
    (inverseNativeWidthFuel contracts clockDepth target)
    (inverseSourceWordFuel contracts clockDepth machine advantageExponent
      target)

noncomputable def inverseRequestFrameBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrencePacketPairBits target
    (inverseNativeWidthBits contracts clockDepth target)
    (inverseSourceWordBits contracts clockDepth machine advantageExponent
      target)
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
      (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent target)))
    (Nat.pair
      (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent target))
      (encodeBitInput
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target)))

set_option maxHeartbeats 400000 in
-- The statement carries both numeral streams and their envelopes at one
-- target, so elaborating it alone exceeds the default budget.
/-- **The three numerals, executed.**  On the schedule diagonal the fixed
stream returns exactly the tail of the Case-2 request word. -/
theorem run_inverseRequestFrameProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target : ℕ)
    (hdiagonal :
      target =
        sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
          target)) :
    runNPOracleProgram
        (inverseRequestFrameProgram contracts clockDepth machine
          advantageExponent)
        (inverseRequestFrameBits contracts clockDepth machine advantageExponent
          target)
        (inverseRequestFrameFuel contracts clockDepth machine advantageExponent
          target)
        (initialNPOracleState target target) =
      some
        (Nat.pair
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
            (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
              target)))
          (Nat.pair
            (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))
            (encodeBitInput
              (inverseRefuterInput contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                advantageExponent target)))) := by
  have harity :
      runNPOracleProgram (inverseNativeWidthProgram contracts clockDepth)
          (inverseNativeWidthBits contracts clockDepth target)
          (inverseNativeWidthFuel contracts clockDepth target)
          (initialNPOracleState target target) =
        some
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
            (sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))) := by
    rw [← hdiagonal]
    exact run_nativeWidthProgram
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program target
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget target)
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget target)
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.execute
        target)
      (run_publishedShapeProgram
        (publishedHierarchyOuterPCP contracts clockDepth) target)
  exact run_occurrencePacketPairProgram
    (inverseNativeWidthProgram contracts clockDepth)
    (inverseSourceWordProgram contracts clockDepth machine advantageExponent)
    target (inverseNativeWidthBits contracts clockDepth target)
    (inverseNativeWidthFuel contracts clockDepth target)
    (inverseSourceWordBits contracts clockDepth machine advantageExponent
      target)
    (inverseSourceWordFuel contracts clockDepth machine advantageExponent
      target)
    _ _ harity
    (run_inverseSourceWordProgram contracts clockDepth machine advantageExponent
      target hdiagonal)

/-! ## 4. The request word from the oracle's own code -/

/-- **The remaining premise.**  One fixed program that, from the requested
public length alone, emits the *recovered oracle's own* circuit code — no
restriction, no substitution, no arity padding, and no numeral beside it. -/
def InverseScheduledCircuitEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (circuitProgram : NPOracleProgram) (circuitBits circuitFuel : ℕ → ℕ) :
    Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)),
    inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes = .caseTwo caseTwo →
    runNPOracleProgram circuitProgram (circuitBits target) (circuitFuel target)
        (initialNPOracleState target target) =
      some (encodeBooleanCircuit caseTwo.circuit)

/-- The request-word stream: the oracle's own code beside the three numerals. -/
noncomputable def inverseSubstitutionRequestProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (circuitProgram : NPOracleProgram) : NPOracleProgram :=
  occurrencePacketPairProgram circuitProgram
    (inverseRequestFrameProgram contracts clockDepth machine advantageExponent)

noncomputable def inverseSubstitutionRequestFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (circuitProgram : NPOracleProgram) (circuitFuel : ℕ → ℕ) (target : ℕ) :
    ℕ :=
  occurrencePacketPairFuel circuitProgram
    (inverseRequestFrameProgram contracts clockDepth machine advantageExponent)
    (circuitFuel target)
    (inverseRequestFrameFuel contracts clockDepth machine advantageExponent
      target)

open Classical in
/-- The request word's width at one target, quoted at the oracle the branch
carries. -/
noncomputable def inverseSubstitutionRequestBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (circuitBits : ℕ → ℕ) (target : ℕ) : ℕ :=
  if hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target) then
    match
      inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes with
    | .caseOne _ => 0
    | .caseTwo caseTwo =>
        occurrencePacketPairBits target (circuitBits target)
          (inverseRequestFrameBits contracts clockDepth machine
            advantageExponent target)
          (encodeBooleanCircuit caseTwo.circuit)
          (Nat.pair
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
              (sourceLength
                (inverseChainSourceIndex contracts clockDepth advantageExponent target)))
            (Nat.pair
              (sourceLength
                (inverseChainSourceIndex contracts clockDepth advantageExponent target))
              (encodeBitInput
                (inverseRefuterInput contracts
                  (publishedHierarchyOuterPCP contracts clockDepth) machine
                  advantageExponent target))))
  else 0

set_option maxHeartbeats 1600000 in
-- The statement carries the paired stream, both envelopes and the branch read
-- at one target, so elaborating it alone exceeds the default budget.
/-- **The Case-2 request word, discharged from the oracle's own code.**  The
native width, the scheduled source length and the refuter word are all
published streams on the schedule diagonal, so the whole request word follows
from one program emitting `encodeBooleanCircuit caseTwo.circuit`. -/
theorem inverseSubstitutionRequestWord_ofCircuitEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target =
        sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
    (circuitProgram : NPOracleProgram) (circuitBits circuitFuel : ℕ → ℕ)
    (hcircuits :
      InverseScheduledCircuitEncoding contracts clockDepth machine
        advantageExponent circuitProgram circuitBits circuitFuel) :
    InverseSubstitutionRequestWord contracts clockDepth machine
      advantageExponent
      (inverseSubstitutionRequestProgram contracts clockDepth machine
        advantageExponent circuitProgram)
      (inverseSubstitutionRequestBits contracts clockDepth machine
        advantageExponent circuitBits)
      (inverseSubstitutionRequestFuel contracts clockDepth machine
        advantageExponent circuitProgram circuitFuel) := by
  intro target hlarge hyes caseTwo hbranch
  have hdiag : target =
      sourceLength (inverseChainSourceIndex contracts clockDepth advantageExponent target) :=
    hdiagonal target hlarge
  have hcircuit := hcircuits target hlarge hyes caseTwo hbranch
  have hbits :
      inverseSubstitutionRequestBits contracts clockDepth machine
          advantageExponent circuitBits target =
        occurrencePacketPairBits target (circuitBits target)
          (inverseRequestFrameBits contracts clockDepth machine
            advantageExponent target)
          (encodeBooleanCircuit caseTwo.circuit)
          (Nat.pair
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
              (sourceLength
                (inverseChainSourceIndex contracts clockDepth advantageExponent target)))
            (Nat.pair
              (sourceLength
                (inverseChainSourceIndex contracts clockDepth advantageExponent target))
              (encodeBitInput
                (inverseRefuterInput contracts
                  (publishedHierarchyOuterPCP contracts clockDepth) machine
                  advantageExponent target)))) := by
    simp only [inverseSubstitutionRequestBits]
    rw [dif_pos hyes, hbranch]
  rw [hbits, inverseSubstitutionRequestProgram,
    inverseSubstitutionRequestFuel]
  exact run_occurrencePacketPairProgram circuitProgram
    (inverseRequestFrameProgram contracts clockDepth machine advantageExponent)
    target (circuitBits target)
    (circuitFuel target)
    (inverseRequestFrameBits contracts clockDepth machine advantageExponent
      target)
    (inverseRequestFrameFuel contracts clockDepth machine advantageExponent
      target)
    _ _ hcircuit
    (run_inverseRequestFrameProgram contracts clockDepth machine
      advantageExponent target hdiag)

end NearCubicWires.RuntimeCaseTwoRequestWordFrame
