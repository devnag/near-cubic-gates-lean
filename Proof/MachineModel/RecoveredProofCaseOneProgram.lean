import Proof.MachineModel.CanonicalTargetLanguageProgram
import Proof.MachineModel.RecoveredProofAmplifierSeedProgram

/-!
# The Case-1 half of the executable target language

Everything Case 1 needs is now a fixed instruction stream.  This module links
the five stages into one program and one exact run theorem.

1. `nativeContextCallProgram (recoveredProofAmplifierSeedProgram seed)` — the
   whole recovery is run once at the *source* input length while the outer
   program keeps the public target length, and the requested point code is
   preserved beside the result.
2. A seven-instruction frame adapter producing the canonical native request of
   the published amplifier's construction program.
3. `preserveRightProgram (nativeCallProgram construction.program)` — the one
   construction call of `run_amplifierConstructionCallProgram_pair`, again with
   the point code preserved.
4. An eight-instruction frame adapter producing
   `CanonicalTargetBitProgram.targetBitCaseOneInput`.
5. `targetBitProgram` itself, whose Case-1 outputs are exactly
   `inverseCaseOneTargetFunction` and `fixedCaseOneTargetFunction` by
   `CanonicalTargetLanguageProgram.run_targetBitProgram_inverseCaseOne` and
   `run_targetBitProgram_fixedCaseOne`.

The public input of the composed program is the refuter-word frame
`pair (encodeBitInput refuterWord) (pair sourceLength pointCode)`.  Producing
that frame from the point code alone is one published refuter call, the same
seam already isolated by
`CanonicalTargetLanguageProgram.inverseRefuterInput_eq_of_description`.
-/

namespace NearCubicWires.RecoveredProofCaseOneProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveredProofAmplifierSeedProgram
open NearCubicWires.RecoveredProofEncodingProgram
open NearCubicWires.RecoveredProofRequestCompilerProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The construction-call frame adapter

Input `pair (pair arity encoded) (pair calleeLength pointCode)`, output
`pair (nativeInputRequest arity (pair arity encoded)) pointCode`. -/

private def constructionFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairLeft 2 3 2
  , .unpairRight 0 4 3
  , .unpairRight 4 5 4
  , .pair 3 2 6 5
  , .pair 6 5 0 6
  , .halt 0
  ]

@[simp] private theorem constructionFrameProgram_oracleFree :
    OracleFree constructionFrameProgram := by
  rfl

def constructionFrameBits
    (arity encoded calleeLength pointCode : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair (Nat.pair arity encoded) (Nat.pair calleeLength pointCode))
      (Nat.pair (nativeInputRequest arity (Nat.pair arity encoded))
        pointCode))

private theorem run_constructionFrameProgram
    (inputLength arity encoded calleeLength pointCode : ℕ) :
    runNPOracleProgram constructionFrameProgram
        (constructionFrameBits arity encoded calleeLength pointCode) 7
        (initialNPOracleState inputLength
          (Nat.pair (Nat.pair arity encoded)
            (Nat.pair calleeLength pointCode))) =
      some
        (Nat.pair (nativeInputRequest arity (Nat.pair arity encoded))
          pointCode) := by
  have hinputBits :
      natBitLength
          (Nat.pair (Nat.pair arity encoded)
            (Nat.pair calleeLength pointCode)) ≤
        constructionFrameBits arity encoded calleeLength pointCode :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength
          (Nat.pair (nativeInputRequest arity (Nat.pair arity encoded))
            pointCode) ≤
        constructionFrameBits arity encoded calleeLength pointCode :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hrequestBits :
      natBitLength (Nat.pair arity encoded) ≤
        constructionFrameBits arity encoded calleeLength pointCode :=
    (natBitLength_mono
      (Nat.left_le_pair (Nat.pair arity encoded)
        (Nat.pair calleeLength pointCode))).trans hinputBits
  have harityBits :
      natBitLength arity ≤
        constructionFrameBits arity encoded calleeLength pointCode :=
    (natBitLength_mono (Nat.left_le_pair arity encoded)).trans hrequestBits
  have hframeBits :
      natBitLength (Nat.pair calleeLength pointCode) ≤
        constructionFrameBits arity encoded calleeLength pointCode :=
    (natBitLength_mono
      (Nat.right_le_pair (Nat.pair arity encoded)
        (Nat.pair calleeLength pointCode))).trans hinputBits
  have hpointBits :
      natBitLength pointCode ≤
        constructionFrameBits arity encoded calleeLength pointCode :=
    (natBitLength_mono
      (Nat.right_le_pair calleeLength pointCode)).trans hframeBits
  have hnativeBits :
      natBitLength (nativeInputRequest arity (Nat.pair arity encoded)) ≤
        constructionFrameBits arity encoded calleeLength pointCode :=
    (natBitLength_mono
      (Nat.left_le_pair (nativeInputRequest arity (Nat.pair arity encoded))
        pointCode)).trans houtputBits
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := Nat.pair arity encoded)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hrequestBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := arity)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harityBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair calleeLength pointCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hframeBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := pointCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpointBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := nativeInputRequest arity (Nat.pair arity encoded))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, nativeInputRequest])
    hnativeBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (nativeInputRequest arity (Nat.pair arity encoded)) pointCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## 2. The target-bit frame adapter

Input `pair (pair outputArity descriptor) pointCode`, output
`targetBitCaseOneInput outputArity descriptor pointCode`. -/

private def targetBitFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairLeft 2 3 2
  , .unpairRight 0 4 3
  , .pair 3 4 5 4
  , .pair 5 2 6 5
  , .set 7 0 6
  , .pair 7 6 0 7
  , .halt 0
  ]

@[simp] private theorem targetBitFrameProgram_oracleFree :
    OracleFree targetBitFrameProgram := by
  rfl

def targetBitFrameBits (outputArity descriptor pointCode : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair (Nat.pair outputArity descriptor) pointCode)
      (targetBitCaseOneInput outputArity descriptor pointCode))

private theorem run_targetBitFrameProgram
    (inputLength outputArity descriptor pointCode : ℕ) :
    runNPOracleProgram targetBitFrameProgram
        (targetBitFrameBits outputArity descriptor pointCode) 8
        (initialNPOracleState inputLength
          (Nat.pair (Nat.pair outputArity descriptor) pointCode)) =
      some (targetBitCaseOneInput outputArity descriptor pointCode) := by
  have hinputBits :
      natBitLength (Nat.pair (Nat.pair outputArity descriptor) pointCode) ≤
        targetBitFrameBits outputArity descriptor pointCode :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength (targetBitCaseOneInput outputArity descriptor pointCode) ≤
        targetBitFrameBits outputArity descriptor pointCode :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hshapeBits :
      natBitLength (Nat.pair outputArity descriptor) ≤
        targetBitFrameBits outputArity descriptor pointCode :=
    (natBitLength_mono
      (Nat.left_le_pair (Nat.pair outputArity descriptor) pointCode)).trans
      hinputBits
  have harityBits :
      natBitLength outputArity ≤
        targetBitFrameBits outputArity descriptor pointCode :=
    (natBitLength_mono
      (Nat.left_le_pair outputArity descriptor)).trans hshapeBits
  have hpointBits :
      natBitLength pointCode ≤
        targetBitFrameBits outputArity descriptor pointCode :=
    (natBitLength_mono
      (Nat.right_le_pair (Nat.pair outputArity descriptor) pointCode)).trans
      hinputBits
  have hbodyBits :
      natBitLength
          (paddedAmplifierEvaluationInput outputArity descriptor pointCode) ≤
        targetBitFrameBits outputArity descriptor pointCode :=
    (natBitLength_mono
      (Nat.right_le_pair 0
        (paddedAmplifierEvaluationInput outputArity descriptor
          pointCode))).trans houtputBits
  have hprefixBits :
      natBitLength (bitInputPrefixInput outputArity pointCode) ≤
        targetBitFrameBits outputArity descriptor pointCode :=
    (natBitLength_mono
      (Nat.left_le_pair (bitInputPrefixInput outputArity pointCode)
        (Nat.pair outputArity descriptor))).trans hbodyBits
  have hzeroBits :
      natBitLength 0 ≤ targetBitFrameBits outputArity descriptor pointCode :=
    (natBitLength_mono (Nat.zero_le _)).trans harityBits
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := Nat.pair outputArity descriptor)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hshapeBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := outputArity)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harityBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := pointCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpointBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (value := bitInputPrefixInput outputArity pointCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, bitInputPrefixInput])
    hprefixBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := paddedAmplifierEvaluationInput outputArity descriptor pointCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        paddedAmplifierEvaluationInput])
    hbodyBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := targetBitCaseOneInput outputArity descriptor pointCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, targetBitCaseOneInput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## 3. The composed Case-1 program -/

private def caseOneTailProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm) : NPOracleProgram :=
  linkPrograms constructionFrameProgram
    (linkPrograms
      (preserveRightProgram (nativeCallProgram algorithm.construction.program))
      (linkPrograms targetBitFrameProgram (targetBitProgram algorithm)))

/-- One fixed program computing the Case-1 canonical target bit from the
refuter-word frame, given the single named recovery seed stage. -/
def caseOneTargetBitProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (seed : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (nativeContextCallProgram (recoveredProofAmplifierSeedProgram seed))
    (caseOneTailProgram algorithm)

/-- The seed of the published amplifier request at one scheduled word. -/
def scheduledAmplifierRequest
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) : AmplifierRequest :=
  ⟨scheduledWidth outer sourceIndex,
    recoveredOuterProofFunction (paddedOuterPCP outer) input⟩

def caseOneTargetBitFuel
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (seed : NPOracleProgram) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex))
    (seedFuel targetFuel : ℕ) : ℕ :=
  linkFuel (caseOneTailProgram algorithm)
    (nativeContextCallFuel (recoveredProofAmplifierSeedProgram seed)
      (recoveredProofAmplifierSeedFuel outer sourceIndex input seedFuel)
      (sourceLength sourceIndex) (encodeBitInput input))
    (linkFuel
      (linkPrograms
        (preserveRightProgram
          (nativeCallProgram algorithm.construction.program))
        (linkPrograms targetBitFrameProgram (targetBitProgram algorithm)))
      7
      (linkFuel
        (linkPrograms targetBitFrameProgram (targetBitProgram algorithm))
        (preserveRightFuel
          (nativeCallFuel algorithm.construction.program
            (algorithm.construction.budget
              (scheduledAmplifierRequest outer sourceIndex input))
            (scheduledWidth outer sourceIndex)
            (amplifierRequestCode
              (recoveredOuterProofFunction (paddedOuterPCP outer) input))))
        (linkFuel (targetBitProgram algorithm) 8 targetFuel)))

def caseOneTargetBitBits
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex))
    (seedBits target pointCode targetBits : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength target) <|
      max
        (nativeContextCallBits target (sourceLength sourceIndex)
          (encodeBitInput input) pointCode
          (amplifierRequestCode
            (recoveredOuterProofFunction (paddedOuterPCP outer) input))
          (recoveredProofAmplifierSeedBits outer sourceIndex input
            seedBits)) <|
        max
          (constructionFrameBits (scheduledWidth outer sourceIndex)
            (encodeBoolFunction
              (recoveredOuterProofFunction (paddedOuterPCP outer) input))
            (sourceLength sourceIndex) pointCode) <|
          max
            (preserveRightBits
              (nativeCallBits target (scheduledWidth outer sourceIndex)
                (amplifierRequestCode
                  (recoveredOuterProofFunction (paddedOuterPCP outer) input))
                (algorithm.constructionCode
                  (scheduledAmplifierRequest outer sourceIndex input))
                (algorithm.construction.budget
                  (scheduledAmplifierRequest outer sourceIndex input)))
              (nativeInputRequest (scheduledWidth outer sourceIndex)
                (amplifierRequestCode
                  (recoveredOuterProofFunction (paddedOuterPCP outer) input)))
              pointCode
              (Nat.pair
                (algorithm.outputArity
                  (scheduledAmplifierRequest outer sourceIndex input))
                (algorithm.descriptor
                  (scheduledAmplifierRequest outer sourceIndex input)))) <|
            max
              (targetBitFrameBits
                (algorithm.outputArity
                  (scheduledAmplifierRequest outer sourceIndex input))
                (algorithm.descriptor
                  (scheduledAmplifierRequest outer sourceIndex input))
                pointCode)
              targetBits

/-- Exact Case-1 execution of the composed program.  The only hypotheses are
the named recovery seed stage and one already certified target-bit run; every
other stage is discharged here. -/
theorem run_caseOneTargetBitProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (seed : NPOracleProgram) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex))
    (seedBits seedFuel target pointCode targetBits targetFuel value : ℕ)
    (hseed :
      runNPOracleProgram seed seedBits seedFuel
          (initialNPOracleState (sourceLength sourceIndex)
            (encodeBitInput input)) =
        some (recoveredProofCompilerSeedOutput outer sourceIndex input))
    (htarget :
      runNPOracleProgram (targetBitProgram algorithm) targetBits targetFuel
          (initialNPOracleState target
            (targetBitCaseOneInput
              (algorithm.outputArity
                (scheduledAmplifierRequest outer sourceIndex input))
              (algorithm.descriptor
                (scheduledAmplifierRequest outer sourceIndex input))
              pointCode)) =
        some value) :
    runNPOracleProgram (caseOneTargetBitProgram algorithm seed)
        (caseOneTargetBitBits algorithm outer sourceIndex input seedBits
          target pointCode targetBits)
        (caseOneTargetBitFuel algorithm seed outer sourceIndex input seedFuel
          targetFuel)
        (initialNPOracleState target
          (Nat.pair (encodeBitInput input)
            (Nat.pair (sourceLength sourceIndex) pointCode))) =
      some value := by
  have hpositive :
      1 ≤ caseOneTargetBitBits algorithm outer sourceIndex input seedBits
        target pointCode targetBits :=
    Nat.le_max_left _ _
  have hlengthBits :
      natBitLength target ≤
        caseOneTargetBitBits algorithm outer sourceIndex input seedBits
          target pointCode targetBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      nativeContextCallBits target (sourceLength sourceIndex)
          (encodeBitInput input) pointCode
          (amplifierRequestCode
            (recoveredOuterProofFunction (paddedOuterPCP outer) input))
          (recoveredProofAmplifierSeedBits outer sourceIndex input
            seedBits) ≤
        caseOneTargetBitBits algorithm outer sourceIndex input seedBits
          target pointCode targetBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hframeBits :
      constructionFrameBits (scheduledWidth outer sourceIndex)
          (encodeBoolFunction
            (recoveredOuterProofFunction (paddedOuterPCP outer) input))
          (sourceLength sourceIndex) pointCode ≤
        caseOneTargetBitBits algorithm outer sourceIndex input seedBits
          target pointCode targetBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hconstructionBits :
      preserveRightBits
          (nativeCallBits target (scheduledWidth outer sourceIndex)
            (amplifierRequestCode
              (recoveredOuterProofFunction (paddedOuterPCP outer) input))
            (algorithm.constructionCode
              (scheduledAmplifierRequest outer sourceIndex input))
            (algorithm.construction.budget
              (scheduledAmplifierRequest outer sourceIndex input)))
          (nativeInputRequest (scheduledWidth outer sourceIndex)
            (amplifierRequestCode
              (recoveredOuterProofFunction (paddedOuterPCP outer) input)))
          pointCode
          (Nat.pair
            (algorithm.outputArity
              (scheduledAmplifierRequest outer sourceIndex input))
            (algorithm.descriptor
              (scheduledAmplifierRequest outer sourceIndex input))) ≤
        caseOneTargetBitBits algorithm outer sourceIndex input seedBits
          target pointCode targetBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have htargetFrameBits :
      targetBitFrameBits
          (algorithm.outputArity
            (scheduledAmplifierRequest outer sourceIndex input))
          (algorithm.descriptor
            (scheduledAmplifierRequest outer sourceIndex input))
          pointCode ≤
        caseOneTargetBitBits algorithm outer sourceIndex input seedBits
          target pointCode targetBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have htargetBits :
      targetBits ≤
        caseOneTargetBitBits algorithm outer sourceIndex input seedBits
          target pointCode targetBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcall :=
    run_bits_mono
      (run_nativeContextCallProgram (recoveredProofAmplifierSeedProgram seed)
        target (sourceLength sourceIndex) (encodeBitInput input) pointCode
        (amplifierRequestCode
          (recoveredOuterProofFunction (paddedOuterPCP outer) input))
        (recoveredProofAmplifierSeedBits outer sourceIndex input seedBits)
        (recoveredProofAmplifierSeedFuel outer sourceIndex input seedFuel)
        (run_recoveredProofAmplifierSeedProgram seed outer sourceIndex input
          seedBits seedFuel hseed))
      hcallBits
  have hframe :=
    run_bits_mono
      (run_constructionFrameProgram target (scheduledWidth outer sourceIndex)
        (encodeBoolFunction
          (recoveredOuterProofFunction (paddedOuterPCP outer) input))
        (sourceLength sourceIndex) pointCode)
      hframeBits
  have hconstruction :=
    run_bits_mono
      (run_preserveRightProgram
        (nativeCallProgram algorithm.construction.program) target
        (nativeCallBits target (scheduledWidth outer sourceIndex)
          (amplifierRequestCode
            (recoveredOuterProofFunction (paddedOuterPCP outer) input))
          (algorithm.constructionCode
            (scheduledAmplifierRequest outer sourceIndex input))
          (algorithm.construction.budget
            (scheduledAmplifierRequest outer sourceIndex input)))
        (nativeCallFuel algorithm.construction.program
          (algorithm.construction.budget
            (scheduledAmplifierRequest outer sourceIndex input))
          (scheduledWidth outer sourceIndex)
          (amplifierRequestCode
            (recoveredOuterProofFunction (paddedOuterPCP outer) input)))
        (nativeInputRequest (scheduledWidth outer sourceIndex)
          (amplifierRequestCode
            (recoveredOuterProofFunction (paddedOuterPCP outer) input)))
        pointCode
        (Nat.pair
          (algorithm.outputArity
            (scheduledAmplifierRequest outer sourceIndex input))
          (algorithm.descriptor
            (scheduledAmplifierRequest outer sourceIndex input)))
        (run_amplifierConstructionCallProgram_pair algorithm target
          (scheduledWidth outer sourceIndex)
          (recoveredOuterProofFunction (paddedOuterPCP outer) input)))
      hconstructionBits
  have htargetFrame :=
    run_bits_mono
      (run_targetBitFrameProgram target
        (algorithm.outputArity
          (scheduledAmplifierRequest outer sourceIndex input))
        (algorithm.descriptor
          (scheduledAmplifierRequest outer sourceIndex input))
        pointCode)
      htargetFrameBits
  have htail :=
    run_linkPrograms hpositive hlengthBits htargetFrame
      (run_bits_mono htarget htargetBits)
  have htail2 := run_linkPrograms hpositive hlengthBits hconstruction htail
  have htail3 := run_linkPrograms hpositive hlengthBits hframe htail2
  have hrun := run_linkPrograms hpositive hlengthBits hcall htail3
  simpa only [caseOneTargetBitProgram, caseOneTailProgram,
    caseOneTargetBitFuel, amplifierRequestCode] using hrun

theorem run_caseOneTargetBitProgram_inverse
    (contracts : PublishedContracts) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (seed : NPOracleProgram)
    (advantageExponent : ℝ) (target : ℕ)
    (honset :
      (inverseEnvelope contracts outer
        (inverseCoreAdvantagePower advantageExponent)).targetOnset ≤ target)
    {input : BitInput
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      input)
    (hready :
      inverseCaseOneOnset contracts outer
          (inverseCoreAdvantagePower advantageExponent) ≤
        inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
    (point : BitInput target) (seedBits seedFuel : ℕ)
    (hseed :
      runNPOracleProgram seed seedBits seedFuel
          (initialNPOracleState
            (sourceLength (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
            (encodeBitInput input)) =
        some
          (recoveredProofCompilerSeedOutput outer
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target))
            input)) :
    runNPOracleProgram
        (caseOneTargetBitProgram (publishedAmplifier contracts).algorithm seed)
        (caseOneTargetBitBits (publishedAmplifier contracts).algorithm outer
          (inverseSourceIndex
            (inverseSelectedSource contracts outer
              (inverseCoreAdvantagePower advantageExponent) target))
          input seedBits target (encodeBitInput point)
          (targetBitCaseOneBits (publishedAmplifier contracts).algorithm target
            ((publishedAmplifier contracts).algorithm.outputArity
              (scheduledAmplifierRequest outer
                (inverseSourceIndex
                  (inverseSelectedSource contracts outer
                    (inverseCoreAdvantagePower advantageExponent) target))
                input))
            ((publishedAmplifier contracts).algorithm.descriptor
              (scheduledAmplifierRequest outer
                (inverseSourceIndex
                  (inverseSelectedSource contracts outer
                    (inverseCoreAdvantagePower advantageExponent) target))
                input))
            (encodeBitInput point)))
        (caseOneTargetBitFuel (publishedAmplifier contracts).algorithm seed
          outer
          (inverseSourceIndex
            (inverseSelectedSource contracts outer
              (inverseCoreAdvantagePower advantageExponent) target))
          input seedFuel
          (targetBitCaseOneFuel (publishedAmplifier contracts).algorithm
            ((publishedAmplifier contracts).algorithm.outputArity
              (scheduledAmplifierRequest outer
                (inverseSourceIndex
                  (inverseSelectedSource contracts outer
                    (inverseCoreAdvantagePower advantageExponent) target))
                input))
            ((publishedAmplifier contracts).algorithm.descriptor
              (scheduledAmplifierRequest outer
                (inverseSourceIndex
                  (inverseSelectedSource contracts outer
                    (inverseCoreAdvantagePower advantageExponent) target))
                input))
            (encodeBitInput point)))
        (initialNPOracleState target
          (Nat.pair (encodeBitInput input)
            (Nat.pair
              (sourceLength (inverseSourceIndex
                (inverseSelectedSource contracts outer
                  (inverseCoreAdvantagePower advantageExponent) target)))
              (encodeBitInput point)))) =
      some
        (inverseCaseOneTargetFunction contracts outer advantageExponent target
          honset data hyes hready point).toNat :=
  run_caseOneTargetBitProgram (publishedAmplifier contracts).algorithm seed
    outer
    (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
    input seedBits seedFuel target (encodeBitInput point) _ _ _ hseed
    (run_targetBitProgram_inverseCaseOne contracts outer advantageExponent
      target honset data hyes hready point)

theorem run_caseOneTargetBitProgram_fixed
    (contracts : PublishedContracts) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (seed : NPOracleProgram)
    (requestedRate target : ℕ)
    (honset :
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target)
    {input : BitInput
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
      input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤
        fixedSelectedSource contracts outer requestedRate target)
    (point : BitInput target) (seedBits seedFuel : ℕ)
    (hseed :
      runNPOracleProgram seed seedBits seedFuel
          (initialNPOracleState
            (sourceLength
              (fixedSelectedSource contracts outer requestedRate target))
            (encodeBitInput input)) =
        some
          (recoveredProofCompilerSeedOutput outer
            (fixedSelectedSource contracts outer requestedRate target)
            input)) :
    runNPOracleProgram
        (caseOneTargetBitProgram (publishedAmplifier contracts).algorithm seed)
        (caseOneTargetBitBits (publishedAmplifier contracts).algorithm outer
          (fixedSelectedSource contracts outer requestedRate target)
          input seedBits target (encodeBitInput point)
          (targetBitCaseOneBits (publishedAmplifier contracts).algorithm target
            ((publishedAmplifier contracts).algorithm.outputArity
              (scheduledAmplifierRequest outer
                (fixedSelectedSource contracts outer requestedRate target)
                input))
            ((publishedAmplifier contracts).algorithm.descriptor
              (scheduledAmplifierRequest outer
                (fixedSelectedSource contracts outer requestedRate target)
                input))
            (encodeBitInput point)))
        (caseOneTargetBitFuel (publishedAmplifier contracts).algorithm seed
          outer (fixedSelectedSource contracts outer requestedRate target)
          input seedFuel
          (targetBitCaseOneFuel (publishedAmplifier contracts).algorithm
            ((publishedAmplifier contracts).algorithm.outputArity
              (scheduledAmplifierRequest outer
                (fixedSelectedSource contracts outer requestedRate target)
                input))
            ((publishedAmplifier contracts).algorithm.descriptor
              (scheduledAmplifierRequest outer
                (fixedSelectedSource contracts outer requestedRate target)
                input))
            (encodeBitInput point)))
        (initialNPOracleState target
          (Nat.pair (encodeBitInput input)
            (Nat.pair
              (sourceLength
                (fixedSelectedSource contracts outer requestedRate target))
              (encodeBitInput point)))) =
      some
        (fixedCaseOneTargetFunction contracts outer requestedRate target
          honset data hyes hready point).toNat :=
  run_caseOneTargetBitProgram (publishedAmplifier contracts).algorithm seed
    outer (fixedSelectedSource contracts outer requestedRate target)
    input seedBits seedFuel target (encodeBitInput point) _ _ _ hseed
    (run_targetBitProgram_fixedCaseOne contracts outer requestedRate target
      honset data hyes hready point)

end NearCubicWires.RecoveredProofCaseOneProgram
