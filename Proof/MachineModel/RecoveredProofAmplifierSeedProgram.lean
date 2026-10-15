import Proof.MachineModel.RecoveredProofRequestCompilerProgram

/-!
# From the raw refuter word to the published amplifier's seed request

`RecoveredProofRequestCompilerProgram` builds the balanced request list of the
C.12 recovery formula and retains the schedule frame beside it.  This module
consumes that pair once and produces the exact `AmplifierRequest.code` of the
recovered outer proof.

Three fixed stages, no new recovery path:

* the request compiler,
* `RecoveredProofEncodingProgram.recoveredProofEncodingProgram` run through the
  shared context-preserving wrapper — its public length is already the callee
  length retained by the compiler, so no relocation is needed here,
* one six-instruction adapter that reads the retained arity and emits
  `pair arity (encodeBoolFunction …)`.

The composed output is literally
`RecoveredProofEncodingProgram.amplifierRequestCode` of the recovered proof, so
`run_amplifierConstructionCallProgram_pair` may be applied immediately.
-/

namespace NearCubicWires.RecoveredProofAmplifierSeedProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveredProofEncodingProgram
open NearCubicWires.RecoveredProofRequestCompilerProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The seed-request adapter

Input `pair encoded (pair calleeLength (pair arity word))`, output
`pair arity encoded`.  The word and the callee length are consumed here: the
amplifier's construction program needs neither. -/

private def amplifierSeedRequestAdapterProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .unpairLeft 4 5 4
  , .pair 5 2 0 5
  , .halt 0
  ]

@[simp] private theorem amplifierSeedRequestAdapterProgram_oracleFree :
    OracleFree amplifierSeedRequestAdapterProgram := by
  rfl

def amplifierSeedRequestAdapterBits
    (encoded calleeLength arity word : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair encoded (Nat.pair calleeLength (Nat.pair arity word)))
      (Nat.pair arity encoded))

private theorem run_amplifierSeedRequestAdapterProgram
    (inputLength encoded calleeLength arity word : ℕ) :
    runNPOracleProgram amplifierSeedRequestAdapterProgram
        (amplifierSeedRequestAdapterBits encoded calleeLength arity word) 6
        (initialNPOracleState inputLength
          (Nat.pair encoded (Nat.pair calleeLength (Nat.pair arity word)))) =
      some (Nat.pair arity encoded) := by
  have hinputBits :
      natBitLength
          (Nat.pair encoded (Nat.pair calleeLength (Nat.pair arity word))) ≤
        amplifierSeedRequestAdapterBits encoded calleeLength arity word :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength (Nat.pair arity encoded) ≤
        amplifierSeedRequestAdapterBits encoded calleeLength arity word :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hencodedBits :
      natBitLength encoded ≤
        amplifierSeedRequestAdapterBits encoded calleeLength arity word :=
    (natBitLength_mono
      (Nat.left_le_pair encoded
        (Nat.pair calleeLength (Nat.pair arity word)))).trans hinputBits
  have hframeBits :
      natBitLength (Nat.pair calleeLength (Nat.pair arity word)) ≤
        amplifierSeedRequestAdapterBits encoded calleeLength arity word :=
    (natBitLength_mono
      (Nat.right_le_pair encoded
        (Nat.pair calleeLength (Nat.pair arity word)))).trans hinputBits
  have hpayloadBits :
      natBitLength (Nat.pair arity word) ≤
        amplifierSeedRequestAdapterBits encoded calleeLength arity word :=
    (natBitLength_mono
      (Nat.right_le_pair calleeLength (Nat.pair arity word))).trans hframeBits
  have harityBits :
      natBitLength arity ≤
        amplifierSeedRequestAdapterBits encoded calleeLength arity word :=
    (natBitLength_mono (Nat.left_le_pair arity word)).trans hpayloadBits
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := encoded)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hencodedBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair calleeLength (Nat.pair arity word))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hframeBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair arity word)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpayloadBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := arity)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harityBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair arity encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## 2. The composed seed-request producer -/

def recoveredProofAmplifierSeedProgram (seed : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (recoveredProofRequestCompilerProgram seed)
    (linkPrograms (preserveRightProgram recoveredProofEncodingProgram)
      amplifierSeedRequestAdapterProgram)

def recoveredProofAmplifierSeedFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) (seedFuel : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram recoveredProofEncodingProgram)
      amplifierSeedRequestAdapterProgram)
    (recoveredProofRequestCompilerFuel outer sourceIndex input seedFuel)
    (linkFuel amplifierSeedRequestAdapterProgram
      (preserveRightFuel
        (recoveredProofEncodingFuel (paddedOuterPCP outer) input
          (sourceLength sourceIndex)))
      6)

def recoveredProofAmplifierSeedBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) (seedBits : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength (sourceLength sourceIndex)) <|
      max
        (recoveredProofRequestCompilerBits outer sourceIndex input seedBits) <|
        max
          (preserveRightBits
            (recoveredProofEncodingBits (paddedOuterPCP outer) input
              (sourceLength sourceIndex))
            (recoveredProofEncodingInput (paddedOuterPCP outer) input
              (sourceLength sourceIndex))
            (Nat.pair (sourceLength sourceIndex)
              (Nat.pair (scheduledWidth outer sourceIndex)
                (encodeBitInput input)))
            (encodeBoolFunction
              (recoveredOuterProofFunction (paddedOuterPCP outer) input)))
          (amplifierSeedRequestAdapterBits
            (encodeBoolFunction
              (recoveredOuterProofFunction (paddedOuterPCP outer) input))
            (sourceLength sourceIndex) (scheduledWidth outer sourceIndex)
            (encodeBitInput input))

/-- Exact seed-request production.  Modulo the single named seed stage, one
fixed program turns the raw refuter word into the published amplifier's own
request code for the C.12-recovered accepting proof.  Every SAT query on this
path is inside `recoveredProofEncodingProgram`. -/
theorem run_recoveredProofAmplifierSeedProgram
    (seed : NPOracleProgram) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex))
    (seedBits seedFuel : ℕ)
    (hseed :
      runNPOracleProgram seed seedBits seedFuel
          (initialNPOracleState (sourceLength sourceIndex)
            (encodeBitInput input)) =
        some (recoveredProofCompilerSeedOutput outer sourceIndex input)) :
    runNPOracleProgram (recoveredProofAmplifierSeedProgram seed)
        (recoveredProofAmplifierSeedBits outer sourceIndex input seedBits)
        (recoveredProofAmplifierSeedFuel outer sourceIndex input seedFuel)
        (initialNPOracleState (sourceLength sourceIndex)
          (encodeBitInput input)) =
      some
        (Nat.pair (scheduledWidth outer sourceIndex)
          (encodeBoolFunction
            (recoveredOuterProofFunction (paddedOuterPCP outer) input))) := by
  have hpositive :
      1 ≤ recoveredProofAmplifierSeedBits outer sourceIndex input seedBits :=
    Nat.le_max_left _ _
  have hlengthBits :
      natBitLength (sourceLength sourceIndex) ≤
        recoveredProofAmplifierSeedBits outer sourceIndex input seedBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcompilerBits :
      recoveredProofRequestCompilerBits outer sourceIndex input seedBits ≤
        recoveredProofAmplifierSeedBits outer sourceIndex input seedBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpreserveBits :
      preserveRightBits
          (recoveredProofEncodingBits (paddedOuterPCP outer) input
            (sourceLength sourceIndex))
          (recoveredProofEncodingInput (paddedOuterPCP outer) input
            (sourceLength sourceIndex))
          (Nat.pair (sourceLength sourceIndex)
            (Nat.pair (scheduledWidth outer sourceIndex)
              (encodeBitInput input)))
          (encodeBoolFunction
            (recoveredOuterProofFunction (paddedOuterPCP outer) input)) ≤
        recoveredProofAmplifierSeedBits outer sourceIndex input seedBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hadapterBits :
      amplifierSeedRequestAdapterBits
          (encodeBoolFunction
            (recoveredOuterProofFunction (paddedOuterPCP outer) input))
          (sourceLength sourceIndex) (scheduledWidth outer sourceIndex)
          (encodeBitInput input) ≤
        recoveredProofAmplifierSeedBits outer sourceIndex input seedBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcompiler :=
    run_bits_mono
      (run_recoveredProofRequestCompilerProgram seed outer sourceIndex input
        seedBits seedFuel hseed)
      hcompilerBits
  have hpreserve :=
    run_bits_mono
      (run_preserveRightProgram recoveredProofEncodingProgram
        (sourceLength sourceIndex)
        (recoveredProofEncodingBits (paddedOuterPCP outer) input
          (sourceLength sourceIndex))
        (recoveredProofEncodingFuel (paddedOuterPCP outer) input
          (sourceLength sourceIndex))
        (recoveredProofEncodingInput (paddedOuterPCP outer) input
          (sourceLength sourceIndex))
        (Nat.pair (sourceLength sourceIndex)
          (Nat.pair (scheduledWidth outer sourceIndex)
            (encodeBitInput input)))
        (encodeBoolFunction
          (recoveredOuterProofFunction (paddedOuterPCP outer) input))
        (run_recoveredProofEncodingProgram (paddedOuterPCP outer) input
          (sourceLength sourceIndex)))
      hpreserveBits
  have hadapter :=
    run_bits_mono
      (run_amplifierSeedRequestAdapterProgram (sourceLength sourceIndex)
        (encodeBoolFunction
          (recoveredOuterProofFunction (paddedOuterPCP outer) input))
        (sourceLength sourceIndex) (scheduledWidth outer sourceIndex)
        (encodeBitInput input))
      hadapterBits
  have hsecond := run_linkPrograms hpositive hlengthBits hpreserve hadapter
  have hrun := run_linkPrograms hpositive hlengthBits hcompiler hsecond
  simpa only [recoveredProofAmplifierSeedProgram,
    recoveredProofAmplifierSeedFuel] using hrun

/-- The composed output is the published amplifier's own request code. -/
theorem scheduledAmplifierRequestCode
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) :
    Nat.pair (scheduledWidth outer sourceIndex)
        (encodeBoolFunction
          (recoveredOuterProofFunction (paddedOuterPCP outer) input)) =
      amplifierRequestCode
        (recoveredOuterProofFunction (paddedOuterPCP outer) input) :=
  rfl

end NearCubicWires.RecoveredProofAmplifierSeedProgram
