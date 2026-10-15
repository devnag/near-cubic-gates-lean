import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.TaggedProgramChoice
import Proof.Foundations.VerifiedLinker

/-!
# Canonical heterogeneous fork call

Many validators must derive two independent facts from the same canonical
word.  This adapter tags two in-machine copies, dispatches them through the
existing fixed choice program, and reuses the sole paired-call controller.
The caller supplies neither a duplicated value nor an intermediate result.
-/

namespace NearCubicWires.CanonicalForkCall

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

def forkTaggedInput (raw : ℕ) : ℕ :=
  Nat.pair (Nat.pair 0 raw) (Nat.pair 1 raw)

private def forkTaggedInputProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .pair 2 0 3 2
  , .set 2 1 3
  , .pair 2 0 4 4
  , .pair 3 4 0 5
  , .halt 0
  ]

private def forkTaggedInputBits (raw : ℕ) : ℕ :=
  max (natBitLength raw) (natBitLength (forkTaggedInput raw))

private theorem forkTaggedInputProgram_oracleFree :
    OracleFree forkTaggedInputProgram := by
  rfl

private theorem run_forkTaggedInputProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram forkTaggedInputProgram
        (forkTaggedInputBits raw) 6
        (initialNPOracleState inputLength raw) =
      some (forkTaggedInput raw) := by
  let first := Nat.pair 0 raw
  let second := Nat.pair 1 raw
  let output := Nat.pair first second
  have hraw : natBitLength raw ≤ forkTaggedInputBits raw :=
    Nat.le_max_left _ _
  have houtput :
      natBitLength output ≤ forkTaggedInputBits raw := by
    change
      natBitLength (forkTaggedInput raw) ≤ forkTaggedInputBits raw
    exact Nat.le_max_right _ _
  have hfirst : natBitLength first ≤ forkTaggedInputBits raw := by
    exact
      (natBitLength_mono (Nat.left_le_pair first second)).trans houtput
  have hsecond : natBitLength second ≤ forkTaggedInputBits raw := by
    exact
      (natBitLength_mono (Nat.right_le_pair first second)).trans houtput
  have hzero : natBitLength 0 ≤ forkTaggedInputBits raw := by
    exact (natBitLength_mono (Nat.zero_le raw)).trans hraw
  have hone : natBitLength 1 ≤ forkTaggedInputBits raw := by
    apply (natBitLength_mono ?_).trans hsecond
    exact Nat.left_le_pair 1 raw
  rw [show 6 = 5 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := first)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, first])
    hfirst]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := 1)
    (by rfl) rfl hone]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := second)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, second])
    hsecond]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, output, first, second])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        output, first, second, forkTaggedInput])
    houtput

def forkCallProgram
    (first second : NPOracleProgram) : NPOracleProgram :=
  linkPrograms forkTaggedInputProgram <|
    pairedCallProgram (taggedProgramChoice first second)

theorem forkCallProgram_oracleFree
    (first second : NPOracleProgram)
    (hfirst : OracleFree first) (hsecond : OracleFree second) :
    OracleFree (forkCallProgram first second) := by
  exact oracleFree_linkPrograms forkTaggedInputProgram_oracleFree <|
    pairedCallProgram_oracleFree
      (taggedProgramChoice first second)
      (taggedProgramChoice_oracleFree first second hfirst hsecond)

private def forkFirstChoiceBits
    (inputLength raw firstBits firstOutput : ℕ) : ℕ :=
  max firstBits <|
    max
      (natBitLength
        (Nat.pair inputLength (Nat.pair 0 raw)))
      (natBitLength firstOutput)

private def forkSecondChoiceBits
    (inputLength raw secondBits secondOutput : ℕ) : ℕ :=
  max secondBits <|
    max
      (natBitLength
        (Nat.pair inputLength (Nat.pair 1 raw)))
      (natBitLength secondOutput)

private def forkPairedBits
    (inputLength raw firstBits secondBits firstOutput secondOutput : ℕ) :
    ℕ :=
  pairedCallBits inputLength
    (forkFirstChoiceBits inputLength raw firstBits firstOutput)
    (forkSecondChoiceBits inputLength raw secondBits secondOutput)
    (Nat.pair 0 raw) (Nat.pair 1 raw) firstOutput secondOutput

def forkCallBits
    (inputLength raw firstBits secondBits firstOutput secondOutput : ℕ) :
    ℕ :=
  max (forkTaggedInputBits raw)
    (forkPairedBits inputLength raw firstBits secondBits
      firstOutput secondOutput)

def forkCallFuel
    (first second : NPOracleProgram)
    (firstFuel secondFuel : ℕ) : ℕ :=
  linkFuel (pairedCallProgram (taggedProgramChoice first second)) 6 <|
    pairedCallFuel (taggedProgramChoice first second)
      (taggedProgramChoiceFuel firstFuel)
      (taggedProgramChoiceFuel secondFuel)

theorem run_forkCallProgram
    (first second : NPOracleProgram)
    (inputLength raw firstBits secondBits firstFuel secondFuel
      firstOutput secondOutput : ℕ)
    (hfirst :
      runNPOracleProgram first firstBits firstFuel
          (initialNPOracleState inputLength raw) =
        some firstOutput)
    (hsecond :
      runNPOracleProgram second secondBits secondFuel
          (initialNPOracleState inputLength raw) =
        some secondOutput) :
    runNPOracleProgram (forkCallProgram first second)
        (forkCallBits inputLength raw firstBits secondBits
          firstOutput secondOutput)
        (forkCallFuel first second firstFuel secondFuel)
        (initialNPOracleState inputLength raw) =
      some (Nat.pair firstOutput secondOutput) := by
  let firstChoiceBits :=
    forkFirstChoiceBits inputLength raw firstBits firstOutput
  let secondChoiceBits :=
    forkSecondChoiceBits inputLength raw secondBits secondOutput
  let pairedBits :=
    forkPairedBits inputLength raw firstBits secondBits
      firstOutput secondOutput
  let maximumBits :=
    forkCallBits inputLength raw firstBits secondBits
      firstOutput secondOutput
  have htaggedBits :
      forkTaggedInputBits raw ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpairedBits : pairedBits ≤ maximumBits :=
    Nat.le_max_right _ _
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply (show natBitLength inputLength ≤ pairedBits from ?_).trans
      hpairedBits
    simp [pairedBits, forkPairedBits, pairedCallBits]
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have htagged :
      runNPOracleProgram forkTaggedInputProgram maximumBits 6
          (initialNPOracleState inputLength raw) =
        some (forkTaggedInput raw) := by
    exact run_bits_mono
      (run_forkTaggedInputProgram inputLength raw) htaggedBits
  have hfirstSource : firstBits ≤ firstChoiceBits := by
    exact Nat.le_max_left _ _
  have hfirstInput :
      natBitLength
          (Nat.pair inputLength (Nat.pair 0 raw)) ≤
        firstChoiceBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hfirstOutput :
      natBitLength firstOutput ≤ firstChoiceBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hfirstChoice :
      runNPOracleProgram (taggedProgramChoice first second)
          firstChoiceBits (taggedProgramChoiceFuel firstFuel)
          (initialNPOracleState inputLength (Nat.pair 0 raw)) =
        some firstOutput := by
    exact run_taggedProgramChoice_zero first second
      inputLength raw firstChoiceBits firstFuel firstOutput
      hfirstInput (run_bits_mono hfirst hfirstSource) hfirstOutput
  have hsecondSource : secondBits ≤ secondChoiceBits := by
    exact Nat.le_max_left _ _
  have hsecondInput :
      natBitLength
          (Nat.pair inputLength (Nat.pair 1 raw)) ≤
        secondChoiceBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsecondOutput :
      natBitLength secondOutput ≤ secondChoiceBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hsecondChoice :
      runNPOracleProgram (taggedProgramChoice first second)
          secondChoiceBits (taggedProgramChoiceFuel secondFuel)
          (initialNPOracleState inputLength (Nat.pair 1 raw)) =
        some secondOutput := by
    exact run_taggedProgramChoice_nonzero first second
      inputLength 1 raw secondChoiceBits secondFuel secondOutput
      one_ne_zero hsecondInput
      (run_bits_mono hsecond hsecondSource) hsecondOutput
  have hpaired :
      runNPOracleProgram
          (pairedCallProgram (taggedProgramChoice first second))
          pairedBits
          (pairedCallFuel (taggedProgramChoice first second)
            (taggedProgramChoiceFuel firstFuel)
            (taggedProgramChoiceFuel secondFuel))
          (initialNPOracleState inputLength (forkTaggedInput raw)) =
        some (Nat.pair firstOutput secondOutput) := by
    simpa [pairedBits, forkPairedBits, forkTaggedInput] using
      run_pairedCallProgram (taggedProgramChoice first second)
        inputLength firstChoiceBits secondChoiceBits
        (taggedProgramChoiceFuel firstFuel)
        (taggedProgramChoiceFuel secondFuel)
        (Nat.pair 0 raw) (Nat.pair 1 raw)
        firstOutput secondOutput hfirstChoice hsecondChoice
  have hpaired' :
      runNPOracleProgram
          (pairedCallProgram (taggedProgramChoice first second))
          maximumBits
          (pairedCallFuel (taggedProgramChoice first second)
            (taggedProgramChoiceFuel firstFuel)
            (taggedProgramChoiceFuel secondFuel))
          (initialNPOracleState inputLength (forkTaggedInput raw)) =
        some (Nat.pair firstOutput secondOutput) :=
    run_bits_mono hpaired hpairedBits
  have hrun :=
    run_linkPrograms hpositive hlength htagged hpaired'
  simpa [forkCallProgram, forkCallFuel] using hrun

end NearCubicWires.CanonicalForkCall
