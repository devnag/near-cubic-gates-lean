import Proof.MachineModel.BalancedClauseStreamFlattenProgram
import Proof.MachineModel.BitInputPrefixProgram
import Proof.MachineModel.CanonicalTwoPowProgram
import Proof.MachineModel.CircuitInputTautologyProgram
import Proof.MachineModel.TaggedProgramChoice
import Proof.MachineModel.RecoveredProofRequestCompilerProgram

namespace NearCubicWires.OuterProofRecoveryFormulaSeedProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CircuitInputCNF
open NearCubicWires.CircuitInputTautologyProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveredProofRequestCompilerProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## 1. The chunk schedule of the recovery formula -/

/-- Raw clauses of one decision row, indexed by the randomness code. -/
def outerProofRowStream
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (code : ℕ) : List ℕ :=
  (outerProofRowFormula pcp input
    (bitInputOfCode (pcp.nativeWidth n) code)).map rawEncodedClause

/-- The chunk emitted at one schedule index.  The dispatch bit is the bit at
position `pcp.nativeWidth n`; the remaining bits are the chunk's own address. -/
def outerProofChunkStream
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (index : ℕ) : List ℕ :=
  if index.testBit (pcp.nativeWidth n) then
    outerProofRowStream pcp input (bitInputPrefix (pcp.nativeWidth n) index)
  else
    [rawEncodedClause
      (circuitInputTautology (bitInputPrefix (pcp.nativeWidth n) index))]

private theorem circuitInputTautologies_eq_rangeMap (count : ℕ) :
    circuitInputTautologies count =
      (List.range count).map circuitInputTautology := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [circuitInputTautologies, inductionHypothesis, List.range_succ,
        List.map_append]
      rfl

private theorem flatten_singletons {α : Type} (values : List ℕ)
    (function : ℕ → α) :
    (values.map fun value => [function value]).flatten =
      values.map function := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp [inductionHypothesis]

private theorem map_flatMap_map {α β γ : Type}
    (values : List α) (chunk : α → List β) (function : β → γ) :
    (values.flatMap chunk).map function =
      (values.map fun value => (chunk value).map function).flatten := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp [inductionHypothesis]

private theorem testBit_of_lt_two_pow {width index : ℕ}
    (hindex : index < 2 ^ width) : index.testBit width = false := by
  simpa using Nat.testBit_lt_two_pow hindex

private theorem testBit_toNat (value bit : ℕ) :
    (value.testBit bit).toNat = value / 2 ^ bit % 2 := by
  unfold Nat.testBit
  rw [Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (value / 2 ^ bit) with hmod | hmod
  · simp [hmod]
  · simp [hmod]

private theorem testBit_add_two_pow {width offset : ℕ}
    (hoffset : offset < 2 ^ width) :
    (2 ^ width + offset).testBit width = true := by
  have hdiv : (2 ^ width + offset) / 2 ^ width = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have : (1 + 1) * 2 ^ width = 2 ^ width + 2 ^ width := by ring
      omega
  have htoNat : ((2 ^ width + offset).testBit width).toNat = 1 := by
    rw [testBit_toNat, hdiv]
  cases hbit : (2 ^ width + offset).testBit width with
  | false => rw [hbit] at htoNat; exact absurd htoNat (by decide)
  | true => rfl

private theorem prefix_add_two_pow {width offset : ℕ}
    (hoffset : offset < 2 ^ width) :
    bitInputPrefix width (2 ^ width + offset) = offset := by
  unfold bitInputPrefix
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt hoffset]

/-- The chunk schedule splits into the tautology block and the decision-row
block in the formula's own order. -/
theorem outerProofChunkStreams_eq_blocks
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n) :
    (List.range (2 ^ (pcp.nativeWidth n + 1))).map
        (outerProofChunkStream pcp input) =
      ((List.range (2 ^ pcp.nativeWidth n)).map fun address =>
          [rawEncodedClause (circuitInputTautology address)]) ++
        (List.range (2 ^ pcp.nativeWidth n)).map
          (outerProofRowStream pcp input) := by
  have htwo : 2 ^ (pcp.nativeWidth n + 1) =
      2 ^ pcp.nativeWidth n + 2 ^ pcp.nativeWidth n := by
    rw [pow_succ]
    omega
  rw [htwo, List.range_add, List.map_append, List.map_map]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · apply List.map_congr_left
    intro address haddress
    have hlt : address < 2 ^ pcp.nativeWidth n := List.mem_range.mp haddress
    simp only [outerProofChunkStream, testBit_of_lt_two_pow hlt,
      Bool.false_eq_true, if_false, bitInputPrefix,
      Nat.mod_eq_of_lt hlt]
  · apply List.map_congr_left
    intro offset hoffset
    have hlt : offset < 2 ^ pcp.nativeWidth n := List.mem_range.mp hoffset
    simp only [Function.comp_apply, outerProofChunkStream,
      testBit_add_two_pow hlt, if_true, prefix_add_two_pow hlt]

/-- Flattening the chunk schedule reproduces the raw clause list of the whole
C.12 recovery formula. -/
theorem outerProofChunkStreams_flatten
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n) :
    ((List.range (2 ^ (pcp.nativeWidth n + 1))).map
        (outerProofChunkStream pcp input)).flatten =
      (outerProofRecoveryFormula pcp input).map rawEncodedClause := by
  have htautology :
      ((List.range (2 ^ pcp.nativeWidth n)).map fun address =>
          [rawEncodedClause (circuitInputTautology address)]).flatten =
        (circuitInputTautologies (2 ^ pcp.nativeWidth n)).map
          rawEncodedClause := by
    rw [flatten_singletons, circuitInputTautologies_eq_rangeMap, List.map_map]
    rfl
  have hrows :
      ((List.range (2 ^ pcp.nativeWidth n)).map
          (outerProofRowStream pcp input)).flatten =
        ((allBitInputs (pcp.nativeWidth n)).flatMap
          (outerProofRowFormula pcp input)).map rawEncodedClause := by
    rw [map_flatMap_map, allBitInputs, List.map_map]
    rfl
  rw [outerProofChunkStreams_eq_blocks pcp input, List.flatten_append,
    htautology, hrows, outerProofRecoveryFormula, List.map_append]

/-- Exact stream identity consumed by the seed frame below. -/
theorem encodeTaggedList_outerProofChunkStreams
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n) :
    encodeTaggedList
        (((List.range (2 ^ (pcp.nativeWidth n + 1))).map
          (outerProofChunkStream pcp input)).flatten) =
      rawClauseStream (outerProofRecoveryFormula pcp input) := by
  rw [outerProofChunkStreams_flatten pcp input]
  rfl

/-! ## 2. The fixed chunk callee

The balanced range generator hands the callee `pair index context` at the
public length, with `context = pair width (encodeBitInput input)`.  Three fixed
adapters turn that into the tagged dispatcher's own ABI: the dispatch bit at
position `width` becomes the tag, and the low `width` bits become the shared
payload address. -/

/-- Dispatch bit of one schedule index. -/
def outerProofChunkTag (width index : ℕ) : ℕ :=
  (index.testBit width).toNat

/-- Shared payload of both branches: the local address beside the retained
context. -/
def outerProofChunkPayload (width index inputCode : ℕ) : ℕ :=
  Nat.pair (bitInputPrefix width index) (Nat.pair width inputCode)

private def outerProofChunkPreFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .pair 4 2 5 4
  , .testBit 2 4 6 5
  , .pair 6 3 7 6
  , .pair 5 7 0 7
  , .halt 0
  ]

@[simp] private theorem outerProofChunkPreFrameProgram_oracleFree :
    OracleFree outerProofChunkPreFrameProgram := by
  rfl

/-- Common frame of both branches: the local address request beside the
tagged context. -/
def outerProofChunkPreFrameOutput (width index inputCode : ℕ) : ℕ :=
  Nat.pair (bitInputPrefixInput width index)
    (Nat.pair (outerProofChunkTag width index) (Nat.pair width inputCode))

def outerProofChunkPreFrameBits (width index inputCode : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair index (Nat.pair width inputCode))
      (max (outerProofChunkTag width index)
        (outerProofChunkPreFrameOutput width index inputCode)))

private theorem run_outerProofChunkPreFrameProgram
    (inputLength width index inputCode : ℕ) :
    runNPOracleProgram outerProofChunkPreFrameProgram
        (outerProofChunkPreFrameBits width index inputCode) 8
        (initialNPOracleState inputLength
          (Nat.pair index (Nat.pair width inputCode))) =
      some (outerProofChunkPreFrameOutput width index inputCode) := by
  have hinputBits :
      natBitLength (Nat.pair index (Nat.pair width inputCode)) ≤
        outerProofChunkPreFrameBits width index inputCode :=
    natBitLength_mono (Nat.le_max_left _ _)
  have htagBits :
      natBitLength (outerProofChunkTag width index) ≤
        outerProofChunkPreFrameBits width index inputCode :=
    natBitLength_mono ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have houtputBits :
      natBitLength (outerProofChunkPreFrameOutput width index inputCode) ≤
        outerProofChunkPreFrameBits width index inputCode :=
    natBitLength_mono ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hindexBits :
      natBitLength index ≤
        outerProofChunkPreFrameBits width index inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair index (Nat.pair width inputCode))).trans hinputBits
  have hcontextBits :
      natBitLength (Nat.pair width inputCode) ≤
        outerProofChunkPreFrameBits width index inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair index (Nat.pair width inputCode))).trans hinputBits
  have hwidthBits :
      natBitLength width ≤
        outerProofChunkPreFrameBits width index inputCode :=
    (natBitLength_mono (Nat.left_le_pair width inputCode)).trans hcontextBits
  have hrequestBits :
      natBitLength (bitInputPrefixInput width index) ≤
        outerProofChunkPreFrameBits width index inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair (bitInputPrefixInput width index)
        (Nat.pair (outerProofChunkTag width index)
          (Nat.pair width inputCode)))).trans houtputBits
  have hframeBits :
      natBitLength
          (Nat.pair (outerProofChunkTag width index)
            (Nat.pair width inputCode)) ≤
        outerProofChunkPreFrameBits width index inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair (bitInputPrefixInput width index)
        (Nat.pair (outerProofChunkTag width index)
          (Nat.pair width inputCode)))).trans houtputBits
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hindexBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair width inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hwidthBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := bitInputPrefixInput width index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitInputPrefixInput])
    hrequestBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_testBit_instruction (value := outerProofChunkTag width index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, outerProofChunkTag])
    htagBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (outerProofChunkTag width index) (Nat.pair width inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := outerProofChunkPreFrameOutput width index inputCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        outerProofChunkPreFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

private def outerProofChunkPostFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 5 6 5
  , .pair 4 6 0 6
  , .halt 0
  ]

@[simp] private theorem outerProofChunkPostFrameProgram_oracleFree :
    OracleFree outerProofChunkPostFrameProgram := by
  rfl

def outerProofChunkPostFrameInput (width index inputCode : ℕ) : ℕ :=
  Nat.pair (bitInputPrefix width index)
    (Nat.pair (outerProofChunkTag width index) (Nat.pair width inputCode))

def outerProofChunkPostFrameOutput (width index inputCode : ℕ) : ℕ :=
  Nat.pair (outerProofChunkTag width index)
    (outerProofChunkPayload width index inputCode)

def outerProofChunkPostFrameBits (width index inputCode : ℕ) : ℕ :=
  natBitLength
    (max (outerProofChunkPostFrameInput width index inputCode)
      (outerProofChunkPostFrameOutput width index inputCode))

private theorem run_outerProofChunkPostFrameProgram
    (inputLength width index inputCode : ℕ) :
    runNPOracleProgram outerProofChunkPostFrameProgram
        (outerProofChunkPostFrameBits width index inputCode) 7
        (initialNPOracleState inputLength
          (outerProofChunkPostFrameInput width index inputCode)) =
      some (outerProofChunkPostFrameOutput width index inputCode) := by
  have hinputBits :
      natBitLength (outerProofChunkPostFrameInput width index inputCode) ≤
        outerProofChunkPostFrameBits width index inputCode :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength (outerProofChunkPostFrameOutput width index inputCode) ≤
        outerProofChunkPostFrameBits width index inputCode :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hlocalBits :
      natBitLength (bitInputPrefix width index) ≤
        outerProofChunkPostFrameBits width index inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair (bitInputPrefix width index)
        (Nat.pair (outerProofChunkTag width index)
          (Nat.pair width inputCode)))).trans hinputBits
  have htaggedBits :
      natBitLength
          (Nat.pair (outerProofChunkTag width index)
            (Nat.pair width inputCode)) ≤
        outerProofChunkPostFrameBits width index inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair (bitInputPrefix width index)
        (Nat.pair (outerProofChunkTag width index)
          (Nat.pair width inputCode)))).trans hinputBits
  have htagBits :
      natBitLength (outerProofChunkTag width index) ≤
        outerProofChunkPostFrameBits width index inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair (outerProofChunkTag width index)
        (Nat.pair width inputCode))).trans htaggedBits
  have hcontextBits :
      natBitLength (Nat.pair width inputCode) ≤
        outerProofChunkPostFrameBits width index inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair (outerProofChunkTag width index)
        (Nat.pair width inputCode))).trans htaggedBits
  have hpayloadBits :
      natBitLength (outerProofChunkPayload width index inputCode) ≤
        outerProofChunkPostFrameBits width index inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair (outerProofChunkTag width index)
        (outerProofChunkPayload width index inputCode))).trans houtputBits
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := bitInputPrefix width index)
    (by rfl) rfl
    (by simp [initialNPOracleState, outerProofChunkPostFrameInput])
    hlocalBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (outerProofChunkTag width index) (Nat.pair width inputCode))
    (by rfl) rfl
    (by
      simp [initialNPOracleState, outerProofChunkPostFrameInput,
        NPOracleState.write, NPOracleState.jump])
    htaggedBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := outerProofChunkTag width index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htagBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair width inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := outerProofChunkPayload width index inputCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, outerProofChunkPayload])
    hpayloadBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := outerProofChunkPostFrameOutput width index inputCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        outerProofChunkPostFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- The tagged dispatcher's ABI, assembled by the two frames around the shared
low-bit normalizer. -/
def outerProofChunkFrameProgram : NPOracleProgram :=
  linkPrograms outerProofChunkPreFrameProgram
    (linkPrograms (preserveRightProgram bitInputPrefixProgram)
      outerProofChunkPostFrameProgram)

theorem outerProofChunkFrameProgram_oracleFree :
    OracleFree outerProofChunkFrameProgram := by
  apply oracleFree_linkPrograms
  · exact outerProofChunkPreFrameProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact preserveRightProgram_oracleFree bitInputPrefixProgram
        bitInputPrefixProgram_oracleFree
    · exact outerProofChunkPostFrameProgram_oracleFree

def outerProofChunkFrameFuel (width index : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram bitInputPrefixProgram)
      outerProofChunkPostFrameProgram)
    8
    (linkFuel outerProofChunkPostFrameProgram
      (preserveRightFuel (bitInputPrefixFuel width index)) 7)

def outerProofChunkFrameBits
    (inputLength width index inputCode : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max (outerProofChunkPreFrameBits width index inputCode) <|
        max
          (preserveRightBits (bitInputPrefixBits width index)
            (bitInputPrefixInput width index)
            (Nat.pair (outerProofChunkTag width index)
              (Nat.pair width inputCode))
            (bitInputPrefix width index))
          (outerProofChunkPostFrameBits width index inputCode)

private theorem run_bitInputPrefixExact
    (inputLength width value : ℕ) :
    runNPOracleProgram bitInputPrefixProgram
        (bitInputPrefixBits width value) (bitInputPrefixFuel width value)
        (initialNPOracleState inputLength
          (bitInputPrefixInput width value)) =
      some (bitInputPrefix width value) :=
  run_bitInputPrefixProgram inputLength width value
    (bitInputPrefixBits width value) 0 (Nat.le_refl _)

private theorem run_outerProofChunkPrefixStage
    (inputLength width index inputCode : ℕ) :
    runNPOracleProgram (preserveRightProgram bitInputPrefixProgram)
        (preserveRightBits (bitInputPrefixBits width index)
          (bitInputPrefixInput width index)
          (Nat.pair (outerProofChunkTag width index)
            (Nat.pair width inputCode))
          (bitInputPrefix width index))
        (preserveRightFuel (bitInputPrefixFuel width index))
        (initialNPOracleState inputLength
          (outerProofChunkPreFrameOutput width index inputCode)) =
      some (outerProofChunkPostFrameInput width index inputCode) :=
  run_preserveRightProgram bitInputPrefixProgram inputLength
    (bitInputPrefixBits width index) (bitInputPrefixFuel width index)
    (bitInputPrefixInput width index)
    (Nat.pair (outerProofChunkTag width index) (Nat.pair width inputCode))
    (bitInputPrefix width index)
    (run_bitInputPrefixExact inputLength width index)

private theorem run_outerProofChunkTailStage
    (inputLength width index inputCode maximumBits : ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlengthBits : natBitLength inputLength ≤ maximumBits)
    (hprefixBits :
      preserveRightBits (bitInputPrefixBits width index)
          (bitInputPrefixInput width index)
          (Nat.pair (outerProofChunkTag width index)
            (Nat.pair width inputCode))
          (bitInputPrefix width index) ≤ maximumBits)
    (hpostBits :
      outerProofChunkPostFrameBits width index inputCode ≤ maximumBits) :
    runNPOracleProgram
        (linkPrograms (preserveRightProgram bitInputPrefixProgram)
          outerProofChunkPostFrameProgram)
        maximumBits
        (linkFuel outerProofChunkPostFrameProgram
          (preserveRightFuel (bitInputPrefixFuel width index)) 7)
        (initialNPOracleState inputLength
          (outerProofChunkPreFrameOutput width index inputCode)) =
      some (outerProofChunkPostFrameOutput width index inputCode) :=
  run_linkPrograms hpositive hlengthBits
    (run_bits_mono
      (run_outerProofChunkPrefixStage inputLength width index inputCode)
      hprefixBits)
    (run_bits_mono
      (run_outerProofChunkPostFrameProgram inputLength width index inputCode)
      hpostBits)

private theorem run_outerProofChunkFrameProgram
    (inputLength width index inputCode : ℕ) :
    runNPOracleProgram outerProofChunkFrameProgram
        (outerProofChunkFrameBits inputLength width index inputCode)
        (outerProofChunkFrameFuel width index)
        (initialNPOracleState inputLength
          (Nat.pair index (Nat.pair width inputCode))) =
      some (outerProofChunkPostFrameOutput width index inputCode) := by
  have hpositive :
      1 ≤ outerProofChunkFrameBits inputLength width index inputCode :=
    Nat.le_max_left _ _
  have hlengthBits :
      natBitLength inputLength ≤
        outerProofChunkFrameBits inputLength width index inputCode :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreBits :
      outerProofChunkPreFrameBits width index inputCode ≤
        outerProofChunkFrameBits inputLength width index inputCode :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprefixBits :
      preserveRightBits (bitInputPrefixBits width index)
          (bitInputPrefixInput width index)
          (Nat.pair (outerProofChunkTag width index)
            (Nat.pair width inputCode))
          (bitInputPrefix width index) ≤
        outerProofChunkFrameBits inputLength width index inputCode :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpostBits :
      outerProofChunkPostFrameBits width index inputCode ≤
        outerProofChunkFrameBits inputLength width index inputCode :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpre :=
    run_bits_mono
      (run_outerProofChunkPreFrameProgram inputLength width index inputCode)
      hpreBits
  have hsecond :=
    run_outerProofChunkTailStage inputLength width index inputCode
      (outerProofChunkFrameBits inputLength width index inputCode)
      hpositive hlengthBits hprefixBits hpostBits
  exact run_linkPrograms hpositive hlengthBits hpre hsecond

/-! ### The zero-tag branch: one published input tautology -/

private def outerProofChunkTakeLeftProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] private theorem outerProofChunkTakeLeftProgram_oracleFree :
    OracleFree outerProofChunkTakeLeftProgram := by
  rfl

private theorem run_outerProofChunkTakeLeftProgram
    {maximumBits : ℕ} (inputLength left right : ℕ)
    (hleftBits : natBitLength left ≤ maximumBits) :
    runNPOracleProgram outerProofChunkTakeLeftProgram maximumBits 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some left := by
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hleftBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hleftBits

/-- The zero-tag callee: drop the retained context and emit the published input
tautology of the requested proof-table address. -/
def outerProofTautologyEntryProgram : NPOracleProgram :=
  linkPrograms outerProofChunkTakeLeftProgram circuitInputTautologyProgram

theorem outerProofTautologyEntryProgram_oracleFree :
    OracleFree outerProofTautologyEntryProgram := by
  apply oracleFree_linkPrograms
  · exact outerProofChunkTakeLeftProgram_oracleFree
  · exact circuitInputTautologyProgram_oracleFree

def outerProofTautologyEntryFuel : ℕ :=
  linkFuel circuitInputTautologyProgram 2 circuitInputTautologyFuel

private theorem run_outerProofTautologyEntryStage
    (inputLength width index inputCode maximumBits : ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlengthBits : natBitLength inputLength ≤ maximumBits)
    (hlocalBits : natBitLength (bitInputPrefix width index) ≤ maximumBits)
    (htautologyBits :
      circuitInputTautologyMaximumBits (bitInputPrefix width index) ≤
        maximumBits) :
    runNPOracleProgram outerProofTautologyEntryProgram maximumBits
        outerProofTautologyEntryFuel
        (initialNPOracleState inputLength
          (outerProofChunkPayload width index inputCode)) =
      some
        (rawClauseStream
          [circuitInputTautology (bitInputPrefix width index)]) :=
  run_linkPrograms hpositive hlengthBits
    (run_outerProofChunkTakeLeftProgram inputLength
      (bitInputPrefix width index) (Nat.pair width inputCode) hlocalBits)
    (run_bits_mono
      (run_circuitInputTautologyProgram inputLength
        (bitInputPrefix width index))
      htautologyBits)

/-! ### The fixed chunk callee -/

/-- The exact chunk code emitted at one schedule index. -/
def outerProofChunkOutput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (index : ℕ) : ℕ :=
  encodeTaggedList (outerProofChunkStream pcp input index)

private theorem outerProofChunkOutput_tautology
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    {index : ℕ} (hindex : index.testBit (pcp.nativeWidth n) = false) :
    outerProofChunkOutput pcp input index =
      rawClauseStream
        [circuitInputTautology
          (bitInputPrefix (pcp.nativeWidth n) index)] := by
  simp only [outerProofChunkOutput, outerProofChunkStream, hindex,
    Bool.false_eq_true, if_false]
  rfl

private theorem outerProofChunkTag_false {width index : ℕ}
    (hindex : index.testBit width = false) :
    outerProofChunkTag width index = 0 := by
  simp [outerProofChunkTag, hindex]

private theorem outerProofChunkTag_true {width index : ℕ}
    (hindex : index.testBit width = true) :
    outerProofChunkTag width index = 1 := by
  simp [outerProofChunkTag, hindex]

/-- One fixed chunk callee: the frame adapters, then the shared tagged
dispatcher between the published tautology emitter and the named row stage. -/
def outerProofChunkProgram (row : NPOracleProgram) : NPOracleProgram :=
  linkPrograms outerProofChunkFrameProgram
    (taggedProgramChoice outerProofTautologyEntryProgram row)

theorem outerProofChunkProgram_oracleFree
    {row : NPOracleProgram} (hrow : OracleFree row) :
    OracleFree (outerProofChunkProgram row) := by
  apply oracleFree_linkPrograms
  · exact outerProofChunkFrameProgram_oracleFree
  · exact taggedProgramChoice_oracleFree outerProofTautologyEntryProgram row
      outerProofTautologyEntryProgram_oracleFree hrow

def outerProofChunkSourceFuel (width index rowFuel : ℕ) : ℕ :=
  if index.testBit width then rowFuel else outerProofTautologyEntryFuel

def outerProofChunkFuel
    (row : NPOracleProgram) (width index rowFuel : ℕ) : ℕ :=
  linkFuel (taggedProgramChoice outerProofTautologyEntryProgram row)
    (outerProofChunkFrameFuel width index)
    (taggedProgramChoiceFuel (outerProofChunkSourceFuel width index rowFuel))

def outerProofChunkBits
    (inputLength width index inputCode output rowBits : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max (outerProofChunkFrameBits inputLength width index inputCode) <|
        max
          (natBitLength
            (Nat.pair inputLength
              (outerProofChunkPostFrameOutput width index inputCode))) <|
          max (natBitLength output) <|
            max (natBitLength (bitInputPrefix width index)) <|
              max
                (circuitInputTautologyMaximumBits
                  (bitInputPrefix width index))
                rowBits

/-- Exact chunk emission.  At a tautology index the callee is unconditional; at
a decision-row index it forwards to the single named row stage. -/
theorem run_outerProofChunkProgram
    (row : NPOracleProgram)
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (index rowBits rowFuel : ℕ)
    (hrow : index.testBit (pcp.nativeWidth n) = true →
      runNPOracleProgram row rowBits rowFuel
          (initialNPOracleState n
            (outerProofChunkPayload (pcp.nativeWidth n) index
              (encodeBitInput input))) =
        some (outerProofChunkOutput pcp input index)) :
    runNPOracleProgram (outerProofChunkProgram row)
        (outerProofChunkBits n (pcp.nativeWidth n) index (encodeBitInput input)
          (outerProofChunkOutput pcp input index) rowBits)
        (outerProofChunkFuel row (pcp.nativeWidth n) index rowFuel)
        (initialNPOracleState n
          (Nat.pair index
            (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))) =
      some (outerProofChunkOutput pcp input index) := by
  set width := pcp.nativeWidth n with hwidth
  set inputCode := encodeBitInput input with hinputCode
  set output := outerProofChunkOutput pcp input index with houtput
  set maximumBits :=
    outerProofChunkBits n width index inputCode output rowBits with hmaximumBits
  have hpositive : 1 ≤ maximumBits :=
    Nat.le_max_left _ _
  have hlengthBits : natBitLength n ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hframeBits :
      outerProofChunkFrameBits n width index inputCode ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hchoiceBits :
      natBitLength
          (Nat.pair n (outerProofChunkPostFrameOutput width index inputCode)) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have houtputBits : natBitLength output ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlocalBits :
      natBitLength (bitInputPrefix width index) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have htautologyBits :
      circuitInputTautologyMaximumBits (bitInputPrefix width index) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrowBits : rowBits ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hframe :=
    run_bits_mono
      (run_outerProofChunkFrameProgram n width index inputCode)
      hframeBits
  have hchoice :
      runNPOracleProgram
          (taggedProgramChoice outerProofTautologyEntryProgram row)
          maximumBits
          (taggedProgramChoiceFuel
            (outerProofChunkSourceFuel width index rowFuel))
          (initialNPOracleState n
            (outerProofChunkPostFrameOutput width index inputCode)) =
        some output := by
    cases hindex : index.testBit width with
    | false =>
        have hsource :=
          run_outerProofTautologyEntryStage n width index inputCode
            maximumBits hpositive hlengthBits hlocalBits htautologyBits
        have hvalue :
            output =
              rawClauseStream
                [circuitInputTautology (bitInputPrefix width index)] :=
          outerProofChunkOutput_tautology pcp input hindex
        rw [hvalue] at houtputBits ⊢
        rw [show outerProofChunkPostFrameOutput width index inputCode =
            Nat.pair 0 (outerProofChunkPayload width index inputCode) by
          rw [outerProofChunkPostFrameOutput, outerProofChunkTag_false hindex]]
        rw [show outerProofChunkSourceFuel width index rowFuel =
            outerProofTautologyEntryFuel by
          rw [outerProofChunkSourceFuel, hindex, if_neg (by simp)]]
        refine run_taggedProgramChoice_zero outerProofTautologyEntryProgram row
          n (outerProofChunkPayload width index inputCode) maximumBits
          outerProofTautologyEntryFuel _ ?_ hsource houtputBits
        rw [show Nat.pair 0 (outerProofChunkPayload width index inputCode) =
            outerProofChunkPostFrameOutput width index inputCode by
          rw [outerProofChunkPostFrameOutput, outerProofChunkTag_false hindex]]
        exact hchoiceBits
    | true =>
        have hsource := run_bits_mono (hrow hindex) hrowBits
        rw [show outerProofChunkPostFrameOutput width index inputCode =
            Nat.pair 1 (outerProofChunkPayload width index inputCode) by
          rw [outerProofChunkPostFrameOutput, outerProofChunkTag_true hindex]]
        rw [show outerProofChunkSourceFuel width index rowFuel = rowFuel by
          rw [outerProofChunkSourceFuel, hindex, if_pos rfl]]
        refine run_taggedProgramChoice_nonzero outerProofTautologyEntryProgram
          row n 1 (outerProofChunkPayload width index inputCode) maximumBits
          rowFuel output (by omega) ?_ hsource houtputBits
        rw [show Nat.pair 1 (outerProofChunkPayload width index inputCode) =
            outerProofChunkPostFrameOutput width index inputCode by
          rw [outerProofChunkPostFrameOutput, outerProofChunkTag_true hindex]]
        exact hchoiceBits
  exact run_linkPrograms hpositive hlengthBits hframe hchoice

/-! ## 3. The whole raw clause stream

One canonical balanced range, one canonical balanced call, and the canonical
clause-stream flattener turn the schedule parameters into the exact raw clause
stream of the C.12 recovery formula. -/

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) : value ≤ values.foldr max 0 := by
  induction values with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons head rest inductionHypothesis =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · exact hhead ▸ Nat.le_max_left _ _
      · exact (inductionHypothesis htail).trans (Nat.le_max_right _ _)

/-- The schedule's atom list, in the generator's own order. -/
def outerProofRangeAtoms (inputLength width inputCode : ℕ) : List ℕ :=
  (List.range (2 ^ (width + 1))).map fun index =>
    balancedRangeRequestAtom inputLength index (Nat.pair width inputCode)

private theorem balancedRangeRequestAtoms_eq_outerProofRangeAtoms
    (inputLength width inputCode : ℕ) :
    balancedRangeRequestAtoms inputLength (Nat.pair width inputCode) 0
        (2 ^ (width + 1)) =
      outerProofRangeAtoms inputLength width inputCode := by
  rw [balancedRangeRequestAtoms_eq_map_range]
  simp [outerProofRangeAtoms]

/-- Schedule index recovered from one generated atom. -/
def outerProofAtomIndex (atom : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair atom).2).1

@[simp] theorem outerProofAtomIndex_atom
    (inputLength index context : ℕ) :
    outerProofAtomIndex (balancedRangeRequestAtom inputLength index context) =
      index := by
  simp [outerProofAtomIndex, balancedRangeRequestAtom]

def outerProofAtomOutput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (atom : ℕ) : ℕ :=
  outerProofChunkOutput pcp input (outerProofAtomIndex atom)

def outerProofAtomCallFuel
    (row : NPOracleProgram) (width : ℕ) (rowFuel : ℕ → ℕ) (atom : ℕ) : ℕ :=
  outerProofChunkFuel row width (outerProofAtomIndex atom)
    (rowFuel (bitInputPrefix width (outerProofAtomIndex atom)))

def outerProofAtomCallBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (rowBits : ℕ → ℕ) (atom : ℕ) : ℕ :=
  outerProofChunkBits n (pcp.nativeWidth n) (outerProofAtomIndex atom)
    (encodeBitInput input)
    (outerProofChunkOutput pcp input (outerProofAtomIndex atom))
    (rowBits
      (bitInputPrefix (pcp.nativeWidth n) (outerProofAtomIndex atom)))

private theorem outerProofRangeAtoms_outputs
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n) :
    (outerProofRangeAtoms n (pcp.nativeWidth n)
        (encodeBitInput input)).map (outerProofAtomOutput pcp input) =
      ((List.range (2 ^ (pcp.nativeWidth n + 1))).map
        (outerProofChunkStream pcp input)).map encodeTaggedList := by
  rw [outerProofRangeAtoms, List.map_map, List.map_map]
  apply List.map_congr_left
  intro index _
  simp [outerProofAtomOutput, outerProofChunkOutput]

/-- The fixed stream builder.  Its only parameter is the named row stage. -/
def outerProofFormulaStreamProgram (row : NPOracleProgram) : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram
    (linkPrograms outerProofChunkTakeLeftProgram
      (linkPrograms (balancedCallProgram (outerProofChunkProgram row))
        balancedClauseStreamFlattenProgram))

theorem outerProofFormulaStreamProgram_oracleFree
    {row : NPOracleProgram} (hrow : OracleFree row) :
    OracleFree (outerProofFormulaStreamProgram row) := by
  apply oracleFree_linkPrograms
  · exact generatedBalancedRangeProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact outerProofChunkTakeLeftProgram_oracleFree
    · apply oracleFree_linkPrograms
      · exact balancedCallProgram_oracleFree
          (outerProofChunkProgram_oracleFree hrow)
      · exact balancedClauseStreamFlattenProgram_oracleFree

def outerProofFormulaStreamFuel
    (row : NPOracleProgram)
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (rowFuel : ℕ → ℕ) : ℕ :=
  linkFuel
    (linkPrograms outerProofChunkTakeLeftProgram
      (linkPrograms (balancedCallProgram (outerProofChunkProgram row))
        balancedClauseStreamFlattenProgram))
    (generatedBalancedRangeFuel n (2 ^ (pcp.nativeWidth n + 1))
      (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))
    (linkFuel
      (linkPrograms (balancedCallProgram (outerProofChunkProgram row))
        balancedClauseStreamFlattenProgram)
      2
      (linkFuel balancedClauseStreamFlattenProgram
        (balancedCallFuel (outerProofChunkProgram row)
          (outerProofAtomCallFuel row (pcp.nativeWidth n) rowFuel)
          (outerProofRangeAtoms n (pcp.nativeWidth n) (encodeBitInput input)))
        (balancedClauseStreamFlattenFuel
          ((List.range (2 ^ (pcp.nativeWidth n + 1))).map
            (outerProofChunkStream pcp input)))))

def outerProofFormulaStreamBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (rowBits : ℕ → ℕ) : ℕ :=
  max 1 <|
    max (natBitLength n) <|
      max
        (generatedBalancedRangeRequiredBits n (2 ^ (pcp.nativeWidth n + 1))
          (Nat.pair (pcp.nativeWidth n) (encodeBitInput input))) <|
        max
          (natBitLength
            (encodeBalancedList
              (outerProofRangeAtoms n (pcp.nativeWidth n)
                (encodeBitInput input)))) <|
          max
            (balancedCallRequiredBits (outerProofAtomOutput pcp input)
              (outerProofRangeAtoms n (pcp.nativeWidth n)
                (encodeBitInput input))) <|
            max
              (((outerProofRangeAtoms n (pcp.nativeWidth n)
                (encodeBitInput input)).map
                  (outerProofAtomCallBits pcp input rowBits)).foldr max 0)
              (balancedClauseStreamFlattenMaximumBits
                ((List.range (2 ^ (pcp.nativeWidth n + 1))).map
                  (outerProofChunkStream pcp input)))

/-- Exact stream construction.  Modulo the single named row stage, one fixed
oracle-free program emits the whole raw clause stream of the C.12 recovery
formula from the schedule parameters. -/
theorem run_outerProofFormulaStreamProgram
    (row : NPOracleProgram)
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (rowBits rowFuel : ℕ → ℕ)
    (hrow : ∀ code, code < 2 ^ pcp.nativeWidth n →
      runNPOracleProgram row (rowBits code) (rowFuel code)
          (initialNPOracleState n
            (Nat.pair code
              (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))) =
        some (encodeTaggedList (outerProofRowStream pcp input code))) :
    runNPOracleProgram (outerProofFormulaStreamProgram row)
        (outerProofFormulaStreamBits pcp input rowBits)
        (outerProofFormulaStreamFuel row pcp input rowFuel)
        (initialNPOracleState n
          (generatedBalancedRangeInput (2 ^ (pcp.nativeWidth n + 1))
            (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))) =
      some (rawClauseStream (outerProofRecoveryFormula pcp input)) := by
  set width := pcp.nativeWidth n with hwidth
  set inputCode := encodeBitInput input with hinputCode
  set atoms := outerProofRangeAtoms n width inputCode with hatoms
  set streams :=
    (List.range (2 ^ (width + 1))).map (outerProofChunkStream pcp input)
    with hstreams
  set maximumBits := outerProofFormulaStreamBits pcp input rowBits
    with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength n ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hrangeBits :
      generatedBalancedRangeRequiredBits n (2 ^ (width + 1))
          (Nat.pair width inputCode) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlistBits :
      natBitLength (encodeBalancedList atoms) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      balancedCallRequiredBits (outerProofAtomOutput pcp input) atoms ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hatomBits :
      (atoms.map (outerProofAtomCallBits pcp input rowBits)).foldr max 0 ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hflattenBits :
      balancedClauseStreamFlattenMaximumBits streams ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel n (2 ^ (width + 1))
            (Nat.pair width inputCode))
          (initialNPOracleState n
            (generatedBalancedRangeInput (2 ^ (width + 1))
              (Nat.pair width inputCode))) =
        some (Nat.pair (encodeBalancedList atoms) (Nat.pair width inputCode)) := by
    rw [hatoms, ← balancedRangeRequestAtoms_eq_outerProofRangeAtoms]
    exact run_bits_mono
      (run_generatedBalancedRangeProgram n (2 ^ (width + 1))
        (Nat.pair width inputCode))
      hrangeBits
  have htake :
      runNPOracleProgram outerProofChunkTakeLeftProgram maximumBits 2
          (initialNPOracleState n
            (Nat.pair (encodeBalancedList atoms) (Nat.pair width inputCode))) =
        some (encodeBalancedList atoms) :=
    run_outerProofChunkTakeLeftProgram n (encodeBalancedList atoms)
      (Nat.pair width inputCode) hlistBits
  have hcall :
      runNPOracleProgram (balancedCallProgram (outerProofChunkProgram row))
          maximumBits
          (balancedCallFuel (outerProofChunkProgram row)
            (outerProofAtomCallFuel row width rowFuel) atoms)
          (initialNPOracleState n (encodeBalancedList atoms)) =
        some (encodeBalancedList (streams.map encodeTaggedList)) := by
    rw [← outerProofRangeAtoms_outputs pcp input]
    refine run_balancedCallProgram_from n atoms
      (outerProofAtomCallFuel row width rowFuel)
      (outerProofAtomOutput pcp input) hcallBits ?_
    intro atom hatom
    have hcalleeBits :
        outerProofAtomCallBits pcp input rowBits atom ≤ maximumBits :=
      (le_foldr_max_of_mem (List.mem_map_of_mem hatom)).trans hatomBits
    rw [hatoms, outerProofRangeAtoms, List.mem_map] at hatom
    obtain ⟨index, _hindex, hatomEq⟩ := hatom
    rw [← hatomEq] at hcalleeBits ⊢
    simp only [outerProofAtomCallBits, outerProofAtomIndex_atom]
      at hcalleeBits
    have hleft :
        (Nat.unpair
          (balancedRangeRequestAtom n index (Nat.pair width inputCode))).1 =
          n := by
      simp [balancedRangeRequestAtom]
    have hright :
        (Nat.unpair
          (balancedRangeRequestAtom n index (Nat.pair width inputCode))).2 =
          Nat.pair index (Nat.pair width inputCode) := by
      simp [balancedRangeRequestAtom]
    rw [hleft, hright]
    simp only [outerProofAtomOutput, outerProofAtomCallFuel,
      outerProofAtomIndex_atom]
    refine run_bits_mono
      (run_outerProofChunkProgram row pcp input index
        (rowBits (bitInputPrefix width index))
        (rowFuel (bitInputPrefix width index)) ?_)
      hcalleeBits
    intro hbit
    have hlt : bitInputPrefix width index < 2 ^ width :=
      Nat.mod_lt _ (pow_pos (by omega : 0 < 2) width)
    have hvalue :
        outerProofChunkOutput pcp input index =
          encodeTaggedList
            (outerProofRowStream pcp input (bitInputPrefix width index)) := by
      simp only [outerProofChunkOutput, outerProofChunkStream, hbit, if_true]
      rfl
    rw [hvalue, outerProofChunkPayload]
    exact hrow (bitInputPrefix width index) hlt
  have hflatten :
      runNPOracleProgram balancedClauseStreamFlattenProgram maximumBits
          (balancedClauseStreamFlattenFuel streams)
          (initialNPOracleState n
            (encodeBalancedList (streams.map encodeTaggedList))) =
        some (encodeTaggedList streams.flatten) :=
    run_bits_mono (run_balancedClauseStreamFlattenProgram streams n)
      hflattenBits
  have hthird := run_linkPrograms hpositive hlengthBits hcall hflatten
  have hsecond := run_linkPrograms hpositive hlengthBits htake hthird
  have hrun := run_linkPrograms hpositive hlengthBits hrange hsecond
  rw [← encodeTaggedList_outerProofChunkStreams pcp input]
  exact hrun

/-! ## 4. The seed frame

The seed request of `RecoveredProofRequestCompilerProgram` is the emitted
stream beside the proof-address count and the retained schedule frame.  Three
straight-line adapters and two applications of the published dyadic
exponential produce it; the scheduled width enters as the single immediate of
the instruction stream. -/

private theorem two_pow_succ (width : ℕ) :
    2 ^ width + 2 ^ width = 2 ^ (width + 1) := by
  rw [pow_succ]
  omega

private def outerProofSeedPreludeProgram (width : ℕ) : NPOracleProgram :=
  [ .set 2 width 1
  , .pair 2 0 3 2
  , .pair 2 3 0 3
  , .halt 0
  ]

@[simp] private theorem outerProofSeedPreludeProgram_oracleFree
    (width : ℕ) : OracleFree (outerProofSeedPreludeProgram width) := by
  rfl

def outerProofSeedPreludeOutput (width inputCode : ℕ) : ℕ :=
  Nat.pair width (Nat.pair width inputCode)

def outerProofSeedPreludeBits (width inputCode : ℕ) : ℕ :=
  natBitLength (outerProofSeedPreludeOutput width inputCode)

private theorem run_outerProofSeedPreludeProgram
    (inputLength width inputCode : ℕ) :
    runNPOracleProgram (outerProofSeedPreludeProgram width)
        (outerProofSeedPreludeBits width inputCode) 4
        (initialNPOracleState inputLength inputCode) =
      some (outerProofSeedPreludeOutput width inputCode) := by
  have houtputBits :
      natBitLength (outerProofSeedPreludeOutput width inputCode) ≤
        outerProofSeedPreludeBits width inputCode :=
    Nat.le_refl _
  have hwidthBits :
      natBitLength width ≤ outerProofSeedPreludeBits width inputCode :=
    natBitLength_mono (Nat.left_le_pair width (Nat.pair width inputCode))
  have hcontextBits :
      natBitLength (Nat.pair width inputCode) ≤
        outerProofSeedPreludeBits width inputCode :=
    natBitLength_mono (Nat.right_le_pair width (Nat.pair width inputCode))
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := width) (by rfl) rfl hwidthBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair width inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := outerProofSeedPreludeOutput width inputCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        outerProofSeedPreludeOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

def outerProofSeedRangeFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .add 2 2 4 3
  , .pair 4 3 5 4
  , .copy 1 6 5
  , .pair 6 3 7 6
  , .pair 2 7 8 7
  , .pair 5 8 0 8
  , .halt 0
  ]

@[simp] theorem outerProofSeedRangeFrameProgram_oracleFree :
    OracleFree outerProofSeedRangeFrameProgram := by
  rfl

def outerProofSeedRangeFrameInput (width inputCode : ℕ) : ℕ :=
  Nat.pair (2 ^ width) (Nat.pair width inputCode)

/-- The retained frame threaded past the stream builder: the proof-address
count, the public length, and the schedule context. -/
def outerProofSeedRetainedFrame
    (inputLength width inputCode : ℕ) : ℕ :=
  Nat.pair (2 ^ width)
    (Nat.pair inputLength (Nat.pair width inputCode))

def outerProofSeedRangeFrameOutput
    (inputLength width inputCode : ℕ) : ℕ :=
  Nat.pair
    (generatedBalancedRangeInput (2 ^ (width + 1))
      (Nat.pair width inputCode))
    (outerProofSeedRetainedFrame inputLength width inputCode)

def outerProofSeedRangeFrameBits
    (inputLength width inputCode : ℕ) : ℕ :=
  natBitLength
    (max (outerProofSeedRangeFrameInput width inputCode)
      (outerProofSeedRangeFrameOutput inputLength width inputCode))

theorem run_outerProofSeedRangeFrameProgram
    (inputLength width inputCode : ℕ) :
    runNPOracleProgram outerProofSeedRangeFrameProgram
        (outerProofSeedRangeFrameBits inputLength width inputCode) 9
        (initialNPOracleState inputLength
          (outerProofSeedRangeFrameInput width inputCode)) =
      some (outerProofSeedRangeFrameOutput inputLength width inputCode) := by
  have hinputBits :
      natBitLength (outerProofSeedRangeFrameInput width inputCode) ≤
        outerProofSeedRangeFrameBits inputLength width inputCode :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength (outerProofSeedRangeFrameOutput inputLength width inputCode)
        ≤ outerProofSeedRangeFrameBits inputLength width inputCode :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hcountBits :
      natBitLength (2 ^ width) ≤
        outerProofSeedRangeFrameBits inputLength width inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair (2 ^ width) (Nat.pair width inputCode))).trans
      hinputBits
  have hcontextBits :
      natBitLength (Nat.pair width inputCode) ≤
        outerProofSeedRangeFrameBits inputLength width inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair (2 ^ width) (Nat.pair width inputCode))).trans
      hinputBits
  have hrangeBits :
      natBitLength
          (generatedBalancedRangeInput (2 ^ (width + 1))
            (Nat.pair width inputCode)) ≤
        outerProofSeedRangeFrameBits inputLength width inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair
        (generatedBalancedRangeInput (2 ^ (width + 1))
          (Nat.pair width inputCode))
        (outerProofSeedRetainedFrame inputLength width inputCode))).trans
      houtputBits
  have hdoubleBits :
      natBitLength (2 ^ (width + 1)) ≤
        outerProofSeedRangeFrameBits inputLength width inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair (2 ^ (width + 1)) (Nat.pair width inputCode))).trans
      hrangeBits
  have hretainedBits :
      natBitLength (outerProofSeedRetainedFrame inputLength width inputCode) ≤
        outerProofSeedRangeFrameBits inputLength width inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair
        (generatedBalancedRangeInput (2 ^ (width + 1))
          (Nat.pair width inputCode))
        (outerProofSeedRetainedFrame inputLength width inputCode))).trans
      houtputBits
  have hframeBits :
      natBitLength (Nat.pair inputLength (Nat.pair width inputCode)) ≤
        outerProofSeedRangeFrameBits inputLength width inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair (2 ^ width)
        (Nat.pair inputLength (Nat.pair width inputCode)))).trans hretainedBits
  have hlengthBits :
      natBitLength inputLength ≤
        outerProofSeedRangeFrameBits inputLength width inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair inputLength (Nat.pair width inputCode))).trans
      hframeBits
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := 2 ^ width)
    (by rfl) rfl
    (by simp [initialNPOracleState, outerProofSeedRangeFrameInput])
    hcountBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair width inputCode)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, outerProofSeedRangeFrameInput,
        NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_add_instruction (value := 2 ^ (width + 1))
    (by rfl) rfl
    (by
      simp only [NPOracleState.write, NPOracleState.jump]
      simpa using two_pow_succ width)
    hdoubleBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      generatedBalancedRangeInput (2 ^ (width + 1)) (Nat.pair width inputCode))
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        generatedBalancedRangeInput])
    hrangeBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_copy_instruction (value := inputLength)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hlengthBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair inputLength (Nat.pair width inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := outerProofSeedRetainedFrame inputLength width inputCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        outerProofSeedRetainedFrame])
    hretainedBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := outerProofSeedRangeFrameOutput inputLength width inputCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        outerProofSeedRangeFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

def outerProofSeedResultFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 4 2 6 5
  , .pair 6 5 0 6
  , .halt 0
  ]

@[simp] theorem outerProofSeedResultFrameProgram_oracleFree :
    OracleFree outerProofSeedResultFrameProgram := by
  rfl

def outerProofSeedResultFrameInput
    (inputLength width inputCode stream : ℕ) : ℕ :=
  Nat.pair stream (outerProofSeedRetainedFrame inputLength width inputCode)

def outerProofSeedResultFrameOutput
    (inputLength width inputCode stream : ℕ) : ℕ :=
  Nat.pair (Nat.pair (2 ^ width) stream)
    (Nat.pair inputLength (Nat.pair width inputCode))

def outerProofSeedResultFrameBits
    (inputLength width inputCode stream : ℕ) : ℕ :=
  natBitLength
    (max (outerProofSeedResultFrameInput inputLength width inputCode stream)
      (outerProofSeedResultFrameOutput inputLength width inputCode stream))

theorem run_outerProofSeedResultFrameProgram
    (inputLength width inputCode stream : ℕ) :
    runNPOracleProgram outerProofSeedResultFrameProgram
        (outerProofSeedResultFrameBits inputLength width inputCode stream) 7
        (initialNPOracleState inputLength
          (outerProofSeedResultFrameInput inputLength width inputCode
            stream)) =
      some
        (outerProofSeedResultFrameOutput inputLength width inputCode
          stream) := by
  have hinputBits :
      natBitLength
          (outerProofSeedResultFrameInput inputLength width inputCode stream) ≤
        outerProofSeedResultFrameBits inputLength width inputCode stream :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength
          (outerProofSeedResultFrameOutput inputLength width inputCode
            stream) ≤
        outerProofSeedResultFrameBits inputLength width inputCode stream :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hstreamBits :
      natBitLength stream ≤
        outerProofSeedResultFrameBits inputLength width inputCode stream :=
    (natBitLength_mono
      (Nat.left_le_pair stream
        (outerProofSeedRetainedFrame inputLength width inputCode))).trans
      hinputBits
  have hretainedBits :
      natBitLength (outerProofSeedRetainedFrame inputLength width inputCode) ≤
        outerProofSeedResultFrameBits inputLength width inputCode stream :=
    (natBitLength_mono
      (Nat.right_le_pair stream
        (outerProofSeedRetainedFrame inputLength width inputCode))).trans
      hinputBits
  have hcountBits :
      natBitLength (2 ^ width) ≤
        outerProofSeedResultFrameBits inputLength width inputCode stream :=
    (natBitLength_mono
      (Nat.left_le_pair (2 ^ width)
        (Nat.pair inputLength (Nat.pair width inputCode)))).trans hretainedBits
  have hframeBits :
      natBitLength (Nat.pair inputLength (Nat.pair width inputCode)) ≤
        outerProofSeedResultFrameBits inputLength width inputCode stream :=
    (natBitLength_mono
      (Nat.right_le_pair (2 ^ width)
        (Nat.pair inputLength (Nat.pair width inputCode)))).trans hretainedBits
  have hseedBits :
      natBitLength (Nat.pair (2 ^ width) stream) ≤
        outerProofSeedResultFrameBits inputLength width inputCode stream :=
    (natBitLength_mono
      (Nat.left_le_pair (Nat.pair (2 ^ width) stream)
        (Nat.pair inputLength (Nat.pair width inputCode)))).trans houtputBits
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := stream)
    (by rfl) rfl
    (by simp [initialNPOracleState, outerProofSeedResultFrameInput])
    hstreamBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := outerProofSeedRetainedFrame inputLength width inputCode)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, outerProofSeedResultFrameInput,
        NPOracleState.write, NPOracleState.jump])
    hretainedBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := 2 ^ width)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        outerProofSeedRetainedFrame])
    hcountBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair inputLength (Nat.pair width inputCode))
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        outerProofSeedRetainedFrame])
    hframeBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (2 ^ width) stream)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hseedBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      outerProofSeedResultFrameOutput inputLength width inputCode stream)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        outerProofSeedResultFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ### The composed seed program -/

/-- The Case-1 recovery seed.  Its only parameters are the named row stage and
the scheduled width numeral. -/
def outerProofFormulaSeedProgram
    (row : NPOracleProgram) (width : ℕ) : NPOracleProgram :=
  linkPrograms (outerProofSeedPreludeProgram width)
    (linkPrograms (preserveRightProgram binaryTwoPowProgram)
      (linkPrograms outerProofSeedRangeFrameProgram
        (linkPrograms
          (preserveRightProgram (outerProofFormulaStreamProgram row))
          outerProofSeedResultFrameProgram)))

theorem outerProofFormulaSeedProgram_oracleFree
    {row : NPOracleProgram} (hrow : OracleFree row) (width : ℕ) :
    OracleFree (outerProofFormulaSeedProgram row width) := by
  apply oracleFree_linkPrograms
  · exact outerProofSeedPreludeProgram_oracleFree width
  · apply oracleFree_linkPrograms
    · exact preserveRightProgram_oracleFree binaryTwoPowProgram
        binaryTwoPowProgram_oracleFree
    · apply oracleFree_linkPrograms
      · exact outerProofSeedRangeFrameProgram_oracleFree
      · apply oracleFree_linkPrograms
        · exact preserveRightProgram_oracleFree _
            (outerProofFormulaStreamProgram_oracleFree hrow)
        · exact outerProofSeedResultFrameProgram_oracleFree

def outerProofFormulaSeedFuel
    (row : NPOracleProgram)
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (rowFuel : ℕ → ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram binaryTwoPowProgram)
      (linkPrograms outerProofSeedRangeFrameProgram
        (linkPrograms
          (preserveRightProgram (outerProofFormulaStreamProgram row))
          outerProofSeedResultFrameProgram)))
    4
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

def outerProofFormulaSeedBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (rowBits : ℕ → ℕ) : ℕ :=
  max 1 <|
    max (natBitLength n) <|
      max
        (outerProofSeedPreludeBits (pcp.nativeWidth n)
          (encodeBitInput input)) <|
        max
          (preserveRightBits (binaryTwoPowBits (pcp.nativeWidth n))
            (pcp.nativeWidth n)
            (Nat.pair (pcp.nativeWidth n) (encodeBitInput input))
            (2 ^ pcp.nativeWidth n)) <|
          max
            (outerProofSeedRangeFrameBits n (pcp.nativeWidth n)
              (encodeBitInput input)) <|
            max
              (preserveRightBits
                (outerProofFormulaStreamBits pcp input rowBits)
                (generatedBalancedRangeInput (2 ^ (pcp.nativeWidth n + 1))
                  (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))
                (outerProofSeedRetainedFrame n (pcp.nativeWidth n)
                  (encodeBitInput input))
                (rawClauseStream (outerProofRecoveryFormula pcp input)))
              (outerProofSeedResultFrameBits n (pcp.nativeWidth n)
                (encodeBitInput input)
                (rawClauseStream (outerProofRecoveryFormula pcp input)))

/-- Exact seed construction.  Modulo the single named row stage, one fixed
oracle-free program turns the raw refuter word into the proof-address count
paired with the raw clause stream of the C.12 recovery formula, beside the
retained schedule frame. -/
theorem run_outerProofFormulaSeedProgram
    (row : NPOracleProgram)
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (rowBits rowFuel : ℕ → ℕ)
    (hrow : ∀ code, code < 2 ^ pcp.nativeWidth n →
      runNPOracleProgram row (rowBits code) (rowFuel code)
          (initialNPOracleState n
            (Nat.pair code
              (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))) =
        some (encodeTaggedList (outerProofRowStream pcp input code))) :
    runNPOracleProgram
        (outerProofFormulaSeedProgram row (pcp.nativeWidth n))
        (outerProofFormulaSeedBits pcp input rowBits)
        (outerProofFormulaSeedFuel row pcp input rowFuel)
        (initialNPOracleState n (encodeBitInput input)) =
      some
        (Nat.pair
          (Nat.pair (2 ^ pcp.nativeWidth n)
            (rawClauseStream (outerProofRecoveryFormula pcp input)))
          (Nat.pair n
            (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))) := by
  have hpositive : 1 ≤ outerProofFormulaSeedBits pcp input rowBits :=
    Nat.le_max_left _ _
  have hlengthBits :
      natBitLength n ≤ outerProofFormulaSeedBits pcp input rowBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreludeBits :
      outerProofSeedPreludeBits (pcp.nativeWidth n) (encodeBitInput input) ≤
        outerProofFormulaSeedBits pcp input rowBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have htwoPowBits :
      preserveRightBits (binaryTwoPowBits (pcp.nativeWidth n))
          (pcp.nativeWidth n)
          (Nat.pair (pcp.nativeWidth n) (encodeBitInput input))
          (2 ^ pcp.nativeWidth n) ≤
        outerProofFormulaSeedBits pcp input rowBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrangeFrameBits :
      outerProofSeedRangeFrameBits n (pcp.nativeWidth n)
          (encodeBitInput input) ≤
        outerProofFormulaSeedBits pcp input rowBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hstreamBits :
      preserveRightBits (outerProofFormulaStreamBits pcp input rowBits)
          (generatedBalancedRangeInput (2 ^ (pcp.nativeWidth n + 1))
            (Nat.pair (pcp.nativeWidth n) (encodeBitInput input)))
          (outerProofSeedRetainedFrame n (pcp.nativeWidth n)
            (encodeBitInput input))
          (rawClauseStream (outerProofRecoveryFormula pcp input)) ≤
        outerProofFormulaSeedBits pcp input rowBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hresultBits :
      outerProofSeedResultFrameBits n (pcp.nativeWidth n)
          (encodeBitInput input)
          (rawClauseStream (outerProofRecoveryFormula pcp input)) ≤
        outerProofFormulaSeedBits pcp input rowBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprelude :=
    run_bits_mono
      (run_outerProofSeedPreludeProgram n (pcp.nativeWidth n)
        (encodeBitInput input))
      hpreludeBits
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
        (run_outerProofFormulaStreamProgram row pcp input rowBits rowFuel
          hrow))
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

/-! ## 5. The scheduled instance

At the published schedule the emitted seed is literally
`RecoveredProofRequestCompilerProgram.recoveredProofCompilerSeedOutput`. -/

/-- Exact Case-1 seed production for the scheduled recovery, modulo the single
named decision-row stage. -/
theorem run_outerProofRecoveryFormulaSeedProgram
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
        (outerProofFormulaSeedProgram row (scheduledWidth outer sourceIndex))
        (outerProofFormulaSeedBits (paddedOuterPCP outer) input rowBits)
        (outerProofFormulaSeedFuel row (paddedOuterPCP outer) input rowFuel)
        (initialNPOracleState (sourceLength sourceIndex)
          (encodeBitInput input)) =
      some
        (RecoveredProofRequestCompilerProgram.recoveredProofCompilerSeedOutput
          outer sourceIndex input) :=
  run_outerProofFormulaSeedProgram row (paddedOuterPCP outer) input rowBits
    rowFuel hrow

end NearCubicWires.OuterProofRecoveryFormulaSeedProgram
