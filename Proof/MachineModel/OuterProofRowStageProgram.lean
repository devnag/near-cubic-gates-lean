import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.CaseAnalysis.CaseOneTargetLanguageClosure
import Proof.MachineModel.OuterProofRowProgram

/-!
# The decision-row stage of the C.12 recovery formula, executed

`OuterProofRowProgram` reduced one decision row to three named frontiers: the
coordinate callee of its address fold, the per-clause emitter of its raw clause
list, and the top assembly that joins them.  This module discharges all three
and instantiates the resulting Case-1 chain.

Section 1 builds the coordinate callee whose contract is the `hweight`
hypothesis of `run_rowAddressProgram`: from `pair bit (rowWeightContext …)` a
straight-line prelude frames the published query runner's own request code, the
published query runner returns the projection code, a second frame builds the
published projected-random-bit request, and the published dyadic exponential
followed by the published bit-serial multiplier turn the resulting bit into its
weighted contribution.

Section 2 builds the per-clause emitter: three applications of the published
`ThreeCNF` literal codec, each re-signed and redirected through one published
balanced lookup into the row's own address table, assembled into the singleton
tagged clause list consumed by the published clause-stream flattener.

Section 3 assembles the whole row: the published low-bit normalizer selects the
native randomness, the published decision runner emits the decision code, the
address table of `OuterProofRowProgram` supplies every proof-table address, and
one published range, call and flattener emit the row's raw clause stream.

Section 4 instantiates the Case-1 chain: `hrow` is discharged, so both the
recovery seed and the Case-1 target bit run unconditionally.
-/
namespace NearCubicWires.OuterProofRowStageProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalEncodedListLengthProgram
open NearCubicWires.CanonicalEncodedListLookupProgram
open NearCubicWires.CanonicalProjectedRandomBitProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalThreeCNFLiteralProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseOneTargetLanguageClosure
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.OuterProofRowProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RecoveredProofRequestCompilerProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## 0. Shared helpers -/

private theorem run_fuel_mono {program : NPOracleProgram}
    {maximumBits fuel target : ℕ} {state : NPOracleState} {output : ℕ}
    (hexec : runNPOracleProgram program maximumBits fuel state = some output)
    (hfuel : fuel ≤ target) :
    runNPOracleProgram program maximumBits target state = some output := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  exact run_fuel_add hexec extra

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmember : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmember
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at hmember
      simp only [List.foldr_cons]
      rcases hmember with rfl | hmember
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmember).trans (Nat.le_max_right _ _)

/-- Exchange the two components of a paired register-zero request. -/
private def rowSwapProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 2 0 3
  , .halt 0
  ]

@[simp] private theorem rowSwapProgram_oracleFree :
    OracleFree rowSwapProgram := by
  rfl

private def rowSwapBits (left right : ℕ) : ℕ :=
  natBitLength (max (Nat.pair left right) (Nat.pair right left))

private theorem run_rowSwapProgram (inputLength left right : ℕ) :
    runNPOracleProgram rowSwapProgram (rowSwapBits left right) 4
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.pair right left) := by
  have hinputBits :
      natBitLength (Nat.pair left right) ≤ rowSwapBits left right :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength (Nat.pair right left) ≤ rowSwapBits left right :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hleftBits : natBitLength left ≤ rowSwapBits left right :=
    (natBitLength_mono (Nat.left_le_pair left right)).trans hinputBits
  have hrightBits : natBitLength right ≤ rowSwapBits left right :=
    (natBitLength_mono (Nat.right_le_pair left right)).trans hinputBits
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hleftBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := right)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hrightBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair right left)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## 1. The coordinate callee of the address fold -/

/-- The published query runner's own request code at one coordinate. -/
def rowQueryRequestCode (inputLength inputCode query bit : ℕ) : ℕ :=
  Nat.pair inputLength (Nat.pair inputCode (Nat.pair query bit))

/-- Frame retained past the query call. -/
def rowWeightRetained (native randomnessCode bit : ℕ) : ℕ :=
  Nat.pair native (Nat.pair randomnessCode bit)

/-- The published query runner's uniform budget at one public length.  Its
charged measure does not mention the requested coordinate. -/
def rowQueryBudget {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) : ℕ :=
  polynomialBudget pcp.query.coefficient pcp.query.degree
    (n + pcp.nativeWidth n + pcp.queryCount n)

private theorem run_rowQueryStage
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query bit : ℕ)
    (hquery : query < pcp.queryCount n) (hbit : bit < pcp.nativeWidth n) :
    runNPOracleProgram pcp.query.program (rowQueryBudget pcp n)
        (rowQueryBudget pcp n)
        (initialNPOracleState n
          (rowQueryRequestCode n (encodeBitInput input) query bit)) =
      some (rowProjectionCode pcp input query bit) := by
  have hrun :=
    pcp.query.run_eq_execute (pcp.queryRequest input ⟨query, hquery⟩ ⟨bit, hbit⟩)
  unfold rowProjectionCode
  rw [dif_pos hquery, dif_pos hbit]
  exact hrun

/-- Straight-line prelude of the coordinate callee: the published query
runner's request code beside the frame retained past the call. -/
private def rowWeightPreludeProgram : NPOracleProgram :=
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
  , .pair 8 2 12 11
  , .pair 11 12 13 12
  , .pair 10 13 14 13
  , .pair 6 2 15 14
  , .pair 4 15 16 15
  , .pair 14 16 0 16
  , .halt 0
  ]

@[simp] private theorem rowWeightPreludeProgram_oracleFree :
    OracleFree rowWeightPreludeProgram := by
  rfl

def rowWeightPreludeOutput
    (inputLength native randomnessCode query inputCode bit : ℕ) : ℕ :=
  Nat.pair (rowQueryRequestCode inputLength inputCode query bit)
    (rowWeightRetained native randomnessCode bit)

def rowWeightPreludeBits
    (inputLength native randomnessCode query inputCode bit : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair bit
        (rowWeightContext inputLength native randomnessCode query inputCode))
      (rowWeightPreludeOutput inputLength native randomnessCode query inputCode
        bit))

private theorem run_rowWeightPreludeProgram
    (inputLength native randomnessCode query inputCode bit : ℕ) :
    runNPOracleProgram rowWeightPreludeProgram
        (rowWeightPreludeBits inputLength native randomnessCode query inputCode
          bit)
        17
        (initialNPOracleState inputLength
          (Nat.pair bit
            (rowWeightContext inputLength native randomnessCode query
              inputCode))) =
      some
        (rowWeightPreludeOutput inputLength native randomnessCode query
          inputCode bit) := by
  set maximumBits :=
    rowWeightPreludeBits inputLength native randomnessCode query inputCode bit
    with hmaximumBits
  have hinputBits :
      natBitLength
          (Nat.pair bit
            (rowWeightContext inputLength native randomnessCode query
              inputCode)) ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength
          (rowWeightPreludeOutput inputLength native randomnessCode query
            inputCode bit) ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hbitBits : natBitLength bit ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair bit
        (rowWeightContext inputLength native randomnessCode query
          inputCode))).trans hinputBits
  have hcontextBits :
      natBitLength
          (rowWeightContext inputLength native randomnessCode query
            inputCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair bit
        (rowWeightContext inputLength native randomnessCode query
          inputCode))).trans hinputBits
  have hnativeBits : natBitLength native ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair native
        (Nat.pair randomnessCode
          (Nat.pair query (Nat.pair inputLength inputCode))))).trans
      hcontextBits
  have hfirstTailBits :
      natBitLength
          (Nat.pair randomnessCode
            (Nat.pair query (Nat.pair inputLength inputCode))) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair native
        (Nat.pair randomnessCode
          (Nat.pair query (Nat.pair inputLength inputCode))))).trans
      hcontextBits
  have hrandomnessBits : natBitLength randomnessCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair randomnessCode
        (Nat.pair query (Nat.pair inputLength inputCode)))).trans
      hfirstTailBits
  have hsecondTailBits :
      natBitLength (Nat.pair query (Nat.pair inputLength inputCode)) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair randomnessCode
        (Nat.pair query (Nat.pair inputLength inputCode)))).trans
      hfirstTailBits
  have hqueryBits : natBitLength query ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair query (Nat.pair inputLength inputCode))).trans
      hsecondTailBits
  have hthirdTailBits :
      natBitLength (Nat.pair inputLength inputCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair query (Nat.pair inputLength inputCode))).trans
      hsecondTailBits
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair inputLength inputCode)).trans
      hthirdTailBits
  have hcodeBits : natBitLength inputCode ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair inputLength inputCode)).trans
      hthirdTailBits
  have hrequestBits :
      natBitLength (rowQueryRequestCode inputLength inputCode query bit) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (rowQueryRequestCode inputLength inputCode query bit)
        (rowWeightRetained native randomnessCode bit))).trans houtputBits
  have hretainedBits :
      natBitLength (rowWeightRetained native randomnessCode bit) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair (rowQueryRequestCode inputLength inputCode query bit)
        (rowWeightRetained native randomnessCode bit))).trans houtputBits
  have hinnerRequestBits :
      natBitLength (Nat.pair inputCode (Nat.pair query bit)) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair inputLength
        (Nat.pair inputCode (Nat.pair query bit)))).trans hrequestBits
  have hqueryBitBits :
      natBitLength (Nat.pair query bit) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair inputCode (Nat.pair query bit))).trans
      hinnerRequestBits
  have hrandomnessBitBits :
      natBitLength (Nat.pair randomnessCode bit) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair native (Nat.pair randomnessCode bit))).trans
      hretainedBits
  rw [show 17 = 16 + 1 by omega]
  rw [run_unpairLeft_instruction (value := bit)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hbitBits]
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := rowWeightContext inputLength native randomnessCode query
      inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairLeft_instruction (value := native)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowWeightContext])
    hnativeBits]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair randomnessCode (Nat.pair query (Nat.pair inputLength inputCode)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowWeightContext])
    hfirstTailBits]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := randomnessCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrandomnessBits]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair query (Nat.pair inputLength inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsecondTailBits]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := query)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hqueryBits]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair inputLength inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hthirdTailBits]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputLength)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hlengthBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcodeBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair query bit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hqueryBitBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputCode (Nat.pair query bit))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinnerRequestBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (value := rowQueryRequestCode inputLength inputCode query bit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowQueryRequestCode])
    hrequestBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair randomnessCode bit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrandomnessBitBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := rowWeightRetained native randomnessCode bit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowWeightRetained])
    hretainedBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      rowWeightPreludeOutput inputLength native randomnessCode query inputCode
        bit)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rowWeightPreludeOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Straight-line frame from the returned projection code to the published
projected-random-bit request. -/
private def rowWeightMidFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 2 6 8 7
  , .pair 4 8 9 8
  , .pair 9 7 0 9
  , .halt 0
  ]

@[simp] private theorem rowWeightMidFrameProgram_oracleFree :
    OracleFree rowWeightMidFrameProgram := by
  rfl

def rowWeightMidFrameOutput
    (native randomnessCode bit projectionCode : ℕ) : ℕ :=
  Nat.pair (projectedRandomBitInput native projectionCode randomnessCode) bit

def rowWeightMidFrameBits
    (native randomnessCode bit projectionCode : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair projectionCode (rowWeightRetained native randomnessCode bit))
      (rowWeightMidFrameOutput native randomnessCode bit projectionCode))

private theorem run_rowWeightMidFrameProgram
    (inputLength native randomnessCode bit projectionCode : ℕ) :
    runNPOracleProgram rowWeightMidFrameProgram
        (rowWeightMidFrameBits native randomnessCode bit projectionCode) 10
        (initialNPOracleState inputLength
          (Nat.pair projectionCode
            (rowWeightRetained native randomnessCode bit))) =
      some
        (rowWeightMidFrameOutput native randomnessCode bit projectionCode) := by
  set maximumBits :=
    rowWeightMidFrameBits native randomnessCode bit projectionCode
    with hmaximumBits
  have hinputBits :
      natBitLength
          (Nat.pair projectionCode
            (rowWeightRetained native randomnessCode bit)) ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength
          (rowWeightMidFrameOutput native randomnessCode bit projectionCode) ≤
        maximumBits :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hprojectionBits : natBitLength projectionCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair projectionCode
        (rowWeightRetained native randomnessCode bit))).trans hinputBits
  have hretainedBits :
      natBitLength (rowWeightRetained native randomnessCode bit) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair projectionCode
        (rowWeightRetained native randomnessCode bit))).trans hinputBits
  have hnativeBits : natBitLength native ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair native (Nat.pair randomnessCode bit))).trans
      hretainedBits
  have htailBits :
      natBitLength (Nat.pair randomnessCode bit) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair native (Nat.pair randomnessCode bit))).trans
      hretainedBits
  have hrandomnessBits : natBitLength randomnessCode ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair randomnessCode bit)).trans htailBits
  have hbitBits : natBitLength bit ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair randomnessCode bit)).trans htailBits
  have hrequestBits :
      natBitLength
          (projectedRandomBitInput native projectionCode randomnessCode) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair
        (projectedRandomBitInput native projectionCode randomnessCode)
        bit)).trans houtputBits
  have hpayloadBits :
      natBitLength (Nat.pair projectionCode randomnessCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair native
        (Nat.pair projectionCode randomnessCode))).trans hrequestBits
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := projectionCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hprojectionBits]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := rowWeightRetained native randomnessCode bit)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hretainedBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := native)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowWeightRetained])
    hnativeBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair randomnessCode bit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowWeightRetained])
    htailBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := randomnessCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrandomnessBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := bit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hbitBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair projectionCode randomnessCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpayloadBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := projectedRandomBitInput native projectionCode randomnessCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, projectedRandomBitInput])
    hrequestBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := rowWeightMidFrameOutput native randomnessCode bit projectionCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rowWeightMidFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Dyadic exponential followed by the published bit-serial multiplier. -/
private def rowWeightScaleProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram binaryTwoPowProgram) bitSerialMulProgram

private def rowWeightSwapStageProgram : NPOracleProgram :=
  linkPrograms rowSwapProgram rowWeightScaleProgram

private def rowWeightBitStageProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram projectedRandomBitProgram)
    rowWeightSwapStageProgram

private def rowWeightMidStageProgram : NPOracleProgram :=
  linkPrograms rowWeightMidFrameProgram rowWeightBitStageProgram

private def rowWeightQueryStageProgram (query : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (preserveRightProgram query) rowWeightMidStageProgram

/-- The coordinate callee of the address fold: one published query call, one
published projected-random-bit evaluation, the published dyadic exponential and
the published bit-serial multiplier. -/
def rowWeightProgram (query : NPOracleProgram) : NPOracleProgram :=
  linkPrograms rowWeightPreludeProgram (rowWeightQueryStageProgram query)

theorem rowWeightProgram_oracleFree
    {query : NPOracleProgram} (hquery : OracleFree query) :
    OracleFree (rowWeightProgram query) := by
  apply oracleFree_linkPrograms
  · exact rowWeightPreludeProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact preserveRightProgram_oracleFree query hquery
    · apply oracleFree_linkPrograms
      · exact rowWeightMidFrameProgram_oracleFree
      · apply oracleFree_linkPrograms
        · exact preserveRightProgram_oracleFree projectedRandomBitProgram
            projectedRandomBitProgram_oracleFree
        · apply oracleFree_linkPrograms
          · exact rowSwapProgram_oracleFree
          · apply oracleFree_linkPrograms
            · exact preserveRightProgram_oracleFree binaryTwoPowProgram
                binaryTwoPowProgram_oracleFree
            · exact bitSerialMulProgram_oracleFree

/-- Exact projected bit selected at one address coordinate. -/
def rowWeightBitValue
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode query bit : ℕ) : ℕ :=
  projectedRandomBitOutput (pcp.nativeWidth n)
    (rowProjectionCode pcp input query bit) randomnessCode

def rowWeightFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode query bit : ℕ) : ℕ :=
  linkFuel (rowWeightQueryStageProgram pcp.query.program) 17
    (linkFuel rowWeightMidStageProgram
      (preserveRightFuel (rowQueryBudget pcp n))
      (linkFuel rowWeightBitStageProgram 10
        (linkFuel rowWeightSwapStageProgram
          (preserveRightFuel
            (projectedRandomBitFuel (pcp.nativeWidth n)
              (rowProjectionCode pcp input query bit) randomnessCode))
          (linkFuel rowWeightScaleProgram 4
            (linkFuel bitSerialMulProgram
              (preserveRightFuel (binaryTwoPowFuel bit))
              (bitSerialMulFuel
                (rowWeightBitValue pcp input randomnessCode query bit)))))))

def rowWeightBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode query bit : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength n) <|
      max
        (rowWeightPreludeBits n (pcp.nativeWidth n) randomnessCode query
          (encodeBitInput input) bit) <|
        max
          (preserveRightBits (rowQueryBudget pcp n)
            (rowQueryRequestCode n (encodeBitInput input) query bit)
            (rowWeightRetained (pcp.nativeWidth n) randomnessCode bit)
            (rowProjectionCode pcp input query bit)) <|
          max
            (rowWeightMidFrameBits (pcp.nativeWidth n) randomnessCode bit
              (rowProjectionCode pcp input query bit)) <|
            max
              (preserveRightBits
                (projectedRandomBitBits n (pcp.nativeWidth n)
                  (rowProjectionCode pcp input query bit) randomnessCode)
                (projectedRandomBitInput (pcp.nativeWidth n)
                  (rowProjectionCode pcp input query bit) randomnessCode)
                bit (rowWeightBitValue pcp input randomnessCode query bit)) <|
              max
                (rowSwapBits
                  (rowWeightBitValue pcp input randomnessCode query bit) bit) <|
                max
                  (preserveRightBits (binaryTwoPowBits bit) bit
                    (rowWeightBitValue pcp input randomnessCode query bit)
                    (2 ^ bit))
                  (bitSerialMulBits n (2 ^ bit)
                    (rowWeightBitValue pcp input randomnessCode query bit))

/-- **The coordinate callee, executed.**  Modulo nothing at all, one fixed
program returns the exact weight contributed by one address coordinate of one
query index. -/
theorem run_rowWeightProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode query bit : ℕ)
    (hquery : query < pcp.queryCount n) (hbit : bit < pcp.nativeWidth n) :
    runNPOracleProgram (rowWeightProgram pcp.query.program)
        (rowWeightBits pcp input randomnessCode query bit)
        (rowWeightFuel pcp input randomnessCode query bit)
        (initialNPOracleState n
          (Nat.pair bit
            (rowWeightContext n (pcp.nativeWidth n) randomnessCode query
              (encodeBitInput input)))) =
      some
        (rowAddressWeight (pcp.nativeWidth n) randomnessCode bit
          (rowProjectionCode pcp input query bit)) := by
  set native := pcp.nativeWidth n with hnative
  set inputCode := encodeBitInput input with hinputCode
  set projectionCode := rowProjectionCode pcp input query bit
    with hprojectionCode
  set value := rowWeightBitValue pcp input randomnessCode query bit with hvalue
  set maximumBits := rowWeightBits pcp input randomnessCode query bit
    with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength n ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreludeBits :
      rowWeightPreludeBits n native randomnessCode query inputCode bit ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hqueryBits :
      preserveRightBits (rowQueryBudget pcp n)
          (rowQueryRequestCode n inputCode query bit)
          (rowWeightRetained native randomnessCode bit) projectionCode ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hmidBits :
      rowWeightMidFrameBits native randomnessCode bit projectionCode ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprojectedBits :
      preserveRightBits
          (projectedRandomBitBits n native projectionCode randomnessCode)
          (projectedRandomBitInput native projectionCode randomnessCode) bit
          value ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hswapBits : rowSwapBits value bit ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have htwoPowBits :
      preserveRightBits (binaryTwoPowBits bit) bit value (2 ^ bit) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans <|
                (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hmulBits : bitSerialMulBits n (2 ^ bit) value ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans <|
                (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprelude :=
    run_bits_mono
      (run_rowWeightPreludeProgram n native randomnessCode query inputCode bit)
      hpreludeBits
  have hqueryStage :
      runNPOracleProgram (preserveRightProgram pcp.query.program) maximumBits
          (preserveRightFuel (rowQueryBudget pcp n))
          (initialNPOracleState n
            (rowWeightPreludeOutput n native randomnessCode query inputCode
              bit)) =
        some
          (Nat.pair projectionCode
            (rowWeightRetained native randomnessCode bit)) :=
    run_bits_mono
      (run_preserveRightProgram pcp.query.program n (rowQueryBudget pcp n)
        (rowQueryBudget pcp n) (rowQueryRequestCode n inputCode query bit)
        (rowWeightRetained native randomnessCode bit) projectionCode
        (run_rowQueryStage pcp input query bit hquery hbit))
      hqueryBits
  have hmid :=
    run_bits_mono
      (run_rowWeightMidFrameProgram n native randomnessCode bit projectionCode)
      hmidBits
  have hprojected :
      runNPOracleProgram (preserveRightProgram projectedRandomBitProgram)
          maximumBits
          (preserveRightFuel
            (projectedRandomBitFuel native projectionCode randomnessCode))
          (initialNPOracleState n
            (rowWeightMidFrameOutput native randomnessCode bit
              projectionCode)) =
        some (Nat.pair value bit) :=
    run_bits_mono
      (run_preserveRightProgram projectedRandomBitProgram n
        (projectedRandomBitBits n native projectionCode randomnessCode)
        (projectedRandomBitFuel native projectionCode randomnessCode)
        (projectedRandomBitInput native projectionCode randomnessCode) bit
        value
        (run_projectedRandomBitProgram n native projectionCode randomnessCode))
      hprojectedBits
  have hswap :=
    run_bits_mono (run_rowSwapProgram n value bit) hswapBits
  have htwoPow :
      runNPOracleProgram (preserveRightProgram binaryTwoPowProgram) maximumBits
          (preserveRightFuel (binaryTwoPowFuel bit))
          (initialNPOracleState n (Nat.pair bit value)) =
        some (Nat.pair (2 ^ bit) value) :=
    run_bits_mono
      (run_preserveRightProgram binaryTwoPowProgram n (binaryTwoPowBits bit)
        (binaryTwoPowFuel bit) bit value (2 ^ bit)
        (run_binaryTwoPowProgram n bit (binaryTwoPowBits bit) (Nat.le_refl _)))
      htwoPowBits
  have hmul :
      runNPOracleProgram bitSerialMulProgram maximumBits
          (bitSerialMulFuel value)
          (initialNPOracleState n (Nat.pair (2 ^ bit) value)) =
        some (2 ^ bit * value) :=
    run_bits_mono (run_bitSerialMulProgram n (2 ^ bit) value) hmulBits
  have hscale := run_linkPrograms hpositive hlengthBits htwoPow hmul
  have hswapStage := run_linkPrograms hpositive hlengthBits hswap hscale
  have hbitStage := run_linkPrograms hpositive hlengthBits hprojected hswapStage
  have hmidStage := run_linkPrograms hpositive hlengthBits hmid hbitStage
  have hqueryLinked :=
    run_linkPrograms hpositive hlengthBits hqueryStage hmidStage
  have hrun := run_linkPrograms hpositive hlengthBits hprelude hqueryLinked
  rw [show rowAddressWeight native randomnessCode bit projectionCode =
      2 ^ bit * value by
    rw [rowAddressWeight, hvalue, rowWeightBitValue, ← hnative,
      ← hprojectionCode]
    ring]
  exact hrun

/-! ### The query-uniform envelope consumed by the address table -/

private theorem le_foldr_max_of_range_map {count query : ℕ} (weightOf : ℕ → ℕ)
    (hquery : query < count) :
    weightOf query ≤ ((List.range count).map weightOf).foldr max 0 :=
  le_foldr_max_of_mem (List.mem_map_of_mem (List.mem_range.mpr hquery))

/-- Query-uniform fuel envelope: the address table's callee contract charges
one budget per coordinate, not per coordinate and query index. -/
def rowWeightTableFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode bit : ℕ) : ℕ :=
  ((List.range (pcp.queryCount n)).map fun query =>
    rowWeightFuel pcp input randomnessCode query bit).foldr max 0

/-- Query-uniform width envelope of the same contract. -/
def rowWeightTableBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode bit : ℕ) : ℕ :=
  ((List.range (pcp.queryCount n)).map fun query =>
    rowWeightBits pcp input randomnessCode query bit).foldr max 0

/-- The exact `hweight` hypothesis of `run_rowAddressTableProgram`. -/
theorem run_rowWeightProgram_uniform
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode query bit : ℕ)
    (hquery : query < pcp.queryCount n) (hbit : bit < pcp.nativeWidth n) :
    runNPOracleProgram (rowWeightProgram pcp.query.program)
        (rowWeightTableBits pcp input randomnessCode bit)
        (rowWeightTableFuel pcp input randomnessCode bit)
        (initialNPOracleState n
          (Nat.pair bit
            (rowWeightContext n (pcp.nativeWidth n) randomnessCode query
              (encodeBitInput input)))) =
      some
        (rowAddressWeight (pcp.nativeWidth n) randomnessCode bit
          (rowProjectionCode pcp input query bit)) := by
  have hbitsBound :
      rowWeightBits pcp input randomnessCode query bit ≤
        rowWeightTableBits pcp input randomnessCode bit :=
    le_foldr_max_of_range_map
      (fun candidate => rowWeightBits pcp input randomnessCode candidate bit)
      hquery
  have hfuelBound :
      rowWeightFuel pcp input randomnessCode query bit ≤
        rowWeightTableFuel pcp input randomnessCode bit :=
    le_foldr_max_of_range_map
      (fun candidate => rowWeightFuel pcp input randomnessCode candidate bit)
      hquery
  exact run_fuel_mono
    (run_bits_mono
      (run_rowWeightProgram pcp input randomnessCode query bit hquery hbit)
      hbitsBound)
    hfuelBound

/-! ## 2. The per-clause emitter -/

/-- Public context of one decision row's clause emitter. -/
def rowClauseContext (count decisionCode tableCode : ℕ) : ℕ :=
  Nat.pair count (Nat.pair decisionCode tableCode)

/-- The exact literal-stage request at one clause position. -/
def rowLiteralRequest
    (count decisionCode tableCode clauseIndex position : ℕ) : ℕ :=
  Nat.pair (threeCNFLiteralInput count decisionCode clauseIndex position)
    (Nat.pair count tableCode)

/-- Proof-table index selected by one emitted literal. -/
def rowLiteralAddressIndex (count decisionCode clauseIndex position : ℕ) : ℕ :=
  (Nat.unpair
    (threeCNFLiteralOutput count decisionCode clauseIndex position)).2

/-- Re-signed tag of one emitted literal. -/
def rowLiteralSign (count decisionCode clauseIndex position : ℕ) : ℕ :=
  1 -
    (Nat.unpair
      (threeCNFLiteralOutput count decisionCode clauseIndex position)).1

theorem rowLiteralAddressIndex_lt
    (count decisionCode clauseIndex position : ℕ) (hcount : 0 < count) :
    rowLiteralAddressIndex count decisionCode clauseIndex position < count := by
  unfold rowLiteralAddressIndex threeCNFLiteralOutput
    CanonicalLiteralDecodeProgram.literalDecodeOutput
  simp only [Nat.unpair_pair]
  exact Nat.mod_lt _ hcount

theorem rowLiteralCode_eq_pair (address : ℕ → ℕ)
    (count decisionCode clauseIndex position : ℕ) :
    rowLiteralCode address
        (threeCNFLiteralOutput count decisionCode clauseIndex position) =
      Nat.pair (rowLiteralSign count decisionCode clauseIndex position)
        (address
          (rowLiteralAddressIndex count decisionCode clauseIndex position)) :=
  rfl

/-- Straight-line frame from the decoded literal to the published balanced
lookup of its proof-table address. -/
private def rowLiteralLookupFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 2 6 5
  , .unpairRight 2 7 6
  , .set 8 1 7
  , .subtract 8 6 9 8
  , .pair 7 5 10 9
  , .pair 4 10 11 10
  , .pair 11 9 0 11
  , .halt 0
  ]

@[simp] private theorem rowLiteralLookupFrameProgram_oracleFree :
    OracleFree rowLiteralLookupFrameProgram := by
  rfl

def rowLiteralLookupFrameOutput (count tableCode literalCode : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair count (Nat.pair (Nat.unpair literalCode).2 tableCode))
    (1 - (Nat.unpair literalCode).1)

def rowLiteralLookupFrameBits (count tableCode literalCode : ℕ) : ℕ :=
  natBitLength
    (max 1
      (max (Nat.pair literalCode (Nat.pair count tableCode))
        (rowLiteralLookupFrameOutput count tableCode literalCode)))

private theorem run_rowLiteralLookupFrameProgram
    (inputLength count tableCode literalCode : ℕ) :
    runNPOracleProgram rowLiteralLookupFrameProgram
        (rowLiteralLookupFrameBits count tableCode literalCode) 12
        (initialNPOracleState inputLength
          (Nat.pair literalCode (Nat.pair count tableCode))) =
      some (rowLiteralLookupFrameOutput count tableCode literalCode) := by
  set maximumBits := rowLiteralLookupFrameBits count tableCode literalCode
    with hmaximumBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have hinputBits :
      natBitLength (Nat.pair literalCode (Nat.pair count tableCode)) ≤
        maximumBits :=
    natBitLength_mono ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have houtputBits :
      natBitLength (rowLiteralLookupFrameOutput count tableCode literalCode) ≤
        maximumBits :=
    natBitLength_mono ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hliteralBits : natBitLength literalCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair literalCode (Nat.pair count tableCode))).trans
      hinputBits
  have hcontextBits :
      natBitLength (Nat.pair count tableCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair literalCode (Nat.pair count tableCode))).trans
      hinputBits
  have hcountBits : natBitLength count ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair count tableCode)).trans hcontextBits
  have htableBits : natBitLength tableCode ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair count tableCode)).trans hcontextBits
  have htagBits :
      natBitLength (Nat.unpair literalCode).1 ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_left_le literalCode)).trans hliteralBits
  have hindexBits :
      natBitLength (Nat.unpair literalCode).2 ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_right_le literalCode)).trans hliteralBits
  have hlookupBits :
      natBitLength
          (Nat.pair count (Nat.pair (Nat.unpair literalCode).2 tableCode)) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair
        (Nat.pair count (Nat.pair (Nat.unpair literalCode).2 tableCode))
        (1 - (Nat.unpair literalCode).1))).trans houtputBits
  have hsignBits :
      natBitLength (1 - (Nat.unpair literalCode).1) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair
        (Nat.pair count (Nat.pair (Nat.unpair literalCode).2 tableCode))
        (1 - (Nat.unpair literalCode).1))).trans houtputBits
  have hpayloadBits :
      natBitLength (Nat.pair (Nat.unpair literalCode).2 tableCode) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair count
        (Nat.pair (Nat.unpair literalCode).2 tableCode))).trans hlookupBits
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := literalCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hliteralBits]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair count tableCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := count)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcountBits]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := tableCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htableBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair literalCode).1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htagBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair literalCode).2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hindexBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_subtract_instruction (value := 1 - (Nat.unpair literalCode).1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsignBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.unpair literalCode).2 tableCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpayloadBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair count (Nat.pair (Nat.unpair literalCode).2 tableCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hlookupBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := rowLiteralLookupFrameOutput count tableCode literalCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        rowLiteralLookupFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- One emitted literal: the published `ThreeCNF` literal codec, then the
published balanced lookup of the selected proof-table address. -/
def rowLiteralProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram threeCNFLiteralProgram)
    (linkPrograms rowLiteralLookupFrameProgram
      (linkPrograms (preserveRightProgram canonicalBalancedLookupProgram)
        rowSwapProgram))

theorem rowLiteralProgram_oracleFree : OracleFree rowLiteralProgram := by
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree threeCNFLiteralProgram
      threeCNFLiteralProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact rowLiteralLookupFrameProgram_oracleFree
    · apply oracleFree_linkPrograms
      · exact preserveRightProgram_oracleFree canonicalBalancedLookupProgram
          canonicalBalancedLookupProgram_oracleFree
      · exact rowSwapProgram_oracleFree

private def rowLiteralLookupStageProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram canonicalBalancedLookupProgram)
    rowSwapProgram

private def rowLiteralFrameStageProgram : NPOracleProgram :=
  linkPrograms rowLiteralLookupFrameProgram rowLiteralLookupStageProgram

def rowLiteralFuel
    (count decisionCode clauseIndex position : ℕ) (table : List ℕ) : ℕ :=
  linkFuel rowLiteralFrameStageProgram
    (preserveRightFuel
      (threeCNFLiteralFuel count decisionCode clauseIndex position))
    (linkFuel rowLiteralLookupStageProgram 12
      (linkFuel rowSwapProgram
        (preserveRightFuel
          (balancedLookupFuel table
            (rowLiteralAddressIndex count decisionCode clauseIndex position)))
        4))

def rowLiteralBits
    (inputLength count decisionCode clauseIndex position : ℕ)
    (table : List ℕ) (address : ℕ → ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max
        (preserveRightBits
          (threeCNFLiteralBits inputLength count decisionCode clauseIndex
            position)
          (threeCNFLiteralInput count decisionCode clauseIndex position)
          (Nat.pair count (encodeBalancedList table))
          (threeCNFLiteralOutput count decisionCode clauseIndex position)) <|
        max
          (rowLiteralLookupFrameBits count (encodeBalancedList table)
            (threeCNFLiteralOutput count decisionCode clauseIndex
              position)) <|
          max
            (preserveRightBits
              (balancedLookupMaximumBits table
                (rowLiteralAddressIndex count decisionCode clauseIndex
                  position))
              (balancedLookupInput table
                (rowLiteralAddressIndex count decisionCode clauseIndex
                  position))
              (rowLiteralSign count decisionCode clauseIndex position)
              (address
                (rowLiteralAddressIndex count decisionCode clauseIndex
                  position)))
            (rowSwapBits
              (address
                (rowLiteralAddressIndex count decisionCode clauseIndex
                  position))
              (rowLiteralSign count decisionCode clauseIndex position))

/-- **One emitted literal, executed.**  The published codec supplies the sign
and the query index; the published balanced lookup supplies that index's
proof-table address. -/
theorem run_rowLiteralProgram
    (inputLength count decisionCode clauseIndex position : ℕ)
    (table : List ℕ) (address : ℕ → ℕ) (hcount : 0 < count)
    (hlength : table.length = count)
    (htable : ∀ (index : ℕ) (hindex : index < table.length),
      table[index] = address index) :
    runNPOracleProgram rowLiteralProgram
        (rowLiteralBits inputLength count decisionCode clauseIndex position
          table address)
        (rowLiteralFuel count decisionCode clauseIndex position table)
        (initialNPOracleState inputLength
          (rowLiteralRequest count decisionCode (encodeBalancedList table)
            clauseIndex position)) =
      some
        (rowLiteralCode address
          (threeCNFLiteralOutput count decisionCode clauseIndex position)) := by
  set tableCode := encodeBalancedList table with htableCode
  set literalCode := threeCNFLiteralOutput count decisionCode clauseIndex position
    with hliteralCode
  set index := rowLiteralAddressIndex count decisionCode clauseIndex position
    with hindex
  set sign := rowLiteralSign count decisionCode clauseIndex position with hsign
  set maximumBits :=
    rowLiteralBits inputLength count decisionCode clauseIndex position table
      address with hmaximumBits
  have hindexLt : index < table.length := by
    rw [hlength, hindex]
    exact rowLiteralAddressIndex_lt count decisionCode clauseIndex position
      hcount
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcodecBits :
      preserveRightBits
          (threeCNFLiteralBits inputLength count decisionCode clauseIndex
            position)
          (threeCNFLiteralInput count decisionCode clauseIndex position)
          (Nat.pair count tableCode) literalCode ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hframeBits :
      rowLiteralLookupFrameBits count tableCode literalCode ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlookupBits :
      preserveRightBits (balancedLookupMaximumBits table index)
          (balancedLookupInput table index) sign (address index) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hswapBits : rowSwapBits (address index) sign ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcodec :
      runNPOracleProgram (preserveRightProgram threeCNFLiteralProgram)
          maximumBits
          (preserveRightFuel
            (threeCNFLiteralFuel count decisionCode clauseIndex position))
          (initialNPOracleState inputLength
            (rowLiteralRequest count decisionCode tableCode clauseIndex
              position)) =
        some (Nat.pair literalCode (Nat.pair count tableCode)) :=
    run_bits_mono
      (run_preserveRightProgram threeCNFLiteralProgram inputLength
        (threeCNFLiteralBits inputLength count decisionCode clauseIndex
          position)
        (threeCNFLiteralFuel count decisionCode clauseIndex position)
        (threeCNFLiteralInput count decisionCode clauseIndex position)
        (Nat.pair count tableCode) literalCode
        (run_threeCNFLiteralProgram inputLength count decisionCode clauseIndex
          position hcount))
      hcodecBits
  have hframe :
      runNPOracleProgram rowLiteralLookupFrameProgram maximumBits 12
          (initialNPOracleState inputLength
            (Nat.pair literalCode (Nat.pair count tableCode))) =
        some (Nat.pair (balancedLookupInput table index) sign) := by
    refine run_bits_mono
      (run_rowLiteralLookupFrameProgram inputLength count tableCode literalCode)
      hframeBits |>.trans ?_
    rw [rowLiteralLookupFrameOutput, balancedLookupInput, hlength]
    rfl
  have hlookup :
      runNPOracleProgram (preserveRightProgram canonicalBalancedLookupProgram)
          maximumBits
          (preserveRightFuel (balancedLookupFuel table index))
          (initialNPOracleState inputLength
            (Nat.pair (balancedLookupInput table index) sign)) =
        some (Nat.pair (address index) sign) := by
    refine run_bits_mono
      (run_preserveRightProgram canonicalBalancedLookupProgram inputLength
        (balancedLookupMaximumBits table index)
        (balancedLookupFuel table index) (balancedLookupInput table index) sign
        (address index) ?_)
      hlookupBits
    rw [← htable index hindexLt]
    exact run_canonicalBalancedLookupProgram table index inputLength hindexLt
  have hswap :=
    run_bits_mono (run_rowSwapProgram inputLength (address index) sign)
      hswapBits
  have hlookupStage := run_linkPrograms hpositive hlengthBits hlookup hswap
  have hframeStage := run_linkPrograms hpositive hlengthBits hframe hlookupStage
  exact run_linkPrograms hpositive hlengthBits hcodec hframeStage

/-! ### The literal stage, addressed by its position numeral -/

/-- Request of one clause emitter: the clause index beside the row context. -/
def rowClausePayload (count decisionCode tableCode clauseIndex : ℕ) : ℕ :=
  Nat.pair clauseIndex (rowClauseContext count decisionCode tableCode)

/-- Straight-line frame from `pair position payload` to the literal stage's
own request. -/
private def rowLiteralFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .set 10 0 9
  , .pair 4 10 11 10
  , .pair 8 11 12 11
  , .pair 2 10 13 12
  , .pair 12 13 14 13
  , .pair 14 6 15 14
  , .pair 6 9 16 15
  , .pair 15 16 0 16
  , .halt 0
  ]

@[simp] private theorem rowLiteralFrameProgram_oracleFree :
    OracleFree rowLiteralFrameProgram := by
  rfl

def rowLiteralFrameBits
    (count decisionCode tableCode clauseIndex position : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair position (rowClausePayload count decisionCode tableCode
        clauseIndex))
      (rowLiteralRequest count decisionCode tableCode clauseIndex position))

private theorem run_rowLiteralFrameProgram
    (inputLength count decisionCode tableCode clauseIndex position : ℕ) :
    runNPOracleProgram rowLiteralFrameProgram
        (rowLiteralFrameBits count decisionCode tableCode clauseIndex position)
        17
        (initialNPOracleState inputLength
          (Nat.pair position
            (rowClausePayload count decisionCode tableCode clauseIndex))) =
      some
        (rowLiteralRequest count decisionCode tableCode clauseIndex
          position) := by
  set maximumBits :=
    rowLiteralFrameBits count decisionCode tableCode clauseIndex position
    with hmaximumBits
  have hinputBits :
      natBitLength
          (Nat.pair position
            (rowClausePayload count decisionCode tableCode clauseIndex)) ≤
        maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength
          (rowLiteralRequest count decisionCode tableCode clauseIndex
            position) ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hpositionBits : natBitLength position ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair position
        (rowClausePayload count decisionCode tableCode clauseIndex))).trans
      hinputBits
  have hpayloadBits :
      natBitLength (rowClausePayload count decisionCode tableCode
        clauseIndex) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair position
        (rowClausePayload count decisionCode tableCode clauseIndex))).trans
      hinputBits
  have hclauseBits : natBitLength clauseIndex ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair clauseIndex
        (rowClauseContext count decisionCode tableCode))).trans hpayloadBits
  have hcontextBits :
      natBitLength (rowClauseContext count decisionCode tableCode) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair clauseIndex
        (rowClauseContext count decisionCode tableCode))).trans hpayloadBits
  have hcountBits : natBitLength count ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair count (Nat.pair decisionCode tableCode))).trans
      hcontextBits
  have htailBits :
      natBitLength (Nat.pair decisionCode tableCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair count (Nat.pair decisionCode tableCode))).trans
      hcontextBits
  have hdecisionBits : natBitLength decisionCode ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair decisionCode tableCode)).trans
      htailBits
  have htableBits : natBitLength tableCode ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair decisionCode tableCode)).trans
      htailBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le count)).trans hcountBits
  have hliteralInputBits :
      natBitLength (threeCNFLiteralInput count decisionCode clauseIndex
        position) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair
        (threeCNFLiteralInput count decisionCode clauseIndex position)
        (Nat.pair count tableCode))).trans houtputBits
  have hpairContextBits :
      natBitLength (Nat.pair count tableCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair
        (threeCNFLiteralInput count decisionCode clauseIndex position)
        (Nat.pair count tableCode))).trans houtputBits
  have hnestedBits :
      natBitLength
          (encodedNestedListLookupInput decisionCode clauseIndex position 0) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair
        (encodedNestedListLookupInput decisionCode clauseIndex position 0)
        count)).trans hliteralInputBits
  have hspineBits :
      natBitLength (encodedListLookupInput decisionCode clauseIndex 0) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (encodedListLookupInput decisionCode clauseIndex 0)
        (Nat.pair position 0))).trans hnestedBits
  have hpositionCodeBits :
      natBitLength (Nat.pair position 0) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair (encodedListLookupInput decisionCode clauseIndex 0)
        (Nat.pair position 0))).trans hnestedBits
  have hclauseCodeBits :
      natBitLength (Nat.pair clauseIndex 0) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair decisionCode (Nat.pair clauseIndex 0))).trans
      hspineBits
  rw [show 17 = 16 + 1 by omega]
  rw [run_unpairLeft_instruction (value := position)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hpositionBits]
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := rowClausePayload count decisionCode tableCode clauseIndex)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpayloadBits]
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairLeft_instruction (value := clauseIndex)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowClausePayload])
    hclauseBits]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := rowClauseContext count decisionCode tableCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowClausePayload])
    hcontextBits]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := count)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowClauseContext])
    hcountBits]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair decisionCode tableCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowClauseContext])
    htailBits]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := decisionCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hdecisionBits]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := tableCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htableBits]
  rw [show 9 = 8 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair clauseIndex 0)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hclauseCodeBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction
    (value := encodedListLookupInput decisionCode clauseIndex 0)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, encodedListLookupInput])
    hspineBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair position 0)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpositionCodeBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (value := encodedNestedListLookupInput decisionCode clauseIndex position 0)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        encodedNestedListLookupInput])
    hnestedBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := threeCNFLiteralInput count decisionCode clauseIndex position)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, threeCNFLiteralInput])
    hliteralInputBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair count tableCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpairContextBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := rowLiteralRequest count decisionCode tableCode clauseIndex
      position)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowLiteralRequest])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- The complete literal stage: the position frame followed by the emitted
literal. -/
def rowLiteralStageProgram : NPOracleProgram :=
  linkPrograms rowLiteralFrameProgram rowLiteralProgram

theorem rowLiteralStageProgram_oracleFree :
    OracleFree rowLiteralStageProgram :=
  oracleFree_linkPrograms rowLiteralFrameProgram_oracleFree
    rowLiteralProgram_oracleFree

def rowLiteralStageFuel
    (count decisionCode clauseIndex position : ℕ) (table : List ℕ) : ℕ :=
  linkFuel rowLiteralProgram 17
    (rowLiteralFuel count decisionCode clauseIndex position table)

def rowLiteralStageBits
    (inputLength count decisionCode clauseIndex position : ℕ)
    (table : List ℕ) (address : ℕ → ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max
        (rowLiteralFrameBits count decisionCode (encodeBalancedList table)
          clauseIndex position)
        (rowLiteralBits inputLength count decisionCode clauseIndex position
          table address)

theorem run_rowLiteralStageProgram
    (inputLength count decisionCode clauseIndex position : ℕ)
    (table : List ℕ) (address : ℕ → ℕ) (hcount : 0 < count)
    (hlength : table.length = count)
    (htable : ∀ (index : ℕ) (hindex : index < table.length),
      table[index] = address index) :
    runNPOracleProgram rowLiteralStageProgram
        (rowLiteralStageBits inputLength count decisionCode clauseIndex
          position table address)
        (rowLiteralStageFuel count decisionCode clauseIndex position table)
        (initialNPOracleState inputLength
          (Nat.pair position
            (rowClausePayload count decisionCode (encodeBalancedList table)
              clauseIndex))) =
      some
        (rowLiteralCode address
          (threeCNFLiteralOutput count decisionCode clauseIndex position)) := by
  set maximumBits :=
    rowLiteralStageBits inputLength count decisionCode clauseIndex position
      table address with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hframeBits :
      rowLiteralFrameBits count decisionCode (encodeBalancedList table)
          clauseIndex position ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hliteralBits :
      rowLiteralBits inputLength count decisionCode clauseIndex position table
          address ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hframe :=
    run_bits_mono
      (run_rowLiteralFrameProgram inputLength count decisionCode
        (encodeBalancedList table) clauseIndex position)
      hframeBits
  have hliteral :=
    run_bits_mono
      (run_rowLiteralProgram inputLength count decisionCode clauseIndex
        position table address hcount hlength htable)
      hliteralBits
  exact run_linkPrograms hpositive hlengthBits hframe hliteral

/-! ### The three literals of one clause -/

private def rowClauseSplitProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .set 3 1 2
  , .set 4 2 3
  , .pair 2 0 5 4
  , .pair 3 0 6 5
  , .pair 4 0 7 6
  , .pair 6 7 8 7
  , .pair 5 8 0 8
  , .halt 0
  ]

@[simp] private theorem rowClauseSplitProgram_oracleFree :
    OracleFree rowClauseSplitProgram := by
  rfl

def rowClauseSplitOutput (payload : ℕ) : ℕ :=
  Nat.pair (Nat.pair 0 payload)
    (Nat.pair (Nat.pair 1 payload) (Nat.pair 2 payload))

def rowClauseSplitBits (payload : ℕ) : ℕ :=
  natBitLength (rowClauseSplitOutput payload)

private theorem run_rowClauseSplitProgram (inputLength payload : ℕ) :
    runNPOracleProgram rowClauseSplitProgram (rowClauseSplitBits payload) 9
        (initialNPOracleState inputLength payload) =
      some (rowClauseSplitOutput payload) := by
  set maximumBits := rowClauseSplitBits payload with hmaximumBits
  have houtputBits :
      natBitLength (rowClauseSplitOutput payload) ≤ maximumBits :=
    Nat.le_refl _
  have hfirstBits : natBitLength (Nat.pair 0 payload) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (Nat.pair 0 payload)
        (Nat.pair (Nat.pair 1 payload) (Nat.pair 2 payload)))).trans
      houtputBits
  have hrestBits :
      natBitLength (Nat.pair (Nat.pair 1 payload) (Nat.pair 2 payload)) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair (Nat.pair 0 payload)
        (Nat.pair (Nat.pair 1 payload) (Nat.pair 2 payload)))).trans
      houtputBits
  have hsecondBits : natBitLength (Nat.pair 1 payload) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (Nat.pair 1 payload) (Nat.pair 2 payload))).trans
      hrestBits
  have hthirdBits : natBitLength (Nat.pair 2 payload) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair (Nat.pair 1 payload) (Nat.pair 2 payload))).trans
      hrestBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair 0 payload)).trans hfirstBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair 1 payload)).trans hsecondBits
  have htwoBits : natBitLength 2 ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair 2 payload)).trans hthirdBits
  rw [show 9 = 8 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_set_instruction (value := 2) (by rfl) rfl htwoBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 0 payload)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hfirstBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 payload)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hsecondBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 2 payload)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hthirdBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair 1 payload) (Nat.pair 2 payload))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrestBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := rowClauseSplitOutput payload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowClauseSplitOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

private def rowClauseRotateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 5 2 6 5
  , .pair 4 6 0 6
  , .halt 0
  ]

@[simp] private theorem rowClauseRotateProgram_oracleFree :
    OracleFree rowClauseRotateProgram := by
  rfl

def rowClauseRotateBits (first second third : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair first (Nat.pair second third))
      (Nat.pair second (Nat.pair third first)))

private theorem run_rowClauseRotateProgram
    (inputLength first second third : ℕ) :
    runNPOracleProgram rowClauseRotateProgram
        (rowClauseRotateBits first second third) 7
        (initialNPOracleState inputLength
          (Nat.pair first (Nat.pair second third))) =
      some (Nat.pair second (Nat.pair third first)) := by
  set maximumBits := rowClauseRotateBits first second third with hmaximumBits
  have hinputBits :
      natBitLength (Nat.pair first (Nat.pair second third)) ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength (Nat.pair second (Nat.pair third first)) ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hfirstBits : natBitLength first ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair first (Nat.pair second third))).trans hinputBits
  have htailBits :
      natBitLength (Nat.pair second third) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair first (Nat.pair second third))).trans hinputBits
  have hsecondBits : natBitLength second ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair second third)).trans htailBits
  have hthirdBits : natBitLength third ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair second third)).trans htailBits
  have hrotatedBits :
      natBitLength (Nat.pair third first) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair second (Nat.pair third first))).trans houtputBits
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := first)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hfirstBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair second third)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := second)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsecondBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := third)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hthirdBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair third first)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrotatedBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair second (Nat.pair third first))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

private def rowClauseFinishProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 5 2 6 5
  , .pair 4 6 7 6
  , .set 8 0 7
  , .set 9 1 8
  , .pair 7 8 10 9
  , .pair 9 10 0 10
  , .halt 0
  ]

@[simp] private theorem rowClauseFinishProgram_oracleFree :
    OracleFree rowClauseFinishProgram := by
  rfl

def rowClauseFinishBits (first second third : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair third (Nat.pair first second))
      (encodeTaggedList [Nat.pair first (Nat.pair second third)]))

private theorem run_rowClauseFinishProgram
    (inputLength first second third : ℕ) :
    runNPOracleProgram rowClauseFinishProgram
        (rowClauseFinishBits first second third) 11
        (initialNPOracleState inputLength
          (Nat.pair third (Nat.pair first second))) =
      some (encodeTaggedList [Nat.pair first (Nat.pair second third)]) := by
  set maximumBits := rowClauseFinishBits first second third with hmaximumBits
  have hinputBits :
      natBitLength (Nat.pair third (Nat.pair first second)) ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength
          (encodeTaggedList [Nat.pair first (Nat.pair second third)]) ≤
        maximumBits :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hthirdBits : natBitLength third ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair third (Nat.pair first second))).trans hinputBits
  have hheadBits :
      natBitLength (Nat.pair first second) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair third (Nat.pair first second))).trans hinputBits
  have hfirstBits : natBitLength first ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair first second)).trans hheadBits
  have hsecondBits : natBitLength second ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair first second)).trans hheadBits
  have hcellBits :
      natBitLength (Nat.pair (Nat.pair first (Nat.pair second third)) 0) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair 1
        (Nat.pair (Nat.pair first (Nat.pair second third)) 0))).trans
      houtputBits
  have hclauseBits :
      natBitLength (Nat.pair first (Nat.pair second third)) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (Nat.pair first (Nat.pair second third)) 0)).trans
      hcellBits
  have htailBits :
      natBitLength (Nat.pair second third) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair first (Nat.pair second third))).trans hclauseBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le first)).trans hfirstBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair 1
        (Nat.pair (Nat.pair first (Nat.pair second third)) 0))).trans
      houtputBits
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := third)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hthirdBits]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair first second)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hheadBits]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := first)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hfirstBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := second)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsecondBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair second third)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair first (Nat.pair second third))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hclauseBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair first (Nat.pair second third)) 0)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcellBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := encodeTaggedList [Nat.pair first (Nat.pair second third)])
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, encodeTaggedList])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ### The composed clause emitter -/

/-- One emitted literal of one clause. -/
def rowClauseLiteral (count decisionCode : ℕ) (address : ℕ → ℕ)
    (clauseIndex position : ℕ) : ℕ :=
  rowLiteralCode address
    (threeCNFLiteralOutput count decisionCode clauseIndex position)

theorem rowClauseCode_eq_literals (count decisionCode : ℕ)
    (address : ℕ → ℕ) (clauseIndex : ℕ) :
    rowClauseCode count decisionCode address clauseIndex =
      Nat.pair (rowClauseLiteral count decisionCode address clauseIndex 0)
        (Nat.pair (rowClauseLiteral count decisionCode address clauseIndex 1)
          (rowClauseLiteral count decisionCode address clauseIndex 2)) :=
  rfl

private def rowClauseThirdStageProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram rowLiteralStageProgram)
    rowClauseFinishProgram

private def rowClauseSecondRotateProgram : NPOracleProgram :=
  linkPrograms rowClauseRotateProgram rowClauseThirdStageProgram

private def rowClauseSecondStageProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram rowLiteralStageProgram)
    rowClauseSecondRotateProgram

private def rowClauseFirstRotateProgram : NPOracleProgram :=
  linkPrograms rowClauseRotateProgram rowClauseSecondStageProgram

private def rowClauseFirstStageProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram rowLiteralStageProgram)
    rowClauseFirstRotateProgram

/-- The per-clause emitter: three published literal decodes, three published
balanced lookups, and the singleton tagged clause list consumed by the
published clause-stream flattener. -/
def rowClauseProgram : NPOracleProgram :=
  linkPrograms rowClauseSplitProgram rowClauseFirstStageProgram

theorem rowClauseProgram_oracleFree : OracleFree rowClauseProgram := by
  apply oracleFree_linkPrograms
  · exact rowClauseSplitProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact preserveRightProgram_oracleFree rowLiteralStageProgram
        rowLiteralStageProgram_oracleFree
    · apply oracleFree_linkPrograms
      · exact rowClauseRotateProgram_oracleFree
      · apply oracleFree_linkPrograms
        · exact preserveRightProgram_oracleFree rowLiteralStageProgram
            rowLiteralStageProgram_oracleFree
        · apply oracleFree_linkPrograms
          · exact rowClauseRotateProgram_oracleFree
          · apply oracleFree_linkPrograms
            · exact preserveRightProgram_oracleFree rowLiteralStageProgram
                rowLiteralStageProgram_oracleFree
            · exact rowClauseFinishProgram_oracleFree

def rowClauseFuel (count decisionCode clauseIndex : ℕ) (table : List ℕ) : ℕ :=
  linkFuel rowClauseFirstStageProgram 9
    (linkFuel rowClauseFirstRotateProgram
      (preserveRightFuel
        (rowLiteralStageFuel count decisionCode clauseIndex 0 table))
      (linkFuel rowClauseSecondStageProgram 7
        (linkFuel rowClauseSecondRotateProgram
          (preserveRightFuel
            (rowLiteralStageFuel count decisionCode clauseIndex 1 table))
          (linkFuel rowClauseThirdStageProgram 7
            (linkFuel rowClauseFinishProgram
              (preserveRightFuel
                (rowLiteralStageFuel count decisionCode clauseIndex 2 table))
              11)))))

def rowClauseBits
    (inputLength count decisionCode clauseIndex : ℕ) (table : List ℕ)
    (address : ℕ → ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max
        (rowClauseSplitBits
          (rowClausePayload count decisionCode (encodeBalancedList table)
            clauseIndex)) <|
        max
          (preserveRightBits
            (rowLiteralStageBits inputLength count decisionCode clauseIndex 0
              table address)
            (Nat.pair 0
              (rowClausePayload count decisionCode (encodeBalancedList table)
                clauseIndex))
            (Nat.pair
              (Nat.pair 1
                (rowClausePayload count decisionCode (encodeBalancedList table)
                  clauseIndex))
              (Nat.pair 2
                (rowClausePayload count decisionCode (encodeBalancedList table)
                  clauseIndex)))
            (rowClauseLiteral count decisionCode address clauseIndex 0)) <|
          max
            (rowClauseRotateBits
              (rowClauseLiteral count decisionCode address clauseIndex 0)
              (Nat.pair 1
                (rowClausePayload count decisionCode (encodeBalancedList table)
                  clauseIndex))
              (Nat.pair 2
                (rowClausePayload count decisionCode (encodeBalancedList table)
                  clauseIndex))) <|
            max
              (preserveRightBits
                (rowLiteralStageBits inputLength count decisionCode clauseIndex
                  1 table address)
                (Nat.pair 1
                  (rowClausePayload count decisionCode
                    (encodeBalancedList table) clauseIndex))
                (Nat.pair
                  (Nat.pair 2
                    (rowClausePayload count decisionCode
                      (encodeBalancedList table) clauseIndex))
                  (rowClauseLiteral count decisionCode address clauseIndex 0))
                (rowClauseLiteral count decisionCode address clauseIndex 1)) <|
              max
                (rowClauseRotateBits
                  (rowClauseLiteral count decisionCode address clauseIndex 1)
                  (Nat.pair 2
                    (rowClausePayload count decisionCode
                      (encodeBalancedList table) clauseIndex))
                  (rowClauseLiteral count decisionCode address
                    clauseIndex 0)) <|
                max
                  (preserveRightBits
                    (rowLiteralStageBits inputLength count decisionCode
                      clauseIndex 2 table address)
                    (Nat.pair 2
                      (rowClausePayload count decisionCode
                        (encodeBalancedList table) clauseIndex))
                    (Nat.pair
                      (rowClauseLiteral count decisionCode address clauseIndex
                        0)
                      (rowClauseLiteral count decisionCode address clauseIndex
                        1))
                    (rowClauseLiteral count decisionCode address clauseIndex 2))
                  (rowClauseFinishBits
                    (rowClauseLiteral count decisionCode address clauseIndex 0)
                    (rowClauseLiteral count decisionCode address clauseIndex 1)
                    (rowClauseLiteral count decisionCode address clauseIndex 2))

/-- **The per-clause emitter, executed.**  From the clause index and the row
context the fixed program emits the singleton tagged list of that clause's raw
code. -/
theorem run_rowClauseProgram
    (inputLength count decisionCode clauseIndex : ℕ) (table : List ℕ)
    (address : ℕ → ℕ) (hcount : 0 < count) (hlength : table.length = count)
    (htable : ∀ (index : ℕ) (hindex : index < table.length),
      table[index] = address index) :
    runNPOracleProgram rowClauseProgram
        (rowClauseBits inputLength count decisionCode clauseIndex table address)
        (rowClauseFuel count decisionCode clauseIndex table)
        (initialNPOracleState inputLength
          (rowClausePayload count decisionCode (encodeBalancedList table)
            clauseIndex)) =
      some
        (encodeTaggedList
          [rowClauseCode count decisionCode address clauseIndex]) := by
  set tableCode := encodeBalancedList table with htableCode
  set payload := rowClausePayload count decisionCode tableCode clauseIndex
    with hpayload
  set first := rowClauseLiteral count decisionCode address clauseIndex 0
    with hfirst
  set second := rowClauseLiteral count decisionCode address clauseIndex 1
    with hsecond
  set third := rowClauseLiteral count decisionCode address clauseIndex 2
    with hthird
  set maximumBits :=
    rowClauseBits inputLength count decisionCode clauseIndex table address
    with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsplitBits : rowClauseSplitBits payload ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hstageOneBits :
      preserveRightBits
          (rowLiteralStageBits inputLength count decisionCode clauseIndex 0
            table address)
          (Nat.pair 0 payload)
          (Nat.pair (Nat.pair 1 payload) (Nat.pair 2 payload)) first ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrotateOneBits :
      rowClauseRotateBits first (Nat.pair 1 payload) (Nat.pair 2 payload) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hstageTwoBits :
      preserveRightBits
          (rowLiteralStageBits inputLength count decisionCode clauseIndex 1
            table address)
          (Nat.pair 1 payload) (Nat.pair (Nat.pair 2 payload) first) second ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrotateTwoBits :
      rowClauseRotateBits second (Nat.pair 2 payload) first ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hstageThreeBits :
      preserveRightBits
          (rowLiteralStageBits inputLength count decisionCode clauseIndex 2
            table address)
          (Nat.pair 2 payload) (Nat.pair first second) third ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans <|
                (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hfinishBits :
      rowClauseFinishBits first second third ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans <|
                (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hsplit :=
    run_bits_mono (run_rowClauseSplitProgram inputLength payload) hsplitBits
  have hstageOne :
      runNPOracleProgram (preserveRightProgram rowLiteralStageProgram)
          maximumBits
          (preserveRightFuel
            (rowLiteralStageFuel count decisionCode clauseIndex 0 table))
          (initialNPOracleState inputLength (rowClauseSplitOutput payload)) =
        some
          (Nat.pair first
            (Nat.pair (Nat.pair 1 payload) (Nat.pair 2 payload))) :=
    run_bits_mono
      (run_preserveRightProgram rowLiteralStageProgram inputLength
        (rowLiteralStageBits inputLength count decisionCode clauseIndex 0 table
          address)
        (rowLiteralStageFuel count decisionCode clauseIndex 0 table)
        (Nat.pair 0 payload)
        (Nat.pair (Nat.pair 1 payload) (Nat.pair 2 payload)) first
        (run_rowLiteralStageProgram inputLength count decisionCode clauseIndex 0
          table address hcount hlength htable))
      hstageOneBits
  have hrotateOne :=
    run_bits_mono
      (run_rowClauseRotateProgram inputLength first (Nat.pair 1 payload)
        (Nat.pair 2 payload))
      hrotateOneBits
  have hstageTwo :
      runNPOracleProgram (preserveRightProgram rowLiteralStageProgram)
          maximumBits
          (preserveRightFuel
            (rowLiteralStageFuel count decisionCode clauseIndex 1 table))
          (initialNPOracleState inputLength
            (Nat.pair (Nat.pair 1 payload)
              (Nat.pair (Nat.pair 2 payload) first))) =
        some (Nat.pair second (Nat.pair (Nat.pair 2 payload) first)) :=
    run_bits_mono
      (run_preserveRightProgram rowLiteralStageProgram inputLength
        (rowLiteralStageBits inputLength count decisionCode clauseIndex 1 table
          address)
        (rowLiteralStageFuel count decisionCode clauseIndex 1 table)
        (Nat.pair 1 payload) (Nat.pair (Nat.pair 2 payload) first) second
        (run_rowLiteralStageProgram inputLength count decisionCode clauseIndex 1
          table address hcount hlength htable))
      hstageTwoBits
  have hrotateTwo :=
    run_bits_mono
      (run_rowClauseRotateProgram inputLength second (Nat.pair 2 payload) first)
      hrotateTwoBits
  have hstageThree :
      runNPOracleProgram (preserveRightProgram rowLiteralStageProgram)
          maximumBits
          (preserveRightFuel
            (rowLiteralStageFuel count decisionCode clauseIndex 2 table))
          (initialNPOracleState inputLength
            (Nat.pair (Nat.pair 2 payload) (Nat.pair first second))) =
        some (Nat.pair third (Nat.pair first second)) :=
    run_bits_mono
      (run_preserveRightProgram rowLiteralStageProgram inputLength
        (rowLiteralStageBits inputLength count decisionCode clauseIndex 2 table
          address)
        (rowLiteralStageFuel count decisionCode clauseIndex 2 table)
        (Nat.pair 2 payload) (Nat.pair first second) third
        (run_rowLiteralStageProgram inputLength count decisionCode clauseIndex 2
          table address hcount hlength htable))
      hstageThreeBits
  have hfinish :=
    run_bits_mono
      (run_rowClauseFinishProgram inputLength first second third) hfinishBits
  have hthirdStage := run_linkPrograms hpositive hlengthBits hstageThree hfinish
  have hsecondRotate :=
    run_linkPrograms hpositive hlengthBits hrotateTwo hthirdStage
  have hsecondStage :=
    run_linkPrograms hpositive hlengthBits hstageTwo hsecondRotate
  have hfirstRotate :=
    run_linkPrograms hpositive hlengthBits hrotateOne hsecondStage
  have hfirstStage :=
    run_linkPrograms hpositive hlengthBits hstageOne hfirstRotate
  exact run_linkPrograms hpositive hlengthBits hsplit hfirstStage

/-! ## 3. The raw clause stream of one decision row -/

/-- Singleton chunk emitted at one clause index. -/
def rowStreamChunks (count decisionCode : ℕ) (address : ℕ → ℕ) :
    List (List ℕ) :=
  (List.range (encodedListLength decisionCode)).map fun clauseIndex =>
    [rowClauseCode count decisionCode address clauseIndex]

/-- Clause atoms of one decision row, in the generator's own order. -/
def rowStreamAtoms (inputLength count decisionCode tableCode : ℕ) : List ℕ :=
  balancedRangeRequestAtoms inputLength
    (rowClauseContext count decisionCode tableCode) 0
    (encodedListLength decisionCode)

def rowStreamAtomOutput (count decisionCode : ℕ) (address : ℕ → ℕ)
    (atom : ℕ) : ℕ :=
  encodeTaggedList
    [rowClauseCode count decisionCode address (rowAtomIndex atom)]

def rowStreamAtomFuel (count decisionCode : ℕ) (table : List ℕ)
    (atom : ℕ) : ℕ :=
  rowClauseFuel count decisionCode (rowAtomIndex atom) table

def rowStreamAtomBits (inputLength count decisionCode : ℕ) (table : List ℕ)
    (address : ℕ → ℕ) (atom : ℕ) : ℕ :=
  rowClauseBits inputLength count decisionCode (rowAtomIndex atom) table
    address

private theorem flatten_singletons (values : List ℕ) (chunk : ℕ → ℕ) :
    ((values.map fun value => [chunk value]).flatten) = values.map chunk := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp [inductionHypothesis]

theorem rowStreamChunks_flatten (count decisionCode : ℕ) (address : ℕ → ℕ) :
    (rowStreamChunks count decisionCode address).flatten =
      rowRawStream count decisionCode address := by
  unfold rowStreamChunks rowRawStream
  exact flatten_singletons (List.range (encodedListLength decisionCode))
    (rowClauseCode count decisionCode address)

theorem rowStreamAtoms_outputs
    (inputLength count decisionCode tableCode : ℕ) (address : ℕ → ℕ) :
    (rowStreamAtoms inputLength count decisionCode tableCode).map
        (rowStreamAtomOutput count decisionCode address) =
      (rowStreamChunks count decisionCode address).map encodeTaggedList := by
  unfold rowStreamAtoms rowStreamChunks
  rw [balancedRangeRequestAtoms_eq_map_range, List.map_map, List.map_map]
  refine List.map_congr_left fun offset _ => ?_
  simp [rowStreamAtomOutput]

private def rowStreamTakeLeftProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] private theorem rowStreamTakeLeftProgram_oracleFree :
    OracleFree rowStreamTakeLeftProgram := by
  rfl

private theorem run_rowStreamTakeLeftProgram
    {maximumBits : ℕ} (inputLength left right : ℕ)
    (hleftBits : natBitLength left ≤ maximumBits) :
    runNPOracleProgram rowStreamTakeLeftProgram maximumBits 2
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

/-- Straight-line frame from the emitted address table to the clause
schedule's own range request. -/
private def rowLengthFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 5 2 6 5
  , .pair 4 6 7 6
  , .pair 5 7 0 7
  , .halt 0
  ]

@[simp] private theorem rowLengthFrameProgram_oracleFree :
    OracleFree rowLengthFrameProgram := by
  rfl

def rowLengthFrameOutput (count decisionCode tableCode : ℕ) : ℕ :=
  Nat.pair decisionCode (rowClauseContext count decisionCode tableCode)

def rowLengthFrameBits (count decisionCode tableCode : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair tableCode (Nat.pair count decisionCode))
      (rowLengthFrameOutput count decisionCode tableCode))

private theorem run_rowLengthFrameProgram
    (inputLength count decisionCode tableCode : ℕ) :
    runNPOracleProgram rowLengthFrameProgram
        (rowLengthFrameBits count decisionCode tableCode) 8
        (initialNPOracleState inputLength
          (Nat.pair tableCode (Nat.pair count decisionCode))) =
      some (rowLengthFrameOutput count decisionCode tableCode) := by
  set maximumBits := rowLengthFrameBits count decisionCode tableCode
    with hmaximumBits
  have hinputBits :
      natBitLength (Nat.pair tableCode (Nat.pair count decisionCode)) ≤
        maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength (rowLengthFrameOutput count decisionCode tableCode) ≤
        maximumBits :=
    natBitLength_mono (Nat.le_max_right _ _)
  have htableBits : natBitLength tableCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair tableCode (Nat.pair count decisionCode))).trans
      hinputBits
  have hframeBits :
      natBitLength (Nat.pair count decisionCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair tableCode (Nat.pair count decisionCode))).trans
      hinputBits
  have hcountBits : natBitLength count ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair count decisionCode)).trans hframeBits
  have hdecisionBits : natBitLength decisionCode ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair count decisionCode)).trans hframeBits
  have hcontextBits :
      natBitLength (rowClauseContext count decisionCode tableCode) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair decisionCode
        (rowClauseContext count decisionCode tableCode))).trans houtputBits
  have hpayloadBits :
      natBitLength (Nat.pair decisionCode tableCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair count (Nat.pair decisionCode tableCode))).trans
      hcontextBits
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tableCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    htableBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair count decisionCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hframeBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := count)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcountBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := decisionCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hdecisionBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair decisionCode tableCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpayloadBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := rowClauseContext count decisionCode tableCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowClauseContext])
    hcontextBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := rowLengthFrameOutput count decisionCode tableCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowLengthFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

private def rowStreamFlattenStageProgram : NPOracleProgram :=
  linkPrograms (balancedCallProgram rowClauseProgram)
    balancedClauseStreamFlattenProgram

private def rowStreamCallStageProgram : NPOracleProgram :=
  linkPrograms rowStreamTakeLeftProgram rowStreamFlattenStageProgram

private def rowStreamRangeStageProgram : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram rowStreamCallStageProgram

private def rowStreamLengthStageProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram encodedListLengthProgram)
    rowStreamRangeStageProgram

/-- The clause-stream half of the row: one published length fold, one published
range, one published balanced call and the published clause-stream
flattener. -/
def rowStreamProgram : NPOracleProgram :=
  linkPrograms rowLengthFrameProgram rowStreamLengthStageProgram

theorem rowStreamProgram_oracleFree : OracleFree rowStreamProgram := by
  apply oracleFree_linkPrograms
  · exact rowLengthFrameProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact preserveRightProgram_oracleFree encodedListLengthProgram
        encodedListLengthProgram_oracleFree
    · apply oracleFree_linkPrograms
      · exact generatedBalancedRangeProgram_oracleFree
      · apply oracleFree_linkPrograms
        · exact rowStreamTakeLeftProgram_oracleFree
        · apply oracleFree_linkPrograms
          · exact balancedCallProgram_oracleFree rowClauseProgram_oracleFree
          · exact balancedClauseStreamFlattenProgram_oracleFree

def rowStreamFuel (inputLength count decisionCode : ℕ) (table : List ℕ)
    (address : ℕ → ℕ) : ℕ :=
  linkFuel rowStreamLengthStageProgram 8
    (linkFuel rowStreamRangeStageProgram
      (preserveRightFuel (encodedListLengthFuel decisionCode))
      (linkFuel rowStreamCallStageProgram
        (generatedBalancedRangeFuel inputLength
          (encodedListLength decisionCode)
          (rowClauseContext count decisionCode (encodeBalancedList table)))
        (linkFuel rowStreamFlattenStageProgram 2
          (linkFuel balancedClauseStreamFlattenProgram
            (balancedCallFuel rowClauseProgram
              (rowStreamAtomFuel count decisionCode table)
              (rowStreamAtoms inputLength count decisionCode
                (encodeBalancedList table)))
            (balancedClauseStreamFlattenFuel
              (rowStreamChunks count decisionCode address))))))

def rowStreamBits (inputLength count decisionCode : ℕ) (table : List ℕ)
    (address : ℕ → ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max
        (rowLengthFrameBits count decisionCode (encodeBalancedList table)) <|
        max
          (preserveRightBits (encodedListLengthBits decisionCode) decisionCode
            (rowClauseContext count decisionCode (encodeBalancedList table))
            (encodedListLength decisionCode)) <|
          max
            (generatedBalancedRangeRequiredBits inputLength
              (encodedListLength decisionCode)
              (rowClauseContext count decisionCode
                (encodeBalancedList table))) <|
            max
              (natBitLength
                (encodeBalancedList
                  (rowStreamAtoms inputLength count decisionCode
                    (encodeBalancedList table)))) <|
              max
                (balancedCallRequiredBits
                  (rowStreamAtomOutput count decisionCode address)
                  (rowStreamAtoms inputLength count decisionCode
                    (encodeBalancedList table))) <|
                max
                  (((rowStreamAtoms inputLength count decisionCode
                    (encodeBalancedList table)).map
                      (rowStreamAtomBits inputLength count decisionCode table
                        address)).foldr max 0)
                  (balancedClauseStreamFlattenMaximumBits
                    (rowStreamChunks count decisionCode address))

/-- **The clause stream, executed.**  From the emitted address table and the
decision code the fixed program emits the exact raw clause stream of one
decision row. -/
theorem run_rowStreamProgram
    (inputLength count decisionCode : ℕ) (table : List ℕ) (address : ℕ → ℕ)
    (hcount : 0 < count) (hlength : table.length = count)
    (htable : ∀ (index : ℕ) (hindex : index < table.length),
      table[index] = address index) :
    runNPOracleProgram rowStreamProgram
        (rowStreamBits inputLength count decisionCode table address)
        (rowStreamFuel inputLength count decisionCode table address)
        (initialNPOracleState inputLength
          (Nat.pair (encodeBalancedList table)
            (Nat.pair count decisionCode))) =
      some (encodeTaggedList (rowRawStream count decisionCode address)) := by
  set tableCode := encodeBalancedList table with htableCode
  set context := rowClauseContext count decisionCode tableCode with hcontext
  set clauseCount := encodedListLength decisionCode with hclauseCount
  set atoms := rowStreamAtoms inputLength count decisionCode tableCode
    with hatoms
  set chunks := rowStreamChunks count decisionCode address with hchunks
  set maximumBits := rowStreamBits inputLength count decisionCode table address
    with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hframeBits :
      rowLengthFrameBits count decisionCode tableCode ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcountBits :
      preserveRightBits (encodedListLengthBits decisionCode) decisionCode
          context clauseCount ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrangeBits :
      generatedBalancedRangeRequiredBits inputLength clauseCount context ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlistBits :
      natBitLength (encodeBalancedList atoms) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      balancedCallRequiredBits
          (rowStreamAtomOutput count decisionCode address) atoms ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hatomBits :
      (atoms.map
          (rowStreamAtomBits inputLength count decisionCode table
            address)).foldr max 0 ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans <|
                (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hflattenBits :
      balancedClauseStreamFlattenMaximumBits chunks ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans <|
                (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hframe :=
    run_bits_mono
      (run_rowLengthFrameProgram inputLength count decisionCode tableCode)
      hframeBits
  have hlengthStage :
      runNPOracleProgram (preserveRightProgram encodedListLengthProgram)
          maximumBits
          (preserveRightFuel (encodedListLengthFuel decisionCode))
          (initialNPOracleState inputLength
            (rowLengthFrameOutput count decisionCode tableCode)) =
        some (generatedBalancedRangeInput clauseCount context) :=
    run_bits_mono
      (run_preserveRightProgram encodedListLengthProgram inputLength
        (encodedListLengthBits decisionCode)
        (encodedListLengthFuel decisionCode) decisionCode context clauseCount
        (run_encodedListLengthProgram inputLength decisionCode))
      hcountBits
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel inputLength clauseCount context)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput clauseCount context)) =
        some (Nat.pair (encodeBalancedList atoms) context) :=
    run_bits_mono
      (run_generatedBalancedRangeProgram inputLength clauseCount context)
      hrangeBits
  have htake :
      runNPOracleProgram rowStreamTakeLeftProgram maximumBits 2
          (initialNPOracleState inputLength
            (Nat.pair (encodeBalancedList atoms) context)) =
        some (encodeBalancedList atoms) :=
    run_rowStreamTakeLeftProgram inputLength (encodeBalancedList atoms) context
      hlistBits
  have hcall :
      runNPOracleProgram (balancedCallProgram rowClauseProgram) maximumBits
          (balancedCallFuel rowClauseProgram
            (rowStreamAtomFuel count decisionCode table) atoms)
          (initialNPOracleState inputLength (encodeBalancedList atoms)) =
        some (encodeBalancedList (chunks.map encodeTaggedList)) := by
    rw [← rowStreamAtoms_outputs inputLength count decisionCode tableCode
      address]
    refine run_balancedCallProgram_from inputLength atoms
      (rowStreamAtomFuel count decisionCode table)
      (rowStreamAtomOutput count decisionCode address) hcallBits ?_
    intro atom hatom
    have hcalleeBits :
        rowStreamAtomBits inputLength count decisionCode table address atom ≤
          maximumBits :=
      (le_foldr_max_of_mem (List.mem_map_of_mem hatom)).trans hatomBits
    rw [hatoms, rowStreamAtoms, balancedRangeRequestAtoms_eq_map_range,
      List.mem_map] at hatom
    obtain ⟨offset, _hoffset, hatomEq⟩ := hatom
    rw [← hatomEq] at hcalleeBits ⊢
    have hleft :
        (Nat.unpair
          (balancedRangeRequestAtom inputLength (0 + offset) context)).1 =
          inputLength := by
      simp [balancedRangeRequestAtom]
    have hright :
        (Nat.unpair
          (balancedRangeRequestAtom inputLength (0 + offset) context)).2 =
          rowClausePayload count decisionCode tableCode (0 + offset) := by
      simp [balancedRangeRequestAtom, rowClausePayload, hcontext]
    rw [hleft, hright]
    simp only [rowStreamAtomOutput, rowStreamAtomFuel, rowStreamAtomBits,
      rowAtomIndex_balancedRangeRequestAtom] at hcalleeBits ⊢
    exact run_bits_mono
      (run_rowClauseProgram inputLength count decisionCode (0 + offset) table
        address hcount hlength htable)
      hcalleeBits
  have hflatten :
      runNPOracleProgram balancedClauseStreamFlattenProgram maximumBits
          (balancedClauseStreamFlattenFuel chunks)
          (initialNPOracleState inputLength
            (encodeBalancedList (chunks.map encodeTaggedList))) =
        some (encodeTaggedList chunks.flatten) :=
    run_bits_mono
      (run_balancedClauseStreamFlattenProgram chunks inputLength) hflattenBits
  have hflattenStage := run_linkPrograms hpositive hlengthBits hcall hflatten
  have hcallStage := run_linkPrograms hpositive hlengthBits htake hflattenStage
  have hrangeStage := run_linkPrograms hpositive hlengthBits hrange hcallStage
  have hlengthLinked :=
    run_linkPrograms hpositive hlengthBits hlengthStage hrangeStage
  have hrun := run_linkPrograms hpositive hlengthBits hframe hlengthLinked
  rw [← rowStreamChunks_flatten count decisionCode address]
  exact hrun

/-! ### The address-table half of the row -/

private theorem encodeBitInput_rowRandomnessCode (native code : ℕ) :
    encodeBitInput
        (fun bit : Fin native =>
          (rowRandomnessCode native code).testBit bit.val) =
      rowRandomnessCode native code :=
  encodeBitInput_testBit
    (Nat.mod_lt code (pow_pos (by omega : 0 < 2) native))

/-- The published decision runner's uniform budget at one public length. -/
def rowDecisionBudget {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) : ℕ :=
  polynomialBudget pcp.decisionRunner.coefficient pcp.decisionRunner.degree
    (n + pcp.nativeWidth n + pcp.queryCount n)

private theorem rowDecisionRequestCode
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) :
    ProjectionDecisionRequest.code
        (pcp.decisionRequest input
          (fun bit =>
            (rowRandomnessCode (pcp.nativeWidth n) code).testBit bit.val)) =
      Nat.pair n
        (Nat.pair (encodeBitInput input)
          (rowRandomnessCode (pcp.nativeWidth n) code)) := by
  simp only [ExecutableProjectionPCP.decisionRequest,
    ProjectionDecisionRequest.code]
  rw [encodeBitInput_rowRandomnessCode]

private theorem run_rowDecisionStage
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) :
    runNPOracleProgram pcp.decisionRunner.program (rowDecisionBudget pcp n)
        (rowDecisionBudget pcp n)
        (initialNPOracleState n
          (Nat.pair n
            (Nat.pair (encodeBitInput input)
              (rowRandomnessCode (pcp.nativeWidth n) code)))) =
      some (rowDecisionCode pcp input code) := by
  have hrun :=
    pcp.decisionRunner.run_eq_execute
      (pcp.decisionRequest input
        (fun bit =>
          (rowRandomnessCode (pcp.nativeWidth n) code).testBit bit.val))
  rw [rowDecisionRequestCode pcp input code] at hrun
  exact hrun

/-! ### The two scheduled numerals, read at run time

Both numerals the row needs — the native randomness width and the query count —
are the two components of `ExecutableProjectionPCP.shapeCode`, and that code is
produced by the published shape runner from the public length alone.  Register
one carries that public length through every linked stage, so each stage that
needs a numeral reloads it, runs the shape program and unpairs.  No numeral is
ever an immediate, and no frame above the row changes shape. -/

/-- Reload the public length register as the request code. -/
private def rowLengthLoadProgram : NPOracleProgram :=
  [ .copy 1 0 1
  , .halt 0
  ]

@[simp] private theorem rowLengthLoadProgram_oracleFree :
    OracleFree rowLengthLoadProgram := by
  rfl

private theorem run_rowLengthLoadProgram
    (inputLength inputCode maximumBits : ℕ)
    (hbits : natBitLength inputLength ≤ maximumBits) :
    runNPOracleProgram rowLengthLoadProgram maximumBits 2
        (initialNPOracleState inputLength inputCode) =
      some inputLength := by
  rw [show 2 = 1 + 1 by omega]
  rw [run_copy_instruction (value := inputLength)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hbits

/-- The published shape runner at the row's own public length. -/
private def rowShapeProgram (shape : NPOracleProgram) : NPOracleProgram :=
  linkPrograms rowLengthLoadProgram shape

private theorem rowShapeProgram_oracleFree {shape : NPOracleProgram}
    (hshape : OracleFree shape) : OracleFree (rowShapeProgram shape) :=
  oracleFree_linkPrograms rowLengthLoadProgram_oracleFree hshape

private def rowShapeBits (shapeBits inputLength : ℕ) : ℕ :=
  max 1 (max (natBitLength inputLength) shapeBits)

private def rowShapeFuel (shape : NPOracleProgram) (shapeFuel : ℕ) : ℕ :=
  linkFuel shape 2 shapeFuel

private theorem run_rowShapeProgram (shape : NPOracleProgram)
    (inputLength inputCode shapeBits shapeFuel shapeCode : ℕ)
    (hshape :
      runNPOracleProgram shape shapeBits shapeFuel
          (initialNPOracleState inputLength inputLength) =
        some shapeCode) :
    runNPOracleProgram (rowShapeProgram shape)
        (rowShapeBits shapeBits inputLength) (rowShapeFuel shape shapeFuel)
        (initialNPOracleState inputLength inputCode) =
      some shapeCode := by
  have hpositive : 1 ≤ rowShapeBits shapeBits inputLength :=
    Nat.le_max_left _ _
  have hlengthBits :
      natBitLength inputLength ≤ rowShapeBits shapeBits inputLength :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hshapeBits : shapeBits ≤ rowShapeBits shapeBits inputLength :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact run_linkPrograms hpositive hlengthBits
    (run_rowLengthLoadProgram inputLength inputCode _ hlengthBits)
    (run_bits_mono hshape hshapeBits)

/-- The one frame lemma of the runtime numerals: lift the public length in
front of the frame the stage retains. -/
private def rowFrameLiftProgram : NPOracleProgram :=
  [ .copy 1 2 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] private theorem rowFrameLiftProgram_oracleFree :
    OracleFree rowFrameLiftProgram := by
  rfl

private def rowFrameLiftBits (inputLength frame : ℕ) : ℕ :=
  natBitLength (Nat.pair inputLength frame)

private theorem run_rowFrameLiftProgram (inputLength frame : ℕ) :
    runNPOracleProgram rowFrameLiftProgram (rowFrameLiftBits inputLength frame)
        3 (initialNPOracleState inputLength frame) =
      some (Nat.pair inputLength frame) := by
  have houtputBits :
      natBitLength (Nat.pair inputLength frame) ≤
        rowFrameLiftBits inputLength frame :=
    Nat.le_refl _
  have hlengthBits :
      natBitLength inputLength ≤ rowFrameLiftBits inputLength frame :=
    natBitLength_mono (Nat.left_le_pair inputLength frame)
  rw [show 3 = 2 + 1 by omega]
  rw [run_copy_instruction (value := inputLength)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hlengthBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputLength frame)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Install the computed shape code in front of a retained frame. -/
private def rowShapeStageProgram (shape : NPOracleProgram) : NPOracleProgram :=
  linkPrograms rowFrameLiftProgram
    (preserveRightProgram (rowShapeProgram shape))

private theorem rowShapeStageProgram_oracleFree {shape : NPOracleProgram}
    (hshape : OracleFree shape) : OracleFree (rowShapeStageProgram shape) :=
  oracleFree_linkPrograms rowFrameLiftProgram_oracleFree
    (preserveRightProgram_oracleFree _ (rowShapeProgram_oracleFree hshape))

private def rowShapeStageBits (shapeBits inputLength frame shapeCode : ℕ) :
    ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max (rowFrameLiftBits inputLength frame)
        (preserveRightBits (rowShapeBits shapeBits inputLength) inputLength
          frame shapeCode)

private def rowShapeStageFuel (shape : NPOracleProgram) (shapeFuel : ℕ) : ℕ :=
  linkFuel (preserveRightProgram (rowShapeProgram shape)) 3
    (preserveRightFuel (rowShapeFuel shape shapeFuel))

private theorem run_rowShapeStageProgram (shape : NPOracleProgram)
    (inputLength shapeBits shapeFuel frame shapeCode : ℕ)
    (hshape :
      runNPOracleProgram shape shapeBits shapeFuel
          (initialNPOracleState inputLength inputLength) =
        some shapeCode) :
    runNPOracleProgram (rowShapeStageProgram shape)
        (rowShapeStageBits shapeBits inputLength frame shapeCode)
        (rowShapeStageFuel shape shapeFuel)
        (initialNPOracleState inputLength frame) =
      some (Nat.pair shapeCode frame) := by
  set maximumBits := rowShapeStageBits shapeBits inputLength frame shapeCode
    with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hliftBits : rowFrameLiftBits inputLength frame ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hstageBits :
      preserveRightBits (rowShapeBits shapeBits inputLength) inputLength frame
          shapeCode ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact run_linkPrograms hpositive hlengthBits
    (run_bits_mono (run_rowFrameLiftProgram inputLength frame) hliftBits)
    (run_bits_mono
      (run_preserveRightProgram (rowShapeProgram shape) inputLength
        (rowShapeBits shapeBits inputLength) (rowShapeFuel shape shapeFuel)
        inputLength frame shapeCode
        (run_rowShapeProgram shape inputLength inputLength shapeBits shapeFuel
          shapeCode hshape))
      hstageBits)

/-- Straight-line core of the row's prelude: the scheduled native width is the
left component of the shape code installed in front of the frame, and the
padded high bits of the requested randomness are dropped by the published
low-bit normalizer. -/
private def rowSeedPreludeCoreProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairLeft 3 5 4
  , .unpairRight 3 6 5
  , .unpairRight 6 7 6
  , .pair 4 5 8 7
  , .pair 8 7 0 8
  , .halt 0
  ]

@[simp] private theorem rowSeedPreludeCoreProgram_oracleFree :
    OracleFree rowSeedPreludeCoreProgram := by
  rfl

def rowSeedPreludeOutput (native code inputCode : ℕ) : ℕ :=
  Nat.pair (bitInputPrefixInput native code) inputCode

private def rowSeedPreludeCoreBits (native count width code inputCode : ℕ) :
    ℕ :=
  natBitLength
    (max
      (Nat.pair (Nat.pair native count)
        (Nat.pair code (Nat.pair width inputCode)))
      (rowSeedPreludeOutput native code inputCode))

private theorem run_rowSeedPreludeCoreProgram
    (inputLength native count width code inputCode : ℕ) :
    runNPOracleProgram rowSeedPreludeCoreProgram
        (rowSeedPreludeCoreBits native count width code inputCode) 9
        (initialNPOracleState inputLength
          (Nat.pair (Nat.pair native count)
            (Nat.pair code (Nat.pair width inputCode)))) =
      some (rowSeedPreludeOutput native code inputCode) := by
  set maximumBits := rowSeedPreludeCoreBits native count width code inputCode
    with hmaximumBits
  have hinputBits :
      natBitLength
          (Nat.pair (Nat.pair native count)
            (Nat.pair code (Nat.pair width inputCode))) ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength (rowSeedPreludeOutput native code inputCode) ≤
        maximumBits :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hshapeBits : natBitLength (Nat.pair native count) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (Nat.pair native count)
        (Nat.pair code (Nat.pair width inputCode)))).trans hinputBits
  have hframeBits :
      natBitLength (Nat.pair code (Nat.pair width inputCode)) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair (Nat.pair native count)
        (Nat.pair code (Nat.pair width inputCode)))).trans hinputBits
  have hnativeBits : natBitLength native ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair native count)).trans hshapeBits
  have hcodeBits : natBitLength code ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair code (Nat.pair width inputCode))).trans hframeBits
  have htailBits :
      natBitLength (Nat.pair width inputCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair code (Nat.pair width inputCode))).trans hframeBits
  have hinputCodeBits : natBitLength inputCode ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair width inputCode)).trans htailBits
  have hrequestBits :
      natBitLength (bitInputPrefixInput native code) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (bitInputPrefixInput native code) inputCode)).trans
      houtputBits
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := Nat.pair native count)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hshapeBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair code (Nat.pair width inputCode))
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hframeBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := native)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hnativeBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcodeBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair width inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinputCodeBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := bitInputPrefixInput native code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitInputPrefixInput])
    hrequestBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := rowSeedPreludeOutput native code inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowSeedPreludeOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Straight-line prelude of the row, with the native width read rather than
baked. -/
private def rowSeedPreludeProgram (shape : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (rowShapeStageProgram shape) rowSeedPreludeCoreProgram

private theorem rowSeedPreludeProgram_oracleFree {shape : NPOracleProgram}
    (hshape : OracleFree shape) :
    OracleFree (rowSeedPreludeProgram shape) :=
  oracleFree_linkPrograms (rowShapeStageProgram_oracleFree hshape)
    rowSeedPreludeCoreProgram_oracleFree

def rowSeedPreludeBits
    (shapeBits inputLength native count width code inputCode : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max
        (rowShapeStageBits shapeBits inputLength
          (Nat.pair code (Nat.pair width inputCode)) (Nat.pair native count))
        (rowSeedPreludeCoreBits native count width code inputCode)

def rowSeedPreludeFuel (shape : NPOracleProgram) (shapeFuel : ℕ) : ℕ :=
  linkFuel rowSeedPreludeCoreProgram (rowShapeStageFuel shape shapeFuel) 9

private theorem run_rowSeedPreludeProgram (shape : NPOracleProgram)
    (inputLength shapeBits shapeFuel native count width code inputCode : ℕ)
    (hshape :
      runNPOracleProgram shape shapeBits shapeFuel
          (initialNPOracleState inputLength inputLength) =
        some (Nat.pair native count)) :
    runNPOracleProgram (rowSeedPreludeProgram shape)
        (rowSeedPreludeBits shapeBits inputLength native count width code
          inputCode)
        (rowSeedPreludeFuel shape shapeFuel)
        (initialNPOracleState inputLength
          (Nat.pair code (Nat.pair width inputCode))) =
      some (rowSeedPreludeOutput native code inputCode) := by
  set maximumBits :=
    rowSeedPreludeBits shapeBits inputLength native count width code inputCode
    with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hstageBits :
      rowShapeStageBits shapeBits inputLength
          (Nat.pair code (Nat.pair width inputCode))
          (Nat.pair native count) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcoreBits :
      rowSeedPreludeCoreBits native count width code inputCode ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact run_linkPrograms hpositive hlengthBits
    (run_bits_mono
      (run_rowShapeStageProgram shape inputLength shapeBits shapeFuel
        (Nat.pair code (Nat.pair width inputCode)) (Nat.pair native count)
        hshape)
      hstageBits)
    (run_bits_mono
      (run_rowSeedPreludeCoreProgram inputLength native count width code
        inputCode)
      hcoreBits)

/-- Straight-line frame building the published decision runner's own request
code beside the retained randomness frame. -/
private def rowDecisionFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .copy 1 4 3
  , .pair 3 2 5 4
  , .pair 4 5 6 5
  , .pair 6 0 0 6
  , .halt 0
  ]

@[simp] private theorem rowDecisionFrameProgram_oracleFree :
    OracleFree rowDecisionFrameProgram := by
  rfl

def rowDecisionFrameOutput (inputLength randomnessCode inputCode : ℕ) : ℕ :=
  Nat.pair (Nat.pair inputLength (Nat.pair inputCode randomnessCode))
    (Nat.pair randomnessCode inputCode)

def rowDecisionFrameBits (inputLength randomnessCode inputCode : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair randomnessCode inputCode)
      (rowDecisionFrameOutput inputLength randomnessCode inputCode))

private theorem run_rowDecisionFrameProgram
    (inputLength randomnessCode inputCode : ℕ) :
    runNPOracleProgram rowDecisionFrameProgram
        (rowDecisionFrameBits inputLength randomnessCode inputCode) 7
        (initialNPOracleState inputLength
          (Nat.pair randomnessCode inputCode)) =
      some (rowDecisionFrameOutput inputLength randomnessCode inputCode) := by
  set maximumBits := rowDecisionFrameBits inputLength randomnessCode inputCode
    with hmaximumBits
  have hinputBits :
      natBitLength (Nat.pair randomnessCode inputCode) ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength
          (rowDecisionFrameOutput inputLength randomnessCode inputCode) ≤
        maximumBits :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hrandomnessBits : natBitLength randomnessCode ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair randomnessCode inputCode)).trans
      hinputBits
  have hinputCodeBits : natBitLength inputCode ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair randomnessCode inputCode)).trans
      hinputBits
  have hrequestBits :
      natBitLength (Nat.pair inputLength (Nat.pair inputCode randomnessCode)) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (Nat.pair inputLength (Nat.pair inputCode
        randomnessCode)) (Nat.pair randomnessCode inputCode))).trans
      houtputBits
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair inputLength
        (Nat.pair inputCode randomnessCode))).trans hrequestBits
  have hpayloadBits :
      natBitLength (Nat.pair inputCode randomnessCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair inputLength
        (Nat.pair inputCode randomnessCode))).trans hrequestBits
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := randomnessCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hrandomnessBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hinputCodeBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_copy_instruction (value := inputLength)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hlengthBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputCode randomnessCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpayloadBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair inputLength (Nat.pair inputCode randomnessCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrequestBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := rowDecisionFrameOutput inputLength randomnessCode inputCode)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        rowDecisionFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Straight-line core of the address-table frame: both scheduled numerals are
the two components of the shape code installed in front of the retained clause
frame, and the public length is read from register one. -/
private def rowTableFrameCoreProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairLeft 3 6 5
  , .unpairRight 3 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .copy 1 10 9
  , .pair 10 9 11 10
  , .pair 8 11 12 11
  , .pair 4 12 13 12
  , .pair 5 13 14 13
  , .pair 5 6 15 14
  , .pair 14 15 0 15
  , .halt 0
  ]

@[simp] private theorem rowTableFrameCoreProgram_oracleFree :
    OracleFree rowTableFrameCoreProgram := by
  rfl

def rowTableFrameOutput
    (inputLength native randomnessCode count inputCode decisionCode : ℕ) : ℕ :=
  Nat.pair
    (generatedBalancedRangeInput count
      (rowTableContext inputLength native randomnessCode inputCode))
    (Nat.pair count decisionCode)

private def rowTableFrameCoreBits
    (inputLength native randomnessCode count inputCode decisionCode : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair (Nat.pair native count)
        (Nat.pair decisionCode (Nat.pair randomnessCode inputCode)))
      (rowTableFrameOutput inputLength native randomnessCode count inputCode
        decisionCode))

private theorem run_rowTableFrameCoreProgram
    (inputLength native randomnessCode count inputCode decisionCode : ℕ) :
    runNPOracleProgram rowTableFrameCoreProgram
        (rowTableFrameCoreBits inputLength native randomnessCode count inputCode
          decisionCode)
        16
        (initialNPOracleState inputLength
          (Nat.pair (Nat.pair native count)
            (Nat.pair decisionCode (Nat.pair randomnessCode inputCode)))) =
      some
        (rowTableFrameOutput inputLength native randomnessCode count inputCode
          decisionCode) := by
  set maximumBits :=
    rowTableFrameCoreBits inputLength native randomnessCode count inputCode
      decisionCode with hmaximumBits
  have hinputBits :
      natBitLength
          (Nat.pair (Nat.pair native count)
            (Nat.pair decisionCode (Nat.pair randomnessCode inputCode))) ≤
        maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength
          (rowTableFrameOutput inputLength native randomnessCode count
            inputCode decisionCode) ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hshapeBits : natBitLength (Nat.pair native count) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (Nat.pair native count)
        (Nat.pair decisionCode (Nat.pair randomnessCode inputCode)))).trans
      hinputBits
  have hclauseBits :
      natBitLength (Nat.pair decisionCode (Nat.pair randomnessCode inputCode)) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair (Nat.pair native count)
        (Nat.pair decisionCode (Nat.pair randomnessCode inputCode)))).trans
      hinputBits
  have hnativeBits : natBitLength native ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair native count)).trans hshapeBits
  have hcountBits : natBitLength count ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair native count)).trans hshapeBits
  have hdecisionBits : natBitLength decisionCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair decisionCode
        (Nat.pair randomnessCode inputCode))).trans hclauseBits
  have htailBits :
      natBitLength (Nat.pair randomnessCode inputCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair decisionCode
        (Nat.pair randomnessCode inputCode))).trans hclauseBits
  have hrandomnessBits : natBitLength randomnessCode ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair randomnessCode inputCode)).trans
      htailBits
  have hinputCodeBits : natBitLength inputCode ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair randomnessCode inputCode)).trans
      htailBits
  have hrangeBits :
      natBitLength
          (generatedBalancedRangeInput count
            (rowTableContext inputLength native randomnessCode inputCode)) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair
        (generatedBalancedRangeInput count
          (rowTableContext inputLength native randomnessCode inputCode))
        (Nat.pair count decisionCode))).trans houtputBits
  have hclauseFrameBits :
      natBitLength (Nat.pair count decisionCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair
        (generatedBalancedRangeInput count
          (rowTableContext inputLength native randomnessCode inputCode))
        (Nat.pair count decisionCode))).trans houtputBits
  have hcontextBits :
      natBitLength (rowTableContext inputLength native randomnessCode
        inputCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair count
        (rowTableContext inputLength native randomnessCode
          inputCode))).trans hrangeBits
  have hinnerBits :
      natBitLength
          (Nat.pair randomnessCode (Nat.pair inputLength inputCode)) ≤
        maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair native
        (Nat.pair randomnessCode (Nat.pair inputLength inputCode)))).trans
      hcontextBits
  have hcoreBits :
      natBitLength (Nat.pair inputLength inputCode) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair randomnessCode
        (Nat.pair inputLength inputCode))).trans hinnerBits
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair inputLength inputCode)).trans
      hcoreBits
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairLeft_instruction (value := Nat.pair native count)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hshapeBits]
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair decisionCode (Nat.pair randomnessCode inputCode))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hclauseBits]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairLeft_instruction (value := native)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hnativeBits]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairRight_instruction (value := count)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcountBits]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := decisionCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hdecisionBits]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair randomnessCode inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := randomnessCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrandomnessBits]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinputCodeBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_copy_instruction (value := inputLength)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hlengthBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputLength inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcoreBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair randomnessCode (Nat.pair inputLength inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinnerBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (value := rowTableContext inputLength native randomnessCode inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowTableContext])
    hcontextBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      generatedBalancedRangeInput count
        (rowTableContext inputLength native randomnessCode inputCode))
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        generatedBalancedRangeInput])
    hrangeBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair count decisionCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hclauseFrameBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      rowTableFrameOutput inputLength native randomnessCode count inputCode
        decisionCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowTableFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Straight-line frame building the address table's range request beside the
retained clause frame, with both scheduled numerals read rather than baked. -/
private def rowTableFrameProgram (shape : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (rowShapeStageProgram shape) rowTableFrameCoreProgram

private theorem rowTableFrameProgram_oracleFree {shape : NPOracleProgram}
    (hshape : OracleFree shape) : OracleFree (rowTableFrameProgram shape) :=
  oracleFree_linkPrograms (rowShapeStageProgram_oracleFree hshape)
    rowTableFrameCoreProgram_oracleFree

def rowTableFrameBits
    (shapeBits inputLength native randomnessCode count inputCode
      decisionCode : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max
        (rowShapeStageBits shapeBits inputLength
          (Nat.pair decisionCode (Nat.pair randomnessCode inputCode))
          (Nat.pair native count))
        (rowTableFrameCoreBits inputLength native randomnessCode count inputCode
          decisionCode)

def rowTableFrameFuel (shape : NPOracleProgram) (shapeFuel : ℕ) : ℕ :=
  linkFuel rowTableFrameCoreProgram (rowShapeStageFuel shape shapeFuel) 16

private theorem run_rowTableFrameProgram (shape : NPOracleProgram)
    (inputLength shapeBits shapeFuel native randomnessCode count inputCode
      decisionCode : ℕ)
    (hshape :
      runNPOracleProgram shape shapeBits shapeFuel
          (initialNPOracleState inputLength inputLength) =
        some (Nat.pair native count)) :
    runNPOracleProgram (rowTableFrameProgram shape)
        (rowTableFrameBits shapeBits inputLength native randomnessCode count
          inputCode decisionCode)
        (rowTableFrameFuel shape shapeFuel)
        (initialNPOracleState inputLength
          (Nat.pair decisionCode (Nat.pair randomnessCode inputCode))) =
      some
        (rowTableFrameOutput inputLength native randomnessCode count inputCode
          decisionCode) := by
  set maximumBits :=
    rowTableFrameBits shapeBits inputLength native randomnessCode count
      inputCode decisionCode with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hstageBits :
      rowShapeStageBits shapeBits inputLength
          (Nat.pair decisionCode (Nat.pair randomnessCode inputCode))
          (Nat.pair native count) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcoreBits :
      rowTableFrameCoreBits inputLength native randomnessCode count inputCode
          decisionCode ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact run_linkPrograms hpositive hlengthBits
    (run_bits_mono
      (run_rowShapeStageProgram shape inputLength shapeBits shapeFuel
        (Nat.pair decisionCode (Nat.pair randomnessCode inputCode))
        (Nat.pair native count) hshape)
      hstageBits)
    (run_bits_mono
      (run_rowTableFrameCoreProgram inputLength native randomnessCode count
        inputCode decisionCode)
      hcoreBits)

/-! ### The composed address-table half -/

/-- The emitted address table of one decision row. -/
def rowSeedTable {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) : List ℕ :=
  rowAddressTable (pcp.queryCount n) (pcp.nativeWidth n)
    (rowRandomnessCode (pcp.nativeWidth n) code) (rowProjectionCode pcp input)

theorem rowSeedTable_eq_range_map
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) :
    rowSeedTable pcp input code =
      (List.range (pcp.queryCount n)).map (rowAddressOf pcp input code) :=
  rowAddressTable_eq_rowAddressOf pcp input code

theorem rowSeedTable_length
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) :
    (rowSeedTable pcp input code).length = pcp.queryCount n := by
  rw [rowSeedTable_eq_range_map]
  simp

theorem rowSeedTable_getElem
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) (index : ℕ)
    (hindex : index < (rowSeedTable pcp input code).length) :
    (rowSeedTable pcp input code)[index] = rowAddressOf pcp input code index := by
  have hrange :
      rowSeedTable pcp input code =
        (List.range (pcp.queryCount n)).map (rowAddressOf pcp input code) :=
    rowSeedTable_eq_range_map pcp input code
  simp only [hrange] at hindex ⊢
  simp

private def rowSeedTableStageProgram (query shape : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (rowTableFrameProgram shape)
    (preserveRightProgram (rowAddressTableProgram (rowWeightProgram query)))

private def rowSeedDecisionStageProgram (query decision shape :
    NPOracleProgram) : NPOracleProgram :=
  linkPrograms (preserveRightProgram decision)
    (rowSeedTableStageProgram query shape)

private def rowSeedFrameStageProgram (query decision shape : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms rowDecisionFrameProgram
    (rowSeedDecisionStageProgram query decision shape)

private def rowSeedPrefixStageProgram (query decision shape :
    NPOracleProgram) : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitInputPrefixProgram)
    (rowSeedFrameStageProgram query decision shape)

/-- The address-table half of one decision row. -/
def rowSeedProgram (query decision shape : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (rowSeedPreludeProgram shape)
    (rowSeedPrefixStageProgram query decision shape)

theorem rowSeedProgram_oracleFree
    {query decision shape : NPOracleProgram} (hquery : OracleFree query)
    (hdecision : OracleFree decision) (hshape : OracleFree shape) :
    OracleFree (rowSeedProgram query decision shape) := by
  apply oracleFree_linkPrograms
  · exact rowSeedPreludeProgram_oracleFree hshape
  · apply oracleFree_linkPrograms
    · exact preserveRightProgram_oracleFree bitInputPrefixProgram
        bitInputPrefixProgram_oracleFree
    · apply oracleFree_linkPrograms
      · exact rowDecisionFrameProgram_oracleFree
      · apply oracleFree_linkPrograms
        · exact preserveRightProgram_oracleFree decision hdecision
        · apply oracleFree_linkPrograms
          · exact rowTableFrameProgram_oracleFree hshape
          · exact preserveRightProgram_oracleFree _
              (rowAddressTableProgram_oracleFree
                (rowWeightProgram_oracleFree hquery))

def rowSeedFuel {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) : ℕ :=
  linkFuel
    (rowSeedPrefixStageProgram pcp.query.program pcp.decisionRunner.program
      pcp.shape.program)
    (rowSeedPreludeFuel pcp.shape.program (pcp.shape.budget n))
    (linkFuel
      (rowSeedFrameStageProgram pcp.query.program pcp.decisionRunner.program
        pcp.shape.program)
      (preserveRightFuel (bitInputPrefixFuel (pcp.nativeWidth n) code))
      (linkFuel
        (rowSeedDecisionStageProgram pcp.query.program
          pcp.decisionRunner.program pcp.shape.program)
        7
        (linkFuel
          (rowSeedTableStageProgram pcp.query.program pcp.shape.program)
          (preserveRightFuel (rowDecisionBudget pcp n))
          (linkFuel
            (preserveRightProgram
              (rowAddressTableProgram (rowWeightProgram pcp.query.program)))
            (rowTableFrameFuel pcp.shape.program (pcp.shape.budget n))
            (preserveRightFuel
              (rowAddressTableFuel (rowWeightProgram pcp.query.program)
                (rowWeightTableFuel pcp input
                  (rowRandomnessCode (pcp.nativeWidth n) code))
                n (pcp.nativeWidth n)
                (rowRandomnessCode (pcp.nativeWidth n) code)
                (pcp.queryCount n) (encodeBitInput input)
                (rowProjectionCode pcp input)))))))

def rowSeedBits {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (width code : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength n) <|
      max
        (rowSeedPreludeBits (pcp.shape.budget n) n (pcp.nativeWidth n)
          (pcp.queryCount n) width code (encodeBitInput input)) <|
        max
          (preserveRightBits (bitInputPrefixBits (pcp.nativeWidth n) code)
            (bitInputPrefixInput (pcp.nativeWidth n) code)
            (encodeBitInput input)
            (rowRandomnessCode (pcp.nativeWidth n) code)) <|
          max
            (rowDecisionFrameBits n
              (rowRandomnessCode (pcp.nativeWidth n) code)
              (encodeBitInput input)) <|
            max
              (preserveRightBits (rowDecisionBudget pcp n)
                (Nat.pair n
                  (Nat.pair (encodeBitInput input)
                    (rowRandomnessCode (pcp.nativeWidth n) code)))
                (Nat.pair (rowRandomnessCode (pcp.nativeWidth n) code)
                  (encodeBitInput input))
                (rowDecisionCode pcp input code)) <|
              max
                (rowTableFrameBits (pcp.shape.budget n) n (pcp.nativeWidth n)
                  (rowRandomnessCode (pcp.nativeWidth n) code)
                  (pcp.queryCount n) (encodeBitInput input)
                  (rowDecisionCode pcp input code))
                (preserveRightBits
                  (rowAddressTableBits
                    (rowWeightTableBits pcp input
                      (rowRandomnessCode (pcp.nativeWidth n) code))
                    n (pcp.nativeWidth n)
                    (rowRandomnessCode (pcp.nativeWidth n) code)
                    (pcp.queryCount n) (encodeBitInput input)
                    (rowProjectionCode pcp input))
                  (generatedBalancedRangeInput (pcp.queryCount n)
                    (rowTableContext n (pcp.nativeWidth n)
                      (rowRandomnessCode (pcp.nativeWidth n) code)
                      (encodeBitInput input)))
                  (Nat.pair (pcp.queryCount n) (rowDecisionCode pcp input code))
                  (encodeBalancedList (rowSeedTable pcp input code)))

/-- **The two scheduled numerals, computed by the published shape runner.**
Both are components of one shape code produced from the public length alone. -/
private theorem run_rowShapeRunner
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) :
    runNPOracleProgram pcp.shape.program (pcp.shape.budget n)
        (pcp.shape.budget n) (initialNPOracleState n n) =
      some (Nat.pair (pcp.nativeWidth n) (pcp.queryCount n)) := by
  have hcode :
      Nat.pair (pcp.nativeWidth n) (pcp.queryCount n) = pcp.shape.execute n := by
    simp only [ExecutableProjectionPCP.nativeWidth,
      ExecutableProjectionPCP.queryCount, ExecutableProjectionPCP.shapeCode]
    exact Nat.pair_unpair _
  rw [hcode]
  exact pcp.shape.run_eq_execute n

/-- **The address-table half, executed.**  Modulo nothing, the fixed program
selects the native randomness, calls the published decision runner, and emits
the whole proof-table address list of the requested row. -/
theorem run_rowSeedProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (width code : ℕ) :
    runNPOracleProgram
        (rowSeedProgram pcp.query.program pcp.decisionRunner.program
          pcp.shape.program)
        (rowSeedBits pcp input width code) (rowSeedFuel pcp input code)
        (initialNPOracleState n
          (Nat.pair code (Nat.pair width (encodeBitInput input)))) =
      some
        (Nat.pair (encodeBalancedList (rowSeedTable pcp input code))
          (Nat.pair (pcp.queryCount n) (rowDecisionCode pcp input code))) := by
  set native := pcp.nativeWidth n with hnative
  set count := pcp.queryCount n with hcount
  set inputCode := encodeBitInput input with hinputCode
  set randomnessCode := rowRandomnessCode native code with hrandomnessCode
  set decisionCode := rowDecisionCode pcp input code with hdecisionCode
  set maximumBits := rowSeedBits pcp input width code with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength n ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreludeBits :
      rowSeedPreludeBits (pcp.shape.budget n) n native count width code
          inputCode ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprefixBits :
      preserveRightBits (bitInputPrefixBits native code)
          (bitInputPrefixInput native code) inputCode randomnessCode ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hframeBits :
      rowDecisionFrameBits n randomnessCode inputCode ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hdecisionBits :
      preserveRightBits (rowDecisionBudget pcp n)
          (Nat.pair n (Nat.pair inputCode randomnessCode))
          (Nat.pair randomnessCode inputCode) decisionCode ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have htableFrameBits :
      rowTableFrameBits (pcp.shape.budget n) n native randomnessCode count
          inputCode decisionCode ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have htableBits :
      preserveRightBits
          (rowAddressTableBits (rowWeightTableBits pcp input randomnessCode) n
            native randomnessCode count inputCode (rowProjectionCode pcp input))
          (generatedBalancedRangeInput count
            (rowTableContext n native randomnessCode inputCode))
          (Nat.pair count decisionCode)
          (encodeBalancedList (rowSeedTable pcp input code)) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hshapeRun :
      runNPOracleProgram pcp.shape.program (pcp.shape.budget n)
          (pcp.shape.budget n) (initialNPOracleState n n) =
        some (Nat.pair native count) :=
    run_rowShapeRunner pcp n
  have hprelude :=
    run_bits_mono
      (run_rowSeedPreludeProgram pcp.shape.program n (pcp.shape.budget n)
        (pcp.shape.budget n) native count width code inputCode hshapeRun)
      hpreludeBits
  have hprefixSource :
      runNPOracleProgram bitInputPrefixProgram (bitInputPrefixBits native code)
          (bitInputPrefixFuel native code)
          (initialNPOracleState n (bitInputPrefixInput native code)) =
        some randomnessCode :=
    run_bitInputPrefixProgram n native code (bitInputPrefixBits native code) 0
      (Nat.le_refl _)
  have hprefix :
      runNPOracleProgram (preserveRightProgram bitInputPrefixProgram)
          maximumBits (preserveRightFuel (bitInputPrefixFuel native code))
          (initialNPOracleState n
            (rowSeedPreludeOutput native code inputCode)) =
        some (Nat.pair randomnessCode inputCode) :=
    run_bits_mono
      (run_preserveRightProgram bitInputPrefixProgram n
        (bitInputPrefixBits native code) (bitInputPrefixFuel native code)
        (bitInputPrefixInput native code) inputCode randomnessCode
        hprefixSource)
      hprefixBits
  have hframe :=
    run_bits_mono
      (run_rowDecisionFrameProgram n randomnessCode inputCode) hframeBits
  have hdecision :
      runNPOracleProgram (preserveRightProgram pcp.decisionRunner.program)
          maximumBits (preserveRightFuel (rowDecisionBudget pcp n))
          (initialNPOracleState n
            (rowDecisionFrameOutput n randomnessCode inputCode)) =
        some (Nat.pair decisionCode (Nat.pair randomnessCode inputCode)) :=
    run_bits_mono
      (run_preserveRightProgram pcp.decisionRunner.program n
        (rowDecisionBudget pcp n) (rowDecisionBudget pcp n)
        (Nat.pair n (Nat.pair inputCode randomnessCode))
        (Nat.pair randomnessCode inputCode) decisionCode
        (run_rowDecisionStage pcp input code))
      hdecisionBits
  have htableFrame :=
    run_bits_mono
      (run_rowTableFrameProgram pcp.shape.program n (pcp.shape.budget n)
        (pcp.shape.budget n) native randomnessCode count inputCode decisionCode
        hshapeRun)
      htableFrameBits
  have htable :
      runNPOracleProgram
          (preserveRightProgram
            (rowAddressTableProgram (rowWeightProgram pcp.query.program)))
          maximumBits
          (preserveRightFuel
            (rowAddressTableFuel (rowWeightProgram pcp.query.program)
              (rowWeightTableFuel pcp input randomnessCode) n native
              randomnessCode count inputCode (rowProjectionCode pcp input)))
          (initialNPOracleState n
            (rowTableFrameOutput n native randomnessCode count inputCode
              decisionCode)) =
        some
          (Nat.pair (encodeBalancedList (rowSeedTable pcp input code))
            (Nat.pair count decisionCode)) :=
    run_bits_mono
      (run_preserveRightProgram
        (rowAddressTableProgram (rowWeightProgram pcp.query.program)) n
        (rowAddressTableBits (rowWeightTableBits pcp input randomnessCode) n
          native randomnessCode count inputCode (rowProjectionCode pcp input))
        (rowAddressTableFuel (rowWeightProgram pcp.query.program)
          (rowWeightTableFuel pcp input randomnessCode) n native randomnessCode
          count inputCode (rowProjectionCode pcp input))
        (generatedBalancedRangeInput count
          (rowTableContext n native randomnessCode inputCode))
        (Nat.pair count decisionCode)
        (encodeBalancedList (rowSeedTable pcp input code))
        (run_rowAddressTableProgram (rowWeightProgram pcp.query.program)
          (rowWeightTableBits pcp input randomnessCode)
          (rowWeightTableFuel pcp input randomnessCode) n native randomnessCode
          count inputCode (rowProjectionCode pcp input)
          (fun query hquery bit hbit =>
            run_rowWeightProgram_uniform pcp input randomnessCode query bit
              hquery hbit)))
      htableBits
  have htableStage :=
    run_linkPrograms hpositive hlengthBits htableFrame htable
  have hdecisionStage :=
    run_linkPrograms hpositive hlengthBits hdecision htableStage
  have hframeStage :=
    run_linkPrograms hpositive hlengthBits hframe hdecisionStage
  have hprefixStage :=
    run_linkPrograms hpositive hlengthBits hprefix hframeStage
  exact run_linkPrograms hpositive hlengthBits hprelude hprefixStage

/-! ### The whole decision row -/

/-- **The decision-row stage.**  Its only parameters are the three published
runner programs; no scheduled numeral appears in the stream. -/
def outerProofRowProgram (query decision shape : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (rowSeedProgram query decision shape) rowStreamProgram

theorem outerProofRowProgram_oracleFree
    {query decision shape : NPOracleProgram} (hquery : OracleFree query)
    (hdecision : OracleFree decision) (hshape : OracleFree shape) :
    OracleFree (outerProofRowProgram query decision shape) :=
  oracleFree_linkPrograms (rowSeedProgram_oracleFree hquery hdecision hshape)
    rowStreamProgram_oracleFree

def outerProofRowFuel {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) : ℕ :=
  linkFuel rowStreamProgram (rowSeedFuel pcp input code)
    (rowStreamFuel n (pcp.queryCount n) (rowDecisionCode pcp input code)
      (rowSeedTable pcp input code) (rowAddressOf pcp input code))

def outerProofRowBits {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (width code : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength n) <|
      max (rowSeedBits pcp input width code)
        (rowStreamBits n (pcp.queryCount n) (rowDecisionCode pcp input code)
          (rowSeedTable pcp input code) (rowAddressOf pcp input code))

/-- **The decision-row stage, executed.**  From `pair code (pair width
(encodeBitInput input))` the fixed program emits exactly the raw clause list of
the requested decision row. -/
theorem run_outerProofRowProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (width code : ℕ) (hcount : 0 < pcp.queryCount n) :
    runNPOracleProgram
        (outerProofRowProgram pcp.query.program pcp.decisionRunner.program
          pcp.shape.program)
        (outerProofRowBits pcp input width code)
        (outerProofRowFuel pcp input code)
        (initialNPOracleState n
          (Nat.pair code (Nat.pair width (encodeBitInput input)))) =
      some
        (encodeTaggedList
          (rowRawStream (pcp.queryCount n) (rowDecisionCode pcp input code)
            (rowAddressOf pcp input code))) := by
  set maximumBits := outerProofRowBits pcp input width code with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength n ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hseedBits : rowSeedBits pcp input width code ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hstreamBits :
      rowStreamBits n (pcp.queryCount n) (rowDecisionCode pcp input code)
          (rowSeedTable pcp input code) (rowAddressOf pcp input code) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hseed :=
    run_bits_mono (run_rowSeedProgram pcp input width code) hseedBits
  have hstream :=
    run_bits_mono
      (run_rowStreamProgram n (pcp.queryCount n) (rowDecisionCode pcp input code)
        (rowSeedTable pcp input code) (rowAddressOf pcp input code) hcount
        (rowSeedTable_length pcp input code)
        (fun index hindex => rowSeedTable_getElem pcp input code index hindex))
      hstreamBits
  exact run_linkPrograms hpositive hlengthBits hseed hstream

/-! ## 4. The Case-1 chain, unconditionally -/

/-- The decision-row stage of the hierarchy PCP.  It no longer depends on the
source index: both scheduled numerals are read at run time. -/
def outerProofRowScheduledProgram {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) : NPOracleProgram :=
  outerProofRowProgram outer.pcp.query.program outer.pcp.decisionRunner.program
    outer.pcp.shape.program

theorem outerProofRowScheduledProgram_oracleFree {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    OracleFree (outerProofRowScheduledProgram outer) :=
  outerProofRowProgram_oracleFree outer.pcp.queryOracleFree
    outer.pcp.decisionOracleFree outer.pcp.shapeOracleFree

def outerProofRowScheduledBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) (code : ℕ) : ℕ :=
  outerProofRowBits outer.pcp input (scheduledWidth outer sourceIndex) code

def outerProofRowScheduledFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) (code : ℕ) : ℕ :=
  outerProofRowFuel outer.pcp input code

/-- **The `hrow` premise, discharged.**  At the published schedule the fixed
row stage emits exactly the padded decision row consumed by
`OuterProofRecoveryFormulaSeedProgram`. -/
theorem run_outerProofRowScheduledProgram {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) (code : ℕ)
    (hcount : 0 < outer.pcp.queryCount (sourceLength sourceIndex)) :
    runNPOracleProgram (outerProofRowScheduledProgram outer)
        (outerProofRowScheduledBits outer sourceIndex input code)
        (outerProofRowScheduledFuel outer sourceIndex input code)
        (initialNPOracleState (sourceLength sourceIndex)
          (Nat.pair code
            (Nat.pair (scheduledWidth outer sourceIndex)
              (encodeBitInput input)))) =
      some
        (encodeTaggedList
          (outerProofRowStream (paddedOuterPCP outer) input code)) := by
  rw [← rowRawStream_eq_scheduledOuterProofRowStream outer sourceIndex input
    code hcount]
  exact run_outerProofRowProgram outer.pcp input
    (scheduledWidth outer sourceIndex) code hcount

/-! ### The Case-1 recovery seed -/

/-- The Case-1 recovery seed with its decision-row stage installed. -/
def outerProofRowSeedProgram {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ) : NPOracleProgram :=
  outerProofFormulaSeedProgram (outerProofRowScheduledProgram outer)
    (scheduledWidth outer sourceIndex)

theorem outerProofRowSeedProgram_oracleFree {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ) :
    OracleFree (outerProofRowSeedProgram outer sourceIndex) :=
  outerProofFormulaSeedProgram_oracleFree
    (outerProofRowScheduledProgram_oracleFree outer) _

def outerProofRowSeedBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) : ℕ :=
  outerProofFormulaSeedBits (paddedOuterPCP outer) input
    (outerProofRowScheduledBits outer sourceIndex input)

def outerProofRowSeedFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) : ℕ :=
  outerProofFormulaSeedFuel (outerProofRowScheduledProgram outer)
    (paddedOuterPCP outer) input
    (outerProofRowScheduledFuel outer sourceIndex input)

/-- **The Case-1 recovery seed, unconditionally.**  One fixed oracle-free
program turns the raw refuter word into
`recoveredProofCompilerSeedOutput`; no callee premise remains. -/
theorem run_outerProofRowSeedProgram {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex))
    (hcount : 0 < outer.pcp.queryCount (sourceLength sourceIndex)) :
    runNPOracleProgram (outerProofRowSeedProgram outer sourceIndex)
        (outerProofRowSeedBits outer sourceIndex input)
        (outerProofRowSeedFuel outer sourceIndex input)
        (initialNPOracleState (sourceLength sourceIndex)
          (encodeBitInput input)) =
      some (recoveredProofCompilerSeedOutput outer sourceIndex input) :=
  run_outerProofRecoveryFormulaSeedProgram
    (outerProofRowScheduledProgram outer) outer sourceIndex input
    (outerProofRowScheduledBits outer sourceIndex input)
    (outerProofRowScheduledFuel outer sourceIndex input)
    (fun code _ =>
      run_outerProofRowScheduledProgram outer sourceIndex input code hcount)

/-! ### The Case-1 target bit from the requested point code -/

/-- **The Case-1 target bit, from the point code alone.**  Only the published
target-bit run of the fixed dispatcher remains as a hypothesis: the recovery
side of the Case-1 path is now entirely unconditional. -/
theorem run_caseOneTargetBitFromPointProgram_closed
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceIndex target pointCode targetBits targetFuel value : ℕ)
    (hcount : 0 < outer.pcp.queryCount (sourceLength sourceIndex))
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
        (caseOneTargetBitFromPointProgram algorithm
          source.refuter.runner.program
          (outerProofRowScheduledProgram outer)
          machine.description (sourceLength sourceIndex)
          (scheduledWidth outer sourceIndex))
        (caseOneTargetBitFromPointBits algorithm outer machine sourceIndex
          target pointCode targetBits
          (outerProofRowScheduledBits outer sourceIndex
            (scheduledRefuterWord source machine sourceIndex)))
        (caseOneTargetBitFromPointFuel algorithm
          (outerProofRowScheduledProgram outer) outer machine
          sourceIndex
          (outerProofRowScheduledFuel outer sourceIndex
            (scheduledRefuterWord source machine sourceIndex))
          targetFuel)
        (initialNPOracleState target pointCode) =
      some value :=
  run_caseOneTargetBitFromPointProgram algorithm
    (outerProofRowScheduledProgram outer) outer machine sourceIndex
    target pointCode targetBits targetFuel value
    (outerProofRowScheduledBits outer sourceIndex
      (scheduledRefuterWord source machine sourceIndex))
    (outerProofRowScheduledFuel outer sourceIndex
      (scheduledRefuterWord source machine sourceIndex))
    (fun code _ =>
      run_outerProofRowScheduledProgram outer sourceIndex
        (scheduledRefuterWord source machine sourceIndex) code hcount)
    htarget

/-! ### Both published schedules -/

/-- Source index selected by the inverse schedule at one target length. -/
noncomputable def inverseScheduledIndex (contracts : PublishedContracts)
    {clockDepth : ℕ} {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (advantageExponent : ℝ)
    (target : ℕ) : ℕ :=
  inverseSourceIndex
    (inverseSelectedSource contracts outer
      (inverseCoreAdvantagePower advantageExponent) target)

/-- Source index selected by the fixed-rate schedule at one target length. -/
noncomputable def fixedScheduledIndex (contracts : PublishedContracts)
    {clockDepth : ℕ} {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (requestedRate target : ℕ) : ℕ :=
  fixedSelectedSource contracts outer requestedRate target

/-- **The inverse schedule's Case-1 target bit, unconditionally.**  The
recovery seed is no longer a hypothesis: it is the fixed program of §4. -/
theorem run_caseOneTargetBitProgram_inverse_closed
    (contracts : PublishedContracts) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (advantageExponent : ℝ) (target : ℕ)
    (honset :
      (inverseEnvelope contracts outer
        (inverseCoreAdvantagePower advantageExponent)).targetOnset ≤ target)
    {input : BitInput
      (sourceLength
        (inverseScheduledIndex contracts outer advantageExponent target))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseScheduledIndex contracts outer advantageExponent target) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (inverseScheduledIndex contracts outer advantageExponent target))
      input)
    (hready :
      inverseCaseOneOnset contracts outer
          (inverseCoreAdvantagePower advantageExponent) ≤
        inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
    (point : BitInput target)
    (hcount :
      0 < outer.pcp.queryCount
        (sourceLength
          (inverseScheduledIndex contracts outer advantageExponent target))) :
    runNPOracleProgram
        (caseOneTargetBitProgram (publishedAmplifier contracts).algorithm
          (outerProofRowSeedProgram outer
            (inverseScheduledIndex contracts outer advantageExponent target)))
        (caseOneTargetBitBits (publishedAmplifier contracts).algorithm outer
          (inverseScheduledIndex contracts outer advantageExponent target)
          input
          (outerProofRowSeedBits outer
            (inverseScheduledIndex contracts outer advantageExponent target)
            input)
          target (encodeBitInput point)
          (targetBitCaseOneBits (publishedAmplifier contracts).algorithm target
            ((publishedAmplifier contracts).algorithm.outputArity
              (scheduledAmplifierRequest outer
                (inverseScheduledIndex contracts outer advantageExponent
                  target)
                input))
            ((publishedAmplifier contracts).algorithm.descriptor
              (scheduledAmplifierRequest outer
                (inverseScheduledIndex contracts outer advantageExponent
                  target)
                input))
            (encodeBitInput point)))
        (caseOneTargetBitFuel (publishedAmplifier contracts).algorithm
          (outerProofRowSeedProgram outer
            (inverseScheduledIndex contracts outer advantageExponent target))
          outer
          (inverseScheduledIndex contracts outer advantageExponent target)
          input
          (outerProofRowSeedFuel outer
            (inverseScheduledIndex contracts outer advantageExponent target)
            input)
          (targetBitCaseOneFuel (publishedAmplifier contracts).algorithm
            ((publishedAmplifier contracts).algorithm.outputArity
              (scheduledAmplifierRequest outer
                (inverseScheduledIndex contracts outer advantageExponent
                  target)
                input))
            ((publishedAmplifier contracts).algorithm.descriptor
              (scheduledAmplifierRequest outer
                (inverseScheduledIndex contracts outer advantageExponent
                  target)
                input))
            (encodeBitInput point)))
        (initialNPOracleState target
          (Nat.pair (encodeBitInput input)
            (Nat.pair
              (sourceLength
                (inverseScheduledIndex contracts outer advantageExponent
                  target))
              (encodeBitInput point)))) =
      some
        (inverseCaseOneTargetFunction contracts outer advantageExponent target
          honset data hyes hready point).toNat :=
  run_caseOneTargetBitProgram_inverse contracts outer
    (outerProofRowSeedProgram outer
      (inverseScheduledIndex contracts outer advantageExponent target))
    advantageExponent target honset data hyes hready point
    (outerProofRowSeedBits outer
      (inverseScheduledIndex contracts outer advantageExponent target) input)
    (outerProofRowSeedFuel outer
      (inverseScheduledIndex contracts outer advantageExponent target) input)
    (run_outerProofRowSeedProgram outer
      (inverseScheduledIndex contracts outer advantageExponent target) input
      hcount)

/-- **The fixed-rate schedule's Case-1 target bit, unconditionally.** -/
theorem run_caseOneTargetBitProgram_fixed_closed
    (contracts : PublishedContracts) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (requestedRate target : ℕ)
    (honset :
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target)
    {input : BitInput
      (sourceLength
        (fixedScheduledIndex contracts outer requestedRate target))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedScheduledIndex contracts outer requestedRate target) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedScheduledIndex contracts outer requestedRate target))
      input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤
        fixedSelectedSource contracts outer requestedRate target)
    (point : BitInput target)
    (hcount :
      0 < outer.pcp.queryCount
        (sourceLength
          (fixedScheduledIndex contracts outer requestedRate target))) :
    runNPOracleProgram
        (caseOneTargetBitProgram (publishedAmplifier contracts).algorithm
          (outerProofRowSeedProgram outer
            (fixedScheduledIndex contracts outer requestedRate target)))
        (caseOneTargetBitBits (publishedAmplifier contracts).algorithm outer
          (fixedScheduledIndex contracts outer requestedRate target) input
          (outerProofRowSeedBits outer
            (fixedScheduledIndex contracts outer requestedRate target) input)
          target (encodeBitInput point)
          (targetBitCaseOneBits (publishedAmplifier contracts).algorithm target
            ((publishedAmplifier contracts).algorithm.outputArity
              (scheduledAmplifierRequest outer
                (fixedScheduledIndex contracts outer requestedRate target)
                input))
            ((publishedAmplifier contracts).algorithm.descriptor
              (scheduledAmplifierRequest outer
                (fixedScheduledIndex contracts outer requestedRate target)
                input))
            (encodeBitInput point)))
        (caseOneTargetBitFuel (publishedAmplifier contracts).algorithm
          (outerProofRowSeedProgram outer
            (fixedScheduledIndex contracts outer requestedRate target))
          outer (fixedScheduledIndex contracts outer requestedRate target)
          input
          (outerProofRowSeedFuel outer
            (fixedScheduledIndex contracts outer requestedRate target) input)
          (targetBitCaseOneFuel (publishedAmplifier contracts).algorithm
            ((publishedAmplifier contracts).algorithm.outputArity
              (scheduledAmplifierRequest outer
                (fixedScheduledIndex contracts outer requestedRate target)
                input))
            ((publishedAmplifier contracts).algorithm.descriptor
              (scheduledAmplifierRequest outer
                (fixedScheduledIndex contracts outer requestedRate target)
                input))
            (encodeBitInput point)))
        (initialNPOracleState target
          (Nat.pair (encodeBitInput input)
            (Nat.pair
              (sourceLength
                (fixedScheduledIndex contracts outer requestedRate target))
              (encodeBitInput point)))) =
      some
        (fixedCaseOneTargetFunction contracts outer requestedRate target
          honset data hyes hready point).toNat :=
  run_caseOneTargetBitProgram_fixed contracts outer
    (outerProofRowSeedProgram outer
      (fixedScheduledIndex contracts outer requestedRate target))
    requestedRate target honset data hyes hready point
    (outerProofRowSeedBits outer
      (fixedScheduledIndex contracts outer requestedRate target) input)
    (outerProofRowSeedFuel outer
      (fixedScheduledIndex contracts outer requestedRate target) input)
    (run_outerProofRowSeedProgram outer
      (fixedScheduledIndex contracts outer requestedRate target) input hcount)

end NearCubicWires.OuterProofRowStageProgram
