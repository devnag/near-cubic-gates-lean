import Proof.MachineModel.CanonicalSignedAtomRequestProgram
import Proof.MachineModel.TaggedProgramChoice

namespace NearCubicWires.CanonicalGateAtomHeadListProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalSignedAtomRequestProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

def indexedRangeRequests (inputLength count context : ℕ) : List ℕ :=
  balancedRangeRequestAtoms inputLength context 0 count

private theorem indexedRangeRequests_eq (inputLength count context : ℕ) :
    indexedRangeRequests inputLength count context =
      (List.range count).map fun index =>
        balancedRangeRequestAtom inputLength index context := by
  unfold indexedRangeRequests
  rw [balancedRangeRequestAtoms_eq_map_range]
  simp

private theorem signedAtomFrameIndex_range
    (inputLength index context : ℕ) :
    signedAtomFrameIndex (balancedRangeRequestAtom inputLength index context) =
      index := by
  simp [signedAtomFrameIndex, balancedRangeRequestAtom]

private theorem map_signedAtomFrameIndex_indexed
    (inputLength count context : ℕ) (leafOutput : ℕ → ℕ) :
    (indexedRangeRequests inputLength count context).map
        (fun raw => leafOutput (signedAtomFrameIndex raw)) =
      (List.range count).map leafOutput := by
  rw [indexedRangeRequests_eq, List.map_map]
  refine List.map_congr_left ?_
  intro index _
  simp only [Function.comp_apply]
  rw [signedAtomFrameIndex_range]

def indexedAtomListFuel
    (stage : NPOracleProgram) (inputLength count context : ℕ)
    (leafFuel : ℕ → ℕ) : ℕ :=
  linkFuel (linkPrograms leftProjectionProgram (balancedCallProgram stage))
    (generatedBalancedRangeFuel inputLength count context)
    (linkFuel (balancedCallProgram stage) 2
      (balancedCallFuel stage (fun raw => leafFuel (signedAtomFrameIndex raw))
        (indexedRangeRequests inputLength count context)))

def indexedAtomListStageBits
    (inputLength count context : ℕ) (leafOutput : ℕ → ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , generatedBalancedRangeRequiredBits inputLength count context
  , leftProjectionBits
      (encodeBalancedList (indexedRangeRequests inputLength count context))
      context
  , balancedCallRequiredBits (fun raw => leafOutput (signedAtomFrameIndex raw))
      (indexedRangeRequests inputLength count context)
  ]

def indexedAtomListBits
    (inputLength count context : ℕ) (leafOutput : ℕ → ℕ) : ℕ :=
  (indexedAtomListStageBits inputLength count context leafOutput).foldr max 1

/-- **The indexed atom request list, executed** over any stage meeting one
contract per index, with the framed arity independent of the range length. -/
theorem run_indexedAtomRequestListProgram
    (stage : NPOracleProgram) (inputLength count context maximumBits : ℕ)
    (leafFuel leafOutput : ℕ → ℕ)
    (hbits :
      indexedAtomListBits inputLength count context leafOutput ≤ maximumBits)
    (hleaf : ∀ index : ℕ, index < count →
      runNPOracleProgram stage maximumBits (leafFuel index)
          (initialNPOracleState inputLength (Nat.pair index context)) =
        some (leafOutput index)) :
    runNPOracleProgram (atomRequestListProgram stage) maximumBits
        (indexedAtomListFuel stage inputLength count context leafFuel)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count context)) =
      some (encodeBalancedList ((List.range count).map leafOutput)) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ indexedAtomListStageBits inputLength count context leafOutput) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [indexedAtomListStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [indexedAtomListStageBits]
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel inputLength count context)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput count context)) =
        some
          (Nat.pair
            (encodeBalancedList
              (indexedRangeRequests inputLength count context))
            context) := by
    refine run_bits_mono
      (run_generatedBalancedRangeProgram inputLength count context) ?_
    apply bits_of_member
    simp [indexedAtomListStageBits]
  have hproject :
      runNPOracleProgram leftProjectionProgram maximumBits 2
          (initialNPOracleState inputLength
            (Nat.pair
              (encodeBalancedList
                (indexedRangeRequests inputLength count context))
              context)) =
        some
          (encodeBalancedList
            (indexedRangeRequests inputLength count context)) := by
    refine run_bits_mono
      (run_leftProjectionProgram inputLength
        (encodeBalancedList (indexedRangeRequests inputLength count context))
        context) ?_
    apply bits_of_member
    simp [indexedAtomListStageBits]
  have hcallBits :
      balancedCallRequiredBits
          (fun raw => leafOutput (signedAtomFrameIndex raw))
          (indexedRangeRequests inputLength count context) ≤
        maximumBits := by
    apply bits_of_member
    simp [indexedAtomListStageBits]
  have hexec : ∀ raw : ℕ,
      raw ∈ indexedRangeRequests inputLength count context →
      runNPOracleProgram stage maximumBits
          (leafFuel (signedAtomFrameIndex raw))
          (initialNPOracleState (Nat.unpair raw).1 (Nat.unpair raw).2) =
        some (leafOutput (signedAtomFrameIndex raw)) := by
    intro raw hraw
    rw [indexedRangeRequests_eq] at hraw
    obtain ⟨offset, hoffset, hatom⟩ := List.mem_map.mp hraw
    have hindex : offset < count := List.mem_range.mp hoffset
    have hraw_eq :
        raw = balancedRangeRequestAtom inputLength offset context := hatom.symm
    have hleft : (Nat.unpair raw).1 = inputLength := by
      rw [hraw_eq]
      simp [balancedRangeRequestAtom]
    have hright : (Nat.unpair raw).2 = Nat.pair offset context := by
      rw [hraw_eq]
      simp [balancedRangeRequestAtom]
    have hframeIndex : signedAtomFrameIndex raw = offset := by
      rw [hraw_eq]
      exact signedAtomFrameIndex_range inputLength offset context
    rw [hleft, hright, hframeIndex]
    exact hleaf offset hindex
  have hcall :=
    run_balancedCallProgram_from
      (callee := stage) (maximumBits := maximumBits)
      inputLength (indexedRangeRequests inputLength count context)
      (fun raw => leafFuel (signedAtomFrameIndex raw))
      (fun raw => leafOutput (signedAtomFrameIndex raw)) hcallBits hexec
  rw [map_signedAtomFrameIndex_indexed] at hcall
  exact run_linkPrograms hpositive hlength hrange
    (run_linkPrograms hpositive hlength hproject hcall)

/-- The head atom's own data: the gate's threshold code and requested sign. -/
def gateHeadContext (thresholdCode headWanted : ℕ) : ℕ :=
  Nat.pair thresholdCode headWanted

/-- The shared context of one head list. -/
def gateAtomHeadContext
    (thresholdCode headWanted weightsCode tailWanted maskCode : ℕ) : ℕ :=
  Nat.pair (gateHeadContext thresholdCode headWanted)
    (signedAtomContext weightsCode tailWanted maskCode)

/-! ## §3 The three straight-line adapters

One index duplicator in front of the dispatcher, one head adapter, and one
index shift for the coordinate stage.  Nothing else is added: the coordinate
stage of §4 or §9 of `CanonicalSignedAtomRequestProgram` runs unchanged. -/

def gateAtomIndexTagProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] theorem gateAtomIndexTagProgram_oracleFree :
    OracleFree gateAtomIndexTagProgram := by
  rfl

def gateAtomIndexTagFuel : ℕ := 3

def gateAtomIndexTagBits (index context : ℕ) : ℕ :=
  natBitLength (Nat.pair index (Nat.pair index context))

theorem run_gateAtomIndexTagProgram
    (inputLength index context maximumBits : ℕ)
    (hbits : gateAtomIndexTagBits index context ≤ maximumBits) :
    runNPOracleProgram gateAtomIndexTagProgram maximumBits
        gateAtomIndexTagFuel
        (initialNPOracleState inputLength (Nat.pair index context)) =
      some (Nat.pair index (Nat.pair index context)) := by
  have houtputBits :
      natBitLength (Nat.pair index (Nat.pair index context)) ≤ maximumBits :=
    hbits
  have hindexBits : natBitLength index ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair index (Nat.pair index context))).trans houtputBits
  rw [show gateAtomIndexTagFuel = 2 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [initialNPOracleState]) hindexBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair index (Nat.pair index context)) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := Nat.pair index (Nat.pair index context)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits

/-- Emit the head atom's balanced-call request from the head context and the
public arity. -/
def gateHeadRequestProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .set 6 1 5
  , .pair 5 6 7 6
  , .pair 4 7 8 7
  , .pair 1 8 0 8
  , .halt 0
  ]

@[simp] theorem gateHeadRequestProgram_oracleFree :
    OracleFree gateHeadRequestProgram := by
  rfl

def gateHeadRequestFuel : ℕ := 9

private def gateHeadRequestValues
    (inputLength thresholdCode headWanted rest : ℕ) : List ℕ :=
  [ Nat.pair (gateHeadContext thresholdCode headWanted) rest
  , gateHeadContext thresholdCode headWanted
  , thresholdCode
  , headWanted
  , 1
  , Nat.pair headWanted 1
  , Nat.pair thresholdCode (Nat.pair headWanted 1)
  , Nat.pair inputLength (Nat.pair thresholdCode (Nat.pair headWanted 1))
  ]

def gateHeadRequestBits
    (inputLength thresholdCode headWanted rest : ℕ) : ℕ :=
  natBitLength
    ((gateHeadRequestValues inputLength thresholdCode headWanted
      rest).foldr max 1)

private theorem gateHeadRequest_value_bits
    (inputLength thresholdCode headWanted rest : ℕ) {candidate : ℕ}
    (hcandidate :
      candidate ∈
        gateHeadRequestValues inputLength thresholdCode headWanted rest) :
    natBitLength candidate ≤
      gateHeadRequestBits inputLength thresholdCode headWanted rest :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_gateHeadRequestProgram
    (inputLength index thresholdCode headWanted rest maximumBits : ℕ)
    (hbits :
      gateHeadRequestBits inputLength thresholdCode headWanted rest ≤
        maximumBits) :
    runNPOracleProgram gateHeadRequestProgram maximumBits gateHeadRequestFuel
        (initialNPOracleState inputLength
          (Nat.pair index
            (Nat.pair (gateHeadContext thresholdCode headWanted) rest))) =
      some
        (Nat.pair inputLength
          (Nat.pair thresholdCode (Nat.pair headWanted 1))) := by
  have hcontextBits :
      natBitLength
          (Nat.pair (gateHeadContext thresholdCode headWanted) rest) ≤
        maximumBits :=
    (gateHeadRequest_value_bits inputLength thresholdCode headWanted rest
      (by simp [gateHeadRequestValues])).trans hbits
  have hheadBits :
      natBitLength (gateHeadContext thresholdCode headWanted) ≤ maximumBits :=
    (gateHeadRequest_value_bits inputLength thresholdCode headWanted rest
      (by simp [gateHeadRequestValues])).trans hbits
  have hthresholdBits : natBitLength thresholdCode ≤ maximumBits :=
    (gateHeadRequest_value_bits inputLength thresholdCode headWanted rest
      (by simp [gateHeadRequestValues])).trans hbits
  have hwantedBits : natBitLength headWanted ≤ maximumBits :=
    (gateHeadRequest_value_bits inputLength thresholdCode headWanted rest
      (by simp [gateHeadRequestValues])).trans hbits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (gateHeadRequest_value_bits inputLength thresholdCode headWanted rest
      (by simp [gateHeadRequestValues])).trans hbits
  have hbitPairBits : natBitLength (Nat.pair headWanted 1) ≤ maximumBits :=
    (gateHeadRequest_value_bits inputLength thresholdCode headWanted rest
      (by simp [gateHeadRequestValues])).trans hbits
  have hcodeBits :
      natBitLength (Nat.pair thresholdCode (Nat.pair headWanted 1)) ≤
        maximumBits :=
    (gateHeadRequest_value_bits inputLength thresholdCode headWanted rest
      (by simp [gateHeadRequestValues])).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair inputLength
            (Nat.pair thresholdCode (Nat.pair headWanted 1))) ≤
        maximumBits :=
    (gateHeadRequest_value_bits inputLength thresholdCode headWanted rest
      (by simp [gateHeadRequestValues])).trans hbits
  rw [show gateHeadRequestFuel = 8 + 1 by rfl]
  rw [run_unpairRight_instruction
    (value := Nat.pair (gateHeadContext thresholdCode headWanted) rest)
    (by rfl) rfl (by simp [initialNPOracleState]) hcontextBits]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := gateHeadContext thresholdCode headWanted) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hheadBits]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := thresholdCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateHeadContext])
    hthresholdBits]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := headWanted) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateHeadContext])
    hwantedBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_set_instruction (register := 6) (value := 1) (next := 5)
    (by rfl) rfl honeBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair headWanted 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbitPairBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair thresholdCode (Nat.pair headWanted 1)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcodeBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair inputLength (Nat.pair thresholdCode (Nat.pair headWanted 1)))
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value :=
      Nat.pair inputLength (Nat.pair thresholdCode (Nat.pair headWanted 1)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Shift the generated index past the head and drop the head context, leaving
exactly the coordinate frame of `CanonicalSignedAtomRequestProgram` §1. -/
def gateAtomTailFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .decrement 2 4
  , .pair 2 4 0 5
  , .halt 0
  ]

@[simp] theorem gateAtomTailFrameProgram_oracleFree :
    OracleFree gateAtomTailFrameProgram := by
  rfl

def gateAtomTailFrameFuel : ℕ := 6

private def gateAtomTailFrameValues
    (index headCode rest : ℕ) : List ℕ :=
  [ index
  , Nat.pair headCode rest
  , rest
  , index - 1
  , Nat.pair (index - 1) rest
  ]

def gateAtomTailFrameBits (index headCode rest : ℕ) : ℕ :=
  natBitLength ((gateAtomTailFrameValues index headCode rest).foldr max 1)

private theorem gateAtomTailFrame_value_bits
    (index headCode rest : ℕ) {candidate : ℕ}
    (hcandidate : candidate ∈ gateAtomTailFrameValues index headCode rest) :
    natBitLength candidate ≤ gateAtomTailFrameBits index headCode rest :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_gateAtomTailFrameProgram
    (inputLength index headCode rest maximumBits : ℕ)
    (hbits : gateAtomTailFrameBits index headCode rest ≤ maximumBits) :
    runNPOracleProgram gateAtomTailFrameProgram maximumBits
        gateAtomTailFrameFuel
        (initialNPOracleState inputLength
          (Nat.pair index (Nat.pair headCode rest))) =
      some (Nat.pair (index - 1) rest) := by
  have hindexBits : natBitLength index ≤ maximumBits :=
    (gateAtomTailFrame_value_bits index headCode rest
      (by simp [gateAtomTailFrameValues])).trans hbits
  have hcontextBits : natBitLength (Nat.pair headCode rest) ≤ maximumBits :=
    (gateAtomTailFrame_value_bits index headCode rest
      (by simp [gateAtomTailFrameValues])).trans hbits
  have hcoordinateBits : natBitLength rest ≤ maximumBits :=
    (gateAtomTailFrame_value_bits index headCode rest
      (by simp [gateAtomTailFrameValues])).trans hbits
  have hshiftBits : natBitLength (index - 1) ≤ maximumBits :=
    (gateAtomTailFrame_value_bits index headCode rest
      (by simp [gateAtomTailFrameValues])).trans hbits
  have houtputBits :
      natBitLength (Nat.pair (index - 1) rest) ≤ maximumBits :=
    (gateAtomTailFrame_value_bits index headCode rest
      (by simp [gateAtomTailFrameValues])).trans hbits
  rw [show gateAtomTailFrameFuel = 5 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [initialNPOracleState]) hindexBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair headCode rest)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := rest) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcoordinateBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_decrement_instruction (register := 2) (next := 4)
    (value := index - 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hshiftBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (index - 1) rest) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := Nat.pair (index - 1) rest) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits

/-! ## §4 The dispatched per-index stage

The fixed tag dispatcher of `TaggedProgramChoice` branches on the duplicated
index: zero runs the head adapter, every other index runs the shift followed
by the coordinate stage supplied at link time. -/

/-- The tail branch: shift the index past the head, then the coordinate
stage. -/
def gateAtomTailStageProgram (coordinateStage : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms gateAtomTailFrameProgram coordinateStage

/-- The dispatcher over the duplicated index. -/
def gateAtomChoiceProgram (coordinateStage : NPOracleProgram) :
    NPOracleProgram :=
  taggedProgramChoice gateHeadRequestProgram
    (gateAtomTailStageProgram coordinateStage)

/-- **The head list's per-index stage.** -/
def gateAtomHeadStageProgram (coordinateStage : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms gateAtomIndexTagProgram (gateAtomChoiceProgram coordinateStage)

theorem gateAtomTailStageProgram_oracleFree
    (coordinateStage : NPOracleProgram) (hstage : OracleFree coordinateStage) :
    OracleFree (gateAtomTailStageProgram coordinateStage) :=
  oracleFree_linkPrograms gateAtomTailFrameProgram_oracleFree hstage

theorem gateAtomChoiceProgram_oracleFree
    (coordinateStage : NPOracleProgram) (hstage : OracleFree coordinateStage) :
    OracleFree (gateAtomChoiceProgram coordinateStage) :=
  taggedProgramChoice_oracleFree gateHeadRequestProgram
    (gateAtomTailStageProgram coordinateStage) gateHeadRequestProgram_oracleFree
    (gateAtomTailStageProgram_oracleFree coordinateStage hstage)

theorem gateAtomHeadStageProgram_oracleFree
    (coordinateStage : NPOracleProgram) (hstage : OracleFree coordinateStage) :
    OracleFree (gateAtomHeadStageProgram coordinateStage) :=
  oracleFree_linkPrograms gateAtomIndexTagProgram_oracleFree
    (gateAtomChoiceProgram_oracleFree coordinateStage hstage)

def gateAtomTailStageFuel
    (coordinateStage : NPOracleProgram) (coordinateFuel : ℕ) : ℕ :=
  linkFuel coordinateStage gateAtomTailFrameFuel coordinateFuel

/-- The stage's fuel, as a total function of the generated index. -/
def gateAtomHeadStageFuel
    (coordinateStage : NPOracleProgram) (coordinateFuel : ℕ → ℕ)
    (index : ℕ) : ℕ :=
  linkFuel (gateAtomChoiceProgram coordinateStage) gateAtomIndexTagFuel
    (taggedProgramChoiceFuel
      (if index = 0 then gateHeadRequestFuel
        else
          gateAtomTailStageFuel coordinateStage (coordinateFuel (index - 1))))

/-- The stage's output, as a total function of the generated index. -/
def gateAtomHeadLeafOutput
    (inputLength thresholdCode headWanted : ℕ) (coordinateOutput : ℕ → ℕ)
    (index : ℕ) : ℕ :=
  if index = 0 then
    Nat.pair inputLength (Nat.pair thresholdCode (Nat.pair headWanted 1))
  else coordinateOutput (index - 1)

def gateAtomHeadStageBitsList
    (inputLength index thresholdCode headWanted rest : ℕ)
    (coordinateOutput : ℕ → ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , gateAtomIndexTagBits index
      (Nat.pair (gateHeadContext thresholdCode headWanted) rest)
  , natBitLength
      (Nat.pair inputLength
        (Nat.pair index
          (Nat.pair index
            (Nat.pair (gateHeadContext thresholdCode headWanted) rest))))
  , gateHeadRequestBits inputLength thresholdCode headWanted rest
  , gateAtomTailFrameBits index (gateHeadContext thresholdCode headWanted) rest
  , natBitLength
      (gateAtomHeadLeafOutput inputLength thresholdCode headWanted
        coordinateOutput index)
  ]

def gateAtomHeadStageBits
    (inputLength index thresholdCode headWanted rest : ℕ)
    (coordinateOutput : ℕ → ℕ) : ℕ :=
  (gateAtomHeadStageBitsList inputLength index thresholdCode headWanted rest
    coordinateOutput).foldr max 1

/-- **The head list's per-index stage, executed.**  At index zero the gate's
threshold atom is emitted from the head context; at every later index the
coordinate stage runs unchanged on the shifted index. -/
theorem run_gateAtomHeadStageProgram
    (coordinateStage : NPOracleProgram)
    (inputLength index thresholdCode headWanted rest maximumBits : ℕ)
    (coordinateFuel coordinateOutput : ℕ → ℕ)
    (hbits :
      gateAtomHeadStageBits inputLength index thresholdCode headWanted rest
          coordinateOutput ≤
        maximumBits)
    (hcoordinate : index ≠ 0 →
      runNPOracleProgram coordinateStage maximumBits
          (coordinateFuel (index - 1))
          (initialNPOracleState inputLength (Nat.pair (index - 1) rest)) =
        some (coordinateOutput (index - 1))) :
    runNPOracleProgram (gateAtomHeadStageProgram coordinateStage) maximumBits
        (gateAtomHeadStageFuel coordinateStage coordinateFuel index)
        (initialNPOracleState inputLength
          (Nat.pair index
            (Nat.pair (gateHeadContext thresholdCode headWanted) rest))) =
      some
        (gateAtomHeadLeafOutput inputLength thresholdCode headWanted
          coordinateOutput index) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          gateAtomHeadStageBitsList inputLength index thresholdCode headWanted
            rest coordinateOutput) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [gateAtomHeadStageBitsList]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [gateAtomHeadStageBitsList]
  have htagBits :
      gateAtomIndexTagBits index
          (Nat.pair (gateHeadContext thresholdCode headWanted) rest) ≤
        maximumBits := by
    apply bits_of_member
    simp [gateAtomHeadStageBitsList]
  have hdispatchBits :
      natBitLength
          (Nat.pair inputLength
            (Nat.pair index
              (Nat.pair index
                (Nat.pair (gateHeadContext thresholdCode headWanted)
                  rest)))) ≤
        maximumBits := by
    apply bits_of_member
    simp [gateAtomHeadStageBitsList]
  have hheadBits :
      gateHeadRequestBits inputLength thresholdCode headWanted rest ≤
        maximumBits := by
    apply bits_of_member
    simp [gateAtomHeadStageBitsList]
  have hframeBits :
      gateAtomTailFrameBits index (gateHeadContext thresholdCode headWanted)
          rest ≤
        maximumBits := by
    apply bits_of_member
    simp [gateAtomHeadStageBitsList]
  have houtputBits :
      natBitLength
          (gateAtomHeadLeafOutput inputLength thresholdCode headWanted
            coordinateOutput index) ≤
        maximumBits := by
    apply bits_of_member
    simp [gateAtomHeadStageBitsList]
  have htag :=
    run_gateAtomIndexTagProgram inputLength index
      (Nat.pair (gateHeadContext thresholdCode headWanted) rest) maximumBits
      htagBits
  by_cases hzero : index = 0
  · subst hzero
    have hfuel :
        gateAtomHeadStageFuel coordinateStage coordinateFuel 0 =
          linkFuel (gateAtomChoiceProgram coordinateStage)
            gateAtomIndexTagFuel
            (taggedProgramChoiceFuel gateHeadRequestFuel) := by
      simp [gateAtomHeadStageFuel]
    have hleaf :
        gateAtomHeadLeafOutput inputLength thresholdCode headWanted
            coordinateOutput 0 =
          Nat.pair inputLength
            (Nat.pair thresholdCode (Nat.pair headWanted 1)) := by
      simp [gateAtomHeadLeafOutput]
    rw [hfuel, hleaf]
    have hsource :=
      run_gateHeadRequestProgram inputLength 0 thresholdCode headWanted rest
        maximumBits hheadBits
    have hchoice :=
      run_taggedProgramChoice_zero gateHeadRequestProgram
        (gateAtomTailStageProgram coordinateStage) inputLength
        (Nat.pair 0
          (Nat.pair (gateHeadContext thresholdCode headWanted) rest))
        maximumBits gateHeadRequestFuel
        (Nat.pair inputLength
          (Nat.pair thresholdCode (Nat.pair headWanted 1)))
        hdispatchBits hsource (by rw [hleaf] at houtputBits; exact houtputBits)
    exact run_linkPrograms hpositive hlength htag hchoice
  · have hfuel :
        gateAtomHeadStageFuel coordinateStage coordinateFuel index =
          linkFuel (gateAtomChoiceProgram coordinateStage)
            gateAtomIndexTagFuel
            (taggedProgramChoiceFuel
              (gateAtomTailStageFuel coordinateStage
                (coordinateFuel (index - 1)))) := by
      unfold gateAtomHeadStageFuel
      rw [if_neg hzero]
    have hleaf :
        gateAtomHeadLeafOutput inputLength thresholdCode headWanted
            coordinateOutput index =
          coordinateOutput (index - 1) := by
      unfold gateAtomHeadLeafOutput
      rw [if_neg hzero]
    rw [hfuel, hleaf]
    have hframe :=
      run_gateAtomTailFrameProgram inputLength index
        (gateHeadContext thresholdCode headWanted) rest maximumBits hframeBits
    have hsource :
        runNPOracleProgram (gateAtomTailStageProgram coordinateStage)
            maximumBits
            (gateAtomTailStageFuel coordinateStage
              (coordinateFuel (index - 1)))
            (initialNPOracleState inputLength
              (Nat.pair index
                (Nat.pair (gateHeadContext thresholdCode headWanted) rest))) =
          some (coordinateOutput (index - 1)) :=
      run_linkPrograms hpositive hlength hframe (hcoordinate hzero)
    have hchoice :=
      run_taggedProgramChoice_nonzero gateHeadRequestProgram
        (gateAtomTailStageProgram coordinateStage) inputLength index
        (Nat.pair index
          (Nat.pair (gateHeadContext thresholdCode headWanted) rest))
        maximumBits
        (gateAtomTailStageFuel coordinateStage (coordinateFuel (index - 1)))
        (coordinateOutput (index - 1)) hzero hdispatchBits hsource
        (by rw [hleaf] at houtputBits; exact houtputBits)
    exact run_linkPrograms hpositive hlength htag hchoice

/-! ## §5 The head list over an arbitrary coordinate stage

Mapping §4 across a generated range one longer than the gate's arity is the
whole head list.  The generator, the projection, and the balanced call are the
§10 builder of `CanonicalSignedAtomRequestProgram`, restated by §1 at the
gate's own arity. -/

/-- **The head atom request list builder** over one coordinate stage. -/
def gateAtomHeadListProgram (coordinateStage : NPOracleProgram) :
    NPOracleProgram :=
  atomRequestListProgram (gateAtomHeadStageProgram coordinateStage)

theorem gateAtomHeadListProgram_oracleFree
    (coordinateStage : NPOracleProgram) (hstage : OracleFree coordinateStage) :
    OracleFree (gateAtomHeadListProgram coordinateStage) :=
  atomRequestListProgram_oracleFree (gateAtomHeadStageProgram coordinateStage)
    (gateAtomHeadStageProgram_oracleFree coordinateStage hstage)

def gateAtomHeadListFuel
    (coordinateStage : NPOracleProgram)
    (inputLength count thresholdCode headWanted rest : ℕ)
    (coordinateFuel : ℕ → ℕ) : ℕ :=
  indexedAtomListFuel (gateAtomHeadStageProgram coordinateStage) inputLength
    count (Nat.pair (gateHeadContext thresholdCode headWanted) rest)
    (gateAtomHeadStageFuel coordinateStage coordinateFuel)

def gateAtomHeadListCalleeBits
    (inputLength count thresholdCode headWanted rest : ℕ)
    (coordinateOutput : ℕ → ℕ) : ℕ :=
  ((List.range count).map fun index =>
    gateAtomHeadStageBits inputLength index thresholdCode headWanted rest
      coordinateOutput).foldr max 1

def gateAtomHeadListBits
    (inputLength count thresholdCode headWanted rest : ℕ)
    (coordinateOutput : ℕ → ℕ) : ℕ :=
  max
    (indexedAtomListBits inputLength count
      (Nat.pair (gateHeadContext thresholdCode headWanted) rest)
      (gateAtomHeadLeafOutput inputLength thresholdCode headWanted
        coordinateOutput))
    (gateAtomHeadListCalleeBits inputLength count thresholdCode headWanted
      rest coordinateOutput)

/-- **The head atom request list, executed** over any coordinate stage meeting
one contract per coordinate index. -/
theorem run_gateAtomHeadListProgram
    (coordinateStage : NPOracleProgram)
    (inputLength count thresholdCode headWanted rest maximumBits : ℕ)
    (coordinateFuel coordinateOutput : ℕ → ℕ)
    (hbits :
      gateAtomHeadListBits inputLength count thresholdCode headWanted rest
          coordinateOutput ≤
        maximumBits)
    (hcoordinate : ∀ index : ℕ, index + 1 < count →
      runNPOracleProgram coordinateStage maximumBits (coordinateFuel index)
          (initialNPOracleState inputLength (Nat.pair index rest)) =
        some (coordinateOutput index)) :
    runNPOracleProgram (gateAtomHeadListProgram coordinateStage) maximumBits
        (gateAtomHeadListFuel coordinateStage inputLength count thresholdCode
          headWanted rest coordinateFuel)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count
            (Nat.pair (gateHeadContext thresholdCode headWanted) rest))) =
      some
        (encodeBalancedList
          ((List.range count).map
            (gateAtomHeadLeafOutput inputLength thresholdCode headWanted
              coordinateOutput))) := by
  have hlistBits :
      indexedAtomListBits inputLength count
          (Nat.pair (gateHeadContext thresholdCode headWanted) rest)
          (gateAtomHeadLeafOutput inputLength thresholdCode headWanted
            coordinateOutput) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hcalleeBits :
      gateAtomHeadListCalleeBits inputLength count thresholdCode headWanted
          rest coordinateOutput ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  refine run_indexedAtomRequestListProgram
    (gateAtomHeadStageProgram coordinateStage) inputLength count
    (Nat.pair (gateHeadContext thresholdCode headWanted) rest)
    maximumBits (gateAtomHeadStageFuel coordinateStage coordinateFuel)
    (gateAtomHeadLeafOutput inputLength thresholdCode headWanted
      coordinateOutput)
    hlistBits ?_
  intro index hindex
  have hstageBits :
      gateAtomHeadStageBits inputLength index thresholdCode headWanted rest
          coordinateOutput ≤
        maximumBits := by
    refine le_trans ?_ hcalleeBits
    exact le_foldr_max_of_mem
      (List.mem_map_of_mem (List.mem_range.mpr hindex))
  refine run_gateAtomHeadStageProgram coordinateStage inputLength index
    thresholdCode headWanted rest maximumBits coordinateFuel coordinateOutput
    hstageBits ?_
  intro hnonzero
  have hshift : index - 1 + 1 < count := by
    have hpositive : 1 ≤ index := Nat.one_le_iff_ne_zero.mpr hnonzero
    omega
  exact hcoordinate (index - 1) hshift

/-! ## §6 The uniform head list

Instantiating §5 at the uniform coordinate stage of
`CanonicalSignedAtomRequestProgram` §4 compiles the head lists of
`gateEvaluationLeftAtoms`, `gateEvaluationRightAtoms` and
`residualConstantRightAtoms`'s uniform halves. -/

/-- The uniform coordinate stage's output, as a total function of the
coordinate index. -/
def signedAtomIndexedLeafOutput
    (codes : List ℕ) (wanted maskCode index : ℕ) : ℕ :=
  Nat.pair codes.length
    (Nat.pair (codes.getD index 0)
      (Nat.pair wanted (boolCode (maskCode.testBit index))))

def signedAtomHeadListCalleeBits
    (codes : List ℕ) (wanted maskCode : ℕ) : ℕ :=
  ((List.range codes.length).map fun index =>
    signedAtomRequestBits codes index wanted maskCode
      (codes.getD index 0)).foldr max 1

def signedAtomHeadListBits
    (codes : List ℕ) (thresholdCode headWanted tailWanted maskCode : ℕ) : ℕ :=
  max
    (gateAtomHeadListBits codes.length (codes.length + 1) thresholdCode
      headWanted
      (signedAtomContext (encodeBalancedList codes) tailWanted maskCode)
      (signedAtomIndexedLeafOutput codes tailWanted maskCode))
    (signedAtomHeadListCalleeBits codes tailWanted maskCode)

def signedAtomHeadListFuel
    (codes : List ℕ) (thresholdCode headWanted tailWanted maskCode : ℕ) : ℕ :=
  gateAtomHeadListFuel signedAtomRequestProgram codes.length
    (codes.length + 1) thresholdCode headWanted
    (signedAtomContext (encodeBalancedList codes) tailWanted maskCode)
    (signedAtomRequestFuel codes)

/-- **The uniform head list, executed.** -/
theorem run_signedAtomHeadListProgram
    (codes : List ℕ)
    (thresholdCode headWanted tailWanted maskCode maximumBits : ℕ)
    (hbits :
      signedAtomHeadListBits codes thresholdCode headWanted tailWanted
          maskCode ≤
        maximumBits) :
    runNPOracleProgram (gateAtomHeadListProgram signedAtomRequestProgram)
        maximumBits
        (signedAtomHeadListFuel codes thresholdCode headWanted tailWanted
          maskCode)
        (initialNPOracleState codes.length
          (generatedBalancedRangeInput (codes.length + 1)
            (gateAtomHeadContext thresholdCode headWanted
              (encodeBalancedList codes) tailWanted maskCode))) =
      some
        (encodeBalancedList
          ((List.range (codes.length + 1)).map
            (gateAtomHeadLeafOutput codes.length thresholdCode headWanted
              (signedAtomIndexedLeafOutput codes tailWanted maskCode)))) := by
  have hlistBits :
      gateAtomHeadListBits codes.length (codes.length + 1) thresholdCode
          headWanted
          (signedAtomContext (encodeBalancedList codes) tailWanted maskCode)
          (signedAtomIndexedLeafOutput codes tailWanted maskCode) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hcalleeBits :
      signedAtomHeadListCalleeBits codes tailWanted maskCode ≤ maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  refine run_gateAtomHeadListProgram signedAtomRequestProgram codes.length
    (codes.length + 1) thresholdCode headWanted
    (signedAtomContext (encodeBalancedList codes) tailWanted maskCode)
    maximumBits (signedAtomRequestFuel codes)
    (signedAtomIndexedLeafOutput codes tailWanted maskCode) hlistBits ?_
  intro index hindex
  have hbound : index < codes.length := by omega
  have hgetD : codes.getD index 0 = codes[index] :=
    List.getD_eq_getElem codes 0 hbound
  have hweight : codes[index]? = some (codes.getD index 0) := by
    rw [hgetD]
    exact List.getElem?_eq_getElem hbound
  have hstageBits :
      signedAtomRequestBits codes index tailWanted maskCode
          (codes.getD index 0) ≤
        maximumBits := by
    refine le_trans ?_ hcalleeBits
    exact le_foldr_max_of_mem
      (List.mem_map_of_mem (List.mem_range.mpr hbound))
  exact run_signedAtomRequestProgram codes index tailWanted maskCode
    (codes.getD index 0) maximumBits hweight hstageBits

/-! ## §7 The frozen head list

The same instantiation at the frozen coordinate stage of §9 compiles the head
list of `residualConstantRightAtoms` and of the frozen block of
`residualConstantLeftAtoms`. -/

def frozenAtomHeadListCalleeBits
    (codes : List ℕ) (wanted inputMask liveMask : ℕ) : ℕ :=
  ((List.range codes.length).map fun index =>
    frozenAtomRequestBits codes index wanted inputMask liveMask
      (codes.getD index 0)).foldr max 1

def frozenAtomHeadListBits
    (codes : List ℕ)
    (thresholdCode headWanted tailWanted inputMask liveMask : ℕ) : ℕ :=
  max
    (gateAtomHeadListBits codes.length (codes.length + 1) thresholdCode
      headWanted
      (signedAtomContext (encodeBalancedList codes) tailWanted
        (signedAtomMaskPair inputMask liveMask))
      (frozenAtomLeafOutput codes tailWanted inputMask liveMask))
    (frozenAtomHeadListCalleeBits codes tailWanted inputMask liveMask)

def frozenAtomHeadListFuel
    (codes : List ℕ)
    (thresholdCode headWanted tailWanted inputMask liveMask : ℕ) : ℕ :=
  gateAtomHeadListFuel frozenAtomRequestProgram codes.length
    (codes.length + 1) thresholdCode headWanted
    (signedAtomContext (encodeBalancedList codes) tailWanted
      (signedAtomMaskPair inputMask liveMask))
    (frozenAtomRequestFuel codes)

/-- **The frozen head list, executed.** -/
theorem run_frozenAtomHeadListProgram
    (codes : List ℕ)
    (thresholdCode headWanted tailWanted inputMask liveMask maximumBits : ℕ)
    (hbits :
      frozenAtomHeadListBits codes thresholdCode headWanted tailWanted
          inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram (gateAtomHeadListProgram frozenAtomRequestProgram)
        maximumBits
        (frozenAtomHeadListFuel codes thresholdCode headWanted tailWanted
          inputMask liveMask)
        (initialNPOracleState codes.length
          (generatedBalancedRangeInput (codes.length + 1)
            (gateAtomHeadContext thresholdCode headWanted
              (encodeBalancedList codes) tailWanted
              (signedAtomMaskPair inputMask liveMask)))) =
      some
        (encodeBalancedList
          ((List.range (codes.length + 1)).map
            (gateAtomHeadLeafOutput codes.length thresholdCode headWanted
              (frozenAtomLeafOutput codes tailWanted inputMask liveMask)))) := by
  have hlistBits :
      gateAtomHeadListBits codes.length (codes.length + 1) thresholdCode
          headWanted
          (signedAtomContext (encodeBalancedList codes) tailWanted
            (signedAtomMaskPair inputMask liveMask))
          (frozenAtomLeafOutput codes tailWanted inputMask liveMask) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hcalleeBits :
      frozenAtomHeadListCalleeBits codes tailWanted inputMask liveMask ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  refine run_gateAtomHeadListProgram frozenAtomRequestProgram codes.length
    (codes.length + 1) thresholdCode headWanted
    (signedAtomContext (encodeBalancedList codes) tailWanted
      (signedAtomMaskPair inputMask liveMask))
    maximumBits (frozenAtomRequestFuel codes)
    (frozenAtomLeafOutput codes tailWanted inputMask liveMask) hlistBits ?_
  intro index hindex
  have hbound : index < codes.length := by omega
  have hgetD : codes.getD index 0 = codes[index] :=
    List.getD_eq_getElem codes 0 hbound
  have hweight : codes[index]? = some (codes.getD index 0) := by
    rw [hgetD]
    exact List.getElem?_eq_getElem hbound
  have hstageBits :
      frozenAtomRequestBits codes index tailWanted inputMask liveMask
          (codes.getD index 0) ≤
        maximumBits := by
    refine le_trans ?_ hcalleeBits
    exact le_foldr_max_of_mem
      (List.mem_map_of_mem (List.mem_range.mpr hbound))
  exact run_frozenAtomRequestProgram codes index tailWanted inputMask liveMask
    (codes.getD index 0) maximumBits hweight hstageBits

/-! ## §8 The head lists the machine names

Instantiating the code list at a gate's canonical weight syntax identifies the
executed list with `signedAtomRequests` of the gate's own atom list: the
threshold atom followed by the coordinate atoms, exactly the shape
`run_signedAtomTotalProgram` consumes. -/

private theorem map_gateAtomHeadLeafOutput
    {n : ℕ} (weight : Fin n → ℤ) (threshold : ℤ)
    (headWanted tailWanted : ℕ) (bit : Fin n → Bool)
    (coordinateOutput : ℕ → ℕ)
    (hcoordinate : ∀ index : Fin n,
      coordinateOutput index.val =
        signedAtomRequest n (weight index, tailWanted, bit index)) :
    (List.range (n + 1)).map
        (gateAtomHeadLeafOutput n (encodeInt threshold) headWanted
          coordinateOutput) =
      signedAtomRequests n
        ((threshold, headWanted, true) ::
          List.ofFn fun index : Fin n =>
            (weight index, tailWanted, bit index)) := by
  unfold signedAtomRequests
  refine List.ext_getElem (by simp) ?_
  intro index hleft hright
  have hindex : index < n + 1 := by
    simpa using hleft
  simp only [List.getElem_map, List.getElem_range]
  match index with
  | 0 =>
      simp [gateAtomHeadLeafOutput, signedAtomRequest, nativeInputRequest,
        signedAtomCode, boolCode]
  | offset + 1 =>
      have hoffset : offset < n := by omega
      have hleaf :
          gateAtomHeadLeafOutput n (encodeInt threshold) headWanted
              coordinateOutput (offset + 1) =
            coordinateOutput offset := by
        unfold gateAtomHeadLeafOutput
        rw [if_neg (Nat.succ_ne_zero offset)]
        simp
      rw [hleaf]
      simp only [List.getElem_cons_succ, List.getElem_ofFn]
      exact hcoordinate ⟨offset, hoffset⟩

theorem map_signedAtomHeadLeafOutput_ofFn
    {n : ℕ} (weight : Fin n → ℤ) (threshold : ℤ)
    (headWanted tailWanted maskCode : ℕ) :
    (List.range (((List.ofFn weight).map encodeInt).length + 1)).map
        (gateAtomHeadLeafOutput ((List.ofFn weight).map encodeInt).length
          (encodeInt threshold) headWanted
          (signedAtomIndexedLeafOutput ((List.ofFn weight).map encodeInt)
            tailWanted maskCode)) =
      signedAtomRequests n
        ((threshold, headWanted, true) ::
          List.ofFn fun index : Fin n =>
            (weight index, tailWanted, maskCode.testBit index.val)) := by
  have hlengthCodes : ((List.ofFn weight).map encodeInt).length = n := by
    simp
  rw [hlengthCodes]
  refine map_gateAtomHeadLeafOutput weight threshold headWanted tailWanted
    (fun index => maskCode.testBit index.val)
    (signedAtomIndexedLeafOutput ((List.ofFn weight).map encodeInt) tailWanted
      maskCode) ?_
  intro index
  have hgetD :
      ((List.ofFn weight).map encodeInt).getD index.val 0 =
        encodeInt (weight index) := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  unfold signedAtomIndexedLeafOutput
  rw [hgetD, hlengthCodes]
  simp [signedAtomRequest, nativeInputRequest, signedAtomCode]

theorem map_frozenAtomHeadLeafOutput_ofFn
    {n : ℕ} (weight : Fin n → ℤ) (threshold : ℤ)
    (headWanted tailWanted inputMask liveMask : ℕ) :
    (List.range (((List.ofFn weight).map encodeInt).length + 1)).map
        (gateAtomHeadLeafOutput ((List.ofFn weight).map encodeInt).length
          (encodeInt threshold) headWanted
          (frozenAtomLeafOutput ((List.ofFn weight).map encodeInt) tailWanted
            inputMask liveMask)) =
      signedAtomRequests n
        ((threshold, headWanted, true) ::
          List.ofFn fun index : Fin n =>
            (weight index, tailWanted,
              frozenAtomBit inputMask liveMask index.val)) := by
  have hlengthCodes : ((List.ofFn weight).map encodeInt).length = n := by
    simp
  rw [hlengthCodes]
  refine map_gateAtomHeadLeafOutput weight threshold headWanted tailWanted
    (fun index => frozenAtomBit inputMask liveMask index.val)
    (frozenAtomLeafOutput ((List.ofFn weight).map encodeInt) tailWanted
      inputMask liveMask) ?_
  intro index
  have hgetD :
      ((List.ofFn weight).map encodeInt).getD index.val 0 =
        encodeInt (weight index) := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  unfold frozenAtomLeafOutput
  rw [hgetD, hlengthCodes]
  simp [signedAtomRequest, nativeInputRequest, signedAtomCode]

/-- **The uniform head list of one gate, executed.**  This is the balanced
request list of `run_signedAtomTotalProgram` for `gateEvaluationLeftAtoms`,
`gateEvaluationRightAtoms`, and every other list whose head is the gate's
threshold and whose coordinate selector is a single mask digit. -/
theorem run_signedAtomHeadListProgram_gateAtoms
    {n : ℕ} (gate : NormalizedThresholdGate n)
    (headWanted tailWanted maskCode maximumBits : ℕ)
    (hbits :
      signedAtomHeadListBits ((List.ofFn gate.weight).map encodeInt)
          (encodeInt gate.threshold) headWanted tailWanted maskCode ≤
        maximumBits) :
    runNPOracleProgram (gateAtomHeadListProgram signedAtomRequestProgram)
        maximumBits
        (signedAtomHeadListFuel ((List.ofFn gate.weight).map encodeInt)
          (encodeInt gate.threshold) headWanted tailWanted maskCode)
        (initialNPOracleState ((List.ofFn gate.weight).map encodeInt).length
          (generatedBalancedRangeInput
            (((List.ofFn gate.weight).map encodeInt).length + 1)
            (gateAtomHeadContext (encodeInt gate.threshold) headWanted
              (encodeBalancedList ((List.ofFn gate.weight).map encodeInt))
              tailWanted maskCode))) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            ((gate.threshold, headWanted, true) ::
              gateAtoms gate tailWanted fun index =>
                maskCode.testBit index.val))) := by
  have hrun :=
    run_signedAtomHeadListProgram ((List.ofFn gate.weight).map encodeInt)
      (encodeInt gate.threshold) headWanted tailWanted maskCode maximumBits
      hbits
  rw [map_signedAtomHeadLeafOutput_ofFn gate.weight gate.threshold headWanted
    tailWanted maskCode] at hrun
  exact hrun

/-- **The frozen head list of one gate, executed.**  This is the balanced
request list of `run_signedAtomTotalProgram` for
`residualConstantRightAtoms`. -/
theorem run_frozenAtomHeadListProgram_gateAtoms
    {n : ℕ} (gate : NormalizedThresholdGate n)
    (headWanted tailWanted inputMask liveMask maximumBits : ℕ)
    (hbits :
      frozenAtomHeadListBits ((List.ofFn gate.weight).map encodeInt)
          (encodeInt gate.threshold) headWanted tailWanted inputMask
          liveMask ≤
        maximumBits) :
    runNPOracleProgram (gateAtomHeadListProgram frozenAtomRequestProgram)
        maximumBits
        (frozenAtomHeadListFuel ((List.ofFn gate.weight).map encodeInt)
          (encodeInt gate.threshold) headWanted tailWanted inputMask liveMask)
        (initialNPOracleState ((List.ofFn gate.weight).map encodeInt).length
          (generatedBalancedRangeInput
            (((List.ofFn gate.weight).map encodeInt).length + 1)
            (gateAtomHeadContext (encodeInt gate.threshold) headWanted
              (encodeBalancedList ((List.ofFn gate.weight).map encodeInt))
              tailWanted (signedAtomMaskPair inputMask liveMask)))) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            ((gate.threshold, headWanted, true) ::
              gateAtoms gate tailWanted
                (frozenSelector inputMask liveMask)))) := by
  have hrun :=
    run_frozenAtomHeadListProgram ((List.ofFn gate.weight).map encodeInt)
      (encodeInt gate.threshold) headWanted tailWanted inputMask liveMask
      maximumBits hbits
  rw [map_frozenAtomHeadLeafOutput_ofFn gate.weight gate.threshold headWanted
    tailWanted inputMask liveMask] at hrun
  exact hrun

/-! ## §9 Two coordinate blocks under one head

`residualConstantLeftAtoms` is the only atom list of
`CanonicalSignedGateEvaluationProgram` whose head is followed by *two*
coordinate blocks,

```text
    (gate.threshold, 0, true) ::
      (gateAtoms gate 1 (liveSelector liveMask) ++
        gateAtoms gate 1 (frozenSelector inputMask liveMask))
```

Both blocks are the frozen coordinate stage: taking the live mask of the frozen
pair to be zero recovers the uniform selector, so the two blocks differ only in
the mask pair carried beside the shared weights.  The coordinate stage handed
to §4 is therefore one more tag dispatch, on `index + 1 - n`, which is zero
exactly on the first block. -/

/-- The shared context of a two-block coordinate body. -/
def gateAtomBlockContext
    (weightsCode tailWanted firstMask secondMask : ℕ) : ℕ :=
  Nat.pair weightsCode (Nat.pair tailWanted (Nat.pair firstMask secondMask))

/-- Tag the block index with `index + 1 - n`, which vanishes exactly on the
first block. -/
def gateAtomBlockTagProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .increment 2 2
  , .subtract 2 1 3 3
  , .pair 3 0 0 4
  , .halt 0
  ]

@[simp] theorem gateAtomBlockTagProgram_oracleFree :
    OracleFree gateAtomBlockTagProgram := by
  rfl

def gateAtomBlockTagFuel : ℕ := 5

private def gateAtomBlockTagValues
    (inputLength index context : ℕ) : List ℕ :=
  [ index
  , index + 1
  , index + 1 - inputLength
  , Nat.pair (index + 1 - inputLength) (Nat.pair index context)
  ]

def gateAtomBlockTagBits (inputLength index context : ℕ) : ℕ :=
  natBitLength
    ((gateAtomBlockTagValues inputLength index context).foldr max 1)

private theorem gateAtomBlockTag_value_bits
    (inputLength index context : ℕ) {candidate : ℕ}
    (hcandidate : candidate ∈ gateAtomBlockTagValues inputLength index context) :
    natBitLength candidate ≤ gateAtomBlockTagBits inputLength index context :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_gateAtomBlockTagProgram
    (inputLength index context maximumBits : ℕ)
    (hbits : gateAtomBlockTagBits inputLength index context ≤ maximumBits) :
    runNPOracleProgram gateAtomBlockTagProgram maximumBits
        gateAtomBlockTagFuel
        (initialNPOracleState inputLength (Nat.pair index context)) =
      some
        (Nat.pair (index + 1 - inputLength) (Nat.pair index context)) := by
  have hindexBits : natBitLength index ≤ maximumBits :=
    (gateAtomBlockTag_value_bits inputLength index context
      (by simp [gateAtomBlockTagValues])).trans hbits
  have hsuccBits : natBitLength (index + 1) ≤ maximumBits :=
    (gateAtomBlockTag_value_bits inputLength index context
      (by simp [gateAtomBlockTagValues])).trans hbits
  have htagBits : natBitLength (index + 1 - inputLength) ≤ maximumBits :=
    (gateAtomBlockTag_value_bits inputLength index context
      (by simp [gateAtomBlockTagValues])).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair (index + 1 - inputLength) (Nat.pair index context)) ≤
        maximumBits :=
    (gateAtomBlockTag_value_bits inputLength index context
      (by simp [gateAtomBlockTagValues])).trans hbits
  rw [show gateAtomBlockTagFuel = 4 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [initialNPOracleState]) hindexBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_increment_instruction (register := 2) (next := 2)
    (value := index + 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsuccBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_subtract_instruction (value := index + 1 - inputLength)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htagBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (index + 1 - inputLength) (Nat.pair index context))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := Nat.pair (index + 1 - inputLength) (Nat.pair index context))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Frame the first block's coordinate: keep the index, select the first
mask. -/
def gateAtomFirstBlockFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .pair 6 8 9 8
  , .pair 4 9 10 9
  , .pair 2 10 0 10
  , .halt 0
  ]

@[simp] theorem gateAtomFirstBlockFrameProgram_oracleFree :
    OracleFree gateAtomFirstBlockFrameProgram := by
  rfl

def gateAtomFirstBlockFrameFuel : ℕ := 11

/-- Frame the second block's coordinate: shift the index past the first block,
select the second mask. -/
def gateAtomSecondBlockFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairRight 7 8 7
  , .subtract 2 1 2 8
  , .pair 6 8 9 9
  , .pair 4 9 10 10
  , .pair 2 10 0 11
  , .halt 0
  ]

@[simp] theorem gateAtomSecondBlockFrameProgram_oracleFree :
    OracleFree gateAtomSecondBlockFrameProgram := by
  rfl

def gateAtomSecondBlockFrameFuel : ℕ := 12

private def gateAtomBlockFrameValues
    (index shift weightsCode tailWanted firstMask secondMask mask : ℕ) :
    List ℕ :=
  [ index
  , gateAtomBlockContext weightsCode tailWanted firstMask secondMask
  , weightsCode
  , Nat.pair tailWanted (Nat.pair firstMask secondMask)
  , tailWanted
  , Nat.pair firstMask secondMask
  , mask
  , shift
  , Nat.pair tailWanted mask
  , signedAtomContext weightsCode tailWanted mask
  , Nat.pair shift (signedAtomContext weightsCode tailWanted mask)
  ]

def gateAtomBlockFrameBits
    (index shift weightsCode tailWanted firstMask secondMask mask : ℕ) : ℕ :=
  natBitLength
    ((gateAtomBlockFrameValues index shift weightsCode tailWanted firstMask
      secondMask mask).foldr max 1)

private theorem gateAtomBlockFrame_value_bits
    (index shift weightsCode tailWanted firstMask secondMask mask : ℕ)
    {candidate : ℕ}
    (hcandidate :
      candidate ∈
        gateAtomBlockFrameValues index shift weightsCode tailWanted firstMask
          secondMask mask) :
    natBitLength candidate ≤
      gateAtomBlockFrameBits index shift weightsCode tailWanted firstMask
        secondMask mask :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_gateAtomFirstBlockFrameProgram
    (inputLength index weightsCode tailWanted firstMask secondMask
      maximumBits : ℕ)
    (hbits :
      gateAtomBlockFrameBits index index weightsCode tailWanted firstMask
          secondMask firstMask ≤
        maximumBits) :
    runNPOracleProgram gateAtomFirstBlockFrameProgram maximumBits
        gateAtomFirstBlockFrameFuel
        (initialNPOracleState inputLength
          (Nat.pair index
            (gateAtomBlockContext weightsCode tailWanted firstMask
              secondMask))) =
      some (signedAtomFrame index weightsCode tailWanted firstMask) := by
  have value_bits {candidate : ℕ}
      (hcandidate :
        candidate ∈
          gateAtomBlockFrameValues index index weightsCode tailWanted
            firstMask secondMask firstMask) :
      natBitLength candidate ≤ maximumBits :=
    (gateAtomBlockFrame_value_bits index index weightsCode tailWanted
      firstMask secondMask firstMask hcandidate).trans hbits
  have hindexBits : natBitLength index ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hcontextBits :
      natBitLength
          (gateAtomBlockContext weightsCode tailWanted firstMask secondMask) ≤
        maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hweightsBits : natBitLength weightsCode ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have htailBits :
      natBitLength (Nat.pair tailWanted (Nat.pair firstMask secondMask)) ≤
        maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hwantedBits : natBitLength tailWanted ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hmasksBits :
      natBitLength (Nat.pair firstMask secondMask) ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hmaskBits : natBitLength firstMask ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hpairBits :
      natBitLength (Nat.pair tailWanted firstMask) ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hcoordinateBits :
      natBitLength (signedAtomContext weightsCode tailWanted firstMask) ≤
        maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have houtputBits :
      natBitLength (signedAtomFrame index weightsCode tailWanted firstMask) ≤
        maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues, signedAtomFrame]
  rw [show gateAtomFirstBlockFrameFuel = 10 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [initialNPOracleState]) hindexBits]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := gateAtomBlockContext weightsCode tailWanted firstMask secondMask)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := weightsCode) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, gateAtomBlockContext])
    hweightsBits]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair tailWanted (Nat.pair firstMask secondMask)) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, gateAtomBlockContext])
    htailBits]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tailWanted) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwantedBits]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair firstMask secondMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmasksBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := firstMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmaskBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair tailWanted firstMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpairBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := signedAtomContext weightsCode tailWanted firstMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomContext])
    hcoordinateBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := signedAtomFrame index weightsCode tailWanted firstMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomFrame])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := signedAtomFrame index weightsCode tailWanted firstMask)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

theorem run_gateAtomSecondBlockFrameProgram
    (inputLength index weightsCode tailWanted firstMask secondMask
      maximumBits : ℕ)
    (hbits :
      gateAtomBlockFrameBits index (index - inputLength) weightsCode
          tailWanted firstMask secondMask secondMask ≤
        maximumBits) :
    runNPOracleProgram gateAtomSecondBlockFrameProgram maximumBits
        gateAtomSecondBlockFrameFuel
        (initialNPOracleState inputLength
          (Nat.pair index
            (gateAtomBlockContext weightsCode tailWanted firstMask
              secondMask))) =
      some
        (signedAtomFrame (index - inputLength) weightsCode tailWanted
          secondMask) := by
  have value_bits {candidate : ℕ}
      (hcandidate :
        candidate ∈
          gateAtomBlockFrameValues index (index - inputLength) weightsCode
            tailWanted firstMask secondMask secondMask) :
      natBitLength candidate ≤ maximumBits :=
    (gateAtomBlockFrame_value_bits index (index - inputLength) weightsCode
      tailWanted firstMask secondMask secondMask hcandidate).trans hbits
  have hindexBits : natBitLength index ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hcontextBits :
      natBitLength
          (gateAtomBlockContext weightsCode tailWanted firstMask secondMask) ≤
        maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hweightsBits : natBitLength weightsCode ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have htailBits :
      natBitLength (Nat.pair tailWanted (Nat.pair firstMask secondMask)) ≤
        maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hwantedBits : natBitLength tailWanted ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hmasksBits :
      natBitLength (Nat.pair firstMask secondMask) ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hmaskBits : natBitLength secondMask ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hshiftBits : natBitLength (index - inputLength) ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hpairBits :
      natBitLength (Nat.pair tailWanted secondMask) ≤ maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have hcoordinateBits :
      natBitLength (signedAtomContext weightsCode tailWanted secondMask) ≤
        maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues]
  have houtputBits :
      natBitLength
          (signedAtomFrame (index - inputLength) weightsCode tailWanted
            secondMask) ≤
        maximumBits := by
    apply value_bits
    simp [gateAtomBlockFrameValues, signedAtomFrame]
  rw [show gateAtomSecondBlockFrameFuel = 11 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [initialNPOracleState]) hindexBits]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := gateAtomBlockContext weightsCode tailWanted firstMask secondMask)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := weightsCode) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, gateAtomBlockContext])
    hweightsBits]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair tailWanted (Nat.pair firstMask secondMask)) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, gateAtomBlockContext])
    htailBits]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tailWanted) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwantedBits]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair firstMask secondMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmasksBits]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := secondMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmaskBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_subtract_instruction (value := index - inputLength) (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hshiftBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair tailWanted secondMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpairBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := signedAtomContext weightsCode tailWanted secondMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomContext])
    hcoordinateBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      signedAtomFrame (index - inputLength) weightsCode tailWanted secondMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomFrame])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value :=
      signedAtomFrame (index - inputLength) weightsCode tailWanted secondMask)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## §10 The two-block coordinate stage -/

/-- The first block: keep the index, select the first mask, then the
coordinate stage. -/
def gateAtomFirstBlockStageProgram (coordinateStage : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms gateAtomFirstBlockFrameProgram coordinateStage

/-- The second block: shift the index, select the second mask, then the
coordinate stage. -/
def gateAtomSecondBlockStageProgram (coordinateStage : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms gateAtomSecondBlockFrameProgram coordinateStage

def gateAtomBlockChoiceProgram (coordinateStage : NPOracleProgram) :
    NPOracleProgram :=
  taggedProgramChoice (gateAtomFirstBlockStageProgram coordinateStage)
    (gateAtomSecondBlockStageProgram coordinateStage)

/-- **The two-block coordinate stage**, as consumed by §4. -/
def gateAtomBlockStageProgram (coordinateStage : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms gateAtomBlockTagProgram
    (gateAtomBlockChoiceProgram coordinateStage)

theorem gateAtomFirstBlockStageProgram_oracleFree
    (coordinateStage : NPOracleProgram) (hstage : OracleFree coordinateStage) :
    OracleFree (gateAtomFirstBlockStageProgram coordinateStage) :=
  oracleFree_linkPrograms gateAtomFirstBlockFrameProgram_oracleFree hstage

theorem gateAtomSecondBlockStageProgram_oracleFree
    (coordinateStage : NPOracleProgram) (hstage : OracleFree coordinateStage) :
    OracleFree (gateAtomSecondBlockStageProgram coordinateStage) :=
  oracleFree_linkPrograms gateAtomSecondBlockFrameProgram_oracleFree hstage

theorem gateAtomBlockChoiceProgram_oracleFree
    (coordinateStage : NPOracleProgram) (hstage : OracleFree coordinateStage) :
    OracleFree (gateAtomBlockChoiceProgram coordinateStage) :=
  taggedProgramChoice_oracleFree
    (gateAtomFirstBlockStageProgram coordinateStage)
    (gateAtomSecondBlockStageProgram coordinateStage)
    (gateAtomFirstBlockStageProgram_oracleFree coordinateStage hstage)
    (gateAtomSecondBlockStageProgram_oracleFree coordinateStage hstage)

theorem gateAtomBlockStageProgram_oracleFree
    (coordinateStage : NPOracleProgram) (hstage : OracleFree coordinateStage) :
    OracleFree (gateAtomBlockStageProgram coordinateStage) :=
  oracleFree_linkPrograms gateAtomBlockTagProgram_oracleFree
    (gateAtomBlockChoiceProgram_oracleFree coordinateStage hstage)

def gateAtomBlockStageFuel
    (coordinateStage : NPOracleProgram) (firstFuel secondFuel : ℕ → ℕ)
    (inputLength index : ℕ) : ℕ :=
  linkFuel (gateAtomBlockChoiceProgram coordinateStage) gateAtomBlockTagFuel
    (taggedProgramChoiceFuel
      (if index < inputLength then
        linkFuel coordinateStage gateAtomFirstBlockFrameFuel (firstFuel index)
      else
        linkFuel coordinateStage gateAtomSecondBlockFrameFuel
          (secondFuel (index - inputLength))))

def gateAtomBlockLeafOutput
    (inputLength : ℕ) (firstOutput secondOutput : ℕ → ℕ) (index : ℕ) : ℕ :=
  if index < inputLength then firstOutput index
  else secondOutput (index - inputLength)

def gateAtomBlockStageBitsList
    (inputLength index weightsCode tailWanted firstMask secondMask : ℕ)
    (firstOutput secondOutput : ℕ → ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , gateAtomBlockTagBits inputLength index
      (gateAtomBlockContext weightsCode tailWanted firstMask secondMask)
  , natBitLength
      (Nat.pair inputLength
        (Nat.pair (index + 1 - inputLength)
          (Nat.pair index
            (gateAtomBlockContext weightsCode tailWanted firstMask
              secondMask))))
  , gateAtomBlockFrameBits index index weightsCode tailWanted firstMask
      secondMask firstMask
  , gateAtomBlockFrameBits index (index - inputLength) weightsCode tailWanted
      firstMask secondMask secondMask
  , natBitLength
      (gateAtomBlockLeafOutput inputLength firstOutput secondOutput index)
  ]

def gateAtomBlockStageBits
    (inputLength index weightsCode tailWanted firstMask secondMask : ℕ)
    (firstOutput secondOutput : ℕ → ℕ) : ℕ :=
  (gateAtomBlockStageBitsList inputLength index weightsCode tailWanted
    firstMask secondMask firstOutput secondOutput).foldr max 1

/-- **The two-block coordinate stage, executed.**  The dispatch tag is
`index + 1 - n`, which vanishes exactly on the first block. -/
theorem run_gateAtomBlockStageProgram
    (coordinateStage : NPOracleProgram)
    (inputLength index weightsCode tailWanted firstMask secondMask
      maximumBits : ℕ)
    (firstFuel secondFuel firstOutput secondOutput : ℕ → ℕ)
    (hbits :
      gateAtomBlockStageBits inputLength index weightsCode tailWanted
          firstMask secondMask firstOutput secondOutput ≤
        maximumBits)
    (hfirst : index < inputLength →
      runNPOracleProgram coordinateStage maximumBits (firstFuel index)
          (initialNPOracleState inputLength
            (signedAtomFrame index weightsCode tailWanted firstMask)) =
        some (firstOutput index))
    (hsecond : ¬ index < inputLength →
      runNPOracleProgram coordinateStage maximumBits
          (secondFuel (index - inputLength))
          (initialNPOracleState inputLength
            (signedAtomFrame (index - inputLength) weightsCode tailWanted
              secondMask)) =
        some (secondOutput (index - inputLength))) :
    runNPOracleProgram (gateAtomBlockStageProgram coordinateStage) maximumBits
        (gateAtomBlockStageFuel coordinateStage firstFuel secondFuel
          inputLength index)
        (initialNPOracleState inputLength
          (Nat.pair index
            (gateAtomBlockContext weightsCode tailWanted firstMask
              secondMask))) =
      some
        (gateAtomBlockLeafOutput inputLength firstOutput secondOutput
          index) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          gateAtomBlockStageBitsList inputLength index weightsCode tailWanted
            firstMask secondMask firstOutput secondOutput) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [gateAtomBlockStageBitsList]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [gateAtomBlockStageBitsList]
  have htagBits :
      gateAtomBlockTagBits inputLength index
          (gateAtomBlockContext weightsCode tailWanted firstMask
            secondMask) ≤
        maximumBits := by
    apply bits_of_member
    simp [gateAtomBlockStageBitsList]
  have hdispatchBits :
      natBitLength
          (Nat.pair inputLength
            (Nat.pair (index + 1 - inputLength)
              (Nat.pair index
                (gateAtomBlockContext weightsCode tailWanted firstMask
                  secondMask)))) ≤
        maximumBits := by
    apply bits_of_member
    simp [gateAtomBlockStageBitsList]
  have hfirstFrameBits :
      gateAtomBlockFrameBits index index weightsCode tailWanted firstMask
          secondMask firstMask ≤
        maximumBits := by
    apply bits_of_member
    simp [gateAtomBlockStageBitsList]
  have hsecondFrameBits :
      gateAtomBlockFrameBits index (index - inputLength) weightsCode
          tailWanted firstMask secondMask secondMask ≤
        maximumBits := by
    apply bits_of_member
    simp [gateAtomBlockStageBitsList]
  have houtputBits :
      natBitLength
          (gateAtomBlockLeafOutput inputLength firstOutput secondOutput
            index) ≤
        maximumBits := by
    apply bits_of_member
    simp [gateAtomBlockStageBitsList]
  have htag :=
    run_gateAtomBlockTagProgram inputLength index
      (gateAtomBlockContext weightsCode tailWanted firstMask secondMask)
      maximumBits htagBits
  by_cases hcase : index < inputLength
  · have htagZero : index + 1 - inputLength = 0 := by omega
    rw [htagZero] at htag hdispatchBits
    have hfuel :
        gateAtomBlockStageFuel coordinateStage firstFuel secondFuel
            inputLength index =
          linkFuel (gateAtomBlockChoiceProgram coordinateStage)
            gateAtomBlockTagFuel
            (taggedProgramChoiceFuel
              (linkFuel coordinateStage gateAtomFirstBlockFrameFuel
                (firstFuel index))) := by
      unfold gateAtomBlockStageFuel
      rw [if_pos hcase]
    have hleaf :
        gateAtomBlockLeafOutput inputLength firstOutput secondOutput index =
          firstOutput index := by
      unfold gateAtomBlockLeafOutput
      rw [if_pos hcase]
    rw [hfuel, hleaf]
    rw [hleaf] at houtputBits
    have hframe :=
      run_gateAtomFirstBlockFrameProgram inputLength index weightsCode
        tailWanted firstMask secondMask maximumBits hfirstFrameBits
    have hsource :
        runNPOracleProgram (gateAtomFirstBlockStageProgram coordinateStage)
            maximumBits
            (linkFuel coordinateStage gateAtomFirstBlockFrameFuel
              (firstFuel index))
            (initialNPOracleState inputLength
              (Nat.pair index
                (gateAtomBlockContext weightsCode tailWanted firstMask
                  secondMask))) =
          some (firstOutput index) :=
      run_linkPrograms hpositive hlength hframe (hfirst hcase)
    have hchoice :=
      run_taggedProgramChoice_zero
        (gateAtomFirstBlockStageProgram coordinateStage)
        (gateAtomSecondBlockStageProgram coordinateStage) inputLength
        (Nat.pair index
          (gateAtomBlockContext weightsCode tailWanted firstMask secondMask))
        maximumBits
        (linkFuel coordinateStage gateAtomFirstBlockFrameFuel
          (firstFuel index))
        (firstOutput index) hdispatchBits hsource houtputBits
    exact run_linkPrograms hpositive hlength htag hchoice
  · have htagNonzero : index + 1 - inputLength ≠ 0 := by omega
    have hfuel :
        gateAtomBlockStageFuel coordinateStage firstFuel secondFuel
            inputLength index =
          linkFuel (gateAtomBlockChoiceProgram coordinateStage)
            gateAtomBlockTagFuel
            (taggedProgramChoiceFuel
              (linkFuel coordinateStage gateAtomSecondBlockFrameFuel
                (secondFuel (index - inputLength)))) := by
      unfold gateAtomBlockStageFuel
      rw [if_neg hcase]
    have hleaf :
        gateAtomBlockLeafOutput inputLength firstOutput secondOutput index =
          secondOutput (index - inputLength) := by
      unfold gateAtomBlockLeafOutput
      rw [if_neg hcase]
    rw [hfuel, hleaf]
    rw [hleaf] at houtputBits
    have hframe :=
      run_gateAtomSecondBlockFrameProgram inputLength index weightsCode
        tailWanted firstMask secondMask maximumBits hsecondFrameBits
    have hsource :
        runNPOracleProgram (gateAtomSecondBlockStageProgram coordinateStage)
            maximumBits
            (linkFuel coordinateStage gateAtomSecondBlockFrameFuel
              (secondFuel (index - inputLength)))
            (initialNPOracleState inputLength
              (Nat.pair index
                (gateAtomBlockContext weightsCode tailWanted firstMask
                  secondMask))) =
          some (secondOutput (index - inputLength)) :=
      run_linkPrograms hpositive hlength hframe (hsecond hcase)
    have hchoice :=
      run_taggedProgramChoice_nonzero
        (gateAtomFirstBlockStageProgram coordinateStage)
        (gateAtomSecondBlockStageProgram coordinateStage) inputLength
        (index + 1 - inputLength)
        (Nat.pair index
          (gateAtomBlockContext weightsCode tailWanted firstMask secondMask))
        maximumBits
        (linkFuel coordinateStage gateAtomSecondBlockFrameFuel
          (secondFuel (index - inputLength)))
        (secondOutput (index - inputLength)) htagNonzero hdispatchBits hsource
        houtputBits
    exact run_linkPrograms hpositive hlength htag hchoice

/-! ## §11 The two-block head list at the frozen stage

Both blocks of `residualConstantLeftAtoms` run the frozen coordinate stage:
the first with the live mask paired against zero, which is the uniform live
selector, the second with the genuine mask pair. -/

/-- The coordinate output of a two-block frozen body. -/
def frozenTwoBlockLeafOutput
    (codes : List ℕ) (wanted inputMask liveMask index : ℕ) : ℕ :=
  gateAtomBlockLeafOutput codes.length
    (frozenAtomLeafOutput codes wanted liveMask 0)
    (frozenAtomLeafOutput codes wanted inputMask liveMask) index

/-- The two-block body's context, as the generator receives it. -/
def frozenTwoBlockContext
    (codes : List ℕ) (wanted inputMask liveMask : ℕ) : ℕ :=
  gateAtomBlockContext (encodeBalancedList codes) wanted
    (signedAtomMaskPair liveMask 0) (signedAtomMaskPair inputMask liveMask)

def frozenTwoBlockCoordinateFuel (codes : List ℕ) (index : ℕ) : ℕ :=
  gateAtomBlockStageFuel frozenAtomRequestProgram (frozenAtomRequestFuel codes)
    (frozenAtomRequestFuel codes) codes.length index

def frozenTwoBlockStageCalleeBits
    (codes : List ℕ) (wanted inputMask liveMask : ℕ) : ℕ :=
  max
    (((List.range codes.length).map fun index =>
      frozenAtomRequestBits codes index wanted liveMask 0
        (codes.getD index 0)).foldr max 1)
    (((List.range codes.length).map fun index =>
      frozenAtomRequestBits codes index wanted inputMask liveMask
        (codes.getD index 0)).foldr max 1)

def frozenTwoBlockBlockBits
    (codes : List ℕ) (wanted inputMask liveMask : ℕ) : ℕ :=
  ((List.range (2 * codes.length)).map fun index =>
    gateAtomBlockStageBits codes.length index (encodeBalancedList codes)
      wanted (signedAtomMaskPair liveMask 0)
      (signedAtomMaskPair inputMask liveMask)
      (frozenAtomLeafOutput codes wanted liveMask 0)
      (frozenAtomLeafOutput codes wanted inputMask liveMask)).foldr max 1

def frozenTwoBlockHeadListFuel
    (codes : List ℕ)
    (thresholdCode headWanted tailWanted inputMask liveMask : ℕ) : ℕ :=
  gateAtomHeadListFuel (gateAtomBlockStageProgram frozenAtomRequestProgram)
    codes.length (2 * codes.length + 1) thresholdCode headWanted
    (frozenTwoBlockContext codes tailWanted inputMask liveMask)
    (frozenTwoBlockCoordinateFuel codes)

def frozenTwoBlockHeadListBits
    (codes : List ℕ)
    (thresholdCode headWanted tailWanted inputMask liveMask : ℕ) : ℕ :=
  max
    (gateAtomHeadListBits codes.length (2 * codes.length + 1) thresholdCode
      headWanted (frozenTwoBlockContext codes tailWanted inputMask liveMask)
      (frozenTwoBlockLeafOutput codes tailWanted inputMask liveMask))
    (max (frozenTwoBlockBlockBits codes tailWanted inputMask liveMask)
      (frozenTwoBlockStageCalleeBits codes tailWanted inputMask liveMask))

/-- **The two-block frozen head list, executed.** -/
theorem run_frozenTwoBlockHeadListProgram
    (codes : List ℕ)
    (thresholdCode headWanted tailWanted inputMask liveMask maximumBits : ℕ)
    (hbits :
      frozenTwoBlockHeadListBits codes thresholdCode headWanted tailWanted
          inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram
        (gateAtomHeadListProgram
          (gateAtomBlockStageProgram frozenAtomRequestProgram))
        maximumBits
        (frozenTwoBlockHeadListFuel codes thresholdCode headWanted tailWanted
          inputMask liveMask)
        (initialNPOracleState codes.length
          (generatedBalancedRangeInput (2 * codes.length + 1)
            (Nat.pair (gateHeadContext thresholdCode headWanted)
              (frozenTwoBlockContext codes tailWanted inputMask liveMask)))) =
      some
        (encodeBalancedList
          ((List.range (2 * codes.length + 1)).map
            (gateAtomHeadLeafOutput codes.length thresholdCode headWanted
              (frozenTwoBlockLeafOutput codes tailWanted inputMask
                liveMask)))) := by
  have hlistBits :
      gateAtomHeadListBits codes.length (2 * codes.length + 1) thresholdCode
          headWanted
          (frozenTwoBlockContext codes tailWanted inputMask liveMask)
          (frozenTwoBlockLeafOutput codes tailWanted inputMask liveMask) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hblockBits :
      frozenTwoBlockBlockBits codes tailWanted inputMask liveMask ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hcalleeBits :
      frozenTwoBlockStageCalleeBits codes tailWanted inputMask liveMask ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  refine run_gateAtomHeadListProgram
    (gateAtomBlockStageProgram frozenAtomRequestProgram) codes.length
    (2 * codes.length + 1) thresholdCode headWanted
    (frozenTwoBlockContext codes tailWanted inputMask liveMask) maximumBits
    (frozenTwoBlockCoordinateFuel codes)
    (frozenTwoBlockLeafOutput codes tailWanted inputMask liveMask)
    hlistBits ?_
  intro index hindex
  have hbound : index < 2 * codes.length := by omega
  have hstageBits :
      gateAtomBlockStageBits codes.length index (encodeBalancedList codes)
          tailWanted (signedAtomMaskPair liveMask 0)
          (signedAtomMaskPair inputMask liveMask)
          (frozenAtomLeafOutput codes tailWanted liveMask 0)
          (frozenAtomLeafOutput codes tailWanted inputMask liveMask) ≤
        maximumBits := by
    refine le_trans ?_ hblockBits
    exact le_foldr_max_of_mem
      (List.mem_map_of_mem (List.mem_range.mpr hbound))
  refine run_gateAtomBlockStageProgram frozenAtomRequestProgram codes.length
    index (encodeBalancedList codes) tailWanted
    (signedAtomMaskPair liveMask 0) (signedAtomMaskPair inputMask liveMask)
    maximumBits (frozenAtomRequestFuel codes) (frozenAtomRequestFuel codes)
    (frozenAtomLeafOutput codes tailWanted liveMask 0)
    (frozenAtomLeafOutput codes tailWanted inputMask liveMask) hstageBits
    ?_ ?_
  · intro hfirst
    have hgetD : codes.getD index 0 = codes[index] :=
      List.getD_eq_getElem codes 0 hfirst
    have hweight : codes[index]? = some (codes.getD index 0) := by
      rw [hgetD]
      exact List.getElem?_eq_getElem hfirst
    have hentryBits :
        frozenAtomRequestBits codes index tailWanted liveMask 0
            (codes.getD index 0) ≤
          maximumBits := by
      refine le_trans ?_ ((Nat.le_max_left _ _).trans hcalleeBits)
      exact le_foldr_max_of_mem
        (List.mem_map_of_mem (List.mem_range.mpr hfirst))
    exact run_frozenAtomRequestProgram codes index tailWanted liveMask 0
      (codes.getD index 0) maximumBits hweight hentryBits
  · intro hsecond
    have hshift : index - codes.length < codes.length := by omega
    have hgetD :
        codes.getD (index - codes.length) 0 = codes[index - codes.length] :=
      List.getD_eq_getElem codes 0 hshift
    have hweight :
        codes[index - codes.length]? =
          some (codes.getD (index - codes.length) 0) := by
      rw [hgetD]
      exact List.getElem?_eq_getElem hshift
    have hentryBits :
        frozenAtomRequestBits codes (index - codes.length) tailWanted
            inputMask liveMask (codes.getD (index - codes.length) 0) ≤
          maximumBits := by
      refine le_trans ?_ ((Nat.le_max_right _ _).trans hcalleeBits)
      exact le_foldr_max_of_mem
        (List.mem_map_of_mem (List.mem_range.mpr hshift))
    exact run_frozenAtomRequestProgram codes (index - codes.length) tailWanted
      inputMask liveMask (codes.getD (index - codes.length) 0) maximumBits
      hweight hentryBits

/-! ## §12 The two-block head list the machine names -/

private theorem map_gateAtomTwoBlockLeafOutput
    {n : ℕ} (weight : Fin n → ℤ) (threshold : ℤ)
    (headWanted tailWanted : ℕ) (firstBit secondBit : Fin n → Bool)
    (firstOutput secondOutput : ℕ → ℕ)
    (hfirst : ∀ index : Fin n,
      firstOutput index.val =
        signedAtomRequest n (weight index, tailWanted, firstBit index))
    (hsecond : ∀ index : Fin n,
      secondOutput index.val =
        signedAtomRequest n (weight index, tailWanted, secondBit index)) :
    (List.range (2 * n + 1)).map
        (gateAtomHeadLeafOutput n (encodeInt threshold) headWanted
          (gateAtomBlockLeafOutput n firstOutput secondOutput)) =
      signedAtomRequests n
        ((threshold, headWanted, true) ::
          ((List.ofFn fun index : Fin n =>
              (weight index, tailWanted, firstBit index)) ++
            (List.ofFn fun index : Fin n =>
              (weight index, tailWanted, secondBit index)))) := by
  unfold signedAtomRequests
  refine List.ext_getElem (by simp; omega) ?_
  intro index hleft hright
  have hindex : index < 2 * n + 1 := by
    simpa using hleft
  simp only [List.getElem_map, List.getElem_range]
  match index with
  | 0 =>
      simp [gateAtomHeadLeafOutput, signedAtomRequest, nativeInputRequest,
        signedAtomCode, boolCode]
  | offset + 1 =>
      have hoffset : offset < 2 * n := by omega
      have hleaf :
          gateAtomHeadLeafOutput n (encodeInt threshold) headWanted
              (gateAtomBlockLeafOutput n firstOutput secondOutput)
              (offset + 1) =
            gateAtomBlockLeafOutput n firstOutput secondOutput offset := by
        unfold gateAtomHeadLeafOutput
        rw [if_neg (Nat.succ_ne_zero offset)]
        simp
      rw [hleaf]
      simp only [List.getElem_cons_succ]
      by_cases hcase : offset < n
      · have hblock :
            gateAtomBlockLeafOutput n firstOutput secondOutput offset =
              firstOutput offset := by
          unfold gateAtomBlockLeafOutput
          rw [if_pos hcase]
        rw [hblock, hfirst ⟨offset, hcase⟩]
        rw [List.getElem_append_left (by simpa using hcase)]
        simp
      · have hshift : offset - n < n := by omega
        have hblock :
            gateAtomBlockLeafOutput n firstOutput secondOutput offset =
              secondOutput (offset - n) := by
          unfold gateAtomBlockLeafOutput
          rw [if_neg hcase]
        rw [hblock, hsecond ⟨offset - n, hshift⟩]
        rw [List.getElem_append_right (by simpa using hcase)]
        simp

theorem map_frozenTwoBlockHeadLeafOutput_ofFn
    {n : ℕ} (weight : Fin n → ℤ) (threshold : ℤ)
    (headWanted tailWanted inputMask liveMask : ℕ) :
    (List.range (2 * ((List.ofFn weight).map encodeInt).length + 1)).map
        (gateAtomHeadLeafOutput ((List.ofFn weight).map encodeInt).length
          (encodeInt threshold) headWanted
          (frozenTwoBlockLeafOutput ((List.ofFn weight).map encodeInt)
            tailWanted inputMask liveMask)) =
      signedAtomRequests n
        ((threshold, headWanted, true) ::
          ((List.ofFn fun index : Fin n =>
              (weight index, tailWanted, liveSelector liveMask index)) ++
            (List.ofFn fun index : Fin n =>
              (weight index, tailWanted,
                frozenSelector inputMask liveMask index)))) := by
  have hlengthCodes : ((List.ofFn weight).map encodeInt).length = n := by
    simp
  have hgetD : ∀ index : Fin n,
      ((List.ofFn weight).map encodeInt).getD index.val 0 =
        encodeInt (weight index) := by
    intro index
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  have hleaf :
      frozenTwoBlockLeafOutput ((List.ofFn weight).map encodeInt) tailWanted
          inputMask liveMask =
        gateAtomBlockLeafOutput n
          (frozenAtomLeafOutput ((List.ofFn weight).map encodeInt) tailWanted
            liveMask 0)
          (frozenAtomLeafOutput ((List.ofFn weight).map encodeInt) tailWanted
            inputMask liveMask) := by
    funext index
    unfold frozenTwoBlockLeafOutput
    rw [hlengthCodes]
  rw [hlengthCodes, hleaf]
  refine map_gateAtomTwoBlockLeafOutput weight threshold headWanted tailWanted
    (liveSelector liveMask) (frozenSelector inputMask liveMask)
    (frozenAtomLeafOutput ((List.ofFn weight).map encodeInt) tailWanted
      liveMask 0)
    (frozenAtomLeafOutput ((List.ofFn weight).map encodeInt) tailWanted
      inputMask liveMask) ?_ ?_
  · intro index
    have hbit :
        frozenAtomBit liveMask 0 index.val = liveSelector liveMask index := by
      simp [frozenAtomBit, liveSelector]
    unfold frozenAtomLeafOutput
    rw [hgetD index, hlengthCodes, hbit]
    simp [signedAtomRequest, nativeInputRequest, signedAtomCode]
  · intro index
    have hbit :
        frozenAtomBit inputMask liveMask index.val =
          frozenSelector inputMask liveMask index := by
      simp [frozenAtomBit, frozenSelector]
    unfold frozenAtomLeafOutput
    rw [hgetD index, hlengthCodes, hbit]
    simp [signedAtomRequest, nativeInputRequest, signedAtomCode]

/-- **The two-block frozen head list of one gate, executed.**  At
`headWanted = 0` and `tailWanted = 1` this is exactly the balanced request list
of `run_signedAtomTotalProgram` for `residualConstantLeftAtoms`. -/
theorem run_frozenTwoBlockHeadListProgram_gateAtoms
    {n : ℕ} (gate : NormalizedThresholdGate n)
    (headWanted tailWanted inputMask liveMask maximumBits : ℕ)
    (hbits :
      frozenTwoBlockHeadListBits ((List.ofFn gate.weight).map encodeInt)
          (encodeInt gate.threshold) headWanted tailWanted inputMask
          liveMask ≤
        maximumBits) :
    runNPOracleProgram
        (gateAtomHeadListProgram
          (gateAtomBlockStageProgram frozenAtomRequestProgram))
        maximumBits
        (frozenTwoBlockHeadListFuel ((List.ofFn gate.weight).map encodeInt)
          (encodeInt gate.threshold) headWanted tailWanted inputMask liveMask)
        (initialNPOracleState ((List.ofFn gate.weight).map encodeInt).length
          (generatedBalancedRangeInput
            (2 * ((List.ofFn gate.weight).map encodeInt).length + 1)
            (Nat.pair (gateHeadContext (encodeInt gate.threshold) headWanted)
              (frozenTwoBlockContext ((List.ofFn gate.weight).map encodeInt)
                tailWanted inputMask liveMask)))) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            ((gate.threshold, headWanted, true) ::
              (gateAtoms gate tailWanted (liveSelector liveMask) ++
                gateAtoms gate tailWanted
                  (frozenSelector inputMask liveMask))))) := by
  have hrun :=
    run_frozenTwoBlockHeadListProgram ((List.ofFn gate.weight).map encodeInt)
      (encodeInt gate.threshold) headWanted tailWanted inputMask liveMask
      maximumBits hbits
  rw [map_frozenTwoBlockHeadLeafOutput_ofFn gate.weight gate.threshold
    headWanted tailWanted inputMask liveMask] at hrun
  exact hrun

/-! ## §13 The four atom lists of one gate's residual variable

`CanonicalSignedGateEvaluationProgram` §8 builds `residualVariableInput` from
exactly four balanced request lists.  Each is one instance of §6, §7 or §11 at
the gate's own weight syntax. -/

/-- The gate's canonical weight code list. -/
def gateWeightCodes {n : ℕ} (gate : NormalizedThresholdGate n) : List ℕ :=
  (List.ofFn gate.weight).map encodeInt

@[simp] theorem gateWeightCodes_length {n : ℕ}
    (gate : NormalizedThresholdGate n) : (gateWeightCodes gate).length = n := by
  simp [gateWeightCodes]

/-- The generator input of one head list. -/
def gateHeadListInput (count thresholdCode headWanted rest : ℕ) : ℕ :=
  generatedBalancedRangeInput count
    (Nat.pair (gateHeadContext thresholdCode headWanted) rest)

def gateEvaluationLeftListInput {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask : ℕ) : ℕ :=
  gateHeadListInput (n + 1) (encodeInt gate.threshold) 0
    (signedAtomContext (encodeBalancedList (gateWeightCodes gate)) 1 inputMask)

def gateEvaluationRightListInput {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask : ℕ) : ℕ :=
  gateHeadListInput (n + 1) (encodeInt gate.threshold) 1
    (signedAtomContext (encodeBalancedList (gateWeightCodes gate)) 0 inputMask)

def residualConstantLeftListInput {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  gateHeadListInput (2 * n + 1) (encodeInt gate.threshold) 0
    (frozenTwoBlockContext (gateWeightCodes gate) 1 inputMask liveMask)

def residualConstantRightListInput {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  gateHeadListInput (n + 1) (encodeInt gate.threshold) 1
    (signedAtomContext (encodeBalancedList (gateWeightCodes gate)) 0
      (signedAtomMaskPair inputMask liveMask))

def gateEvaluationLeftListFuel {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask : ℕ) : ℕ :=
  signedAtomHeadListFuel (gateWeightCodes gate) (encodeInt gate.threshold) 0 1
    inputMask

def gateEvaluationRightListFuel {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask : ℕ) : ℕ :=
  signedAtomHeadListFuel (gateWeightCodes gate) (encodeInt gate.threshold) 1 0
    inputMask

def residualConstantLeftListFuel {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  frozenTwoBlockHeadListFuel (gateWeightCodes gate)
    (encodeInt gate.threshold) 0 1 inputMask liveMask

def residualConstantRightListFuel {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  frozenAtomHeadListFuel (gateWeightCodes gate) (encodeInt gate.threshold) 1 0
    inputMask liveMask

def gateEvaluationLeftListBits {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask : ℕ) : ℕ :=
  signedAtomHeadListBits (gateWeightCodes gate) (encodeInt gate.threshold) 0 1
    inputMask

def gateEvaluationRightListBits {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask : ℕ) : ℕ :=
  signedAtomHeadListBits (gateWeightCodes gate) (encodeInt gate.threshold) 1 0
    inputMask

def residualConstantLeftListBits {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  frozenTwoBlockHeadListBits (gateWeightCodes gate)
    (encodeInt gate.threshold) 0 1 inputMask liveMask

def residualConstantRightListBits {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  frozenAtomHeadListBits (gateWeightCodes gate) (encodeInt gate.threshold) 1 0
    inputMask liveMask

/-- **The left atom list of `NormalizedThresholdGate.eval`, executed.** -/
theorem run_gateEvaluationLeftListProgram {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask maximumBits : ℕ)
    (hbits : gateEvaluationLeftListBits gate inputMask ≤ maximumBits) :
    runNPOracleProgram (gateAtomHeadListProgram signedAtomRequestProgram)
        maximumBits (gateEvaluationLeftListFuel gate inputMask)
        (initialNPOracleState n (gateEvaluationLeftListInput gate inputMask)) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            (gateEvaluationLeftAtoms gate (inputSelector inputMask)))) := by
  have hrun :=
    run_signedAtomHeadListProgram_gateAtoms gate 0 1 inputMask maximumBits
      hbits
  rw [show ((List.ofFn gate.weight).map encodeInt).length = n by simp] at hrun
  exact hrun

/-- **The right atom list of `NormalizedThresholdGate.eval`, executed.** -/
theorem run_gateEvaluationRightListProgram {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask maximumBits : ℕ)
    (hbits : gateEvaluationRightListBits gate inputMask ≤ maximumBits) :
    runNPOracleProgram (gateAtomHeadListProgram signedAtomRequestProgram)
        maximumBits (gateEvaluationRightListFuel gate inputMask)
        (initialNPOracleState n
          (gateEvaluationRightListInput gate inputMask)) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            (gateEvaluationRightAtoms gate (inputSelector inputMask)))) := by
  have hrun :=
    run_signedAtomHeadListProgram_gateAtoms gate 1 0 inputMask maximumBits
      hbits
  rw [show ((List.ofFn gate.weight).map encodeInt).length = n by simp] at hrun
  exact hrun

/-- **The left atom list of `residualConstant`, executed.** -/
theorem run_residualConstantLeftListProgram {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask maximumBits : ℕ)
    (hbits :
      residualConstantLeftListBits gate inputMask liveMask ≤ maximumBits) :
    runNPOracleProgram
        (gateAtomHeadListProgram
          (gateAtomBlockStageProgram frozenAtomRequestProgram))
        maximumBits (residualConstantLeftListFuel gate inputMask liveMask)
        (initialNPOracleState n
          (residualConstantLeftListInput gate inputMask liveMask)) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            (residualConstantLeftAtoms gate inputMask liveMask))) := by
  have hrun :=
    run_frozenTwoBlockHeadListProgram_gateAtoms gate 0 1 inputMask liveMask
      maximumBits hbits
  rw [show ((List.ofFn gate.weight).map encodeInt).length = n by simp] at hrun
  exact hrun

/-- **The right atom list of `residualConstant`, executed.** -/
theorem run_residualConstantRightListProgram {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask maximumBits : ℕ)
    (hbits :
      residualConstantRightListBits gate inputMask liveMask ≤ maximumBits) :
    runNPOracleProgram (gateAtomHeadListProgram frozenAtomRequestProgram)
        maximumBits (residualConstantRightListFuel gate inputMask liveMask)
        (initialNPOracleState n
          (residualConstantRightListInput gate inputMask liveMask)) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            (residualConstantRightAtoms gate inputMask liveMask))) := by
  have hrun :=
    run_frozenAtomHeadListProgram_gateAtoms gate 1 0 inputMask liveMask
      maximumBits hbits
  rw [show ((List.ofFn gate.weight).map encodeInt).length = n by simp] at hrun
  exact hrun

/-! ## §14 One gate's residual variable request, assembled

`residualVariableInput` is a pair of pairs of balanced list codes, so the whole
assembly is two paired calls of §13's list producers.  The two lists of a half
are produced by different programs exactly once — on the constant half — and
that is absorbed by one fixed tag dispatcher, so no producer is duplicated. -/

/-- The evaluation half: one paired call of the uniform head list. -/
def residualVariableEvaluationRequestProgram : NPOracleProgram :=
  pairedCallProgram (gateAtomHeadListProgram signedAtomRequestProgram)

/-- The constant half's dispatcher: the two-block list on the zero tag, the
one-block frozen list otherwise. -/
def residualVariableConstantChoiceProgram : NPOracleProgram :=
  taggedProgramChoice
    (gateAtomHeadListProgram
      (gateAtomBlockStageProgram frozenAtomRequestProgram))
    (gateAtomHeadListProgram frozenAtomRequestProgram)

/-- The constant half: one paired call of that dispatcher. -/
def residualVariableConstantRequestProgram : NPOracleProgram :=
  pairedCallProgram residualVariableConstantChoiceProgram

/-- The dispatcher over the two halves. -/
def residualVariableHalfChoiceProgram : NPOracleProgram :=
  taggedProgramChoice residualVariableEvaluationRequestProgram
    residualVariableConstantRequestProgram

/-- **The residual variable request machine.** -/
def residualVariableRequestProgram : NPOracleProgram :=
  pairedCallProgram residualVariableHalfChoiceProgram

theorem residualVariableEvaluationRequestProgram_oracleFree :
    OracleFree residualVariableEvaluationRequestProgram :=
  pairedCallProgram_oracleFree (gateAtomHeadListProgram signedAtomRequestProgram)
    (gateAtomHeadListProgram_oracleFree signedAtomRequestProgram
      signedAtomRequestProgram_oracleFree)

theorem residualVariableConstantChoiceProgram_oracleFree :
    OracleFree residualVariableConstantChoiceProgram :=
  taggedProgramChoice_oracleFree _ _
    (gateAtomHeadListProgram_oracleFree
      (gateAtomBlockStageProgram frozenAtomRequestProgram)
      (gateAtomBlockStageProgram_oracleFree frozenAtomRequestProgram
        frozenAtomRequestProgram_oracleFree))
    (gateAtomHeadListProgram_oracleFree frozenAtomRequestProgram
      frozenAtomRequestProgram_oracleFree)

theorem residualVariableConstantRequestProgram_oracleFree :
    OracleFree residualVariableConstantRequestProgram :=
  pairedCallProgram_oracleFree residualVariableConstantChoiceProgram
    residualVariableConstantChoiceProgram_oracleFree

theorem residualVariableHalfChoiceProgram_oracleFree :
    OracleFree residualVariableHalfChoiceProgram :=
  taggedProgramChoice_oracleFree _ _
    residualVariableEvaluationRequestProgram_oracleFree
    residualVariableConstantRequestProgram_oracleFree

theorem residualVariableRequestProgram_oracleFree :
    OracleFree residualVariableRequestProgram :=
  pairedCallProgram_oracleFree residualVariableHalfChoiceProgram
    residualVariableHalfChoiceProgram_oracleFree

def residualVariableEvaluationRequestInput {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask : ℕ) : ℕ :=
  Nat.pair (gateEvaluationLeftListInput gate inputMask)
    (gateEvaluationRightListInput gate inputMask)

def residualVariableConstantRequestInput {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask : ℕ) : ℕ :=
  Nat.pair (Nat.pair 0 (residualConstantLeftListInput gate inputMask liveMask))
    (Nat.pair 1 (residualConstantRightListInput gate inputMask liveMask))

/-- The request machine's input: the four framed generator requests. -/
def residualVariableRequestInput {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair 0 (residualVariableEvaluationRequestInput gate inputMask))
    (Nat.pair 1
      (residualVariableConstantRequestInput gate inputMask liveMask))

def residualVariableEvaluationRequestFuel {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask : ℕ) : ℕ :=
  pairedCallFuel (gateAtomHeadListProgram signedAtomRequestProgram)
    (gateEvaluationLeftListFuel gate inputMask)
    (gateEvaluationRightListFuel gate inputMask)

def residualVariableConstantRequestFuel {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask : ℕ) : ℕ :=
  pairedCallFuel residualVariableConstantChoiceProgram
    (taggedProgramChoiceFuel
      (residualConstantLeftListFuel gate inputMask liveMask))
    (taggedProgramChoiceFuel
      (residualConstantRightListFuel gate inputMask liveMask))

def residualVariableRequestFuel {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  pairedCallFuel residualVariableHalfChoiceProgram
    (taggedProgramChoiceFuel
      (residualVariableEvaluationRequestFuel gate inputMask))
    (taggedProgramChoiceFuel
      (residualVariableConstantRequestFuel gate inputMask liveMask))

def residualVariableEvaluationRequestBits {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask : ℕ) : ℕ :=
  pairedCallBits n (gateEvaluationLeftListBits gate inputMask)
    (gateEvaluationRightListBits gate inputMask)
    (gateEvaluationLeftListInput gate inputMask)
    (gateEvaluationRightListInput gate inputMask)
    (encodeBalancedList
      (signedAtomRequests n
        (gateEvaluationLeftAtoms gate (inputSelector inputMask))))
    (encodeBalancedList
      (signedAtomRequests n
        (gateEvaluationRightAtoms gate (inputSelector inputMask))))

def residualConstantLeftChoiceBits {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  max (residualConstantLeftListBits gate inputMask liveMask) <|
    max
      (natBitLength
        (Nat.pair n
          (Nat.pair 0 (residualConstantLeftListInput gate inputMask liveMask))))
      (natBitLength
        (encodeBalancedList
          (signedAtomRequests n
            (residualConstantLeftAtoms gate inputMask liveMask))))

def residualConstantRightChoiceBits {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  max (residualConstantRightListBits gate inputMask liveMask) <|
    max
      (natBitLength
        (Nat.pair n
          (Nat.pair 1
            (residualConstantRightListInput gate inputMask liveMask))))
      (natBitLength
        (encodeBalancedList
          (signedAtomRequests n
            (residualConstantRightAtoms gate inputMask liveMask))))

def residualVariableConstantRequestBits {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask : ℕ) : ℕ :=
  pairedCallBits n (residualConstantLeftChoiceBits gate inputMask liveMask)
    (residualConstantRightChoiceBits gate inputMask liveMask)
    (Nat.pair 0 (residualConstantLeftListInput gate inputMask liveMask))
    (Nat.pair 1 (residualConstantRightListInput gate inputMask liveMask))
    (encodeBalancedList
      (signedAtomRequests n
        (residualConstantLeftAtoms gate inputMask liveMask)))
    (encodeBalancedList
      (signedAtomRequests n
        (residualConstantRightAtoms gate inputMask liveMask)))

def residualVariableEvaluationHalfBits {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask : ℕ) : ℕ :=
  max (residualVariableEvaluationRequestBits gate inputMask) <|
    max
      (natBitLength
        (Nat.pair n
          (Nat.pair 0 (residualVariableEvaluationRequestInput gate inputMask))))
      (natBitLength (residualVariableEvaluationInput gate inputMask))

def residualVariableConstantHalfBits {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask : ℕ) : ℕ :=
  max (residualVariableConstantRequestBits gate inputMask liveMask) <|
    max
      (natBitLength
        (Nat.pair n
          (Nat.pair 1
            (residualVariableConstantRequestInput gate inputMask liveMask))))
      (natBitLength (residualVariableConstantInput gate inputMask liveMask))

def residualVariableRequestBits {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  pairedCallBits n (residualVariableEvaluationHalfBits gate inputMask)
    (residualVariableConstantHalfBits gate inputMask liveMask)
    (Nat.pair 0 (residualVariableEvaluationRequestInput gate inputMask))
    (Nat.pair 1
      (residualVariableConstantRequestInput gate inputMask liveMask))
    (residualVariableEvaluationInput gate inputMask)
    (residualVariableConstantInput gate inputMask liveMask)

/-- **The evaluation half's comparison input, executed.** -/
theorem run_residualVariableEvaluationRequestProgram {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask maximumBits : ℕ)
    (hbits : residualVariableEvaluationRequestBits gate inputMask ≤
      maximumBits) :
    runNPOracleProgram residualVariableEvaluationRequestProgram maximumBits
        (residualVariableEvaluationRequestFuel gate inputMask)
        (initialNPOracleState n
          (residualVariableEvaluationRequestInput gate inputMask)) =
      some (residualVariableEvaluationInput gate inputMask) :=
  run_bits_mono
    (run_pairedCallProgram (gateAtomHeadListProgram signedAtomRequestProgram)
      n (gateEvaluationLeftListBits gate inputMask)
      (gateEvaluationRightListBits gate inputMask)
      (gateEvaluationLeftListFuel gate inputMask)
      (gateEvaluationRightListFuel gate inputMask)
      (gateEvaluationLeftListInput gate inputMask)
      (gateEvaluationRightListInput gate inputMask)
      (encodeBalancedList
        (signedAtomRequests n
          (gateEvaluationLeftAtoms gate (inputSelector inputMask))))
      (encodeBalancedList
        (signedAtomRequests n
          (gateEvaluationRightAtoms gate (inputSelector inputMask))))
      (run_gateEvaluationLeftListProgram gate inputMask _ le_rfl)
      (run_gateEvaluationRightListProgram gate inputMask _ le_rfl))
    hbits

theorem run_residualVariableConstantChoiceProgram_left {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask maximumBits : ℕ)
    (hbits :
      residualConstantLeftChoiceBits gate inputMask liveMask ≤ maximumBits) :
    runNPOracleProgram residualVariableConstantChoiceProgram maximumBits
        (taggedProgramChoiceFuel
          (residualConstantLeftListFuel gate inputMask liveMask))
        (initialNPOracleState n
          (Nat.pair 0
            (residualConstantLeftListInput gate inputMask liveMask))) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            (residualConstantLeftAtoms gate inputMask liveMask))) := by
  have hlistBits :
      residualConstantLeftListBits gate inputMask liveMask ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hinputBits :
      natBitLength
          (Nat.pair n
            (Nat.pair 0
              (residualConstantLeftListInput gate inputMask liveMask))) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputBits :
      natBitLength
          (encodeBalancedList
            (signedAtomRequests n
              (residualConstantLeftAtoms gate inputMask liveMask))) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  exact run_taggedProgramChoice_zero _ _ n
    (residualConstantLeftListInput gate inputMask liveMask) maximumBits
    (residualConstantLeftListFuel gate inputMask liveMask) _ hinputBits
    (run_residualConstantLeftListProgram gate inputMask liveMask maximumBits
      hlistBits)
    houtputBits

theorem run_residualVariableConstantChoiceProgram_right {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask maximumBits : ℕ)
    (hbits :
      residualConstantRightChoiceBits gate inputMask liveMask ≤ maximumBits) :
    runNPOracleProgram residualVariableConstantChoiceProgram maximumBits
        (taggedProgramChoiceFuel
          (residualConstantRightListFuel gate inputMask liveMask))
        (initialNPOracleState n
          (Nat.pair 1
            (residualConstantRightListInput gate inputMask liveMask))) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            (residualConstantRightAtoms gate inputMask liveMask))) := by
  have hlistBits :
      residualConstantRightListBits gate inputMask liveMask ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hinputBits :
      natBitLength
          (Nat.pair n
            (Nat.pair 1
              (residualConstantRightListInput gate inputMask liveMask))) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputBits :
      natBitLength
          (encodeBalancedList
            (signedAtomRequests n
              (residualConstantRightAtoms gate inputMask liveMask))) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  exact run_taggedProgramChoice_nonzero _ _ n 1
    (residualConstantRightListInput gate inputMask liveMask) maximumBits
    (residualConstantRightListFuel gate inputMask liveMask) _ one_ne_zero
    hinputBits
    (run_residualConstantRightListProgram gate inputMask liveMask maximumBits
      hlistBits)
    houtputBits

/-- **The constant half's comparison input, executed.** -/
theorem run_residualVariableConstantRequestProgram {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask maximumBits : ℕ)
    (hbits :
      residualVariableConstantRequestBits gate inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram residualVariableConstantRequestProgram maximumBits
        (residualVariableConstantRequestFuel gate inputMask liveMask)
        (initialNPOracleState n
          (residualVariableConstantRequestInput gate inputMask liveMask)) =
      some (residualVariableConstantInput gate inputMask liveMask) :=
  run_bits_mono
    (run_pairedCallProgram residualVariableConstantChoiceProgram n
      (residualConstantLeftChoiceBits gate inputMask liveMask)
      (residualConstantRightChoiceBits gate inputMask liveMask)
      (taggedProgramChoiceFuel
        (residualConstantLeftListFuel gate inputMask liveMask))
      (taggedProgramChoiceFuel
        (residualConstantRightListFuel gate inputMask liveMask))
      (Nat.pair 0 (residualConstantLeftListInput gate inputMask liveMask))
      (Nat.pair 1 (residualConstantRightListInput gate inputMask liveMask))
      (encodeBalancedList
        (signedAtomRequests n
          (residualConstantLeftAtoms gate inputMask liveMask)))
      (encodeBalancedList
        (signedAtomRequests n
          (residualConstantRightAtoms gate inputMask liveMask)))
      (run_residualVariableConstantChoiceProgram_left gate inputMask liveMask
        _ le_rfl)
      (run_residualVariableConstantChoiceProgram_right gate inputMask liveMask
        _ le_rfl))
    hbits

theorem run_residualVariableHalfChoiceProgram_evaluation {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask maximumBits : ℕ)
    (hbits : residualVariableEvaluationHalfBits gate inputMask ≤
      maximumBits) :
    runNPOracleProgram residualVariableHalfChoiceProgram maximumBits
        (taggedProgramChoiceFuel
          (residualVariableEvaluationRequestFuel gate inputMask))
        (initialNPOracleState n
          (Nat.pair 0
            (residualVariableEvaluationRequestInput gate inputMask))) =
      some (residualVariableEvaluationInput gate inputMask) := by
  have hhalfBits :
      residualVariableEvaluationRequestBits gate inputMask ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hinputBits :
      natBitLength
          (Nat.pair n
            (Nat.pair 0
              (residualVariableEvaluationRequestInput gate inputMask))) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputBits :
      natBitLength (residualVariableEvaluationInput gate inputMask) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  exact run_taggedProgramChoice_zero _ _ n
    (residualVariableEvaluationRequestInput gate inputMask) maximumBits
    (residualVariableEvaluationRequestFuel gate inputMask) _ hinputBits
    (run_residualVariableEvaluationRequestProgram gate inputMask maximumBits
      hhalfBits)
    houtputBits

theorem run_residualVariableHalfChoiceProgram_constant {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask maximumBits : ℕ)
    (hbits :
      residualVariableConstantHalfBits gate inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram residualVariableHalfChoiceProgram maximumBits
        (taggedProgramChoiceFuel
          (residualVariableConstantRequestFuel gate inputMask liveMask))
        (initialNPOracleState n
          (Nat.pair 1
            (residualVariableConstantRequestInput gate inputMask
              liveMask))) =
      some (residualVariableConstantInput gate inputMask liveMask) := by
  have hhalfBits :
      residualVariableConstantRequestBits gate inputMask liveMask ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hinputBits :
      natBitLength
          (Nat.pair n
            (Nat.pair 1
              (residualVariableConstantRequestInput gate inputMask
                liveMask))) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputBits :
      natBitLength (residualVariableConstantInput gate inputMask liveMask) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  exact run_taggedProgramChoice_nonzero _ _ n 1
    (residualVariableConstantRequestInput gate inputMask liveMask) maximumBits
    (residualVariableConstantRequestFuel gate inputMask liveMask) _
    one_ne_zero hinputBits
    (run_residualVariableConstantRequestProgram gate inputMask liveMask
      maximumBits hhalfBits)
    houtputBits

/-- **One gate's residual variable request, executed.**  This is exactly the
input `CanonicalSignedGateEvaluationProgram.run_residualVariableProgram`
consumes, assembled from the gate's own weight syntax by two paired calls of
the head-list producers. -/
theorem run_residualVariableRequestProgram {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask maximumBits : ℕ)
    (hbits : residualVariableRequestBits gate inputMask liveMask ≤
      maximumBits) :
    runNPOracleProgram residualVariableRequestProgram maximumBits
        (residualVariableRequestFuel gate inputMask liveMask)
        (initialNPOracleState n
          (residualVariableRequestInput gate inputMask liveMask)) =
      some (residualVariableInput gate inputMask liveMask) :=
  run_bits_mono
    (run_pairedCallProgram residualVariableHalfChoiceProgram n
      (residualVariableEvaluationHalfBits gate inputMask)
      (residualVariableConstantHalfBits gate inputMask liveMask)
      (taggedProgramChoiceFuel
        (residualVariableEvaluationRequestFuel gate inputMask))
      (taggedProgramChoiceFuel
        (residualVariableConstantRequestFuel gate inputMask liveMask))
      (Nat.pair 0 (residualVariableEvaluationRequestInput gate inputMask))
      (Nat.pair 1
        (residualVariableConstantRequestInput gate inputMask liveMask))
      (residualVariableEvaluationInput gate inputMask)
      (residualVariableConstantInput gate inputMask liveMask)
      (run_residualVariableHalfChoiceProgram_evaluation gate inputMask _
        le_rfl)
      (run_residualVariableHalfChoiceProgram_constant gate inputMask liveMask _
        le_rfl))
    hbits

end NearCubicWires.CanonicalGateAtomHeadListProgram
