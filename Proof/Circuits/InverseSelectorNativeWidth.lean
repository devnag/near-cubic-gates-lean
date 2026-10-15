import Proof.Circuits.InverseSelectorRequestSourceAdapter

/-!
# Native width at the inverse selector's scheduled source length

The published shape runner expects its own input length.  The outer request's
length is generally different, so this module calls it through the standard
native contextual call ABI after the executable inverse length stage.  This is
the native-width half of the inverse substitution-request tail and assumes no
schedule diagonal.
-/

namespace NearCubicWires.InverseSelectorNativeWidth

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedDescriptionRequestSourceAdapter
open NearCubicWires.InverseLengthStage
open NearCubicWires.InverseSelectorRequestSourceAdapter
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Frame the scheduled length as a contextual native call -/

def scheduledShapeCallFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 2 3 4 3
  , .pair 2 4 0 4
  , .halt 0
  ]

@[simp] theorem scheduledShapeCallFrameProgram_oracleFree :
    OracleFree scheduledShapeCallFrameProgram := by
  rfl

def scheduledShapeCallFrameBits (sourceLen code : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair sourceLen code)
      (Nat.pair sourceLen (Nat.pair sourceLen code)))

theorem run_scheduledShapeCallFrameProgram
    (inputLength sourceLen code : ℕ) :
    runNPOracleProgram scheduledShapeCallFrameProgram
        (scheduledShapeCallFrameBits sourceLen code) 5
        (initialNPOracleState inputLength (Nat.pair sourceLen code)) =
      some (Nat.pair sourceLen (Nat.pair sourceLen code)) := by
  have hinput :
      natBitLength (Nat.pair sourceLen code) ≤
        scheduledShapeCallFrameBits sourceLen code :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtput :
      natBitLength (Nat.pair sourceLen (Nat.pair sourceLen code)) ≤
        scheduledShapeCallFrameBits sourceLen code :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hsource : natBitLength sourceLen ≤
      scheduledShapeCallFrameBits sourceLen code :=
    (natBitLength_mono (Nat.left_le_pair sourceLen code)).trans hinput
  have hcode : natBitLength code ≤
      scheduledShapeCallFrameBits sourceLen code :=
    (natBitLength_mono (Nat.right_le_pair sourceLen code)).trans hinput
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceLen) (by rfl) rfl
    (by simp [initialNPOracleState]) hsource]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := code) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcode]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair sourceLen code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hinput]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair sourceLen (Nat.pair sourceLen code)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 2. Project the shape runner's native-width field -/

def scheduledShapeNativeWidthProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .unpairLeft 0 0 2
  , .halt 0
  ]

@[simp] theorem scheduledShapeNativeWidthProgram_oracleFree :
    OracleFree scheduledShapeNativeWidthProgram := by
  rfl

def scheduledShapeNativeWidthBits
    (shapeCode sourceLen code : ℕ) : ℕ :=
  natBitLength
    (Nat.pair shapeCode (Nat.pair sourceLen code))

theorem run_scheduledShapeNativeWidthProgram
    (inputLength shapeCode sourceLen code : ℕ) :
    runNPOracleProgram scheduledShapeNativeWidthProgram
        (scheduledShapeNativeWidthBits shapeCode sourceLen code) 3
        (initialNPOracleState inputLength
          (Nat.pair shapeCode (Nat.pair sourceLen code))) =
      some (Nat.unpair shapeCode).1 := by
  have hshape : natBitLength shapeCode ≤
      scheduledShapeNativeWidthBits shapeCode sourceLen code :=
    natBitLength_mono (Nat.left_le_pair _ _)
  have hwidth : natBitLength (Nat.unpair shapeCode).1 ≤
      scheduledShapeNativeWidthBits shapeCode sourceLen code :=
    (natBitLength_mono (Nat.unpair_left_le shapeCode)).trans hshape
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := shapeCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hshape]
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair shapeCode).1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth

/-! ## 3. The scheduled native-width stream -/

noncomputable def inverseSelectorNativeWidthProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) : NPOracleProgram :=
  linkPrograms (inverseLengthProgram contracts clockDepth advantageExponent)
    (linkPrograms scheduledShapeCallFrameProgram
      (linkPrograms
        (nativeContextCallProgram
          (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program)
        scheduledShapeNativeWidthProgram))

noncomputable def inverseSelectorNativeWidthBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  let sourceLen :=
    inverseTailSourceLength contracts clockDepth advantageExponent target
  let shapeBits :=
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget sourceLen
  let shapeCode :=
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.execute sourceLen
  occurrenceStageBits target
    (inverseLengthBits contracts clockDepth advantageExponent
      ⟨target, fixedTargetCodeInput target⟩)
    (occurrenceStageBits target
      (scheduledShapeCallFrameBits sourceLen target)
      (occurrenceStageBits target
        (nativeContextCallBits target sourceLen sourceLen target shapeCode
          shapeBits)
        (scheduledShapeNativeWidthBits shapeCode sourceLen target)))

noncomputable def inverseSelectorNativeWidthFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  let sourceLen :=
    inverseTailSourceLength contracts clockDepth advantageExponent target
  let shapeFuel :=
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget sourceLen
  linkFuel
    (linkPrograms scheduledShapeCallFrameProgram
      (linkPrograms
        (nativeContextCallProgram
          (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program)
        scheduledShapeNativeWidthProgram))
    (inverseLengthFuel contracts clockDepth advantageExponent
      ⟨target, fixedTargetCodeInput target⟩)
    (linkFuel
      (linkPrograms
        (nativeContextCallProgram
          (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program)
        scheduledShapeNativeWidthProgram)
      5
      (linkFuel scheduledShapeNativeWidthProgram
        (nativeContextCallFuel
          (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program
          shapeFuel sourceLen sourceLen)
        3))

set_option maxHeartbeats 800000 in
-- The contextual call transports the dependent scheduled shape result.
theorem run_inverseSelectorNativeWidthProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) :
    runNPOracleProgram
        (inverseSelectorNativeWidthProgram contracts clockDepth
          advantageExponent)
        (inverseSelectorNativeWidthBits contracts clockDepth advantageExponent
          target)
        (inverseSelectorNativeWidthFuel contracts clockDepth advantageExponent
          target)
        (initialNPOracleState target target) =
      some
        ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
          (inverseTailSourceLength contracts clockDepth advantageExponent
            target)) := by
  let sourceLen :=
    inverseTailSourceLength contracts clockDepth advantageExponent target
  let shapeBits :=
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget sourceLen
  let shapeCode :=
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.execute sourceLen
  have hlength := run_inverseLengthProgram contracts clockDepth advantageExponent
    target (fixedTargetCodeInput target)
  have hscheduleLength :
      BankEmittedAtomLoop.inverseScheduleLength contracts clockDepth
          advantageExponent target = sourceLen :=
    rfl
  rw [hscheduleLength] at hlength
  have hlength' :
      runNPOracleProgram
          (inverseLengthProgram contracts clockDepth advantageExponent)
          (inverseLengthBits contracts clockDepth advantageExponent
            ⟨target, fixedTargetCodeInput target⟩)
          (inverseLengthFuel contracts clockDepth advantageExponent
            ⟨target, fixedTargetCodeInput target⟩)
          (initialNPOracleState target target) =
        some (Nat.pair sourceLen target) := by
    simpa [sourceLen] using hlength
  have hframe := run_scheduledShapeCallFrameProgram target sourceLen target
  have hshape :
      runNPOracleProgram
          (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program
          shapeBits shapeBits (initialNPOracleState sourceLen sourceLen) =
        some shapeCode := by
    exact run_publishedShapeProgram
      (publishedHierarchyOuterPCP contracts clockDepth) sourceLen
  have hcall := run_nativeContextCallProgram
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program target
    sourceLen sourceLen target shapeCode shapeBits shapeBits hshape
  have htake := run_scheduledShapeNativeWidthProgram target shapeCode sourceLen
    target
  unfold inverseSelectorNativeWidthProgram inverseSelectorNativeWidthBits
    inverseSelectorNativeWidthFuel
  dsimp only
  exact run_occurrenceStage hlength'
    (run_occurrenceStage hframe (run_occurrenceStage hcall htake))

end NearCubicWires.InverseSelectorNativeWidth
