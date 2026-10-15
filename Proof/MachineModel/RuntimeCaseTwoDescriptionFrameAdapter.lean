import Proof.Circuits.CanonicalDescriptionGroupingDecoder
import Proof.MachineModel.RuntimeCaseTwoCircuitEncodingClosure

/-!
# The description frame at the scheduled branch

`RuntimeCaseTwoCircuitEncodingClosure.InverseDescriptionFrameRuns` asks for one
stage that, from the requested public length alone, emits the description
pool's own request word

> `pair (generatedBalancedRangeInput descriptionWidth atomStream)
>   (pair nativeWidth sizeBound)`.

Three things are bundled there, and this module separates them.

* **The description width.**  `descriptionWidth W B = (B + 1) · (6 + 2 · (W + B
  + 1))` is pure arithmetic over the two numerals, and *nothing in the tree
  emits it*: there is no `descriptionWidthProgram` anywhere.  §1--§2 build it —
  two straight-line stages around the published bit-serial multiplier — and §3
  discharges that half outright.
* **The two numerals.**  They are not computed here: the adapter keeps them
  verbatim from the stage below it.  This is deliberate.  Both are already
  components of the atom loop's own public request context
  (`BoundedOracleStructuralFormulaTable.tableBoundedOracleStructuralFormulaContext`
  pairs the native width second and the size bound fourth), so a stage that has
  produced the atom stream at a target has produced the numerals with it.
* **The atom stream.**  `descriptionAtomContext` is
  `encodeBalancedList (boundedOracleStructuralFormulaAtoms …)`.  No run contract
  in the tree has that as its output: the published route is
  `StructuralAtomEmitterLoopProgram.structuralAtomRangeProgram` — the *first*
  half of the bank-framed emitter, before its `balancedToTaggedProgram`
  retagging — under `StructuralAtomCalleeProgram.structuralAtomRequests_map`,
  and that stage stands on `BankEmittedAtomLoop.InverseCompilerRuns` exactly as
  the selector side does.  The retagged emitter is *not* an alternative: its
  output is `encodeTaggedList`, and converting back costs
  `taggedToBalancedRegisterBitsFor`, whose register width is bounded below by
  `2 ^ (list length)`
  (`ValidatorTaggedIntermediateVerdict.two_pow_length_le_taggedToBalancedRegisterBitsFor`).

So the atom stream enters here as one named premise, in the same shape the
emitter chain already uses, and §3 shows it is the *only* thing the description
frame still needs.
-/

namespace NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.CaseTwoDescriptionBitPoolProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalDescriptionGroupingDecoder
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoRequestWordFrame
open NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbound : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbound

/-! ## 1. The description width, from the two numerals -/

private theorem frameRowWidth_eq (width bound : ℕ) :
    boundedCircuitFieldLimit width bound +
        boundedCircuitFieldLimit width bound + 6 =
      rowWidth width bound := by
  have hwidth : rowWidth width bound =
      6 + 2 * boundedCircuitFieldLimit width bound := rfl
  omega

/-- The word the description frame starts from: the emitter's atom stream
beside the padded native width and the scheduled size cap. -/
def descriptionFrameSource (atoms width bound : ℕ) : ℕ :=
  Nat.pair atoms (Nat.pair width bound)

/-- Register ABI: `r6` the field limit, `r7` the row width, `r5` the row count,
`r2` the retained atom stream. -/
def descriptionFramePrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .add 4 5 6 5
  , .increment 6 6
  , .add 6 6 7 7
  , .set 8 6 8
  , .add 7 8 7 9
  , .increment 5 10
  , .pair 5 7 5 11
  , .pair 2 3 2 12
  , .pair 5 2 0 13
  , .halt 0
  ]

@[simp] theorem descriptionFramePrepProgram_oracleFree :
    OracleFree descriptionFramePrepProgram := by
  rfl

def descriptionFramePrepFuel : ℕ := 14

def descriptionFramePrepOutput (atoms width bound : ℕ) : ℕ :=
  Nat.pair (bitSerialMulInput (bound + 1) (rowWidth width bound))
    (descriptionFrameSource atoms width bound)

def descriptionFramePrepBits (atoms width bound : ℕ) : ℕ :=
  natBitLength
    (max (descriptionFrameSource atoms width bound)
      (descriptionFramePrepOutput atoms width bound))

set_option maxHeartbeats 400000 in
-- The statement carries both frame words and the derived row numerals, so
-- elaborating the width chain alone exceeds the default budget.
theorem run_descriptionFramePrepProgram (inputLength atoms width bound : ℕ) :
    runNPOracleProgram descriptionFramePrepProgram
        (descriptionFramePrepBits atoms width bound) descriptionFramePrepFuel
        (initialNPOracleState inputLength
          (descriptionFrameSource atoms width bound)) =
      some (descriptionFramePrepOutput atoms width bound) := by
  have hlimit : boundedCircuitFieldLimit width bound = width + bound + 1 := rfl
  have hrow : rowWidth width bound =
      6 + 2 * boundedCircuitFieldLimit width bound := rfl
  have hinput :
      natBitLength (descriptionFrameSource atoms width bound) ≤
        descriptionFramePrepBits atoms width bound :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput :
      natBitLength (descriptionFramePrepOutput atoms width bound) ≤
        descriptionFramePrepBits atoms width bound :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hatoms : natBitLength atoms ≤
      descriptionFramePrepBits atoms width bound :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hpair : natBitLength (Nat.pair width bound) ≤
      descriptionFramePrepBits atoms width bound :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hwidth : natBitLength width ≤
      descriptionFramePrepBits atoms width bound :=
    bits_of_le (Nat.left_le_pair _ _) hpair
  have hbound : natBitLength bound ≤
      descriptionFramePrepBits atoms width bound :=
    bits_of_le (Nat.right_le_pair _ _) hpair
  have hproduct :
      natBitLength (bitSerialMulInput (bound + 1) (rowWidth width bound)) ≤
        descriptionFramePrepBits atoms width bound :=
    bits_of_le (Nat.left_le_pair _ _) houtput
  have hrows : natBitLength (bound + 1) ≤
      descriptionFramePrepBits atoms width bound :=
    bits_of_le (Nat.left_le_pair _ _) hproduct
  have hrowWidth : natBitLength (rowWidth width bound) ≤
      descriptionFramePrepBits atoms width bound :=
    bits_of_le (Nat.right_le_pair _ _) hproduct
  have hfield : natBitLength (boundedCircuitFieldLimit width bound) ≤
      descriptionFramePrepBits atoms width bound :=
    bits_of_le (by omega) hrowWidth
  have hsum : natBitLength (width + bound) ≤
      descriptionFramePrepBits atoms width bound :=
    bits_of_le (by omega) hfield
  have hdouble :
      natBitLength
          (boundedCircuitFieldLimit width bound +
            boundedCircuitFieldLimit width bound) ≤
        descriptionFramePrepBits atoms width bound :=
    bits_of_le (by omega) hrowWidth
  have hsix : natBitLength 6 ≤ descriptionFramePrepBits atoms width bound :=
    bits_of_le (by omega) hrowWidth
  rw [show descriptionFramePrepFuel = 13 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := atoms) (by rfl) rfl
    (by simp [initialNPOracleState, descriptionFrameSource]) hatoms]
  rw [show (13 : ℕ) = 12 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair width bound) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      descriptionFrameSource])
    hpair]
  rw [show (12 : ℕ) = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := bound) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbound]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_add_instruction (value := width + bound) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsum]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_increment_instruction (value := boundedCircuitFieldLimit width bound)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hlimit]) hfield]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_add_instruction
    (value :=
      boundedCircuitFieldLimit width bound +
        boundedCircuitFieldLimit width bound)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdouble]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_set_instruction (value := 6) (by rfl) rfl hsix]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_add_instruction (value := rowWidth width bound) (by rfl) rfl
    (by
      rw [← frameRowWidth_eq width bound]
      simp [NPOracleState.write, NPOracleState.jump])
    hrowWidth]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_increment_instruction (value := bound + 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrows]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := bitSerialMulInput (bound + 1) (rowWidth width bound)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSerialMulInput])
    hproduct]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := descriptionFrameSource atoms width bound)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionFrameSource])
    hinput]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := descriptionFramePrepOutput atoms width bound) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      descriptionFramePrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Assemble the pool's request word once the description width is known. -/
def descriptionFramePostProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 4 2 5
  , .pair 2 5 0 6
  , .halt 0
  ]

@[simp] theorem descriptionFramePostProgram_oracleFree :
    OracleFree descriptionFramePostProgram := by
  rfl

def descriptionFramePostFuel : ℕ := 7

def descriptionFramePostOutput (atoms width bound : ℕ) : ℕ :=
  Nat.pair
    (generatedBalancedRangeInput (descriptionWidth width bound) atoms)
    (Nat.pair width bound)

def descriptionFramePostBits (atoms width bound : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair (descriptionWidth width bound)
        (descriptionFrameSource atoms width bound))
      (descriptionFramePostOutput atoms width bound))

theorem run_descriptionFramePostProgram (inputLength atoms width bound : ℕ) :
    runNPOracleProgram descriptionFramePostProgram
        (descriptionFramePostBits atoms width bound) descriptionFramePostFuel
        (initialNPOracleState inputLength
          (Nat.pair (descriptionWidth width bound)
            (descriptionFrameSource atoms width bound))) =
      some (descriptionFramePostOutput atoms width bound) := by
  have hinput :
      natBitLength
          (Nat.pair (descriptionWidth width bound)
            (descriptionFrameSource atoms width bound)) ≤
        descriptionFramePostBits atoms width bound :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput :
      natBitLength (descriptionFramePostOutput atoms width bound) ≤
        descriptionFramePostBits atoms width bound :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hcount : natBitLength (descriptionWidth width bound) ≤
      descriptionFramePostBits atoms width bound :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hsource : natBitLength (descriptionFrameSource atoms width bound) ≤
      descriptionFramePostBits atoms width bound :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hatoms : natBitLength atoms ≤
      descriptionFramePostBits atoms width bound :=
    bits_of_le (Nat.left_le_pair _ _) hsource
  have hpair : natBitLength (Nat.pair width bound) ≤
      descriptionFramePostBits atoms width bound :=
    bits_of_le (Nat.right_le_pair _ _) hsource
  have hrange :
      natBitLength
          (generatedBalancedRangeInput (descriptionWidth width bound) atoms) ≤
        descriptionFramePostBits atoms width bound :=
    bits_of_le (Nat.left_le_pair _ _) houtput
  rw [show descriptionFramePostFuel = 6 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := descriptionWidth width bound)
    (by rfl) rfl (by simp [initialNPOracleState]) hcount]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := descriptionFrameSource atoms width bound) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hsource]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := atoms) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionFrameSource])
    hatoms]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair width bound) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionFrameSource])
    hpair]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := generatedBalancedRangeInput (descriptionWidth width bound) atoms)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      generatedBalancedRangeInput])
    hrange]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := descriptionFramePostOutput atoms width bound) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      descriptionFramePostOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 2. The width stage -/

/-- **The description-width stage.**  From the atom stream and the two numerals
the fixed stream emits the description pool's own request word.  Nothing about
the schedule, the branch or the target enters it. -/
def descriptionFrameWidthProgram : NPOracleProgram :=
  linkPrograms descriptionFramePrepProgram
    (linkPrograms (preserveRightProgram bitSerialMulProgram)
      descriptionFramePostProgram)

theorem descriptionFrameWidthProgram_oracleFree :
    OracleFree descriptionFrameWidthProgram :=
  oracleFree_linkPrograms descriptionFramePrepProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _ bitSerialMulProgram_oracleFree)
      descriptionFramePostProgram_oracleFree)

def descriptionFrameWidthFuel (width bound : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram bitSerialMulProgram)
      descriptionFramePostProgram)
    descriptionFramePrepFuel
    (linkFuel descriptionFramePostProgram
      (preserveRightFuel (bitSerialMulFuel (rowWidth width bound)))
      descriptionFramePostFuel)

def descriptionFrameWidthBits (inputLength atoms width bound : ℕ) : ℕ :=
  occurrenceStageBits inputLength (descriptionFramePrepBits atoms width bound)
    (occurrenceStageBits inputLength
      (preserveRightBits
        (bitSerialMulBits inputLength (bound + 1) (rowWidth width bound))
        (bitSerialMulInput (bound + 1) (rowWidth width bound))
        (descriptionFrameSource atoms width bound)
        (descriptionWidth width bound))
      (descriptionFramePostBits atoms width bound))

theorem run_descriptionFrameWidthProgram (inputLength atoms width bound : ℕ) :
    runNPOracleProgram descriptionFrameWidthProgram
        (descriptionFrameWidthBits inputLength atoms width bound)
        (descriptionFrameWidthFuel width bound)
        (initialNPOracleState inputLength
          (descriptionFrameSource atoms width bound)) =
      some (descriptionFramePostOutput atoms width bound) := by
  have hproduct : (bound + 1) * rowWidth width bound =
      descriptionWidth width bound := rfl
  refine run_occurrenceStage
    (run_descriptionFramePrepProgram inputLength atoms width bound) ?_
  refine run_occurrenceStage ?_
    (run_descriptionFramePostProgram inputLength atoms width bound)
  rw [← hproduct]
  exact run_preserveRightProgram bitSerialMulProgram inputLength
    (bitSerialMulBits inputLength (bound + 1) (rowWidth width bound))
    (bitSerialMulFuel (rowWidth width bound))
    (bitSerialMulInput (bound + 1) (rowWidth width bound))
    (descriptionFrameSource atoms width bound)
    ((bound + 1) * rowWidth width bound)
    (run_bitSerialMulProgram inputLength (bound + 1) (rowWidth width bound))

/-! ## 3. The description frame, from the atom stream alone -/

/-- The padded native width at one target, read at the schedule's own source
length. -/
noncomputable def inverseFrameWidth
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (target : ℕ) : ℕ :=
  (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth)).nativeWidth
    (sourceLength
      (inverseChainSourceIndex contracts clockDepth advantageExponent target))

/-- The scheduled small-oracle size cap at that width. -/
noncomputable def inverseFrameBound
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (target : ℕ) : ℕ :=
  inverseOracleSizeBound contracts advantageExponent
    (inverseFrameWidth contracts clockDepth advantageExponent target)

/-- The emitter's atom stream at one target, balanced. -/
noncomputable def inverseFrameAtoms
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target : ℕ) : ℕ :=
  descriptionAtomContext
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent target)
    (inverseFrameBound contracts clockDepth advantageExponent target)

/-- The pool's request word is the width stage applied to those three
components. -/
theorem canonicalCircuitEncoderInput_eq
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target : ℕ) :
    canonicalCircuitEncoderInput
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target)
        (inverseOracleSizeBound contracts advantageExponent) =
      descriptionFramePostOutput
        (inverseFrameAtoms contracts clockDepth machine advantageExponent target)
        (inverseFrameWidth contracts clockDepth advantageExponent target)
        (inverseFrameBound contracts clockDepth advantageExponent target) :=
  rfl

/-- **The atom-stream premise.**  Started on the requested public length, the
stage returns the emitter's balanced atom stream beside the padded native width
and the scheduled size cap.  Nothing about the description layout is asked of
it — the adapter computes that itself. -/
def InverseDescriptionAtomStreamRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (stream : NPOracleProgram) (streamBits streamFuel : ℕ → ℕ) : Prop :=
  ∀ target : ℕ,
    inverseCaseOneTargetOnset contracts
      (publishedHierarchyOuterPCP contracts clockDepth)
      advantageExponent ≤ target →
    runNPOracleProgram stream (streamBits target) (streamFuel target)
        (initialNPOracleState target target) =
      some
        (descriptionFrameSource
          (inverseFrameAtoms contracts clockDepth machine advantageExponent
            target)
          (inverseFrameWidth contracts clockDepth advantageExponent target)
          (inverseFrameBound contracts clockDepth advantageExponent target))

/-- **The description frame.**  The atom-stream stage, then the width stage. -/
def inverseDescriptionFrameProgram (stream : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms stream descriptionFrameWidthProgram

theorem inverseDescriptionFrameProgram_oracleFree {stream : NPOracleProgram}
    (hstream : OracleFree stream) :
    OracleFree (inverseDescriptionFrameProgram stream) :=
  oracleFree_linkPrograms hstream descriptionFrameWidthProgram_oracleFree

noncomputable def inverseDescriptionFrameFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (streamFuel : ℕ → ℕ) (target : ℕ) : ℕ :=
  linkFuel descriptionFrameWidthProgram (streamFuel target)
    (descriptionFrameWidthFuel
      (inverseFrameWidth contracts clockDepth advantageExponent target)
      (inverseFrameBound contracts clockDepth advantageExponent target))

noncomputable def inverseDescriptionFrameBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (streamBits : ℕ → ℕ) (target : ℕ) : ℕ :=
  occurrenceStageBits target (streamBits target)
    (descriptionFrameWidthBits target
      (inverseFrameAtoms contracts clockDepth machine advantageExponent target)
      (inverseFrameWidth contracts clockDepth advantageExponent target)
      (inverseFrameBound contracts clockDepth advantageExponent target))

/-- **The description frame, from the atom stream alone.**  The description
width — the one component of the pool's request word that no published program
emits — is discharged outright: the adapter derives it from the two numerals by
fixed arithmetic.  What is left of the frame is exactly the balanced atom
stream at one target. -/
theorem inverseDescriptionFrameRuns_ofAtomStream
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (stream : NPOracleProgram) (streamBits streamFuel : ℕ → ℕ)
    (hstream :
      InverseDescriptionAtomStreamRuns contracts clockDepth machine
        advantageExponent stream streamBits streamFuel) :
    InverseDescriptionFrameRuns contracts clockDepth machine advantageExponent
      (inverseDescriptionFrameProgram stream)
      (inverseDescriptionFrameBits contracts clockDepth machine
        advantageExponent streamBits)
      (inverseDescriptionFrameFuel contracts clockDepth advantageExponent
        streamFuel) := by
  intro target hlarge
  rw [canonicalCircuitEncoderInput_eq contracts clockDepth machine
    advantageExponent target]
  exact run_occurrenceStage (hstream target hlarge)
    (run_descriptionFrameWidthProgram target
      (inverseFrameAtoms contracts clockDepth machine advantageExponent target)
      (inverseFrameWidth contracts clockDepth advantageExponent target)
      (inverseFrameBound contracts clockDepth advantageExponent target))

/-! ## 4. The cluster's encoder premise, from the atom stream alone -/

/-- The published Case-2 occurrence-encoding stream at one atom-stream
stage: the description frame of §3 under the discharged grouping decoder. -/
noncomputable def inverseClosedEncodingProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (stream : NPOracleProgram) : NPOracleProgram :=
  inverseSubstitutedEncodingProgram contracts clockDepth
    (inverseSubstitutionRequestProgram contracts clockDepth machine
      advantageExponent
      (inverseCircuitEncodingProgram (inverseDescriptionFrameProgram stream)
        canonicalDescriptionDecoderProgram))

noncomputable def inverseClosedEncodingBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (streamBits : ℕ → ℕ) : ℕ → ℕ :=
  inverseSubstitutedEncodingBits contracts clockDepth machine advantageExponent
    (inverseSubstitutionRequestBits contracts clockDepth machine
      advantageExponent
      (inverseCircuitEncodingBits contracts clockDepth machine advantageExponent
        canonicalDescriptionDecoderBits
        (inverseDescriptionFrameBits contracts clockDepth machine
          advantageExponent streamBits)))

noncomputable def inverseClosedEncodingFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (stream : NPOracleProgram) (streamFuel : ℕ → ℕ) : ℕ → ℕ :=
  inverseSubstitutedEncodingFuel contracts clockDepth machine advantageExponent
    (inverseSubstitutionRequestFuel contracts clockDepth machine
      advantageExponent
      (inverseCircuitEncodingProgram (inverseDescriptionFrameProgram stream)
        canonicalDescriptionDecoderProgram)
      (inverseCircuitEncodingFuel contracts clockDepth machine advantageExponent
        canonicalDescriptionDecoderProgram canonicalDescriptionDecoderFuel
        (inverseDescriptionFrameFuel contracts clockDepth advantageExponent
          streamFuel)))

set_option maxHeartbeats 1600000 in
-- The statement is the cluster's encoder premise at the whole linked stream,
-- so elaborating it alone exceeds the default budget.
/-- **The cluster's encoder premise, from the atom stream alone.**  The
oracle-free grouping decoder of `CanonicalDescriptionGroupingDecoder` is a
theorem, and the description frame is discharged down to the emitter's own
balanced atom stream.  What
`RuntimeCaseTwoOccurrenceEncodingClosure.inverse_clusterResiduals_ofEncoding`
consumes therefore needs only the schedule diagonal and one atom-stream
stage — the same stage the selector side of the emitter already stands on. -/
theorem inverseScheduledOccurrenceEncoding_ofAtomStream
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (stream : NPOracleProgram) (streamBits streamFuel : ℕ → ℕ)
    (hstream :
      InverseDescriptionAtomStreamRuns contracts clockDepth machine
        advantageExponent stream streamBits streamFuel) :
    InverseScheduledOccurrenceEncoding contracts clockDepth machine
      advantageExponent
      (inverseClosedEncodingProgram contracts clockDepth machine
        advantageExponent stream)
      (inverseClosedEncodingBits contracts clockDepth machine advantageExponent
        streamBits)
      (inverseClosedEncodingFuel contracts clockDepth machine advantageExponent
        stream streamFuel) :=
  inverseScheduledOccurrenceEncoding_ofDecoder contracts clockDepth machine
    advantageExponent hdiagonal (inverseDescriptionFrameProgram stream)
    canonicalDescriptionDecoderProgram
    (inverseDescriptionFrameBits contracts clockDepth machine advantageExponent
      streamBits)
    (inverseDescriptionFrameFuel contracts clockDepth advantageExponent
      streamFuel)
    canonicalDescriptionDecoderBits canonicalDescriptionDecoderFuel
    (inverseDescriptionFrameRuns_ofAtomStream contracts clockDepth machine
      advantageExponent stream streamBits streamFuel hstream)
    canonicalDescriptionDecoder_holds

end NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
