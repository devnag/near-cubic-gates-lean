import Proof.Foundations.CanonicalBinaryProgram
import Proof.Foundations.ComponentwiseVerifierParameters
import Proof.Foundations.PCPPClausePadding
import Proof.Foundations.PolynomialSchedule
import Proof.Foundations.SupplierPipeline

/-!
# Source-only recovery arity envelope

This module freezes the quantitative path shared by both headline recoveries.
Source instance `s` has length `2^(s+1)`, the outer proof is padded to the one
canonical width envelope, and the Case-2 oracle cap is one pairing clock.  The
two copy-count tiers differ only where the theorem statements differ:
inverse-polynomial advantage uses logarithmically many blocks, while fixed
advantage uses one constant number of blocks.

Every raw Case-2 XOR arity is bounded by a single smooth polynomial.  Case 1
and Case 2 can therefore be padded to that same arity before the target-length
selector runs; no branch-specific schedule or caller-selected growth function
is exposed.
-/

namespace NearCubicWires.RecoveryScheduleEnvelope

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.PolynomialSchedule
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.ScheduleArithmetic
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

/-- The sole source enumeration used by recovery. -/
def sourceLength (sourceIndex : ℕ) : ℕ :=
  2 ^ (sourceIndex + 1)

/-- Decode the sole source enumeration from a public input length.  Arbitrary
lengths are rounded down; scheduled lengths below recover their index exactly. -/
def sourceIndexOfLength (inputLength : ℕ) : ℕ :=
  Nat.log 2 inputLength - 1

@[simp] theorem sourceIndexOfLength_sourceLength (sourceIndex : ℕ) :
    sourceIndexOfLength (sourceLength sourceIndex) = sourceIndex := by
  simp [sourceIndexOfLength, sourceLength, Nat.log_pow]

/-- The scale represented by an arbitrary public length is never more than a
factor two above that length.  This is the resource bridge used when a compact
schedule index controls a materialized `2^q` intermediate. -/
theorem sourceScaleOfLength_le (inputLength : ℕ) :
    2 ^ (sourceIndexOfLength inputLength + 1) ≤
      2 * (inputLength + 1) := by
  by_cases hzero : inputLength = 0
  · subst inputLength
    simp [sourceIndexOfLength]
  · have hlogPower :
        2 ^ Nat.log 2 inputLength ≤ inputLength :=
      Nat.pow_log_le_self 2 hzero
    have hexponent :
        sourceIndexOfLength inputLength + 1 ≤
          Nat.log 2 inputLength + 1 := by
      unfold sourceIndexOfLength
      omega
    calc
      2 ^ (sourceIndexOfLength inputLength + 1) ≤
          2 ^ (Nat.log 2 inputLength + 1) :=
        Nat.pow_le_pow_right (by omega) hexponent
      _ = 2 ^ Nat.log 2 inputLength * 2 := by
        rw [pow_succ]
      _ ≤ inputLength * 2 :=
        Nat.mul_le_mul_right 2 hlogPower
      _ ≤ 2 * (inputLength + 1) := by omega

/-- A quantity exponential in a linearly scheduled compact arity is still
polynomial in the public machine length.  This is intentionally stated for an
arbitrary schedule function so projection, supplier, and verifier resources
share one proof rather than maintaining mode-specific variants. -/
theorem two_pow_linearScheduleAtLength_le
    (scheduledArity : ℕ → ℕ) (linearCoefficient inputLength : ℕ)
    (hlinear :
      ∀ sourceIndex,
        scheduledArity sourceIndex ≤
          linearCoefficient * (sourceIndex + 1)) :
    2 ^ scheduledArity (sourceIndexOfLength inputLength) ≤
      (2 * (inputLength + 1)) ^ linearCoefficient := by
  calc
    2 ^ scheduledArity (sourceIndexOfLength inputLength) ≤
        2 ^ (linearCoefficient *
          (sourceIndexOfLength inputLength + 1)) :=
      Nat.pow_le_pow_right (by omega) <|
        hlinear (sourceIndexOfLength inputLength)
    _ =
        (2 ^ (sourceIndexOfLength inputLength + 1)) ^
          linearCoefficient := by
      rw [← pow_mul]
      congr 1
      exact Nat.mul_comm _ _
    _ ≤ (2 * (inputLength + 1)) ^ linearCoefficient :=
      Nat.pow_le_pow_left (sourceScaleOfLength_le inputLength) _

/-- The dense supplier ABI may use exponential space in its compact arity,
but that space is polynomial in the public source length.  Charging the
description factor independently keeps this bridge valid for every normalized
circuit family and avoids pretending that a materialized matrix is streamed. -/
theorem supplierRegisterEnvelope_at_sourceLength_le
    (scheduledArity scheduledDescription : ℕ → ℕ)
    (runtimeCoefficient : ℝ)
    (runtimeDegree arityCoefficient descriptionCoefficient
      descriptionDegree sourceIndex : ℕ)
    (hcoefficient : 0 ≤ runtimeCoefficient)
    (harity :
      ∀ index,
        scheduledArity index ≤ arityCoefficient * (index + 1))
    (hdescription :
      ∀ index,
        scheduledArity index + scheduledDescription index + 1 ≤
          descriptionCoefficient *
            (sourceLength index + 1) ^ descriptionDegree) :
    supplierRegisterEnvelope runtimeCoefficient runtimeDegree
        (scheduledArity sourceIndex) (scheduledDescription sourceIndex) ≤
      (runtimeCoefficient *
          (descriptionCoefficient : ℝ) ^ runtimeDegree) *
        (sourceLength sourceIndex + 1 : ℕ) ^
          (arityCoefficient + descriptionDegree * runtimeDegree) := by
  have harityPower :
      2 ^ scheduledArity sourceIndex ≤
        (sourceLength sourceIndex + 1) ^ arityCoefficient := by
    calc
      2 ^ scheduledArity sourceIndex ≤
          2 ^ (arityCoefficient * (sourceIndex + 1)) :=
        Nat.pow_le_pow_right (by omega) (harity sourceIndex)
      _ = (sourceLength sourceIndex) ^ arityCoefficient := by
        unfold sourceLength
        rw [← pow_mul]
        congr 1
        exact Nat.mul_comm _ _
      _ ≤ (sourceLength sourceIndex + 1) ^ arityCoefficient :=
        Nat.pow_le_pow_left (by omega) _
  have harityPowerReal :
      (2 : ℝ) ^ scheduledArity sourceIndex ≤
        (sourceLength sourceIndex + 1 : ℕ) ^ arityCoefficient := by
    exact_mod_cast harityPower
  have hdescriptionReal :
      (scheduledArity sourceIndex +
          scheduledDescription sourceIndex + 1 : ℕ) ≤
        (descriptionCoefficient : ℝ) *
          (sourceLength sourceIndex + 1 : ℕ) ^ descriptionDegree := by
    exact_mod_cast hdescription sourceIndex
  unfold supplierRegisterEnvelope
  calc
    runtimeCoefficient * (2 : ℝ) ^ scheduledArity sourceIndex *
          (scheduledArity sourceIndex +
            scheduledDescription sourceIndex + 1 : ℕ) ^ runtimeDegree ≤
        runtimeCoefficient *
            (sourceLength sourceIndex + 1 : ℕ) ^ arityCoefficient *
          ((descriptionCoefficient : ℝ) *
            (sourceLength sourceIndex + 1 : ℕ) ^ descriptionDegree) ^
              runtimeDegree := by
      gcongr
    _ =
        (runtimeCoefficient *
            (descriptionCoefficient : ℝ) ^ runtimeDegree) *
          (sourceLength sourceIndex + 1 : ℕ) ^
            (arityCoefficient + descriptionDegree * runtimeDegree) := by
      rw [mul_pow, ← pow_mul, pow_add]
      ring

/-! ## Fixed public-length decoder -/

/-- Fixed, oracle-free decoder for the sole source enumeration.  The standard
machine input length in register one is the only source of schedule data;
register zero is deliberately overwritten before it is observed. -/
def sourceIndexProgram : NPOracleProgram :=
  [ .copy 1 2 1
  , .set 0 0 2
  , .branchZero 2 5 3
  , .shiftRight 2 1 2 4
  , .increment 0 2
  , .decrement 0 6
  , .decrement 0 7
  , .halt 0
  ]

@[simp] theorem sourceIndexProgram_oracleFree :
    OracleFree sourceIndexProgram := by
  rfl

/-- The decoder directly charges enough bits for its input-length counter;
it does not hide the register bound behind a pairing clock. -/
def sourceIndexProgramMaximumBits (inputLength : ℕ) : ℕ :=
  inputLength + 2

/-- Three loop instructions per public-length bit, plus fixed setup/exit. -/
def sourceIndexProgramFuel (inputLength : ℕ) : ℕ :=
  3 * natBitLength inputLength + 6

/-- One common linear envelope for both decoder resources.  Downstream
linkers may widen to this bound without introducing a second decoder clock. -/
theorem sourceIndexProgram_resources_le_linear (inputLength : ℕ) :
    max (sourceIndexProgramMaximumBits inputLength)
        (sourceIndexProgramFuel inputLength) ≤
      9 * (inputLength + 1) := by
  rw [max_le_iff]
  constructor
  · simp [sourceIndexProgramMaximumBits]
    omega
  · have hbits := natBitLength_le_succ inputLength
    simp only [sourceIndexProgramFuel]
    omega

private def sourceIndexLoopState
    (inputLength value count : ℕ) : NPOracleState where
  pc := 2
  registers := fun register =>
    if register = 0 then count
    else if register = 1 then inputLength
    else if register = 2 then value
    else 0

private theorem sourceIndexState_ext
    (left right : NPOracleState)
    (hpc : left.pc = right.pc)
    (hregisters : ∀ register, left.registers register =
      right.registers register) :
    left = right := by
  cases left with
  | mk leftPc leftRegisters =>
      cases right with
      | mk rightPc rightRegisters =>
          cases hpc
          congr
          funext register
          exact hregisters register

private def sourceIndexShiftCount (value : ℕ) : ℕ :=
  if value = 0 then 0 else natBitLength value

private theorem sourceIndexShiftCount_shiftRight_succ
    {value : ℕ} (hpositive : 0 < value) :
    sourceIndexShiftCount (value >>> 1) + 1 =
      sourceIndexShiftCount value := by
  rw [Nat.shiftRight_eq_div_pow]
  simp only [pow_one]
  by_cases hone : value = 1
  · subst value
    simp [sourceIndexShiftCount, natBitLength]
  · have htwo : 2 ≤ value := by omega
    have hdivPositive : value / 2 ≠ 0 := by omega
    simp only [sourceIndexShiftCount, if_neg hpositive.ne',
      if_neg hdivPositive, natBitLength]
    rw [Nat.log_div_base]
    have hlogPositive : 0 < Nat.log 2 value :=
      Nat.log_pos (by omega) htwo
    omega

private theorem run_sourceIndexProgram_loop
    (inputLength value count : ℕ)
    (hvalue : value ≤ inputLength)
    (hbound :
      count + sourceIndexShiftCount value ≤ inputLength + 1) :
    runNPOracleProgram sourceIndexProgram (inputLength + 2)
        (3 * sourceIndexShiftCount value + 4)
        (sourceIndexLoopState inputLength value count) =
      some (count + sourceIndexShiftCount value - 2) := by
  induction value using Nat.strong_induction_on generalizing count with
  | h value ih =>
      by_cases hzero : value = 0
      · subst value
        have hcountBits : natBitLength count ≤ inputLength + 2 := by
          exact (natBitLength_le_succ count).trans (by
            simp [sourceIndexShiftCount] at hbound
            omega)
        have hpredBits :
            natBitLength count.pred ≤ inputLength + 2 :=
          (decrement_bits_le count).trans hcountBits
        have hpredPredBits :
            natBitLength count.pred.pred ≤ inputLength + 2 :=
          (decrement_bits_le count.pred).trans hpredBits
        let state0 := sourceIndexLoopState inputLength 0 count
        rw [show 3 * sourceIndexShiftCount 0 + 4 = 3 + 1 by
          simp [sourceIndexShiftCount]]
        rw [run_branchZero_instruction
          (program := sourceIndexProgram) (pc := 2) (register := 2)
          (zeroTarget := 5) (nonzeroTarget := 3) (by rfl) (by rfl)]
        change
          runNPOracleProgram sourceIndexProgram (inputLength + 2) 3
              (state0.jump 5) =
            some (count + sourceIndexShiftCount 0 - 2)
        rw [show 3 = 2 + 1 by omega]
        rw [run_decrement_instruction
          (program := sourceIndexProgram) (pc := 5) (register := 0)
          (next := 6) (value := count.pred) (by rfl) (by rfl)
          (by simp [state0, sourceIndexLoopState, NPOracleState.jump])
          hpredBits]
        rw [show 2 = 1 + 1 by omega]
        rw [run_decrement_instruction
          (program := sourceIndexProgram) (pc := 6) (register := 0)
          (next := 7) (value := count.pred.pred) (by rfl) (by rfl)
          (by simp [state0, sourceIndexLoopState, NPOracleState.write,
            NPOracleState.jump])
          hpredPredBits]
        apply run_halt_instruction
          (program := sourceIndexProgram) (pc := 7) (outputRegister := 0)
          (value := count.pred.pred) (by rfl) (by rfl)
        · simp [state0, sourceIndexLoopState, NPOracleState.write,
            NPOracleState.jump, Nat.pred_eq_sub_one]
        · simpa [Nat.pred_eq_sub_one] using hpredPredBits
      · have hpositive : 0 < value := Nat.pos_of_ne_zero hzero
        have hshiftCount :
            sourceIndexShiftCount (value >>> 1) + 1 =
              sourceIndexShiftCount value :=
          sourceIndexShiftCount_shiftRight_succ hpositive
        have hshiftLt : value >>> 1 < value := by
          rw [Nat.shiftRight_eq_div_pow]
          simp only [pow_one]
          exact Nat.div_lt_self hpositive (by omega)
        have hshiftLe : value >>> 1 ≤ inputLength :=
          (Nat.shiftRight_le value 1).trans hvalue
        have hshiftBits :
            natBitLength (value >>> 1) ≤ inputLength + 2 := by
          exact (natBitLength_le_succ _).trans (by omega)
        have hcountBits :
            natBitLength (count + 1) ≤ inputLength + 2 := by
          exact (natBitLength_le_succ (count + 1)).trans (by
            have hshiftNonnegative :
                0 ≤ sourceIndexShiftCount (value >>> 1) :=
              Nat.zero_le _
            omega)
        let state0 := sourceIndexLoopState inputLength value count
        let shifted :=
          ((state0.jump 3).write 2 (value >>> 1)).jump 4
        let incremented := (shifted.write 0 (count + 1)).jump 2
        have hincremented :
            incremented =
              sourceIndexLoopState inputLength
                (value >>> 1) (count + 1) := by
          apply sourceIndexState_ext
          · rfl
          · intro register
            simp only [incremented, shifted, state0, sourceIndexLoopState,
              NPOracleState.write, NPOracleState.jump]
            by_cases hregisterZero : register = 0
            · subst register
              simp
            · by_cases hregisterOne : register = 1
              · subst register
                simp
              · by_cases hregisterTwo : register = 2
                · subst register
                  simp
                · simp_all
        rw [show
          3 * sourceIndexShiftCount value + 4 =
            (3 * sourceIndexShiftCount (value >>> 1) + 4 + 2) + 1 by
          omega]
        rw [run_branchZero_instruction
          (program := sourceIndexProgram) (pc := 2) (register := 2)
          (zeroTarget := 5) (nonzeroTarget := 3) (by rfl) (by rfl)]
        rw [if_neg (by simp [sourceIndexLoopState, hzero])]
        change
          runNPOracleProgram sourceIndexProgram (inputLength + 2)
              (3 * sourceIndexShiftCount (value >>> 1) + 4 + 2)
              (state0.jump 3) =
            some (count + sourceIndexShiftCount value - 2)
        rw [show
          3 * sourceIndexShiftCount (value >>> 1) + 4 + 2 =
            (3 * sourceIndexShiftCount (value >>> 1) + 4 + 1) + 1 by
          omega]
        rw [run_shiftRight_instruction
          (program := sourceIndexProgram) (pc := 3) (source := 2)
          (amount := 1) (destination := 2) (next := 4)
          (value := value >>> 1) (by rfl) (by rfl)
          (by simp [state0, sourceIndexLoopState]) hshiftBits]
        change
          runNPOracleProgram sourceIndexProgram (inputLength + 2)
              (3 * sourceIndexShiftCount (value >>> 1) + 4 + 1) shifted =
            some (count + sourceIndexShiftCount value - 2)
        rw [show
          3 * sourceIndexShiftCount (value >>> 1) + 4 + 1 =
            (3 * sourceIndexShiftCount (value >>> 1) + 4) + 1 by omega]
        rw [run_increment_instruction
          (program := sourceIndexProgram) (pc := 4) (register := 0)
          (next := 2) (value := count + 1) (by rfl) (by rfl)
          (by simp [shifted, state0, sourceIndexLoopState,
            NPOracleState.write, NPOracleState.jump])
          hcountBits]
        change
          runNPOracleProgram sourceIndexProgram (inputLength + 2)
              (3 * sourceIndexShiftCount (value >>> 1) + 4) incremented =
            some (count + sourceIndexShiftCount value - 2)
        rw [hincremented]
        have hrun :=
          ih (value >>> 1) hshiftLt (count + 1) hshiftLe (by omega)
        rw [hrun]
        congr 2
        omega

/-- Exact interpreter refinement at every public length, including
non-scheduled lengths used by the machine's global one-sidedness theorem. -/
theorem run_sourceIndexProgram_atLength (inputLength inputCode : ℕ) :
    runNPOracleProgram sourceIndexProgram
        (sourceIndexProgramMaximumBits inputLength)
        (sourceIndexProgramFuel inputLength)
        (initialNPOracleState inputLength inputCode) =
      some (sourceIndexOfLength inputLength) := by
  let initial := initialNPOracleState inputLength inputCode
  let copied := (initial.write 2 inputLength).jump 1
  let cleared := (copied.write 0 0).jump 2
  have hlengthBits :
      natBitLength inputLength ≤
        sourceIndexProgramMaximumBits inputLength := by
    exact (natBitLength_le_succ _).trans (by
      simp only [sourceIndexProgramMaximumBits]
      omega)
  have hzeroBits :
      natBitLength 0 ≤ sourceIndexProgramMaximumBits inputLength := by
    simp [natBitLength, sourceIndexProgramMaximumBits]
  have hcleared :
      cleared = sourceIndexLoopState inputLength inputLength 0 := by
    apply sourceIndexState_ext
    · rfl
    · intro register
      simp only [cleared, copied, initial, sourceIndexLoopState,
        initialNPOracleState, NPOracleState.write, NPOracleState.jump]
      split
      · simp
      · split
        · simp
        · split <;> simp_all
  have hshiftBound :
      sourceIndexShiftCount inputLength ≤ inputLength + 1 := by
    unfold sourceIndexShiftCount
    split
    · omega
    · exact (natBitLength_le_succ inputLength).trans (by omega)
  have hloopBase :
      runNPOracleProgram sourceIndexProgram (inputLength + 2)
          (3 * sourceIndexShiftCount inputLength + 4)
          (sourceIndexLoopState inputLength inputLength 0) =
        some (sourceIndexShiftCount inputLength - 2) := by
    simpa using
      run_sourceIndexProgram_loop
        inputLength inputLength 0 le_rfl (by omega)
  have hloop :
      runNPOracleProgram sourceIndexProgram (inputLength + 2)
          (3 * natBitLength inputLength + 4)
          (sourceIndexLoopState inputLength inputLength 0) =
        some (sourceIndexOfLength inputLength) := by
    by_cases hzero : inputLength = 0
    · subst inputLength
      have hrun :=
        NearCubicWires.VerifiedLinker.run_fuel_add hloopBase 3
      simpa [sourceIndexShiftCount, natBitLength, sourceIndexOfLength] using
        hrun
    · simpa [sourceIndexShiftCount, hzero, natBitLength,
        sourceIndexOfLength] using hloopBase
  rw [show sourceIndexProgramFuel inputLength =
      (3 * natBitLength inputLength + 4 + 1) + 1 by
    simp [sourceIndexProgramFuel]]
  rw [run_copy_instruction
    (program := sourceIndexProgram) (pc := 0) (source := 1)
    (destination := 2) (next := 1) (value := inputLength)
    (by rfl) (by rfl)
    (by simp [initialNPOracleState]) hlengthBits]
  change
    runNPOracleProgram sourceIndexProgram
        (sourceIndexProgramMaximumBits inputLength)
        (3 * natBitLength inputLength + 4 + 1) copied =
      some (sourceIndexOfLength inputLength)
  rw [show 3 * natBitLength inputLength + 4 + 1 =
      (3 * natBitLength inputLength + 4) + 1 by omega]
  rw [run_set_instruction
    (program := sourceIndexProgram) (pc := 1) (register := 0)
    (value := 0) (next := 2) (by rfl) (by rfl) hzeroBits]
  change
    runNPOracleProgram sourceIndexProgram
        (sourceIndexProgramMaximumBits inputLength)
        (3 * natBitLength inputLength + 4) cleared =
      some (sourceIndexOfLength inputLength)
  rw [hcleared]
  simpa [sourceIndexProgramMaximumBits] using hloop

/-- Scheduled specialization of `run_sourceIndexProgram_atLength`.  The
arbitrary register-zero payload confirms that no schedule index is serialized
in the private input. -/
theorem run_sourceIndexProgram (sourceIndex inputCode : ℕ) :
    runNPOracleProgram sourceIndexProgram
        (sourceIndexProgramMaximumBits (sourceLength sourceIndex))
        (sourceIndexProgramFuel (sourceLength sourceIndex))
        (initialNPOracleState (sourceLength sourceIndex) inputCode) =
      some sourceIndex := by
  simpa using
    run_sourceIndexProgram_atLength (sourceLength sourceIndex) inputCode

theorem sourceIndex_le_sourceLength (sourceIndex : ℕ) :
    sourceIndex ≤ sourceLength sourceIndex := by
  unfold sourceLength
  exact (Nat.le_succ sourceIndex).trans <|
    Nat.le_of_lt (sourceIndex + 1).lt_two_pow_self

theorem sourceLength_monotone : Monotone sourceLength := by
  intro left right hle
  unfold sourceLength
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- The unique q-bit outer/PCPP width at source index `s`. -/
def scheduledWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ) : ℕ :=
  widthEnvelope outer (sourceLength sourceIndex)

/-- A requested polynomial degree is realized by one pairing-clock depth.
`coefficientExponent` is reused so this is the same power-of-two domination
ledger used by the exponential interpreter bounds. -/
def oracleDepth (requiredDegree : ℕ) : ℕ :=
  coefficientExponent requiredDegree

/-- The only small-oracle size cap used by the outer Case-1/Case-2 split. -/
def oracleSizeBound (requiredDegree width : ℕ) : ℕ :=
  pairClock (oracleDepth requiredDegree) width

theorem requiredDegree_le_oracleDegree (requiredDegree : ℕ) :
    requiredDegree ≤ 2 ^ oracleDepth requiredDegree := by
  exact coefficient_le_two_pow requiredDegree

theorem oracleSizeBound_monotone (requiredDegree : ℕ) :
    Monotone (oracleSizeBound requiredDegree) := by
  intro left right hle
  simpa [oracleSizeBound, pairClock] using
    pairIter_mono_value (oracleDepth requiredDegree) hle

theorem oracleSizeBound_polynomiallyBounded (requiredDegree : ℕ) :
    PolynomiallyBounded (oracleSizeBound requiredDegree) := by
  change PolynomiallyBounded (pairClock (oracleDepth requiredDegree))
  exact pairClock_polynomiallyBounded (oracleDepth requiredDegree)

def oracleSizeBoundConstructible (requiredDegree : ℕ) :
    TimeConstructible (oracleSizeBound requiredDegree) := by
  change TimeConstructible (pairClock (oracleDepth requiredDegree))
  exact pairClockTimeConstructible (oracleDepth requiredDegree)

theorem scheduledWidth_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolynomiallyBounded (scheduledWidth outer) := by
  refine
    ⟨widthLinearCoefficient outer 1, 1,
      widthLinearCoefficient_positive outer 1, ?_⟩
  intro sourceIndex
  simpa [scheduledWidth, sourceLength] using
    widthEnvelope_exponential_le_linear outer 1 sourceIndex

theorem scheduledWidth_monotone
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    Monotone (scheduledWidth outer) := by
  intro left right hle
  apply pairClock_widthEnvelope_mono outer
  unfold sourceLength
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- Source-specialized substitution-size cap.  This is definitionally the
generic PCPP envelope evaluated on the sole source enumeration and oracle cap.
-/
def scheduledSubstitutedSize
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (requiredDegree sourceIndex : ℕ) : ℕ :=
  outer.substitution.sizeCoefficient *
      (scheduledWidth outer sourceIndex +
        oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex) + 1) ^
        outer.substitutionExponent +
    scheduledWidth outer sourceIndex

theorem scheduledSubstitutedSize_eq_envelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (requiredDegree sourceIndex : ℕ) :
    scheduledSubstitutedSize outer requiredDegree sourceIndex =
      substitutedCircuitSizeEnvelope outer
        (oracleSizeBound requiredDegree) (sourceLength sourceIndex) := by
  rfl

theorem scheduledSubstitutedSize_monotone
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (requiredDegree : ℕ) :
    Monotone (scheduledSubstitutedSize outer requiredDegree) := by
  intro left right hle
  unfold scheduledSubstitutedSize
  have hwidth := scheduledWidth_monotone outer hle
  have horacle :=
    oracleSizeBound_monotone requiredDegree hwidth
  gcongr

theorem scheduledOracleSize_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (requiredDegree : ℕ) :
    PolynomiallyBounded
      (fun sourceIndex =>
        oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex)) := by
  exact polynomiallyBounded_comp
    (oracleSizeBound_polynomiallyBounded requiredDegree)
    (scheduledWidth_polynomiallyBounded outer)

theorem scheduledSubstitutedSize_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (requiredDegree : ℕ) :
    PolynomiallyBounded
      (scheduledSubstitutedSize outer requiredDegree) := by
  have hwidth := scheduledWidth_polynomiallyBounded outer
  have horacle :=
    scheduledOracleSize_polynomiallyBounded outer requiredDegree
  have hone := polynomiallyBounded_constant 1
  have hsum :=
    polynomiallyBounded_add
      (polynomiallyBounded_add hwidth horacle) hone
  have hpower :=
    polynomiallyBounded_pow hsum outer.substitutionExponent
  have hscaled :=
    polynomiallyBounded_mul
      (polynomiallyBounded_constant outer.substitution.sizeCoefficient)
      hpower
  change PolynomiallyBounded (fun sourceIndex =>
    outer.substitution.sizeCoefficient *
        (scheduledWidth outer sourceIndex +
          oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex) + 1) ^
          outer.substitutionExponent +
      scheduledWidth outer sourceIndex)
  exact polynomiallyBounded_add hscaled hwidth

/-- The exact source-only clause-address width used for both modes. -/
def scheduledClauseBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceIndex : ℕ) : ℕ :=
  Nat.log 2 <|
    pcppSource.coefficient *
      (scheduledSubstitutedSize outer requiredDegree sourceIndex + 1) ^
        pcppSource.degree

def scheduledClauseCount
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceIndex : ℕ) : ℕ :=
  pcppSource.coefficient *
    (scheduledSubstitutedSize outer requiredDegree sourceIndex + 1) ^
      pcppSource.degree

theorem scheduledClauseBits_eq_envelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceIndex : ℕ) :
    scheduledClauseBits outer pcppSource requiredDegree sourceIndex =
      clauseBitsEnvelope outer pcppSource
        (oracleSizeBound requiredDegree) (sourceLength sourceIndex) := by
  rw [scheduledClauseBits, clauseBitsEnvelope,
    ← scheduledSubstitutedSize_eq_envelope]

theorem scheduledClauseBits_monotone
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) :
    Monotone (scheduledClauseBits outer pcppSource requiredDegree) := by
  intro left right hle
  unfold scheduledClauseBits
  apply Nat.log_mono_right
  gcongr
  exact scheduledSubstitutedSize_monotone outer requiredDegree hle

theorem scheduledClauseCount_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) :
    PolynomiallyBounded
      (scheduledClauseCount outer pcppSource requiredDegree) := by
  have hsub :=
    scheduledSubstitutedSize_polynomiallyBounded outer requiredDegree
  have hsubOne :=
    polynomiallyBounded_add hsub (polynomiallyBounded_constant 1)
  unfold scheduledClauseCount
  exact polynomiallyBounded_mul
    (polynomiallyBounded_constant pcppSource.coefficient)
    (polynomiallyBounded_pow hsubOne pcppSource.degree)

noncomputable def scheduledClauseCountEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) :
    PolynomialEnvelope
      (scheduledClauseCount outer pcppSource requiredDegree) :=
  Classical.choice <|
    polynomiallyBounded_iff_nonemptyEnvelope.mp <|
      scheduledClauseCount_polynomiallyBounded
        outer pcppSource requiredDegree

private theorem log_of_polynomialEnvelope_le_linear
    {function : ℕ → ℕ} (envelope : PolynomialEnvelope function)
    (index : ℕ) :
    Nat.log 2 (function index) ≤
      (coefficientExponent envelope.coefficient + envelope.degree) *
        (index + 1) := by
  let coefficientBits := coefficientExponent envelope.coefficient
  have hcoefficient :
      envelope.coefficient ≤ 2 ^ coefficientBits := by
    simpa [coefficientBits] using
      coefficient_le_two_pow envelope.coefficient
  have hindex :
      index + 1 ≤ 2 ^ (index + 1) :=
    Nat.le_of_lt Nat.lt_two_pow_self
  have hpower :
      function index ≤
        2 ^ (coefficientBits + (index + 1) * envelope.degree) := by
    calc
      function index ≤
          envelope.coefficient * (index + 1) ^ envelope.degree :=
        envelope.bound index
      _ ≤
          2 ^ coefficientBits * (2 ^ (index + 1)) ^ envelope.degree := by
        gcongr
      _ =
          2 ^ (coefficientBits + (index + 1) * envelope.degree) := by
        simp only [← pow_add, ← pow_mul]
  have hlog :
      Nat.log 2 (function index) ≤
        coefficientBits + (index + 1) * envelope.degree :=
    (Nat.log_le_clog 2 _).trans
      (Nat.clog_le_of_le_pow hpower)
  apply hlog.trans
  have hcoefficientBits :
      coefficientBits ≤ coefficientBits * (index + 1) := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left coefficientBits (by omega : 1 ≤ index + 1)
  calc
    coefficientBits + (index + 1) * envelope.degree ≤
        coefficientBits * (index + 1) +
          (index + 1) * envelope.degree := by gcongr
    _ =
        (coefficientExponent envelope.coefficient + envelope.degree) *
          (index + 1) := by
      simp only [coefficientBits]
      ring

noncomputable def scheduledClauseBitLinearCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) : ℕ :=
  coefficientExponent
      (scheduledClauseCountEnvelope
        outer pcppSource requiredDegree).coefficient +
    (scheduledClauseCountEnvelope
      outer pcppSource requiredDegree).degree

theorem scheduledClauseBits_le_linear
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceIndex : ℕ) :
    scheduledClauseBits outer pcppSource requiredDegree sourceIndex ≤
      scheduledClauseBitLinearCoefficient
          outer pcppSource requiredDegree *
        (sourceIndex + 1) := by
  change
    Nat.log 2
        (scheduledClauseCount
          outer pcppSource requiredDegree sourceIndex) ≤ _
  exact log_of_polynomialEnvelope_le_linear
    (scheduledClauseCountEnvelope outer pcppSource requiredDegree)
    sourceIndex

theorem scheduledClauseBits_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) :
    PolynomiallyBounded
      (scheduledClauseBits outer pcppSource requiredDegree) := by
  refine
    ⟨scheduledClauseBitLinearCoefficient
        outer pcppSource requiredDegree,
      1, ?_, ?_⟩
  · unfold scheduledClauseBitLinearCoefficient coefficientExponent
    omega
  · intro sourceIndex
    simpa only [pow_one] using
      scheduledClauseBits_le_linear
        outer pcppSource requiredDegree sourceIndex

/-- Arity of the exact q-bit, clause-padded honest occurrence table. -/
def seedArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceIndex : ℕ) : ℕ :=
  scheduledWidth outer sourceIndex +
    scheduledClauseBits outer pcppSource requiredDegree sourceIndex + 1

theorem seedArity_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) :
    PolynomiallyBounded
      (seedArity outer pcppSource requiredDegree) := by
  exact polynomiallyBounded_add
    (polynomiallyBounded_add
      (scheduledWidth_polynomiallyBounded outer)
      (scheduledClauseBits_polynomiallyBounded
        outer pcppSource requiredDegree))
    (polynomiallyBounded_constant 1)

noncomputable def seedArityLinearCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) : ℕ :=
  widthLinearCoefficient outer 1 +
    scheduledClauseBitLinearCoefficient
      outer pcppSource requiredDegree +
    1

theorem seedArityLinearCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) :
    0 < seedArityLinearCoefficient
      outer pcppSource requiredDegree := by
  unfold seedArityLinearCoefficient
  omega

theorem seedArity_le_linear
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceIndex : ℕ) :
    seedArity outer pcppSource requiredDegree sourceIndex ≤
      seedArityLinearCoefficient outer pcppSource requiredDegree *
        (sourceIndex + 1) := by
  have hwidth :
      scheduledWidth outer sourceIndex ≤
        widthLinearCoefficient outer 1 * (sourceIndex + 1) := by
    simpa [scheduledWidth, sourceLength] using
      widthEnvelope_exponential_le_linear outer 1 sourceIndex
  have hclause :=
    scheduledClauseBits_le_linear
      outer pcppSource requiredDegree sourceIndex
  have hone : 1 ≤ 1 * (sourceIndex + 1) := by simp
  calc
    seedArity outer pcppSource requiredDegree sourceIndex =
        scheduledWidth outer sourceIndex +
          scheduledClauseBits outer pcppSource requiredDegree sourceIndex +
          1 := rfl
    _ ≤
        widthLinearCoefficient outer 1 * (sourceIndex + 1) +
          scheduledClauseBitLinearCoefficient
              outer pcppSource requiredDegree *
            (sourceIndex + 1) +
          1 * (sourceIndex + 1) := by
      gcongr
    _ =
        seedArityLinearCoefficient outer pcppSource requiredDegree *
          (sourceIndex + 1) := by
      unfold seedArityLinearCoefficient
      ring

theorem seedArity_monotone
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) :
    Monotone (seedArity outer pcppSource requiredDegree) := by
  intro left right hle
  unfold seedArity
  exact Nat.add_le_add
    (Nat.add_le_add
      (scheduledWidth_monotone outer hle)
      (scheduledClauseBits_monotone
        outer pcppSource requiredDegree hle))
    (le_refl 1)

theorem sourceIndex_succ_le_scheduledWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ) :
    sourceIndex + 1 ≤ scheduledWidth outer sourceIndex := by
  simpa [scheduledWidth, sourceLength] using
    (sourceExponent_le_widthEnvelope outer :
      sourceIndex + 1 ≤
        widthEnvelope outer (2 ^ (sourceIndex + 1)))

theorem scheduledWidth_le_seedArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceIndex : ℕ) :
    scheduledWidth outer sourceIndex ≤
      seedArity outer pcppSource requiredDegree sourceIndex := by
  unfold seedArity
  omega

theorem sourceIndex_succ_le_seedArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceIndex : ℕ) :
    sourceIndex + 1 ≤
      seedArity outer pcppSource requiredDegree sourceIndex :=
  (sourceIndex_succ_le_scheduledWidth outer sourceIndex).trans
    (scheduledWidth_le_seedArity
      outer pcppSource requiredDegree sourceIndex)

def scheduledLogWidthCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) : ℕ :=
  coefficientExponent (widthLinearCoefficient outer 1 + 2) + 1

theorem scheduledLogWidthCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    0 < scheduledLogWidthCoefficient outer := by
  unfold scheduledLogWidthCoefficient
  omega

theorem scheduledLogWidth_le_sourceLog
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ) :
    logScale (scheduledWidth outer sourceIndex) ≤
      scheduledLogWidthCoefficient outer *
        logScale (sourceIndex + 1) := by
  let widthCoefficient := widthLinearCoefficient outer 1
  let coefficientBits := coefficientExponent (widthCoefficient + 2)
  let sourceLog := logScale (sourceIndex + 1)
  have hwidth :
      scheduledWidth outer sourceIndex ≤
        widthCoefficient * (sourceIndex + 1) := by
    simpa [scheduledWidth, sourceLength, widthCoefficient] using
      widthEnvelope_exponential_le_linear outer 1 sourceIndex
  have hwidthPlus :
      scheduledWidth outer sourceIndex + 2 ≤
        (widthCoefficient + 2) * (sourceIndex + 1) := by
    calc
      scheduledWidth outer sourceIndex + 2 ≤
          widthCoefficient * (sourceIndex + 1) + 2 := by omega
      _ ≤ widthCoefficient * (sourceIndex + 1) +
          2 * (sourceIndex + 1) := by
        gcongr
        omega
      _ = (widthCoefficient + 2) * (sourceIndex + 1) := by ring
  have hcoefficient :
      widthCoefficient + 2 ≤ 2 ^ coefficientBits := by
    simpa [coefficientBits] using
      coefficient_le_two_pow (widthCoefficient + 2)
  have hsource :
      sourceIndex + 1 ≤ 2 ^ sourceLog := by
    exact (Nat.le_add_right (sourceIndex + 1) 2).trans <|
      Nat.le_pow_clog (by omega) (sourceIndex + 1 + 2)
  have hpower :
      scheduledWidth outer sourceIndex + 2 ≤
        2 ^ (coefficientBits + sourceLog) := by
    calc
      scheduledWidth outer sourceIndex + 2 ≤
          (widthCoefficient + 2) * (sourceIndex + 1) := hwidthPlus
      _ ≤ 2 ^ coefficientBits * 2 ^ sourceLog := by gcongr
      _ = 2 ^ (coefficientBits + sourceLog) := by rw [pow_add]
  have hclog :
      logScale (scheduledWidth outer sourceIndex) ≤
        coefficientBits + sourceLog := by
    unfold logScale
    exact Nat.clog_le_of_le_pow hpower
  have hsourceLog : 1 ≤ sourceLog := by
    have := logScale_positive (sourceIndex + 1)
    simp only [sourceLog]
    omega
  calc
    logScale (scheduledWidth outer sourceIndex) ≤
        coefficientBits + sourceLog := hclog
    _ ≤ coefficientBits * sourceLog + sourceLog := by
      gcongr
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left coefficientBits hsourceLog
    _ = scheduledLogWidthCoefficient outer *
        logScale (sourceIndex + 1) := by
      unfold scheduledLogWidthCoefficient
      simp only [coefficientBits, sourceLog]
      ring

/-! ### The same schedule at an arbitrary approximation radius

Every conclusion of the fixed-radius schedule above is reproduced here at an
arbitrary rational radius `delta`, under the two side conditions the imported
XOR contract already demands (`0 < delta` and `delta ≤ 1 / 2`).  The radius is
carried as a rational so that the copy counts stay computable; the schedule the
repaired seam selects is the instantiation at the validity constant of the
selected parameter package.  See the repair record above. -/

/-- Block length that halves the geometric factor at approximation radius
`delta`.  Since `Rat` is kept in lowest terms, `delta.den * delta = delta.num`
is at least one, so the denominator is always at least `1 / delta`: the block
grows like `1 / delta`, which is the whole quantitative price of the repair.
Reading the block off the denominator rather than through `Nat.ceil` keeps it
kernel-cheap, which the downstream witness-limit `rfl`s require. -/
def recoveryBlockOf (delta : ℚ) : ℕ := delta.den

theorem recoveryBlockOf_positive (delta : ℚ) :
    0 < recoveryBlockOf delta :=
  delta.den_pos

private theorem one_le_recoveryBlockOf_mul {delta : ℚ} (hpositive : 0 < delta) :
    (1 : ℝ) ≤ (recoveryBlockOf delta : ℝ) * (delta : ℝ) := by
  have hnumerator : 1 ≤ delta.num := Rat.num_pos.mpr hpositive
  have hproduct : ((delta.den : ℚ)) * delta = (delta.num : ℚ) := by
    rw [mul_comm]
    exact_mod_cast Rat.mul_den_eq_num delta
  have hrational : (1 : ℚ) ≤ (recoveryBlockOf delta : ℚ) * delta := by
    unfold recoveryBlockOf
    rw [hproduct]
    exact_mod_cast hnumerator
  exact_mod_cast hrational

/-- Elementary halving bound.  `(1 - delta) ^ block ≤ 1 / (1 + block * delta)`
follows from `(1 - delta) (1 + delta) ≤ 1` and Bernoulli, so one block of
`1 / delta` repetitions already halves the geometric factor.  No exponential or
logarithm is needed, which keeps the block length a computable natural. -/
private theorem pow_le_half_of_one_le_mul {delta : ℝ} (block : ℕ)
    (hpositive : 0 < delta) (hhalf : delta ≤ 1 / 2)
    (hmul : (1 : ℝ) ≤ (block : ℝ) * delta) :
    (1 - delta) ^ block ≤ (1 / 2 : ℝ) := by
  have hbase : (0 : ℝ) ≤ 1 - delta := by linarith
  have hpowNonneg : (0 : ℝ) ≤ (1 - delta) ^ block := pow_nonneg hbase block
  have hbernoulli : (1 : ℝ) + (block : ℝ) * delta ≤ (1 + delta) ^ block :=
    one_add_mul_le_pow (by linarith) block
  have hsquare : ((1 - delta) * (1 + delta)) ^ block ≤ (1 : ℝ) :=
    pow_le_one₀ (by nlinarith) (by nlinarith)
  have hchain : (1 - delta) ^ block * (1 + (block : ℝ) * delta) ≤ 1 := by
    calc
      (1 - delta) ^ block * (1 + (block : ℝ) * delta) ≤
          (1 - delta) ^ block * (1 + delta) ^ block :=
        mul_le_mul_of_nonneg_left hbernoulli hpowNonneg
      _ = ((1 - delta) * (1 + delta)) ^ block := (mul_pow _ _ block).symm
      _ ≤ 1 := hsquare
  nlinarith [hchain, mul_nonneg hpowNonneg (sub_nonneg.mpr hmul)]

/-- One block halves the geometric factor at every admissible radius.  This is
the general form of `recoveryBlock_halves`. -/
theorem recoveryBlockOf_halves {delta : ℚ} (hpositive : 0 < delta)
    (hhalf : (delta : ℝ) ≤ 1 / 2) :
    (1 - (delta : ℝ)) ^ recoveryBlockOf delta ≤ (1 / 2 : ℝ) :=
  pow_le_half_of_one_le_mul _ (by exact_mod_cast hpositive) hhalf
    (one_le_recoveryBlockOf_mul hpositive)

/-- General form of `xorEpsilon_recoveryBlocks_le`.  The extra block is what
replaces the `1 / 2 - recoveryDelta = 1 / 4` arithmetic: at a small radius the
trailing factor is only bounded by `1 / 2`, so the factor-four reserve is paid
by one further halving instead. -/
private theorem xorEpsilon_blocks_le {delta : ℝ} {block : ℕ}
    (hnonneg : 0 ≤ delta) (hhalf : delta ≤ 1 / 2)
    (hblock : (1 - delta) ^ block ≤ (1 / 2 : ℝ)) (repetitions : ℕ) :
    xorEpsilon delta (block * repetitions + block + 1) ≤
      1 / (2 : ℝ) ^ repetitions / 4 := by
  unfold xorEpsilon
  have hexponent :
      block * repetitions + block + 1 - 1 = block * (repetitions + 1) := by
    simp [Nat.mul_succ]
  rw [hexponent, pow_mul]
  have hbase : (0 : ℝ) ≤ (1 - delta) ^ block :=
    pow_nonneg (by linarith) block
  have hpower :
      ((1 - delta) ^ block) ^ (repetitions + 1) ≤
        (1 / 2 : ℝ) ^ (repetitions + 1) :=
    pow_le_pow_left₀ hbase hblock (repetitions + 1)
  calc
    ((1 - delta) ^ block) ^ (repetitions + 1) * (1 / 2 - delta) ≤
        (1 / 2 : ℝ) ^ (repetitions + 1) * (1 / 2) :=
      mul_le_mul hpower (by linarith) (by linarith) (by positivity)
    _ = 1 / (2 : ℝ) ^ repetitions / 4 := by
      rw [pow_succ, one_div_pow]
      ring

/-- Copy count for inverse-polynomial advantage at approximation radius
`delta`.  General form of `inverseCopies`. -/
def inverseCopiesOf (delta : ℚ)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (rate sourceIndex : ℕ) : ℕ :=
  recoveryBlockOf delta *
      (rate * logScale (scheduledWidth outer sourceIndex)) +
    recoveryBlockOf delta + 1

/-- Copy count for a fixed advantage at approximation radius `delta`.  General
form of `fixedCopies`. -/
def fixedCopiesOf (delta : ℚ) (rate : ℕ) : ℕ :=
  recoveryBlockOf delta * rate + recoveryBlockOf delta + 1

theorem inverseCopiesOf_positive (delta : ℚ)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (rate sourceIndex : ℕ) :
    1 ≤ inverseCopiesOf delta outer rate sourceIndex := by
  unfold inverseCopiesOf
  omega

theorem fixedCopiesOf_positive (delta : ℚ) (rate : ℕ) :
    1 ≤ fixedCopiesOf delta rate := by
  unfold fixedCopiesOf
  omega

theorem inverseCopiesOf_monotone (delta : ℚ)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (rate : ℕ) :
    Monotone (inverseCopiesOf delta outer rate) := by
  intro left right hle
  unfold inverseCopiesOf
  gcongr
  exact logScale_mono (scheduledWidth_monotone outer hle)

/-- The logarithmic copy schedule keeps the explicit factor-four reserve at
every admissible radius.  General form of `xorEpsilon_inverseCopies_le`. -/
theorem xorEpsilon_inverseCopiesOf_le {delta : ℚ} (hpositive : 0 < delta)
    (hhalf : (delta : ℝ) ≤ 1 / 2)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (rate sourceIndex : ℕ) :
    xorEpsilon (delta : ℝ) (inverseCopiesOf delta outer rate sourceIndex) ≤
      1 / (2 : ℝ) ^
        (rate * logScale (scheduledWidth outer sourceIndex)) / 4 := by
  unfold inverseCopiesOf
  exact xorEpsilon_blocks_le
    (by exact_mod_cast le_of_lt hpositive) hhalf
    (recoveryBlockOf_halves hpositive hhalf)
    (rate * logScale (scheduledWidth outer sourceIndex))

/-- The constant-copy schedule keeps the explicit factor-four reserve at every
admissible radius.  General form of `xorEpsilon_fixedCopies_le`. -/
theorem xorEpsilon_fixedCopiesOf_le {delta : ℚ} (hpositive : 0 < delta)
    (hhalf : (delta : ℝ) ≤ 1 / 2) (rate : ℕ) :
    xorEpsilon (delta : ℝ) (fixedCopiesOf delta rate) ≤
      1 / (2 : ℝ) ^ rate / 4 := by
  unfold fixedCopiesOf
  exact xorEpsilon_blocks_le
    (by exact_mod_cast le_of_lt hpositive) hhalf
    (recoveryBlockOf_halves hpositive hhalf) rate

/-! ## The copy schedule at a parametric radius

`Proof/PCP/VerifierThresholdSeam.lean` proves that the fixed radius `recoveryDelta = 1 / 4` cannot
be the radius the componentwise verifier charges: the seam's soundness reserve forces
`6 * zeta < 1 / 288`, while its completeness direction needs the joint clause budget
`2 * delta ≤ 6 * zeta`, i.e. `delta ≤ 3 * zeta`.

The geometric copy schedule is therefore defined above at an arbitrary rational radius `delta`
(`recoveryBlockOf`, `recoveryBlockOf_halves`, `inverseCopiesOf`, `fixedCopiesOf`,
`xorEpsilon_inverseCopiesOf_le`, `xorEpsilon_fixedCopiesOf_le`). The block length grows like
`1 / delta` (an elementary Bernoulli bound), and one extra block replaces the arithmetic
`1 / 2 - recoveryDelta = 1 / 4`, hence the `+ recoveryBlock` in `inverseCopies` and
`fixedCopies`, matched by the `+ recoveryBlock` in `inverseCopiesLinearCoefficient`.

No fixed literal radius can work. `executableParametersOfSource` is
`Classical.choice (existsExecutableSoundnessParameters source.gap)`, and its `zeta` is any
positive rational below `min (3 / 2) ((completeness - soundness) ^ 2 / 43200)`, with
`completeness` and `soundness` arbitrary reals of an arbitrary `UniformPointwisePCPPSource`. So
no positive literal `c` admits a proof of `c ≤ 3 * zeta`, and the radius must be a function of
the selected package: `VerifierThresholdSeam.repairedRecoveryDelta`.

The published schedule below is the generic schedule at `repairedDeltaValue pcppSource`, the
validity constant of the parameter package the componentwise verifier selects for the scheduled
pointwise-PCPP source, so the completeness seam closes at the radius the schedule uses.
`recoveryBlock`, `inverseCopies`, `fixedCopies` and `inverseCopiesLinearCoefficient` take the
`pcppSource` argument; `inverseRawCoreArity`, `fixedRawCoreArity`,
`inverseScheduledRawCoreArity`, `inverseCoreEnvelope` and `fixedCoreEnvelope` already receive it.
`ExecutableSoundnessParameters` (the threshold, `zeta`, the outer error, the estimation error and
both reserves) is unchanged. The admissibility conditions of the imported XOR contract,
`0 ≤ delta` and `delta < 1 / 2`, are proved at this radius in `VerifierThresholdSeam.§9`.

The fixed literal is kept below as `recoveryDelta`, with no schedule depending on it, because it
is the object of the refutation in `VerifierThresholdSeam.§7`;
`repairedDelta_ne_recoveryDelta` records that the two radii differ. -/

/-- Rational code of the retired published validity point.  Nothing in the
schedule depends on it any more; it is kept because `VerifierThresholdSeam.§7`
refutes it. -/
def recoveryDeltaValue : ℚ := 1 / 4

theorem recoveryDeltaValue_positive : 0 < recoveryDeltaValue := by
  norm_num [recoveryDeltaValue]

theorem recoveryDeltaValue_le_half : (recoveryDeltaValue : ℝ) ≤ 1 / 2 := by
  norm_num [recoveryDeltaValue]

/-- Retired fixed validity point. -/
noncomputable def recoveryDelta : ℝ := (recoveryDeltaValue : ℝ)

theorem recoveryDelta_nonnegative : 0 ≤ recoveryDelta := by
  norm_num [recoveryDelta, recoveryDeltaValue]

theorem recoveryDelta_belowHalf : recoveryDelta < 1 / 2 := by
  norm_num [recoveryDelta, recoveryDeltaValue]

/-- The retired radius still reduces to the published literal; only its route
through a named rational code changed. -/
theorem recoveryDelta_eq_quarter : recoveryDelta = (1 / 4 : ℝ) := by
  norm_num [recoveryDelta, recoveryDeltaValue]

/-! ### The repaired approximation radius

The radius the schedule runs at is the validity constant of the parameter
package the componentwise verifier selects for the scheduled pointwise-PCPP
source.  It is choice-opaque: the only facts available about it are its
positivity and the soundness-reserve bound re-proved here. -/

/-- **The repaired Case-2 approximation radius**, as a rational code.  It is
`VerifierThresholdSeam.repairedRecoveryDelta (executableParametersOfSource
pcppSource)` unfolded one step, so the seam of that module closes at exactly
this radius. -/
noncomputable def repairedDeltaValue
    (pcppSource : UniformPointwisePCPPSource) : ℚ :=
  (executableParametersOfSource pcppSource).zeta

theorem repairedDeltaValue_positive
    (pcppSource : UniformPointwisePCPPSource) :
    0 < repairedDeltaValue pcppSource :=
  (executableParametersOfSource pcppSource).zetaPositive

/-- The soundness reserve of the selected package pins the repaired radius
below `1 / 1728`.  This is the only quantitative fact about it that the
schedule uses; `VerifierThresholdSeam.zeta_lt_of_unitGap` states the same bound
for an arbitrary package. -/
private theorem repairedDeltaValue_lt_reserveBound
    (pcppSource : UniformPointwisePCPPSource) :
    (repairedDeltaValue pcppSource : ℝ) < 1 / 1728 := by
  have hsoundness : 0 ≤ pcppSource.soundness :=
    uniformPointwisePCPPSource_soundness_nonnegative pcppSource
  have hcompleteness : pcppSource.completeness ≤ 1 :=
    uniformPointwisePCPPSource_completeness_le_one pcppSource
  have houter :
      (0 : ℝ) < ((executableParametersOfSource pcppSource).outerError : ℝ) := by
    exact_mod_cast (executableParametersOfSource pcppSource).outerErrorPositive
  have hestimation :
      (0 : ℝ) <
        ((executableParametersOfSource pcppSource).estimationError : ℝ) := by
    exact_mod_cast
      (executableParametersOfSource pcppSource).estimationErrorPositive
  have hreserve := (executableParametersOfSource pcppSource).soundReserve
  have hsqrt :
      Real.sqrt
          (12 * ((executableParametersOfSource pcppSource).zeta : ℝ)) <
        1 / 12 := by
    linarith
  have hsquare :
      12 * ((executableParametersOfSource pcppSource).zeta : ℝ) <
        (1 / 12 : ℝ) ^ 2 :=
    (Real.sqrt_lt' (by norm_num)).1 hsqrt
  norm_num at hsquare
  simp only [repairedDeltaValue]
  linarith

theorem repairedDeltaValue_le_half
    (pcppSource : UniformPointwisePCPPSource) :
    (repairedDeltaValue pcppSource : ℝ) ≤ 1 / 2 := by
  have hbound := repairedDeltaValue_lt_reserveBound pcppSource
  linarith

theorem repairedDeltaValue_le_quarter
    (pcppSource : UniformPointwisePCPPSource) :
    (repairedDeltaValue pcppSource : ℝ) ≤ 1 / 4 := by
  have hbound := repairedDeltaValue_lt_reserveBound pcppSource
  linarith

/-- **The repaired Case-2 approximation radius**, as a real.  This is the
radius of the published XOR ledger. -/
noncomputable def repairedDelta
    (pcppSource : UniformPointwisePCPPSource) : ℝ :=
  (repairedDeltaValue pcppSource : ℝ)

theorem repairedDelta_positive
    (pcppSource : UniformPointwisePCPPSource) :
    0 < repairedDelta pcppSource := by
  simp only [repairedDelta]
  exact_mod_cast repairedDeltaValue_positive pcppSource

theorem repairedDelta_nonnegative
    (pcppSource : UniformPointwisePCPPSource) :
    0 ≤ repairedDelta pcppSource :=
  le_of_lt (repairedDelta_positive pcppSource)

theorem repairedDelta_belowHalf
    (pcppSource : UniformPointwisePCPPSource) :
    repairedDelta pcppSource < 1 / 2 := by
  have hbound := repairedDeltaValue_lt_reserveBound pcppSource
  simp only [repairedDelta]
  linarith

theorem repairedDelta_le_quarter
    (pcppSource : UniformPointwisePCPPSource) :
    repairedDelta pcppSource ≤ 1 / 4 :=
  repairedDeltaValue_le_quarter pcppSource

/-- The retired literal and the repaired radius cannot coincide: the former is
`1 / 4`, the latter is below `1 / 1728`.  Recorded so the migration cannot be
mistaken for a no-op. -/
theorem repairedDelta_ne_recoveryDelta
    (pcppSource : UniformPointwisePCPPSource) :
    repairedDelta pcppSource ≠ recoveryDelta := by
  have hbound := repairedDeltaValue_lt_reserveBound pcppSource
  have hvalue : recoveryDelta = (1 / 4 : ℝ) := recoveryDelta_eq_quarter
  intro hequal
  rw [hvalue] at hequal
  simp only [repairedDelta] at hequal
  rw [hequal] at hbound
  norm_num at hbound

/-- One block halves the geometric factor at the repaired radius.  Its length
is `⌈1 / zeta⌉`, which is the whole quantitative price of the repair. -/
noncomputable def recoveryBlock
    (pcppSource : UniformPointwisePCPPSource) : ℕ :=
  recoveryBlockOf (repairedDeltaValue pcppSource)

theorem recoveryBlock_positive
    (pcppSource : UniformPointwisePCPPSource) :
    0 < recoveryBlock pcppSource :=
  recoveryBlockOf_positive (repairedDeltaValue pcppSource)

theorem recoveryBlock_halves
    (pcppSource : UniformPointwisePCPPSource) :
    (1 - repairedDelta pcppSource) ^ recoveryBlock pcppSource ≤ (1 / 2 : ℝ) :=
  recoveryBlockOf_halves (repairedDeltaValue_positive pcppSource)
    (repairedDeltaValue_le_half pcppSource)

/-- Copy count for inverse-polynomial advantage.  `rate` is fixed internally
from the requested final exponent and the downstream size ledger. -/
noncomputable def inverseCopies
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (rate sourceIndex : ℕ) : ℕ :=
  inverseCopiesOf (repairedDeltaValue pcppSource) outer rate sourceIndex

/-- Copy count for a fixed advantage. -/
noncomputable def fixedCopies
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) : ℕ :=
  fixedCopiesOf (repairedDeltaValue pcppSource) rate

theorem inverseCopies_eq
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (rate sourceIndex : ℕ) :
    inverseCopies outer pcppSource rate sourceIndex =
      recoveryBlock pcppSource *
          (rate * logScale (scheduledWidth outer sourceIndex)) +
        recoveryBlock pcppSource + 1 :=
  rfl

theorem fixedCopies_eq
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) :
    fixedCopies pcppSource rate =
      recoveryBlock pcppSource * rate + recoveryBlock pcppSource + 1 :=
  rfl

theorem inverseCopies_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (rate sourceIndex : ℕ) :
    1 ≤ inverseCopies outer pcppSource rate sourceIndex :=
  inverseCopiesOf_positive (repairedDeltaValue pcppSource) outer rate sourceIndex

theorem fixedCopies_positive
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) :
    1 ≤ fixedCopies pcppSource rate :=
  fixedCopiesOf_positive (repairedDeltaValue pcppSource) rate

theorem inverseCopies_monotone
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) :
    Monotone (inverseCopies outer pcppSource rate) :=
  inverseCopiesOf_monotone (repairedDeltaValue pcppSource) outer rate

/-- The logarithmic copy schedule leaves an explicit factor-four reserve
beyond the requested dyadic inverse-polynomial scale. -/
theorem xorEpsilon_inverseCopies_le
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (rate sourceIndex : ℕ) :
    xorEpsilon (repairedDelta pcppSource)
        (inverseCopies outer pcppSource rate sourceIndex) ≤
      1 / (2 : ℝ) ^
        (rate * logScale (scheduledWidth outer sourceIndex)) / 4 :=
  xorEpsilon_inverseCopiesOf_le (repairedDeltaValue_positive pcppSource)
    (repairedDeltaValue_le_half pcppSource) outer rate sourceIndex

/-- The constant-copy schedule has the same explicit factor-four reserve at
the fixed dyadic scale. -/
theorem xorEpsilon_fixedCopies_le
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) :
    xorEpsilon (repairedDelta pcppSource) (fixedCopies pcppSource rate) ≤
      1 / (2 : ℝ) ^ rate / 4 :=
  xorEpsilon_fixedCopiesOf_le (repairedDeltaValue_positive pcppSource)
    (repairedDeltaValue_le_half pcppSource) rate

/-- `logScale q` is an upper binary logarithm, so the dyadic schedule is at
most the requested inverse-polynomial advantage for every positive arity. -/
theorem inverseGeometricBound_le_inversePolynomialAdvantage
    (q rate : ℕ) (hq : 0 < q) :
    1 / (2 : ℝ) ^ (rate * logScale q) / 4 ≤
      inversePolynomialAdvantage q (rate : ℝ) := by
  have hqLog : q ≤ 2 ^ logScale q := by
    exact (Nat.le_add_right q 2).trans
      (Nat.le_pow_clog (by omega) (q + 2))
  have hdenominatorNat :
      q ^ rate ≤ 2 ^ (rate * logScale q) := by
    calc
      q ^ rate ≤ (2 ^ logScale q) ^ rate :=
        Nat.pow_le_pow_left hqLog rate
      _ = 2 ^ (logScale q * rate) := by rw [Nat.pow_mul]
      _ = 2 ^ (rate * logScale q) := by rw [Nat.mul_comm]
  have hdenominator :
      (q : ℝ) ^ rate ≤ (2 : ℝ) ^ (rate * logScale q) := by
    exact_mod_cast hdenominatorNat
  have hqPowerPositive : 0 < (q : ℝ) ^ rate := by
    positivity
  calc
    1 / (2 : ℝ) ^ (rate * logScale q) / 4 ≤
        1 / (2 : ℝ) ^ (rate * logScale q) := by
      exact div_le_self (by positivity) (by norm_num)
    _ ≤ 1 / (q : ℝ) ^ rate :=
      one_div_le_one_div_of_le hqPowerPositive hdenominator
    _ = inversePolynomialAdvantage q (rate : ℝ) := by
      unfold inversePolynomialAdvantage
      symm
      calc
        (q : ℝ) ^ (-(rate : ℝ)) =
            ((q : ℝ) ^ (rate : ℝ))⁻¹ :=
          Real.rpow_neg (by positivity) _
        _ = ((q : ℝ) ^ rate)⁻¹ := by rw [Real.rpow_natCast]
        _ = 1 / (q : ℝ) ^ rate := by rw [one_div]

theorem scheduledLogWidth_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolynomiallyBounded
      (fun sourceIndex => logScale (scheduledWidth outer sourceIndex)) := by
  apply polynomiallyBounded_mono
    (larger := fun sourceIndex => scheduledWidth outer sourceIndex + 2)
  · intro sourceIndex
    exact logScale_le_add_two _
  · exact polynomiallyBounded_add
      (scheduledWidth_polynomiallyBounded outer)
      (polynomiallyBounded_constant 2)

/-- The general schedule stays polynomial at every radius: the radius only
enters through the constant block length. -/
theorem inverseCopiesOf_polynomiallyBounded (delta : ℚ)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (rate : ℕ) :
    PolynomiallyBounded (inverseCopiesOf delta outer rate) := by
  have hscaled :=
    polynomiallyBounded_mul
      (polynomiallyBounded_constant (recoveryBlockOf delta))
      (polynomiallyBounded_mul
        (polynomiallyBounded_constant rate)
        (scheduledLogWidth_polynomiallyBounded outer))
  change PolynomiallyBounded (fun sourceIndex =>
    recoveryBlockOf delta *
        (rate * logScale (scheduledWidth outer sourceIndex)) +
      recoveryBlockOf delta + 1)
  exact polynomiallyBounded_add
    (polynomiallyBounded_add hscaled
      (polynomiallyBounded_constant (recoveryBlockOf delta)))
    (polynomiallyBounded_constant 1)

theorem fixedCopiesOf_polynomiallyBounded (delta : ℚ) (rate : ℕ) :
    PolynomiallyBounded (fun _ => fixedCopiesOf delta rate) :=
  polynomiallyBounded_constant _

theorem inverseCopies_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) :
    PolynomiallyBounded (inverseCopies outer pcppSource rate) :=
  inverseCopiesOf_polynomiallyBounded (repairedDeltaValue pcppSource) outer rate

theorem fixedCopies_polynomiallyBounded
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) :
    PolynomiallyBounded (fun _ => fixedCopies pcppSource rate) :=
  polynomiallyBounded_constant _

noncomputable def inverseRawCoreArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) : ℕ :=
  inverseCopies outer pcppSource rate sourceIndex *
    seedArity outer pcppSource requiredDegree sourceIndex

noncomputable def fixedRawCoreArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) : ℕ :=
  fixedCopies pcppSource rate *
    seedArity outer pcppSource requiredDegree sourceIndex

theorem inverseRawCoreArity_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    PolynomiallyBounded
      (inverseRawCoreArity outer pcppSource requiredDegree rate) := by
  exact polynomiallyBounded_mul
    (inverseCopies_polynomiallyBounded outer pcppSource rate)
    (seedArity_polynomiallyBounded outer pcppSource requiredDegree)

theorem fixedRawCoreArity_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    PolynomiallyBounded
      (fixedRawCoreArity outer pcppSource requiredDegree rate) := by
  exact polynomiallyBounded_mul
    (fixedCopies_polynomiallyBounded pcppSource rate)
    (seedArity_polynomiallyBounded outer pcppSource requiredDegree)

theorem inverseRawCoreArity_monotone
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    Monotone
      (inverseRawCoreArity outer pcppSource requiredDegree rate) := by
  intro left right hle
  unfold inverseRawCoreArity
  exact Nat.mul_le_mul
    (inverseCopies_monotone outer pcppSource rate hle)
    (seedArity_monotone outer pcppSource requiredDegree hle)

theorem fixedRawCoreArity_monotone
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    Monotone
      (fixedRawCoreArity outer pcppSource requiredDegree rate) := by
  intro left right hle
  unfold fixedRawCoreArity
  exact Nat.mul_le_mul (le_refl _) <|
    seedArity_monotone outer pcppSource requiredDegree hle

theorem inverseCopies_mul_sourceIndex_succ_le_rawCoreArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) :
    inverseCopies outer pcppSource rate sourceIndex * (sourceIndex + 1) ≤
      inverseRawCoreArity outer pcppSource
        requiredDegree rate sourceIndex := by
  unfold inverseRawCoreArity
  exact Nat.mul_le_mul_left _ <|
    sourceIndex_succ_le_seedArity
      outer pcppSource requiredDegree sourceIndex

theorem fixedCopies_mul_sourceIndex_succ_le_rawCoreArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) :
    fixedCopies pcppSource rate * (sourceIndex + 1) ≤
      fixedRawCoreArity outer pcppSource
        requiredDegree rate sourceIndex := by
  unfold fixedRawCoreArity
  exact Nat.mul_le_mul_left _ <|
    sourceIndex_succ_le_seedArity
      outer pcppSource requiredDegree sourceIndex

noncomputable def inverseCopiesLinearCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) : ℕ :=
  recoveryBlock pcppSource * rate * scheduledLogWidthCoefficient outer +
    recoveryBlock pcppSource + 1

theorem inverseCopiesLinearCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) :
    0 < inverseCopiesLinearCoefficient outer pcppSource rate := by
  unfold inverseCopiesLinearCoefficient
  omega

theorem inverseCopies_le_sourceLog
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate sourceIndex : ℕ) :
    inverseCopies outer pcppSource rate sourceIndex ≤
      inverseCopiesLinearCoefficient outer pcppSource rate *
        logScale (sourceIndex + 1) := by
  have hlog :=
    scheduledLogWidth_le_sourceLog outer sourceIndex
  have hlogPositive : 1 ≤ logScale (sourceIndex + 1) := by
    have := logScale_positive (sourceIndex + 1)
    omega
  have hscaled :
      recoveryBlock pcppSource *
          (rate * logScale (scheduledWidth outer sourceIndex)) ≤
        recoveryBlock pcppSource *
          (rate *
            (scheduledLogWidthCoefficient outer *
              logScale (sourceIndex + 1))) := by
    gcongr
  have hconstant :
      recoveryBlock pcppSource ≤
        recoveryBlock pcppSource * logScale (sourceIndex + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  rw [inverseCopies_eq]
  unfold inverseCopiesLinearCoefficient
  calc
    recoveryBlock pcppSource *
            (rate * logScale (scheduledWidth outer sourceIndex)) +
          recoveryBlock pcppSource + 1 ≤
        recoveryBlock pcppSource *
              (rate *
                (scheduledLogWidthCoefficient outer *
                  logScale (sourceIndex + 1))) +
            recoveryBlock pcppSource * logScale (sourceIndex + 1) +
          logScale (sourceIndex + 1) :=
      Nat.add_le_add (Nat.add_le_add hscaled hconstant) hlogPositive
    _ =
        (recoveryBlock pcppSource * rate *
              scheduledLogWidthCoefficient outer +
            recoveryBlock pcppSource + 1) *
          logScale (sourceIndex + 1) := by ring

noncomputable def inverseRawLinearCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) : ℕ :=
  inverseCopiesLinearCoefficient outer pcppSource rate *
    seedArityLinearCoefficient outer pcppSource requiredDegree

theorem inverseRawLinearCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    0 < inverseRawLinearCoefficient
      outer pcppSource requiredDegree rate :=
  Nat.mul_pos
    (inverseCopiesLinearCoefficient_positive outer pcppSource rate)
    (seedArityLinearCoefficient_positive
      outer pcppSource requiredDegree)

def inverseSourceMeasure (sourceIndex : ℕ) : ℕ :=
  (sourceIndex + 1) * logScale (sourceIndex + 1)

theorem inverseSourceMeasure_positive (sourceIndex : ℕ) :
    0 < inverseSourceMeasure sourceIndex := by
  unfold inverseSourceMeasure
  exact Nat.mul_pos (by omega) (logScale_positive _)

theorem sourceIndex_succ_le_inverseSourceMeasure (sourceIndex : ℕ) :
    sourceIndex + 1 ≤ inverseSourceMeasure sourceIndex := by
  unfold inverseSourceMeasure
  have hlog : 1 ≤ logScale (sourceIndex + 1) := by
    have := logScale_positive (sourceIndex + 1)
    omega
  simpa only [Nat.mul_one] using
    Nat.mul_le_mul_left (sourceIndex + 1) hlog

theorem inverseSourceMeasure_le_rawCoreArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) (hrate : 1 ≤ rate) :
    inverseSourceMeasure sourceIndex ≤
      inverseRawCoreArity outer pcppSource
        requiredDegree rate sourceIndex := by
  have hwidth :
      logScale (sourceIndex + 1) ≤
        logScale (scheduledWidth outer sourceIndex) :=
    logScale_mono <| sourceIndex_succ_le_scheduledWidth outer sourceIndex
  have hcopies :
      logScale (sourceIndex + 1) ≤
        inverseCopies outer pcppSource rate sourceIndex := by
    rw [inverseCopies_eq]
    have hblock : 1 ≤ recoveryBlock pcppSource * rate :=
      Nat.mul_pos (recoveryBlock_positive pcppSource) hrate
    calc
      logScale (sourceIndex + 1) ≤
          logScale (scheduledWidth outer sourceIndex) := hwidth
      _ ≤
          (recoveryBlock pcppSource * rate) *
            logScale (scheduledWidth outer sourceIndex) := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right
            (logScale (scheduledWidth outer sourceIndex)) hblock
      _ ≤
          recoveryBlock pcppSource *
                (rate * logScale (scheduledWidth outer sourceIndex)) +
              recoveryBlock pcppSource + 1 := by
        rw [Nat.mul_assoc]
        omega
  unfold inverseSourceMeasure inverseRawCoreArity
  calc
    (sourceIndex + 1) * logScale (sourceIndex + 1) =
        logScale (sourceIndex + 1) * (sourceIndex + 1) := by ring
    _ ≤
        inverseCopies outer pcppSource rate sourceIndex *
          seedArity outer pcppSource requiredDegree sourceIndex :=
      Nat.mul_le_mul hcopies
        (sourceIndex_succ_le_seedArity
          outer pcppSource requiredDegree sourceIndex)

theorem inverseRawCoreArity_le_measure
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) :
    inverseRawCoreArity outer pcppSource
        requiredDegree rate sourceIndex ≤
      inverseRawLinearCoefficient outer pcppSource
          requiredDegree rate *
        inverseSourceMeasure sourceIndex := by
  have hcopies :=
    inverseCopies_le_sourceLog outer pcppSource rate sourceIndex
  have hseed :=
    seedArity_le_linear
      outer pcppSource requiredDegree sourceIndex
  unfold inverseRawCoreArity inverseRawLinearCoefficient
    inverseSourceMeasure
  calc
    inverseCopies outer pcppSource rate sourceIndex *
          seedArity outer pcppSource requiredDegree sourceIndex ≤
        (inverseCopiesLinearCoefficient outer pcppSource rate *
            logScale (sourceIndex + 1)) *
          (seedArityLinearCoefficient outer pcppSource requiredDegree *
            (sourceIndex + 1)) := Nat.mul_le_mul hcopies hseed
    _ =
        (inverseCopiesLinearCoefficient outer pcppSource rate *
            seedArityLinearCoefficient outer pcppSource requiredDegree) *
          ((sourceIndex + 1) * logScale (sourceIndex + 1)) := by ring

/-- The predecessor of the first `q log q` crossing.  The bounded search range
is part of the definition, so a concrete language runner can reproduce it by
a linear scan without receiving a semantic schedule witness. -/
def inverseSourceIndex (scheduleIndex : ℕ) : ℕ :=
  Nat.findGreatest
    (fun sourceIndex =>
      inverseSourceMeasure sourceIndex ≤ scheduleIndex + 2)
    (scheduleIndex + 1)

theorem inverseSourceIndex_le (scheduleIndex : ℕ) :
    inverseSourceIndex scheduleIndex ≤ scheduleIndex + 1 :=
  Nat.findGreatest_le _

theorem inverseSourceIndex_measure_le (scheduleIndex : ℕ) :
    inverseSourceMeasure (inverseSourceIndex scheduleIndex) ≤
      scheduleIndex + 2 := by
  unfold inverseSourceIndex
  exact Nat.findGreatest_spec
    (P := fun sourceIndex =>
      inverseSourceMeasure sourceIndex ≤ scheduleIndex + 2)
    (m := 0) (n := scheduleIndex + 1)
    (by omega)
    (by norm_num [inverseSourceMeasure, logScale])

theorem le_inverseSourceIndex_of_measure_le
    (candidate scheduleIndex : ℕ)
    (hmeasure :
      inverseSourceMeasure candidate ≤ scheduleIndex + 2) :
    candidate ≤ inverseSourceIndex scheduleIndex := by
  have hbound : candidate ≤ scheduleIndex + 1 := by
    have :=
      (sourceIndex_succ_le_inverseSourceMeasure candidate).trans hmeasure
    omega
  unfold inverseSourceIndex
  exact Nat.le_findGreatest hbound hmeasure

private theorem two_le_logScale_succ (sourceIndex : ℕ) :
    2 ≤ logScale (sourceIndex + 1) := by
  apply Nat.succ_le_iff.mpr
  unfold logScale
  rw [Nat.lt_clog_iff_pow_lt (by omega)]
  norm_num

theorem inverseSourceIndex_lt_bound (scheduleIndex : ℕ) :
    inverseSourceIndex scheduleIndex < scheduleIndex + 1 := by
  let sourceIndex := inverseSourceIndex scheduleIndex
  have hsource := inverseSourceIndex_le scheduleIndex
  have hmeasure := inverseSourceIndex_measure_le scheduleIndex
  have hlog := two_le_logScale_succ sourceIndex
  by_contra hnot
  have hequal : sourceIndex = scheduleIndex + 1 := by
    dsimp only [sourceIndex] at hsource hnot ⊢
    omega
  change inverseSourceMeasure sourceIndex ≤ scheduleIndex + 2 at hmeasure
  unfold inverseSourceMeasure at hmeasure
  rw [hequal] at hmeasure hlog
  nlinarith

theorem inverseSourceIndex_next_crosses (scheduleIndex : ℕ) :
    scheduleIndex + 2 <
      inverseSourceMeasure (inverseSourceIndex scheduleIndex + 1) := by
  have hnot :=
    Nat.findGreatest_is_greatest
      (P := fun sourceIndex =>
        inverseSourceMeasure sourceIndex ≤ scheduleIndex + 2)
      (n := scheduleIndex + 1)
      (k := inverseSourceIndex scheduleIndex + 1)
      (Nat.lt_succ_self _)
      (by
        have := inverseSourceIndex_lt_bound scheduleIndex
        omega)
  omega

theorem logScale_next_le_double (sourceIndex : ℕ) :
    logScale (sourceIndex + 2) ≤
      2 * logScale (sourceIndex + 1) := by
  let sourceLog := logScale (sourceIndex + 1)
  have hsource :
      sourceIndex + 3 ≤ 2 ^ sourceLog := by
    simpa [sourceLog, logScale] using
      Nat.le_pow_clog (by omega) (sourceIndex + 3)
  have hnext :
      sourceIndex + 4 ≤ 2 ^ (sourceLog + 1) := by
    calc
      sourceIndex + 4 ≤ 2 * (sourceIndex + 3) := by omega
      _ ≤ 2 * 2 ^ sourceLog := by gcongr
      _ = 2 ^ (sourceLog + 1) := by
        rw [Nat.pow_succ]
        ring
  have hclog :
      logScale (sourceIndex + 2) ≤ sourceLog + 1 := by
    unfold logScale
    exact Nat.clog_le_of_le_pow hnext
  have hpositive : 1 ≤ sourceLog := by
    have := logScale_positive (sourceIndex + 1)
    simp only [sourceLog]
    omega
  calc
    logScale (sourceIndex + 2) ≤ sourceLog + 1 := hclog
    _ ≤ 2 * sourceLog := by omega
    _ = 2 * logScale (sourceIndex + 1) := by rfl

theorem inverseSourceMeasure_next_le_four (sourceIndex : ℕ) :
    inverseSourceMeasure (sourceIndex + 1) ≤
      4 * inverseSourceMeasure sourceIndex := by
  have hindex : sourceIndex + 2 ≤ 2 * (sourceIndex + 1) := by omega
  have hlog := logScale_next_le_double sourceIndex
  unfold inverseSourceMeasure
  calc
    (sourceIndex + 1 + 1) * logScale (sourceIndex + 1 + 1) ≤
        (2 * (sourceIndex + 1)) *
          (2 * logScale (sourceIndex + 1)) :=
      Nat.mul_le_mul hindex hlog
    _ = 4 * ((sourceIndex + 1) * logScale (sourceIndex + 1)) := by
      ring

theorem scheduleIndex_succ_lt_four_measure (scheduleIndex : ℕ) :
    scheduleIndex + 1 <
      4 * inverseSourceMeasure (inverseSourceIndex scheduleIndex) := by
  exact (by
    have hcross := inverseSourceIndex_next_crosses scheduleIndex
    have hjump :=
      inverseSourceMeasure_next_le_four
        (inverseSourceIndex scheduleIndex)
    omega)

noncomputable def inverseScheduledRawCoreArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate scheduleIndex : ℕ) : ℕ :=
  inverseRawCoreArity outer pcppSource requiredDegree rate
    (inverseSourceIndex scheduleIndex)

noncomputable def inverseTightCoreCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) : ℕ :=
  2 * inverseRawLinearCoefficient
    outer pcppSource requiredDegree rate

theorem inverseTightCoreCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    0 < inverseTightCoreCoefficient
      outer pcppSource requiredDegree rate := by
  unfold inverseTightCoreCoefficient
  exact Nat.mul_pos (by omega) <|
    inverseRawLinearCoefficient_positive
      outer pcppSource requiredDegree rate

theorem inverseScheduledRawCoreArity_le_linear
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate scheduleIndex : ℕ) :
    inverseScheduledRawCoreArity
        outer pcppSource requiredDegree rate scheduleIndex ≤
      inverseTightCoreCoefficient outer pcppSource requiredDegree rate *
        (scheduleIndex + 1) := by
  let rawCoefficient :=
    inverseRawLinearCoefficient outer pcppSource requiredDegree rate
  have hraw :=
    inverseRawCoreArity_le_measure outer pcppSource
      requiredDegree rate (inverseSourceIndex scheduleIndex)
  have hmeasure := inverseSourceIndex_measure_le scheduleIndex
  calc
    inverseScheduledRawCoreArity
        outer pcppSource requiredDegree rate scheduleIndex ≤
      rawCoefficient *
        inverseSourceMeasure (inverseSourceIndex scheduleIndex) := by
          simpa only [inverseScheduledRawCoreArity, rawCoefficient] using hraw
    _ ≤ rawCoefficient * (scheduleIndex + 2) := by gcongr
    _ ≤ rawCoefficient * (2 * (scheduleIndex + 1)) := by
      gcongr
      omega
    _ =
        inverseTightCoreCoefficient
            outer pcppSource requiredDegree rate *
          (scheduleIndex + 1) := by
      unfold inverseTightCoreCoefficient
      simp only [rawCoefficient]
      ring

noncomputable def inverseCorePaddingFactor
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) : ℕ :=
  8 * inverseRawLinearCoefficient
    outer pcppSource requiredDegree rate

theorem inverseCorePaddingFactor_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    0 < inverseCorePaddingFactor
      outer pcppSource requiredDegree rate := by
  unfold inverseCorePaddingFactor
  exact Nat.mul_pos (by omega) <|
    inverseRawLinearCoefficient_positive
      outer pcppSource requiredDegree rate

theorem inverseTightCore_le_paddingFactor_mul_raw
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate scheduleIndex : ℕ) (hrate : 1 ≤ rate) :
    inverseTightCoreCoefficient outer pcppSource requiredDegree rate *
        (scheduleIndex + 1) <
      inverseCorePaddingFactor outer pcppSource requiredDegree rate *
        inverseScheduledRawCoreArity
          outer pcppSource requiredDegree rate scheduleIndex := by
  let sourceIndex := inverseSourceIndex scheduleIndex
  have hschedule := scheduleIndex_succ_lt_four_measure scheduleIndex
  have hmeasure :=
    inverseSourceMeasure_le_rawCoreArity
      outer pcppSource requiredDegree rate sourceIndex hrate
  have hpositive :=
    inverseRawLinearCoefficient_positive
      outer pcppSource requiredDegree rate
  have hsource :
      scheduleIndex + 1 <
        4 * inverseScheduledRawCoreArity
          outer pcppSource requiredDegree rate scheduleIndex := by
    unfold inverseScheduledRawCoreArity
    dsimp only [sourceIndex] at hmeasure
    omega
  unfold inverseTightCoreCoefficient inverseCorePaddingFactor
  nlinarith

noncomputable def fixedRawLinearCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) : ℕ :=
  fixedCopies pcppSource rate *
    seedArityLinearCoefficient outer pcppSource requiredDegree

theorem fixedRawLinearCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    0 < fixedRawLinearCoefficient
      outer pcppSource requiredDegree rate :=
  Nat.mul_pos (by
    exact fixedCopies_positive pcppSource rate)
    (seedArityLinearCoefficient_positive
      outer pcppSource requiredDegree)

theorem fixedRawCoreArity_le_linear
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) :
    fixedRawCoreArity outer pcppSource requiredDegree rate sourceIndex ≤
      fixedRawLinearCoefficient outer pcppSource requiredDegree rate *
        (sourceIndex + 1) := by
  unfold fixedRawCoreArity fixedRawLinearCoefficient
  calc
    fixedCopies pcppSource rate *
          seedArity outer pcppSource requiredDegree sourceIndex ≤
        fixedCopies pcppSource rate *
          (seedArityLinearCoefficient outer pcppSource requiredDegree *
            (sourceIndex + 1)) :=
      Nat.mul_le_mul_left _ <|
        seedArity_le_linear
          outer pcppSource requiredDegree sourceIndex
    _ =
        (fixedCopies pcppSource rate *
            seedArityLinearCoefficient outer pcppSource requiredDegree) *
          (sourceIndex + 1) := by ring

noncomputable def fixedCorePaddingFactor
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) : ℕ :=
  seedArityLinearCoefficient outer pcppSource requiredDegree

theorem fixedCorePaddingFactor_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree : ℕ) :
    0 < fixedCorePaddingFactor outer pcppSource requiredDegree :=
  seedArityLinearCoefficient_positive
    outer pcppSource requiredDegree

theorem fixedTightCore_le_paddingFactor_mul_raw
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) :
    fixedRawLinearCoefficient outer pcppSource requiredDegree rate *
        (sourceIndex + 1) ≤
      fixedCorePaddingFactor outer pcppSource requiredDegree *
        fixedRawCoreArity outer pcppSource
          requiredDegree rate sourceIndex := by
  have hraw :=
    fixedCopies_mul_sourceIndex_succ_le_rawCoreArity
      outer pcppSource requiredDegree rate sourceIndex
  unfold fixedRawLinearCoefficient fixedCorePaddingFactor
  calc
    fixedCopies pcppSource rate *
          seedArityLinearCoefficient outer pcppSource requiredDegree *
          (sourceIndex + 1) =
        seedArityLinearCoefficient outer pcppSource requiredDegree *
          (fixedCopies pcppSource rate * (sourceIndex + 1)) := by ring
    _ ≤
        seedArityLinearCoefficient outer pcppSource requiredDegree *
          fixedRawCoreArity outer pcppSource
            requiredDegree rate sourceIndex := by gcongr

/-- A smooth envelope has positive degree, which guarantees that every target
eventually has a next half-crossing. -/
structure SmoothCoreEnvelope (rawArity : ℕ → ℕ)
    extends PolynomialEnvelope rawArity where
  degreePositive : 0 < degree

def SmoothCoreEnvelope.coreArity
    {rawArity : ℕ → ℕ} (envelope : SmoothCoreEnvelope rawArity) :
    ℕ → ℕ :=
  polynomialCore envelope.coefficient envelope.degree

theorem SmoothCoreEnvelope.rawArity_le_coreArity
    {rawArity : ℕ → ℕ} (envelope : SmoothCoreEnvelope rawArity)
    (sourceIndex : ℕ) :
    rawArity sourceIndex ≤ envelope.coreArity sourceIndex :=
  envelope.bound sourceIndex

theorem SmoothCoreEnvelope.coreArity_monotone
    {rawArity : ℕ → ℕ} (envelope : SmoothCoreEnvelope rawArity) :
    Monotone envelope.coreArity :=
  polynomialCore_monotone envelope.coefficient envelope.degree

def SmoothCoreEnvelope.targetOnset
    {rawArity : ℕ → ℕ} (envelope : SmoothCoreEnvelope rawArity) : ℕ :=
  2 * envelope.coreArity (polynomialSourceOnset envelope.degree)

/-- Canonical semantic schedule certificate.  The executable selector is
proved against this exact first-crossing object in the machine layer. -/
def SmoothCoreEnvelope.firstCrossingData
    {rawArity : ℕ → ℕ} (envelope : SmoothCoreEnvelope rawArity)
    (target : ℕ) (htarget : envelope.targetOnset ≤ target) :
    FirstCrossingData envelope.coreArity target :=
  polynomialFirstCrossingData envelope.coefficient envelope.degree target
    envelope.coefficientPositive envelope.degreePositive htarget

noncomputable def inverseCoreEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    SmoothCoreEnvelope
      (inverseScheduledRawCoreArity
        outer pcppSource requiredDegree rate) where
  coefficient :=
    inverseTightCoreCoefficient outer pcppSource requiredDegree rate
  degree := 1
  coefficientPositive :=
    inverseTightCoreCoefficient_positive
      outer pcppSource requiredDegree rate
  degreePositive := by omega
  bound := by
    intro scheduleIndex
    simpa only [pow_one] using
      inverseScheduledRawCoreArity_le_linear
        outer pcppSource requiredDegree rate scheduleIndex

noncomputable def fixedCoreEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    SmoothCoreEnvelope
      (fixedRawCoreArity outer pcppSource requiredDegree rate) where
  coefficient :=
    fixedRawLinearCoefficient outer pcppSource requiredDegree rate
  degree := 1
  coefficientPositive :=
    fixedRawLinearCoefficient_positive
      outer pcppSource requiredDegree rate
  degreePositive := by omega
  bound := by
    intro sourceIndex
    simpa only [pow_one] using
      fixedRawCoreArity_le_linear
        outer pcppSource requiredDegree rate sourceIndex

@[simp] theorem inverseCoreEnvelope_coreArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate scheduleIndex : ℕ) :
    (inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
        scheduleIndex =
      inverseTightCoreCoefficient outer pcppSource requiredDegree rate *
        (scheduleIndex + 1) := by
  simp [SmoothCoreEnvelope.coreArity, polynomialCore, inverseCoreEnvelope]

@[simp] theorem fixedCoreEnvelope_coreArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) :
    (fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
        sourceIndex =
      fixedRawLinearCoefficient outer pcppSource requiredDegree rate *
        (sourceIndex + 1) := by
  simp [SmoothCoreEnvelope.coreArity, polynomialCore, fixedCoreEnvelope]

noncomputable def inverseCaseOneWidthFactor
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) : ℕ :=
  12 * inverseTightCoreCoefficient
    outer pcppSource requiredDegree rate

theorem inverseCaseOneWidthFactor_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    0 < inverseCaseOneWidthFactor
      outer pcppSource requiredDegree rate := by
  unfold inverseCaseOneWidthFactor
  exact Nat.mul_pos (by omega) <|
    inverseTightCoreCoefficient_positive
      outer pcppSource requiredDegree rate

/-- Canonical inverse-tier onset needed to absorb the fixed core coefficient
when requesting `power` powers of the selected core. -/
noncomputable def inverseCaseOnePowerOnset
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate power : ℕ) : ℕ :=
  inverseSourceMeasure
    ((inverseCaseOneWidthFactor outer pcppSource requiredDegree rate) ^ power)

theorem inverseCaseOnePowerOnset_ready
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate power scheduleIndex : ℕ)
    (hready :
      inverseCaseOnePowerOnset
        outer pcppSource requiredDegree rate power ≤ scheduleIndex) :
    inverseSourceMeasure
        ((inverseCaseOneWidthFactor outer pcppSource requiredDegree rate) ^
          power) ≤
      scheduleIndex + 2 := by
  unfold inverseCaseOnePowerOnset at hready
  omega

theorem inverseCoreEnvelope_le_widthSquare
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate scheduleIndex : ℕ) :
    (inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
        scheduleIndex ≤
      inverseCaseOneWidthFactor outer pcppSource requiredDegree rate *
        scheduledWidth outer (inverseSourceIndex scheduleIndex) ^ 2 := by
  let sourceIndex := inverseSourceIndex scheduleIndex
  let width := scheduledWidth outer sourceIndex
  let coreCoefficient :=
    inverseTightCoreCoefficient outer pcppSource requiredDegree rate
  have hschedule := scheduleIndex_succ_lt_four_measure scheduleIndex
  have hindex :
      sourceIndex + 1 ≤ width := by
    exact sourceIndex_succ_le_scheduledWidth outer sourceIndex
  have hlog :
      logScale (sourceIndex + 1) ≤ logScale width :=
    logScale_mono hindex
  have hlogWidth : logScale width ≤ 3 * width := by
    calc
      logScale width ≤ width + 2 := logScale_le_add_two width
      _ ≤ 3 * width := by omega
  have hmeasure :
      inverseSourceMeasure sourceIndex ≤ 3 * width ^ 2 := by
    unfold inverseSourceMeasure
    calc
      (sourceIndex + 1) * logScale (sourceIndex + 1) ≤
          width * (3 * width) := Nat.mul_le_mul hindex (hlog.trans hlogWidth)
      _ = 3 * width ^ 2 := by ring
  rw [inverseCoreEnvelope_coreArity]
  calc
    coreCoefficient * (scheduleIndex + 1) ≤
        coreCoefficient *
          (4 * inverseSourceMeasure sourceIndex) := by
      gcongr
    _ ≤ coreCoefficient * (4 * (3 * width ^ 2)) := by
      gcongr
    _ =
        inverseCaseOneWidthFactor outer pcppSource requiredDegree rate *
          scheduledWidth outer (inverseSourceIndex scheduleIndex) ^ 2 := by
      unfold inverseCaseOneWidthFactor
      simp only [sourceIndex, width, coreCoefficient]
      ring

noncomputable def fixedCaseOneWidthFactor
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) : ℕ :=
  fixedRawLinearCoefficient outer pcppSource requiredDegree rate

theorem fixedCaseOneWidthFactor_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate : ℕ) :
    0 < fixedCaseOneWidthFactor
      outer pcppSource requiredDegree rate :=
  fixedRawLinearCoefficient_positive
    outer pcppSource requiredDegree rate

/-- Canonical fixed-tier onset for absorbing the selected core coefficient. -/
noncomputable def fixedCaseOnePowerOnset
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate power : ℕ) : ℕ :=
  (fixedCaseOneWidthFactor outer pcppSource requiredDegree rate) ^ power

theorem fixedCaseOnePowerOnset_ready
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate power sourceIndex : ℕ)
    (hready :
      fixedCaseOnePowerOnset
        outer pcppSource requiredDegree rate power ≤ sourceIndex) :
    (fixedCaseOneWidthFactor outer pcppSource requiredDegree rate) ^ power ≤
      sourceIndex + 1 := by
  unfold fixedCaseOnePowerOnset at hready
  omega

theorem fixedCoreEnvelope_le_width
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) :
    (fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
        sourceIndex ≤
      fixedCaseOneWidthFactor outer pcppSource requiredDegree rate *
        scheduledWidth outer sourceIndex := by
  rw [fixedCoreEnvelope_coreArity]
  unfold fixedCaseOneWidthFactor
  gcongr
  exact sourceIndex_succ_le_scheduledWidth outer sourceIndex

theorem inverseCoreEnvelope_le_paddingFactor_mul_raw
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate scheduleIndex : ℕ) (hrate : 1 ≤ rate) :
    (inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
        scheduleIndex ≤
      inverseCorePaddingFactor outer pcppSource requiredDegree rate *
        inverseScheduledRawCoreArity
          outer pcppSource requiredDegree rate scheduleIndex := by
  rw [inverseCoreEnvelope_coreArity]
  exact Nat.le_of_lt <|
    inverseTightCore_le_paddingFactor_mul_raw
      outer pcppSource requiredDegree rate scheduleIndex hrate

theorem fixedCoreEnvelope_le_paddingFactor_mul_raw
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex : ℕ) :
    (fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
        sourceIndex ≤
      fixedCorePaddingFactor outer pcppSource requiredDegree *
        fixedRawCoreArity outer pcppSource
          requiredDegree rate sourceIndex :=
  by
    rw [fixedCoreEnvelope_coreArity]
    exact fixedTightCore_le_paddingFactor_mul_raw
      outer pcppSource requiredDegree rate sourceIndex

end NearCubicWires.RecoveryScheduleEnvelope
