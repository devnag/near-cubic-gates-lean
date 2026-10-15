import Proof.Foundations.CanonicalBinaryProgram
import Proof.Circuits.RegisterBounds

/-!
# Fixed tagged-stream to canonical-balanced builder

Executable compilers often emit a private forward tagged stream because a
single cons cell is convenient while the stream is being produced.  Public
variable-length values use `encodeBalancedList` so their binary width is
polynomial.  This fixed oracle-free machine is the sole conversion boundary:
it counts the stream, performs the canonical midpoint recursion with an
explicit continuation stack, and returns exactly the balanced encoding.
-/

namespace NearCubicWires.CanonicalBalancedBuilder

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds

/-! Register ABI:

* `r0`: tagged input cursor, then the unconsumed suffix;
* `r1`: current subtree leaf count;
* `r2`: private continuation stack;
* `r3`: completed subtree code and final output;
* `r4`--`r6`: frame and pairing scratch;
* `r7`, `r9`, `r10`: constants zero, one, and two;
* `r8`: saved start of the tagged stream.

A pending frame is `pair rightCount leftCode`; `leftCode = 0` means that the
left subtree is being evaluated.  Every real nonempty subtree code is
positive, so the marker is unambiguous without a second control format. -/
def taggedToBalancedProgram : NPOracleProgram :=
  [ .set 7 0 1,
    .set 9 1 2,
    .set 10 2 3,
    .copy 0 8 4,
    .set 1 0 5,
    .branchZero 0 10 6,
    .unpairRight 0 4 7,
    .unpairRight 4 0 8,
    .increment 1 9,
    .branchZero 7 5 5,
    .copy 8 0 11,
    .set 2 0 12,
    .branchZero 7 13 13,
    .branchZero 1 14 16,
    .set 3 0 15,
    .branchZero 7 29 29,
    .copy 1 4 17,
    .decrement 4 18,
    .branchZero 4 19 23,
    .unpairRight 0 5 20,
    .unpairLeft 5 3 21,
    .unpairRight 5 0 22,
    .pair 9 3 3 29,
    .shiftRight 1 1 4 24,
    .increment 1 25,
    .shiftRight 1 1 1 26,
    .pair 4 7 5 27,
    .pair 5 2 2 28,
    .branchZero 7 13 13,
    .branchZero 2 42 30,
    .unpairLeft 2 5 31,
    .unpairRight 2 2 32,
    .unpairLeft 5 4 33,
    .unpairRight 5 6 34,
    .branchZero 6 35 40,
    .copy 3 6 36,
    .pair 4 6 5 37,
    .pair 5 2 2 38,
    .copy 4 1 39,
    .branchZero 7 13 13,
    .pair 6 3 5 41,
    .pair 10 5 3 29,
    .halt 3 ]

@[simp] theorem taggedToBalancedProgram_length :
    taggedToBalancedProgram.length = 43 := by
  rfl

theorem taggedToBalancedProgram_oracleFree :
    OracleFree taggedToBalancedProgram := by
  rfl

/-- Exact steps from the build dispatcher (`pc = 13`) to the return
dispatcher (`pc = 29`), excluding the caller's continuation handling. -/
def balancedBuildFuel : List ℕ → ℕ
  | [] => 3
  | [_] => 8
  | first :: second :: rest =>
      let values := first :: second :: rest
      let leftLength := (values.length + 1) / 2
      let left := values.take leftLength
      let right := values.drop leftLength
      29 + balancedBuildFuel left + balancedBuildFuel right
termination_by values => values.length
decreasing_by
  all_goals
    simp_wf
    have : ((rest.length + 2 + 1) / 2) ≤ rest.length + 1 := by omega
    simp
    omega

/-- Five instructions per tagged cell count the input.  The remaining eleven
steps initialize control, build the tree, discharge the empty stack, and
halt. -/
def taggedToBalancedFuel (values : List ℕ) : ℕ :=
  11 + 5 * values.length + balancedBuildFuel values

def taggedToBalancedInitialBoundFor
    (inputLength : ℕ) (values : List ℕ) : ℕ :=
  max 2 (max inputLength (encodeTaggedList values))

def taggedToBalancedInitialBound (values : List ℕ) : ℕ :=
  taggedToBalancedInitialBoundFor values.length values

def taggedToBalancedRegisterBitsFor
    (inputLength : ℕ) (values : List ℕ) : ℕ :=
  natBitLength
    (pairIter (taggedToBalancedFuel values)
      (taggedToBalancedInitialBoundFor inputLength values))

def taggedToBalancedRegisterBits (values : List ℕ) : ℕ :=
  taggedToBalancedRegisterBitsFor values.length values

theorem taggedToBalancedInitialBound_positive (values : List ℕ) :
    1 ≤ taggedToBalancedInitialBound values := by
  unfold taggedToBalancedInitialBound
  unfold taggedToBalancedInitialBoundFor
  omega

theorem taggedToBalancedRegisterBits_positive (values : List ℕ) :
    0 < taggedToBalancedRegisterBits values := by
  simp [taggedToBalancedRegisterBits, taggedToBalancedRegisterBitsFor,
    natBitLength]

structure PendingFrame where
  rightCount : ℕ
  leftCode : ℕ
  deriving DecidableEq, Repr

def encodePendingFrame (frame : PendingFrame) : ℕ :=
  Nat.pair frame.rightCount frame.leftCode

def encodePendingStack : List PendingFrame → ℕ
  | [] => 0
  | frame :: rest =>
      Nat.pair (encodePendingFrame frame) (encodePendingStack rest)

@[simp] theorem encodePendingStack_nil :
    encodePendingStack [] = 0 := rfl

@[simp] theorem encodePendingStack_cons
    (frame : PendingFrame) (rest : List PendingFrame) :
    encodePendingStack (frame :: rest) =
      Nat.pair (encodePendingFrame frame) (encodePendingStack rest) := rfl

theorem encodePendingStack_cons_ne_zero
    (frame : PendingFrame) (rest : List PendingFrame)
    (hpositive : 0 < frame.rightCount) :
    encodePendingStack (frame :: rest) ≠ 0 := by
  have hframe : 0 < encodePendingFrame frame := by
    unfold encodePendingFrame
    exact lt_of_lt_of_le hpositive
      (Nat.left_le_pair frame.rightCount frame.leftCode)
  have hstack :
      0 < Nat.pair (encodePendingFrame frame) (encodePendingStack rest) :=
    lt_of_lt_of_le hframe
      (Nat.left_le_pair (encodePendingFrame frame)
        (encodePendingStack rest))
  simpa only [encodePendingStack] using hstack.ne'

/-! ## Exact tagged-stream counting phase -/

private def countTaggedState : List ℕ → NPOracleState → NPOracleState
  | [], state => state.jump 10
  | value :: rest, state =>
      let payload := Nat.pair value (encodeTaggedList rest)
      let state1 := state.jump 6
      let state2 := (state1.write 4 payload).jump 7
      let state3 := (state2.write 0 (encodeTaggedList rest)).jump 8
      let state4 :=
        (state3.write 1 (state.registers 1 + 1)).jump 9
      let state5 := state4.jump 5
      countTaggedState rest state5

private theorem countTaggedState_pc
    (values : List ℕ) (state : NPOracleState) :
    (countTaggedState values state).pc = 10 := by
  induction values generalizing state with
  | nil => rfl
  | cons value rest ih =>
      exact ih _

private theorem countTaggedState_cursor
    (values : List ℕ) (state : NPOracleState)
    (hcursor : state.registers 0 = encodeTaggedList values) :
    (countTaggedState values state).registers 0 = 0 := by
  induction values generalizing state with
  | nil =>
      simpa [countTaggedState, encodeTaggedList] using hcursor
  | cons value rest ih =>
      apply ih
      simp [NPOracleState.write]

private theorem countTaggedState_count
    (values : List ℕ) (state : NPOracleState) :
    (countTaggedState values state).registers 1 =
      state.registers 1 + values.length := by
  induction values generalizing state with
  | nil =>
      simp [countTaggedState]
  | cons value rest ih =>
      simp only [countTaggedState]
      rw [ih]
      simp [NPOracleState.write]
      omega

private theorem countTaggedState_preserves
    (values : List ℕ) (state : NPOracleState) {register : ℕ}
    (hregister : register ≠ 0 ∧ register ≠ 1 ∧ register ≠ 4) :
    (countTaggedState values state).registers register =
      state.registers register := by
  induction values generalizing state with
  | nil => rfl
  | cons value rest ih =>
      simp only [countTaggedState]
      rw [ih]
      simp only [NPOracleState.jump, NPOracleState.write]
      simp [hregister.1, hregister.2.1, hregister.2.2]

theorem initialState_bounded
    (inputLength : ℕ) (values : List ℕ) :
    StateBoundedBy
      (taggedToBalancedInitialBoundFor inputLength values)
      (initialNPOracleState inputLength (encodeTaggedList values)) := by
  intro register
  by_cases hzero : register = 0
  · subst register
    simp [initialNPOracleState, taggedToBalancedInitialBoundFor]
  · by_cases hone : register = 1
    · subst register
      simp [initialNPOracleState, hzero, taggedToBalancedInitialBoundFor]
    · simp [initialNPOracleState, hzero, hone,
        taggedToBalancedInitialBoundFor]

private theorem run_countTaggedState
    (values : List ℕ) {maximumBits bound extraFuel : ℕ}
    (state : NPOracleState)
    (hpc : state.pc = 5)
    (hcursor : state.registers 0 = encodeTaggedList values)
    (hzero : state.registers 7 = 0)
    (hstate : StateBoundedBy bound state)
    (hbound : 1 ≤ bound)
    (hbits :
      natBitLength
          (pairIter (5 * values.length + 1 + extraFuel) bound) ≤
        maximumBits) :
    runNPOracleProgram taggedToBalancedProgram maximumBits
        (5 * values.length + 1 + extraFuel) state =
      runNPOracleProgram taggedToBalancedProgram maximumBits extraFuel
        (countTaggedState values state) ∧
    StateBoundedBy (pairIter (5 * values.length + 1) bound)
      (countTaggedState values state) := by
  induction values generalizing state bound with
  | nil =>
      have hstep :=
        runBranchZeroClocked
          (program := taggedToBalancedProgram)
          (maximumBits := maximumBits) (fuel := extraFuel)
          (bound := bound) (pc := 5) (register := 0)
          (zeroTarget := 10) (nonzeroTarget := 6)
          (by rfl) hpc hstate
      have hcursorZero : state.registers 0 = 0 := by
        simpa only [encodeTaggedList] using hcursor
      constructor
      · simpa [countTaggedState, hcursorZero,
          show 1 + extraFuel = extraFuel + 1 by omega] using hstep.1
      · simpa [countTaggedState, hcursorZero, pairIter] using hstep.2
  | cons value rest ih =>
      let tailSteps := 5 * rest.length + 1
      let totalSteps := 5 * (value :: rest).length + 1 + extraFuel
      let state1 := state.jump 6
      let payload := Nat.pair value (encodeTaggedList rest)
      let state2 := (state1.write 4 payload).jump 7
      let state3 :=
        (state2.write 0 (encodeTaggedList rest)).jump 8
      let state4 :=
        (state3.write 1 (state.registers 1 + 1)).jump 9
      let state5 := state4.jump 5
      have htotal :
          totalSteps = 5 + (tailSteps + extraFuel) := by
        simp [totalSteps, tailSteps]
        omega
      have hcursorNonzero : state.registers 0 ≠ 0 := by
        rw [hcursor]
        intro hzeroCode
        have hpositive :=
          Nat.left_le_pair 1
            (Nat.pair value (encodeTaggedList rest))
        simp only [encodeTaggedList] at hzeroCode
        rw [hzeroCode] at hpositive
        omega
      have hstep1 :=
        runBranchZeroClocked
          (program := taggedToBalancedProgram)
          (maximumBits := maximumBits)
          (fuel := 4 + (tailSteps + extraFuel))
          (bound := bound) (pc := 5) (register := 0)
          (zeroTarget := 10) (nonzeroTarget := 6)
          (by rfl) hpc hstate
      have hrun1 :
          runNPOracleProgram taggedToBalancedProgram maximumBits
              totalSteps state =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              (4 + (tailSteps + extraFuel)) state1 := by
        rw [htotal]
        simpa [state1, hcursorNonzero,
          show 5 + (tailSteps + extraFuel) =
            (4 + (tailSteps + extraFuel)) + 1 by omega] using hstep1.1
      have hstate1 :
          StateBoundedBy (pairIter 1 bound) state1 := by
        simpa [state1, hcursorNonzero, pairIter] using hstep1.2
      have hbits1 :
          natBitLength
              (pairIter (4 + (tailSteps + extraFuel))
                (pairIter 1 bound)) ≤ maximumBits := by
        apply pairIter_cap_suffix
          (total := totalSteps) (consumed := 1)
          (remaining := 4 + (tailSteps + extraFuel))
          (bound := bound)
        · omega
        · simpa only [totalSteps] using hbits
      have hstep2 :=
        runUnpairRightClocked
          (program := taggedToBalancedProgram)
          (maximumBits := maximumBits)
          (fuel := 3 + (tailSteps + extraFuel))
          (bound := pairIter 1 bound) (pc := 6)
          (source := 0) (destination := 4) (next := 7)
          (by rfl) (by rfl) hstate1 (by
            simpa only [show
              4 + (tailSteps + extraFuel) =
                (3 + (tailSteps + extraFuel)) + 1 by omega] using hbits1)
      have hrun2 :
          runNPOracleProgram taggedToBalancedProgram maximumBits
              (4 + (tailSteps + extraFuel)) state1 =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              (3 + (tailSteps + extraFuel)) state2 := by
        rw [show 4 + (tailSteps + extraFuel) =
          (3 + (tailSteps + extraFuel)) + 1 by omega]
        simpa [state2, state1, payload, hcursor, encodeTaggedList] using
          hstep2.1
      have hstate2 :
          StateBoundedBy (pairIter 2 bound) state2 := by
        simpa [state2, state1, payload, hcursor, encodeTaggedList,
          pairIter] using hstep2.2
      have hbits2 :
          natBitLength
              (pairIter (3 + (tailSteps + extraFuel))
                (pairIter 2 bound)) ≤ maximumBits := by
        apply pairIter_cap_suffix
          (total := totalSteps) (consumed := 2)
          (remaining := 3 + (tailSteps + extraFuel))
          (bound := bound)
        · omega
        · simpa only [totalSteps] using hbits
      have hstep3 :=
        runUnpairRightClocked
          (program := taggedToBalancedProgram)
          (maximumBits := maximumBits)
          (fuel := 2 + (tailSteps + extraFuel))
          (bound := pairIter 2 bound) (pc := 7)
          (source := 4) (destination := 0) (next := 8)
          (by rfl) (by rfl) hstate2 (by
            simpa only [show
              3 + (tailSteps + extraFuel) =
                (2 + (tailSteps + extraFuel)) + 1 by omega] using hbits2)
      have hrun3 :
          runNPOracleProgram taggedToBalancedProgram maximumBits
              (3 + (tailSteps + extraFuel)) state2 =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              (2 + (tailSteps + extraFuel)) state3 := by
        rw [show 3 + (tailSteps + extraFuel) =
          (2 + (tailSteps + extraFuel)) + 1 by omega]
        simpa [state3, state2, state1, payload, hcursor,
          encodeTaggedList] using hstep3.1
      have hstate3 :
          StateBoundedBy (pairIter 3 bound) state3 := by
        simpa [state3, state2, state1, payload, hcursor,
          encodeTaggedList, pairIter] using hstep3.2
      have hbits3 :
          natBitLength
              (pairIter (2 + (tailSteps + extraFuel))
                (pairIter 3 bound)) ≤ maximumBits := by
        apply pairIter_cap_suffix
          (total := totalSteps) (consumed := 3)
          (remaining := 2 + (tailSteps + extraFuel))
          (bound := bound)
        · omega
        · simpa only [totalSteps] using hbits
      have hstep4 :=
        runIncrementClocked
          (program := taggedToBalancedProgram)
          (maximumBits := maximumBits)
          (fuel := 1 + (tailSteps + extraFuel))
          (bound := pairIter 3 bound) (pc := 8)
          (register := 1) (next := 9)
          (by rfl) (by rfl) hstate3
          (one_le_pairIter 3 hbound) (by
            simpa only [show
              2 + (tailSteps + extraFuel) =
                (1 + (tailSteps + extraFuel)) + 1 by omega] using hbits3)
      have hrun4 :
          runNPOracleProgram taggedToBalancedProgram maximumBits
              (2 + (tailSteps + extraFuel)) state3 =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              (1 + (tailSteps + extraFuel)) state4 := by
        rw [show 2 + (tailSteps + extraFuel) =
          (1 + (tailSteps + extraFuel)) + 1 by omega]
        simpa [state4, state3, state2, state1] using hstep4.1
      have hstate4 :
          StateBoundedBy (pairIter 4 bound) state4 := by
        simpa [state4, state3, state2, state1, pairIter] using hstep4.2
      have hstep5 :=
        runBranchZeroClocked
          (program := taggedToBalancedProgram)
          (maximumBits := maximumBits)
          (fuel := tailSteps + extraFuel)
          (bound := pairIter 4 bound) (pc := 9) (register := 7)
          (zeroTarget := 5) (nonzeroTarget := 5)
          (by rfl) (by rfl) hstate4
      have hrun5 :
          runNPOracleProgram taggedToBalancedProgram maximumBits
              (1 + (tailSteps + extraFuel)) state4 =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              (tailSteps + extraFuel) state5 := by
        rw [show 1 + (tailSteps + extraFuel) =
          (tailSteps + extraFuel) + 1 by omega]
        simpa [state5, state4, state3, state2, state1] using hstep5.1
      have hstate5 :
          StateBoundedBy (pairIter 5 bound) state5 := by
        simpa [state5, state4, state3, state2, state1, pairIter] using
          hstep5.2
      have hbits5 :
          natBitLength
              (pairIter (tailSteps + extraFuel) (pairIter 5 bound)) ≤
            maximumBits := by
        apply pairIter_cap_suffix
          (total := totalSteps) (consumed := 5)
          (remaining := tailSteps + extraFuel)
          (bound := bound)
        · omega
        · simpa only [totalSteps] using hbits
      have hcursor5 :
          state5.registers 0 = encodeTaggedList rest := by
        simp [state5, state4, state3]
      have hzero5 : state5.registers 7 = 0 := by
        simp [state5, state4, state3, state2, state1, hzero]
      have htail :=
        ih (bound := pairIter 5 bound) state5 (by rfl) hcursor5 hzero5
          hstate5 (one_le_pairIter 5 hbound)
          (by simpa only [tailSteps] using hbits5)
      constructor
      · calc
          runNPOracleProgram taggedToBalancedProgram maximumBits
              (5 * (value :: rest).length + 1 + extraFuel) state =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              totalSteps state := by rfl
          _ =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              (4 + (tailSteps + extraFuel)) state1 := hrun1
          _ =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              (3 + (tailSteps + extraFuel)) state2 := hrun2
          _ =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              (2 + (tailSteps + extraFuel)) state3 := hrun3
          _ =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              (1 + (tailSteps + extraFuel)) state4 := hrun4
          _ =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              (tailSteps + extraFuel) state5 := hrun5
          _ =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              extraFuel (countTaggedState rest state5) := htail.1
          _ =
            runNPOracleProgram taggedToBalancedProgram maximumBits
              extraFuel
                (countTaggedState (value :: rest) state) := by rfl
      · change
          StateBoundedBy
            (pairIter (5 * (value :: rest).length + 1) bound)
              (countTaggedState rest state5)
        rw [show 5 * (value :: rest).length + 1 =
          5 + tailSteps by
            simp [tailSteps]
            omega]
        rw [pairIter_add]
        simpa only [tailSteps] using htail.2

/-! ## Canonical midpoint build phase -/

private def emptyBuildState (state : NPOracleState) : NPOracleState :=
  let state1 := state.jump 14
  let state2 := (state1.write 3 0).jump 15
  state2.jump 29

private theorem run_emptyBuildState
    {maximumBits bound extraFuel : ℕ} (state : NPOracleState)
    (hpc : state.pc = 13)
    (hcount : state.registers 1 = 0)
    (hstate : StateBoundedBy bound state)
    (hbits :
      natBitLength (pairIter (3 + extraFuel) bound) ≤ maximumBits) :
    runNPOracleProgram taggedToBalancedProgram maximumBits
        (3 + extraFuel) state =
      runNPOracleProgram taggedToBalancedProgram maximumBits extraFuel
        (emptyBuildState state) ∧
    StateBoundedBy (pairIter 3 bound) (emptyBuildState state) := by
  let state1 := state.jump 14
  let state2 := (state1.write 3 0).jump 15
  let state3 := state2.jump 29
  have hstep1 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 2 + extraFuel)
      (bound := bound) (pc := 13) (register := 1)
      (zeroTarget := 14) (nonzeroTarget := 16)
      (by rfl) hpc hstate
  have hrun1 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state1 := by
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    simpa [state1, hcount] using hstep1.1
  have hstate1 : StateBoundedBy (pairIter 1 bound) state1 := by
    simpa [state1, hcount, pairIter] using hstep1.2
  have hbits1 :
      natBitLength
          (pairIter (2 + extraFuel) (pairIter 1 bound)) ≤
        maximumBits := by
    apply pairIter_cap_suffix
      (total := 3 + extraFuel) (consumed := 1)
      (remaining := 2 + extraFuel) (bound := bound)
    · omega
    · exact hbits
  have hstep2 :=
    runSetClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 1 + extraFuel)
      (bound := pairIter 1 bound) (pc := 14)
      (register := 3) (value := 0) (next := 15)
      (by rfl) (by rfl) hstate1 (Nat.zero_le _) (by
        simpa only [show
          2 + extraFuel = (1 + extraFuel) + 1 by omega] using hbits1)
  have hrun2 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state1 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state2 := by
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    simpa [state2, state1] using hstep2.1
  have hstate2 : StateBoundedBy (pairIter 2 bound) state2 := by
    simpa [state2, state1, pairIter] using hstep2.2
  have hstep3 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := extraFuel)
      (bound := pairIter 2 bound) (pc := 15) (register := 7)
      (zeroTarget := 29) (nonzeroTarget := 29)
      (by rfl) (by rfl) hstate2
  have hrun3 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state2 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel state3 := by
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    simpa [state3, state2] using hstep3.1
  have hstate3 : StateBoundedBy (pairIter 3 bound) state3 := by
    simpa [state3, state2, pairIter] using hstep3.2
  constructor
  · calc
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state1 := hrun1
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state2 := hrun2
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel state3 := hrun3
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel (emptyBuildState state) := by rfl
  · simpa [emptyBuildState, state1, state2, state3] using hstate3

private def leafBuildState
    (value : ℕ) (suffix : List ℕ)
    (state : NPOracleState) : NPOracleState :=
  let state1 := state.jump 16
  let state2 := (state1.write 4 1).jump 17
  let state3 := (state2.write 4 0).jump 18
  let state4 := state3.jump 19
  let payload := Nat.pair value (encodeTaggedList suffix)
  let state5 := (state4.write 5 payload).jump 20
  let state6 := (state5.write 3 value).jump 21
  let state7 := (state6.write 0 (encodeTaggedList suffix)).jump 22
  (state7.write 3 (Nat.pair 1 value)).jump 29

private theorem run_leafBuildState
    (value : ℕ) (suffix : List ℕ)
    {maximumBits bound extraFuel : ℕ} (state : NPOracleState)
    (hpc : state.pc = 13)
    (hcount : state.registers 1 = 1)
    (hcursor :
      state.registers 0 = encodeTaggedList (value :: suffix))
    (hone : state.registers 9 = 1)
    (hstate : StateBoundedBy bound state)
    (hbits :
      natBitLength (pairIter (8 + extraFuel) bound) ≤ maximumBits) :
    runNPOracleProgram taggedToBalancedProgram maximumBits
        (8 + extraFuel) state =
      runNPOracleProgram taggedToBalancedProgram maximumBits extraFuel
        (leafBuildState value suffix state) ∧
    StateBoundedBy (pairIter 8 bound)
      (leafBuildState value suffix state) := by
  let state1 := state.jump 16
  let state2 := (state1.write 4 1).jump 17
  let state3 := (state2.write 4 0).jump 18
  let state4 := state3.jump 19
  let payload := Nat.pair value (encodeTaggedList suffix)
  let state5 := (state4.write 5 payload).jump 20
  let state6 := (state5.write 3 value).jump 21
  let state7 := (state6.write 0 (encodeTaggedList suffix)).jump 22
  let state8 := (state7.write 3 (Nat.pair 1 value)).jump 29
  have hbitsAfter :
      ∀ consumed remaining,
        8 + extraFuel = consumed + remaining →
        natBitLength
            (pairIter remaining (pairIter consumed bound)) ≤
          maximumBits := by
    intro consumed remaining htotal
    exact pairIter_cap_suffix htotal hbits
  have hstep1 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 7 + extraFuel)
      (bound := bound) (pc := 13) (register := 1)
      (zeroTarget := 14) (nonzeroTarget := 16)
      (by rfl) hpc hstate
  have hrun1 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (8 + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state1 := by
    rw [show 8 + extraFuel = (7 + extraFuel) + 1 by omega]
    simpa [state1, hcount] using hstep1.1
  have hstate1 : StateBoundedBy (pairIter 1 bound) state1 := by
    simpa [state1, hcount, pairIter] using hstep1.2
  have hstep2 :=
    runCopyClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 6 + extraFuel)
      (bound := pairIter 1 bound) (pc := 16)
      (source := 1) (destination := 4) (next := 17)
      (by rfl) (by rfl) hstate1 (by
        simpa only [show
          7 + extraFuel = (6 + extraFuel) + 1 by omega] using
            hbitsAfter 1 (7 + extraFuel) (by omega))
  have hrun2 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state1 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state2 := by
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    simpa [state2, state1, hcount] using hstep2.1
  have hstate2 : StateBoundedBy (pairIter 2 bound) state2 := by
    simpa [state2, state1, hcount, pairIter] using hstep2.2
  have hstep3 :=
    runDecrementClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 5 + extraFuel)
      (bound := pairIter 2 bound) (pc := 17)
      (register := 4) (next := 18)
      (by rfl) (by rfl) hstate2 (by
        simpa only [show
          6 + extraFuel = (5 + extraFuel) + 1 by omega] using
            hbitsAfter 2 (6 + extraFuel) (by omega))
  have hrun3 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state2 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state3 := by
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    simpa [state3, state2, state1] using hstep3.1
  have hstate3 : StateBoundedBy (pairIter 3 bound) state3 := by
    simpa [state3, state2, state1, pairIter] using hstep3.2
  have hstep4 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 4 + extraFuel)
      (bound := pairIter 3 bound) (pc := 18) (register := 4)
      (zeroTarget := 19) (nonzeroTarget := 23)
      (by rfl) (by rfl) hstate3
  have hrun4 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state3 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state4 := by
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    simpa [state4, state3, state2, state1] using hstep4.1
  have hstate4 : StateBoundedBy (pairIter 4 bound) state4 := by
    simpa [state4, state3, state2, state1, pairIter] using hstep4.2
  have hstep5 :=
    runUnpairRightClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 3 + extraFuel)
      (bound := pairIter 4 bound) (pc := 19)
      (source := 0) (destination := 5) (next := 20)
      (by rfl) (by rfl) hstate4 (by
        simpa only [show
          4 + extraFuel = (3 + extraFuel) + 1 by omega] using
            hbitsAfter 4 (4 + extraFuel) (by omega))
  have hrun5 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state4 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state5 := by
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    simpa [state5, state4, state3, state2, state1, payload, hcursor,
      encodeTaggedList] using hstep5.1
  have hstate5 : StateBoundedBy (pairIter 5 bound) state5 := by
    simpa [state5, state4, state3, state2, state1, payload, hcursor,
      encodeTaggedList, pairIter] using hstep5.2
  have hstep6 :=
    runUnpairLeftClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 2 + extraFuel)
      (bound := pairIter 5 bound) (pc := 20)
      (source := 5) (destination := 3) (next := 21)
      (by rfl) (by rfl) hstate5 (by
        simpa only [show
          3 + extraFuel = (2 + extraFuel) + 1 by omega] using
            hbitsAfter 5 (3 + extraFuel) (by omega))
  have hrun6 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state5 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state6 := by
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    simpa [state6, state5, payload] using hstep6.1
  have hstate6 : StateBoundedBy (pairIter 6 bound) state6 := by
    simpa [state6, state5, payload, pairIter] using hstep6.2
  have hstep7 :=
    runUnpairRightClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 1 + extraFuel)
      (bound := pairIter 6 bound) (pc := 21)
      (source := 5) (destination := 0) (next := 22)
      (by rfl) (by rfl) hstate6 (by
        simpa only [show
          2 + extraFuel = (1 + extraFuel) + 1 by omega] using
            hbitsAfter 6 (2 + extraFuel) (by omega))
  have hrun7 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state6 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state7 := by
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    simpa [state7, state6, state5, payload] using hstep7.1
  have hstate7 : StateBoundedBy (pairIter 7 bound) state7 := by
    simpa [state7, state6, state5, payload, pairIter] using hstep7.2
  have hstep8 :=
    runPairClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := extraFuel)
      (bound := pairIter 7 bound) (pc := 22)
      (left := 9) (right := 3) (destination := 3) (next := 29)
      (by rfl) (by rfl) hstate7 (by
        simpa only [show
          1 + extraFuel = extraFuel + 1 by omega] using
            hbitsAfter 7 (1 + extraFuel) (by omega))
  have hrun8 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state7 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel state8 := by
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    simpa [state8, state7, state6, state5, state4, state3, state2,
      state1, hone] using hstep8.1
  have hstate8 : StateBoundedBy (pairIter 8 bound) state8 := by
    simpa [state8, state7, state6, state5, state4, state3, state2,
      state1, hone, pairIter] using hstep8.2
  constructor
  · calc
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (8 + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state1 := hrun1
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state2 := hrun2
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state3 := hrun3
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state4 := hrun4
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state5 := hrun5
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state6 := hrun6
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state7 := hrun7
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel state8 := hrun8
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel (leafBuildState value suffix state) := by rfl
  · simpa [leafBuildState, state1, state2, state3, state4, state5,
      state6, state7, state8, payload] using hstate8

private def descendBranchState
    (count : ℕ) (stack : List PendingFrame)
    (state : NPOracleState) : NPOracleState :=
  let rightCount := Nat.shiftRight count 1
  let leftCount := Nat.shiftRight (count + 1) 1
  let frame := Nat.pair rightCount 0
  let nextStack := Nat.pair frame (encodePendingStack stack)
  let state1 := state.jump 16
  let state2 := (state1.write 4 count).jump 17
  let state3 := (state2.write 4 count.pred).jump 18
  let state4 := state3.jump 23
  let state5 := (state4.write 4 rightCount).jump 24
  let state6 := (state5.write 1 (count + 1)).jump 25
  let state7 := (state6.write 1 leftCount).jump 26
  let state8 := (state7.write 5 frame).jump 27
  let state9 := (state8.write 2 nextStack).jump 28
  state9.jump 13

private theorem run_descendBranchState
    (count : ℕ) (stack : List PendingFrame)
    {maximumBits bound extraFuel : ℕ} (state : NPOracleState)
    (hpc : state.pc = 13)
    (hcount : state.registers 1 = count)
    (hstack : state.registers 2 = encodePendingStack stack)
    (hzero : state.registers 7 = 0)
    (htwo : 2 ≤ count)
    (hstate : StateBoundedBy bound state)
    (hbound : 1 ≤ bound)
    (hbits :
      natBitLength (pairIter (10 + extraFuel) bound) ≤ maximumBits) :
    runNPOracleProgram taggedToBalancedProgram maximumBits
        (10 + extraFuel) state =
      runNPOracleProgram taggedToBalancedProgram maximumBits extraFuel
        (descendBranchState count stack state) ∧
    StateBoundedBy (pairIter 10 bound)
      (descendBranchState count stack state) := by
  let rightCount := Nat.shiftRight count 1
  let leftCount := Nat.shiftRight (count + 1) 1
  let frame := Nat.pair rightCount 0
  let nextStack := Nat.pair frame (encodePendingStack stack)
  let state1 := state.jump 16
  let state2 := (state1.write 4 count).jump 17
  let state3 := (state2.write 4 count.pred).jump 18
  let state4 := state3.jump 23
  let state5 := (state4.write 4 rightCount).jump 24
  let state6 := (state5.write 1 (count + 1)).jump 25
  let state7 := (state6.write 1 leftCount).jump 26
  let state8 := (state7.write 5 frame).jump 27
  let state9 := (state8.write 2 nextStack).jump 28
  let state10 := state9.jump 13
  have hbitsAfter :
      ∀ consumed remaining,
        10 + extraFuel = consumed + remaining →
        natBitLength
            (pairIter remaining (pairIter consumed bound)) ≤
          maximumBits := by
    intro consumed remaining htotal
    exact pairIter_cap_suffix htotal hbits
  have hcountNonzero : state.registers 1 ≠ 0 := by omega
  have hpredNonzero : count - 1 ≠ 0 := by omega
  have hstep1 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 9 + extraFuel)
      (bound := bound) (pc := 13) (register := 1)
      (zeroTarget := 14) (nonzeroTarget := 16)
      (by rfl) hpc hstate
  have hrun1 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (10 + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (9 + extraFuel) state1 := by
    rw [show 10 + extraFuel = (9 + extraFuel) + 1 by omega]
    simpa [state1, hcountNonzero] using hstep1.1
  have hstate1 : StateBoundedBy (pairIter 1 bound) state1 := by
    simpa [state1, hcountNonzero, pairIter] using hstep1.2
  have hstep2 :=
    runCopyClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 8 + extraFuel)
      (bound := pairIter 1 bound) (pc := 16)
      (source := 1) (destination := 4) (next := 17)
      (by rfl) (by rfl) hstate1 (by
        simpa only [show
          9 + extraFuel = (8 + extraFuel) + 1 by omega] using
            hbitsAfter 1 (9 + extraFuel) (by omega))
  have hrun2 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (9 + extraFuel) state1 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (8 + extraFuel) state2 := by
    rw [show 9 + extraFuel = (8 + extraFuel) + 1 by omega]
    simpa [state2, state1, hcount] using hstep2.1
  have hstate2 : StateBoundedBy (pairIter 2 bound) state2 := by
    simpa [state2, state1, hcount, pairIter] using hstep2.2
  have hstep3 :=
    runDecrementClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 7 + extraFuel)
      (bound := pairIter 2 bound) (pc := 17)
      (register := 4) (next := 18)
      (by rfl) (by rfl) hstate2 (by
        simpa only [show
          8 + extraFuel = (7 + extraFuel) + 1 by omega] using
            hbitsAfter 2 (8 + extraFuel) (by omega))
  have hrun3 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (8 + extraFuel) state2 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state3 := by
    rw [show 8 + extraFuel = (7 + extraFuel) + 1 by omega]
    simpa [state3, state2, state1] using hstep3.1
  have hstate3 : StateBoundedBy (pairIter 3 bound) state3 := by
    simpa [state3, state2, state1, pairIter] using hstep3.2
  have hstep4 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 6 + extraFuel)
      (bound := pairIter 3 bound) (pc := 18) (register := 4)
      (zeroTarget := 19) (nonzeroTarget := 23)
      (by rfl) (by rfl) hstate3
  have hrun4 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state3 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state4 := by
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    simpa [state4, state3, state2, state1, hpredNonzero] using hstep4.1
  have hstate4 : StateBoundedBy (pairIter 4 bound) state4 := by
    simpa [state4, state3, state2, state1, hpredNonzero,
      pairIter] using hstep4.2
  have hstep5 :=
    runShiftRightClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 5 + extraFuel)
      (bound := pairIter 4 bound) (pc := 23)
      (source := 1) (amount := 1) (destination := 4) (next := 24)
      (by rfl) (by rfl) hstate4 (by
        simpa only [show
          6 + extraFuel = (5 + extraFuel) + 1 by omega] using
            hbitsAfter 4 (6 + extraFuel) (by omega))
  have hrun5 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state4 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state5 := by
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    simpa [state5, state4, state3, state2, state1, rightCount,
      hcount] using hstep5.1
  have hstate5 : StateBoundedBy (pairIter 5 bound) state5 := by
    simpa [state5, state4, state3, state2, state1, rightCount,
      hcount, pairIter] using hstep5.2
  have hstep6 :=
    runIncrementClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 4 + extraFuel)
      (bound := pairIter 5 bound) (pc := 24)
      (register := 1) (next := 25)
      (by rfl) (by rfl) hstate5
      (one_le_pairIter 5 hbound) (by
        simpa only [show
          5 + extraFuel = (4 + extraFuel) + 1 by omega] using
            hbitsAfter 5 (5 + extraFuel) (by omega))
  have hrun6 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state5 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state6 := by
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    simpa [state6, state5, state4, state3, state2, state1,
      hcount] using hstep6.1
  have hstate6 : StateBoundedBy (pairIter 6 bound) state6 := by
    simpa [state6, state5, state4, state3, state2, state1,
      hcount, pairIter] using hstep6.2
  have hstep7 :=
    runShiftRightClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 3 + extraFuel)
      (bound := pairIter 6 bound) (pc := 25)
      (source := 1) (amount := 1) (destination := 1) (next := 26)
      (by rfl) (by rfl) hstate6 (by
        simpa only [show
          4 + extraFuel = (3 + extraFuel) + 1 by omega] using
            hbitsAfter 6 (4 + extraFuel) (by omega))
  have hrun7 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state6 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state7 := by
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    simpa [state7, state6, state5, state4, state3, state2, state1,
      leftCount, hcount] using hstep7.1
  have hstate7 : StateBoundedBy (pairIter 7 bound) state7 := by
    simpa [state7, state6, state5, state4, state3, state2, state1,
      leftCount, hcount, pairIter] using hstep7.2
  have hstep8 :=
    runPairClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 2 + extraFuel)
      (bound := pairIter 7 bound) (pc := 26)
      (left := 4) (right := 7) (destination := 5) (next := 27)
      (by rfl) (by rfl) hstate7 (by
        simpa only [show
          3 + extraFuel = (2 + extraFuel) + 1 by omega] using
            hbitsAfter 7 (3 + extraFuel) (by omega))
  have hrun8 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state7 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state8 := by
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    simpa [state8, state7, state6, state5, state4, state3, state2,
      state1, frame, rightCount, hzero] using hstep8.1
  have hstate8 : StateBoundedBy (pairIter 8 bound) state8 := by
    simpa [state8, state7, state6, state5, state4, state3, state2,
      state1, frame, rightCount, hzero, pairIter] using hstep8.2
  have hstep9 :=
    runPairClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 1 + extraFuel)
      (bound := pairIter 8 bound) (pc := 27)
      (left := 5) (right := 2) (destination := 2) (next := 28)
      (by rfl) (by rfl) hstate8 (by
        simpa only [show
          2 + extraFuel = (1 + extraFuel) + 1 by omega] using
            hbitsAfter 8 (2 + extraFuel) (by omega))
  have hrun9 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state8 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state9 := by
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    simpa [state9, state8, state7, state6, state5, state4, state3,
      state2, state1, nextStack, frame, rightCount, hstack] using hstep9.1
  have hstate9 : StateBoundedBy (pairIter 9 bound) state9 := by
    simpa [state9, state8, state7, state6, state5, state4, state3,
      state2, state1, nextStack, frame, rightCount, hstack,
      pairIter] using hstep9.2
  have hstep10 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := extraFuel)
      (bound := pairIter 9 bound) (pc := 28) (register := 7)
      (zeroTarget := 13) (nonzeroTarget := 13)
      (by rfl) (by rfl) hstate9
  have hrun10 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state9 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel state10 := by
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    simpa [state10, state9] using hstep10.1
  have hstate10 : StateBoundedBy (pairIter 10 bound) state10 := by
    simpa [state10, state9, pairIter] using hstep10.2
  constructor
  · calc
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (10 + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (9 + extraFuel) state1 := hrun1
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (8 + extraFuel) state2 := hrun2
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state3 := hrun3
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state4 := hrun4
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state5 := hrun5
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state6 := hrun6
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state7 := hrun7
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state8 := hrun8
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state9 := hrun9
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel state10 := hrun10
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel (descendBranchState count stack state) := by rfl
  · simpa [descendBranchState, rightCount, leftCount, frame, nextStack,
      state1, state2, state3, state4, state5, state6, state7, state8,
      state9, state10] using hstate10

private def resumeRightState
    (rightCount leftCode : ℕ) (stack : List PendingFrame)
    (state : NPOracleState) : NPOracleState :=
  let pending := Nat.pair rightCount 0
  let restCode := encodePendingStack stack
  let updated := Nat.pair rightCount leftCode
  let nextStack := Nat.pair updated restCode
  let state1 := state.jump 30
  let state2 := (state1.write 5 pending).jump 31
  let state3 := (state2.write 2 restCode).jump 32
  let state4 := (state3.write 4 rightCount).jump 33
  let state5 := (state4.write 6 0).jump 34
  let state6 := state5.jump 35
  let state7 := (state6.write 6 leftCode).jump 36
  let state8 := (state7.write 5 updated).jump 37
  let state9 := (state8.write 2 nextStack).jump 38
  let state10 := (state9.write 1 rightCount).jump 39
  state10.jump 13

private theorem run_resumeRightState
    (rightCount leftCode : ℕ) (stack : List PendingFrame)
    {maximumBits bound extraFuel : ℕ} (state : NPOracleState)
    (hpc : state.pc = 29)
    (hstack :
      state.registers 2 =
        encodePendingStack
          ({ rightCount := rightCount, leftCode := 0 } :: stack))
    (hresult : state.registers 3 = leftCode)
    (hright : 0 < rightCount)
    (hstate : StateBoundedBy bound state)
    (hbits :
      natBitLength (pairIter (11 + extraFuel) bound) ≤ maximumBits) :
    runNPOracleProgram taggedToBalancedProgram maximumBits
        (11 + extraFuel) state =
      runNPOracleProgram taggedToBalancedProgram maximumBits extraFuel
        (resumeRightState rightCount leftCode stack state) ∧
    StateBoundedBy (pairIter 11 bound)
      (resumeRightState rightCount leftCode stack state) := by
  let pending := Nat.pair rightCount 0
  let restCode := encodePendingStack stack
  let updated := Nat.pair rightCount leftCode
  let nextStack := Nat.pair updated restCode
  let state1 := state.jump 30
  let state2 := (state1.write 5 pending).jump 31
  let state3 := (state2.write 2 restCode).jump 32
  let state4 := (state3.write 4 rightCount).jump 33
  let state5 := (state4.write 6 0).jump 34
  let state6 := state5.jump 35
  let state7 := (state6.write 6 leftCode).jump 36
  let state8 := (state7.write 5 updated).jump 37
  let state9 := (state8.write 2 nextStack).jump 38
  let state10 := (state9.write 1 rightCount).jump 39
  let state11 := state10.jump 13
  have hbitsAfter :
      ∀ consumed remaining,
        11 + extraFuel = consumed + remaining →
        natBitLength
            (pairIter remaining (pairIter consumed bound)) ≤
          maximumBits := by
    intro consumed remaining htotal
    exact pairIter_cap_suffix htotal hbits
  have hstackNonzero : state.registers 2 ≠ 0 := by
    rw [hstack]
    exact encodePendingStack_cons_ne_zero _ _ hright
  have hstep1 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 10 + extraFuel)
      (bound := bound) (pc := 29) (register := 2)
      (zeroTarget := 42) (nonzeroTarget := 30)
      (by rfl) hpc hstate
  have hrun1 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (11 + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (10 + extraFuel) state1 := by
    rw [show 11 + extraFuel = (10 + extraFuel) + 1 by omega]
    simpa [state1, hstackNonzero] using hstep1.1
  have hstate1 : StateBoundedBy (pairIter 1 bound) state1 := by
    simpa [state1, hstackNonzero, pairIter] using hstep1.2
  have hstep2 :=
    runUnpairLeftClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 9 + extraFuel)
      (bound := pairIter 1 bound) (pc := 30)
      (source := 2) (destination := 5) (next := 31)
      (by rfl) (by rfl) hstate1 (by
        simpa only [show
          10 + extraFuel = (9 + extraFuel) + 1 by omega] using
            hbitsAfter 1 (10 + extraFuel) (by omega))
  have hrun2 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (10 + extraFuel) state1 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (9 + extraFuel) state2 := by
    rw [show 10 + extraFuel = (9 + extraFuel) + 1 by omega]
    simpa [state2, state1, pending, restCode, hstack,
      encodePendingFrame] using hstep2.1
  have hstate2 : StateBoundedBy (pairIter 2 bound) state2 := by
    simpa [state2, state1, pending, restCode, hstack,
      encodePendingFrame, pairIter] using hstep2.2
  have hstep3 :=
    runUnpairRightClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 8 + extraFuel)
      (bound := pairIter 2 bound) (pc := 31)
      (source := 2) (destination := 2) (next := 32)
      (by rfl) (by rfl) hstate2 (by
        simpa only [show
          9 + extraFuel = (8 + extraFuel) + 1 by omega] using
            hbitsAfter 2 (9 + extraFuel) (by omega))
  have hrun3 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (9 + extraFuel) state2 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (8 + extraFuel) state3 := by
    rw [show 9 + extraFuel = (8 + extraFuel) + 1 by omega]
    simpa [state3, state2, state1, pending, restCode, hstack,
      encodePendingFrame] using hstep3.1
  have hstate3 : StateBoundedBy (pairIter 3 bound) state3 := by
    simpa [state3, state2, state1, pending, restCode, hstack,
      encodePendingFrame, pairIter] using hstep3.2
  have hstep4 :=
    runUnpairLeftClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 7 + extraFuel)
      (bound := pairIter 3 bound) (pc := 32)
      (source := 5) (destination := 4) (next := 33)
      (by rfl) (by rfl) hstate3 (by
        simpa only [show
          8 + extraFuel = (7 + extraFuel) + 1 by omega] using
            hbitsAfter 3 (8 + extraFuel) (by omega))
  have hrun4 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (8 + extraFuel) state3 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state4 := by
    rw [show 8 + extraFuel = (7 + extraFuel) + 1 by omega]
    simpa [state4, state3, state2, pending] using hstep4.1
  have hstate4 : StateBoundedBy (pairIter 4 bound) state4 := by
    simpa [state4, state3, state2, pending, pairIter] using hstep4.2
  have hstep5 :=
    runUnpairRightClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 6 + extraFuel)
      (bound := pairIter 4 bound) (pc := 33)
      (source := 5) (destination := 6) (next := 34)
      (by rfl) (by rfl) hstate4 (by
        simpa only [show
          7 + extraFuel = (6 + extraFuel) + 1 by omega] using
            hbitsAfter 4 (7 + extraFuel) (by omega))
  have hrun5 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state4 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state5 := by
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    simpa [state5, state4, state3, state2, pending] using hstep5.1
  have hstate5 : StateBoundedBy (pairIter 5 bound) state5 := by
    simpa [state5, state4, state3, state2, pending, pairIter] using
      hstep5.2
  have hstep6 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 5 + extraFuel)
      (bound := pairIter 5 bound) (pc := 34) (register := 6)
      (zeroTarget := 35) (nonzeroTarget := 40)
      (by rfl) (by rfl) hstate5
  have hrun6 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state5 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state6 := by
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    simpa [state6, state5, state4, state3, state2, pending] using
      hstep6.1
  have hstate6 : StateBoundedBy (pairIter 6 bound) state6 := by
    simpa [state6, state5, state4, state3, state2, pending,
      pairIter] using hstep6.2
  have hstep7 :=
    runCopyClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 4 + extraFuel)
      (bound := pairIter 6 bound) (pc := 35)
      (source := 3) (destination := 6) (next := 36)
      (by rfl) (by rfl) hstate6 (by
        simpa only [show
          5 + extraFuel = (4 + extraFuel) + 1 by omega] using
            hbitsAfter 6 (5 + extraFuel) (by omega))
  have hrun7 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state6 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state7 := by
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    simpa [state7, state6, state5, state4, state3, state2, state1,
      hresult] using hstep7.1
  have hstate7 : StateBoundedBy (pairIter 7 bound) state7 := by
    simpa [state7, state6, state5, state4, state3, state2, state1,
      hresult, pairIter] using hstep7.2
  have hstep8 :=
    runPairClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 3 + extraFuel)
      (bound := pairIter 7 bound) (pc := 36)
      (left := 4) (right := 6) (destination := 5) (next := 37)
      (by rfl) (by rfl) hstate7 (by
        simpa only [show
          4 + extraFuel = (3 + extraFuel) + 1 by omega] using
            hbitsAfter 7 (4 + extraFuel) (by omega))
  have hrun8 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state7 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state8 := by
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    simpa [state8, state7, state6, state5, state4, state3, state2,
      state1, updated, pending] using hstep8.1
  have hstate8 : StateBoundedBy (pairIter 8 bound) state8 := by
    simpa [state8, state7, state6, state5, state4, state3, state2,
      state1, updated, pending, pairIter] using hstep8.2
  have hstep9 :=
    runPairClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 2 + extraFuel)
      (bound := pairIter 8 bound) (pc := 37)
      (left := 5) (right := 2) (destination := 2) (next := 38)
      (by rfl) (by rfl) hstate8 (by
        simpa only [show
          3 + extraFuel = (2 + extraFuel) + 1 by omega] using
            hbitsAfter 8 (3 + extraFuel) (by omega))
  have hrun9 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state8 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state9 := by
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    simpa [state9, state8, state7, state6, state5, state4, state3,
      state2, state1, nextStack, updated, restCode] using hstep9.1
  have hstate9 : StateBoundedBy (pairIter 9 bound) state9 := by
    simpa [state9, state8, state7, state6, state5, state4, state3,
      state2, state1, nextStack, updated, restCode, pairIter] using
      hstep9.2
  have hstep10 :=
    runCopyClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 1 + extraFuel)
      (bound := pairIter 9 bound) (pc := 38)
      (source := 4) (destination := 1) (next := 39)
      (by rfl) (by rfl) hstate9 (by
        simpa only [show
          2 + extraFuel = (1 + extraFuel) + 1 by omega] using
            hbitsAfter 9 (2 + extraFuel) (by omega))
  have hrun10 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state9 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state10 := by
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    simpa [state10, state9, state8, state7, state6, state5, state4,
      state3, state2, state1] using hstep10.1
  have hstate10 : StateBoundedBy (pairIter 10 bound) state10 := by
    simpa [state10, state9, state8, state7, state6, state5, state4,
      state3, state2, state1, pairIter] using hstep10.2
  have hstep11 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := extraFuel)
      (bound := pairIter 10 bound) (pc := 39) (register := 7)
      (zeroTarget := 13) (nonzeroTarget := 13)
      (by rfl) (by rfl) hstate10
  have hrun11 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state10 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel state11 := by
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    simpa [state11, state10] using hstep11.1
  have hstate11 : StateBoundedBy (pairIter 11 bound) state11 := by
    simpa [state11, state10, pairIter] using hstep11.2
  constructor
  · calc
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (11 + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (10 + extraFuel) state1 := hrun1
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (9 + extraFuel) state2 := hrun2
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (8 + extraFuel) state3 := hrun3
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state4 := hrun4
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state5 := hrun5
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state6 := hrun6
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state7 := hrun7
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state8 := hrun8
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state9 := hrun9
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state10 := hrun10
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel state11 := hrun11
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel
            (resumeRightState rightCount leftCode stack state) := by rfl
  · simpa [resumeRightState, pending, restCode, updated, nextStack,
      state1, state2, state3, state4, state5, state6, state7, state8,
      state9, state10, state11] using hstate11

private def combineBranchState
    (rightCount leftCode rightCode : ℕ)
    (stack : List PendingFrame) (state : NPOracleState) :
    NPOracleState :=
  let pending := Nat.pair rightCount leftCode
  let restCode := encodePendingStack stack
  let branches := Nat.pair leftCode rightCode
  let result := Nat.pair 2 branches
  let state1 := state.jump 30
  let state2 := (state1.write 5 pending).jump 31
  let state3 := (state2.write 2 restCode).jump 32
  let state4 := (state3.write 4 rightCount).jump 33
  let state5 := (state4.write 6 leftCode).jump 34
  let state6 := state5.jump 40
  let state7 := (state6.write 5 branches).jump 41
  (state7.write 3 result).jump 29

private theorem run_combineBranchState
    (rightCount leftCode rightCode : ℕ)
    (stack : List PendingFrame)
    {maximumBits bound extraFuel : ℕ} (state : NPOracleState)
    (hpc : state.pc = 29)
    (hstack :
      state.registers 2 =
        encodePendingStack
          ({ rightCount := rightCount, leftCode := leftCode } :: stack))
    (hresult : state.registers 3 = rightCode)
    (htwo : state.registers 10 = 2)
    (hright : 0 < rightCount)
    (hleft : leftCode ≠ 0)
    (hstate : StateBoundedBy bound state)
    (hbits :
      natBitLength (pairIter (8 + extraFuel) bound) ≤ maximumBits) :
    runNPOracleProgram taggedToBalancedProgram maximumBits
        (8 + extraFuel) state =
      runNPOracleProgram taggedToBalancedProgram maximumBits extraFuel
        (combineBranchState rightCount leftCode rightCode stack state) ∧
    StateBoundedBy (pairIter 8 bound)
      (combineBranchState rightCount leftCode rightCode stack state) := by
  let pending := Nat.pair rightCount leftCode
  let restCode := encodePendingStack stack
  let branches := Nat.pair leftCode rightCode
  let result := Nat.pair 2 branches
  let state1 := state.jump 30
  let state2 := (state1.write 5 pending).jump 31
  let state3 := (state2.write 2 restCode).jump 32
  let state4 := (state3.write 4 rightCount).jump 33
  let state5 := (state4.write 6 leftCode).jump 34
  let state6 := state5.jump 40
  let state7 := (state6.write 5 branches).jump 41
  let state8 := (state7.write 3 result).jump 29
  have hbitsAfter :
      ∀ consumed remaining,
        8 + extraFuel = consumed + remaining →
        natBitLength
            (pairIter remaining (pairIter consumed bound)) ≤
          maximumBits := by
    intro consumed remaining htotal
    exact pairIter_cap_suffix htotal hbits
  have hstackNonzero : state.registers 2 ≠ 0 := by
    rw [hstack]
    exact encodePendingStack_cons_ne_zero _ _ hright
  have hstep1 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 7 + extraFuel)
      (bound := bound) (pc := 29) (register := 2)
      (zeroTarget := 42) (nonzeroTarget := 30)
      (by rfl) hpc hstate
  have hrun1 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (8 + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state1 := by
    rw [show 8 + extraFuel = (7 + extraFuel) + 1 by omega]
    simpa [state1, hstackNonzero] using hstep1.1
  have hstate1 : StateBoundedBy (pairIter 1 bound) state1 := by
    simpa [state1, hstackNonzero, pairIter] using hstep1.2
  have hstep2 :=
    runUnpairLeftClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 6 + extraFuel)
      (bound := pairIter 1 bound) (pc := 30)
      (source := 2) (destination := 5) (next := 31)
      (by rfl) (by rfl) hstate1 (by
        simpa only [show
          7 + extraFuel = (6 + extraFuel) + 1 by omega] using
            hbitsAfter 1 (7 + extraFuel) (by omega))
  have hrun2 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state1 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state2 := by
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    simpa [state2, state1, pending, restCode, hstack,
      encodePendingFrame] using hstep2.1
  have hstate2 : StateBoundedBy (pairIter 2 bound) state2 := by
    simpa [state2, state1, pending, restCode, hstack,
      encodePendingFrame, pairIter] using hstep2.2
  have hstep3 :=
    runUnpairRightClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 5 + extraFuel)
      (bound := pairIter 2 bound) (pc := 31)
      (source := 2) (destination := 2) (next := 32)
      (by rfl) (by rfl) hstate2 (by
        simpa only [show
          6 + extraFuel = (5 + extraFuel) + 1 by omega] using
            hbitsAfter 2 (6 + extraFuel) (by omega))
  have hrun3 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state2 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state3 := by
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    simpa [state3, state2, state1, pending, restCode, hstack,
      encodePendingFrame] using hstep3.1
  have hstate3 : StateBoundedBy (pairIter 3 bound) state3 := by
    simpa [state3, state2, state1, pending, restCode, hstack,
      encodePendingFrame, pairIter] using hstep3.2
  have hstep4 :=
    runUnpairLeftClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 4 + extraFuel)
      (bound := pairIter 3 bound) (pc := 32)
      (source := 5) (destination := 4) (next := 33)
      (by rfl) (by rfl) hstate3 (by
        simpa only [show
          5 + extraFuel = (4 + extraFuel) + 1 by omega] using
            hbitsAfter 3 (5 + extraFuel) (by omega))
  have hrun4 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state3 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state4 := by
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    simpa [state4, state3, state2, pending] using hstep4.1
  have hstate4 : StateBoundedBy (pairIter 4 bound) state4 := by
    simpa [state4, state3, state2, pending, pairIter] using hstep4.2
  have hstep5 :=
    runUnpairRightClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 3 + extraFuel)
      (bound := pairIter 4 bound) (pc := 33)
      (source := 5) (destination := 6) (next := 34)
      (by rfl) (by rfl) hstate4 (by
        simpa only [show
          4 + extraFuel = (3 + extraFuel) + 1 by omega] using
            hbitsAfter 4 (4 + extraFuel) (by omega))
  have hrun5 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state4 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state5 := by
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    simpa [state5, state4, state3, state2, pending] using hstep5.1
  have hstate5 : StateBoundedBy (pairIter 5 bound) state5 := by
    simpa [state5, state4, state3, state2, pending, pairIter] using
      hstep5.2
  have hstep6 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 2 + extraFuel)
      (bound := pairIter 5 bound) (pc := 34) (register := 6)
      (zeroTarget := 35) (nonzeroTarget := 40)
      (by rfl) (by rfl) hstate5
  have hrun6 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state5 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state6 := by
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    simpa [state6, state5, state4, state3, state2, pending,
      hleft] using hstep6.1
  have hstate6 : StateBoundedBy (pairIter 6 bound) state6 := by
    simpa [state6, state5, state4, state3, state2, pending, hleft,
      pairIter] using hstep6.2
  have hstep7 :=
    runPairClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 1 + extraFuel)
      (bound := pairIter 6 bound) (pc := 40)
      (left := 6) (right := 3) (destination := 5) (next := 41)
      (by rfl) (by rfl) hstate6 (by
        simpa only [show
          2 + extraFuel = (1 + extraFuel) + 1 by omega] using
            hbitsAfter 6 (2 + extraFuel) (by omega))
  have hrun7 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state6 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state7 := by
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    simpa [state7, state6, state5, state4, state3, state2, state1,
      branches, hresult] using hstep7.1
  have hstate7 : StateBoundedBy (pairIter 7 bound) state7 := by
    simpa [state7, state6, state5, state4, state3, state2, state1,
      branches, hresult, pairIter] using hstep7.2
  have hstep8 :=
    runPairClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := extraFuel)
      (bound := pairIter 7 bound) (pc := 41)
      (left := 10) (right := 5) (destination := 3) (next := 29)
      (by rfl) (by rfl) hstate7 (by
        simpa only [show
          1 + extraFuel = extraFuel + 1 by omega] using
            hbitsAfter 7 (1 + extraFuel) (by omega))
  have hrun8 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state7 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel state8 := by
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    simpa [state8, state7, state6, state5, state4, state3, state2,
      state1, result, branches, htwo] using hstep8.1
  have hstate8 : StateBoundedBy (pairIter 8 bound) state8 := by
    simpa [state8, state7, state6, state5, state4, state3, state2,
      state1, result, branches, htwo, pairIter] using hstep8.2
  constructor
  · calc
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (8 + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (7 + extraFuel) state1 := hrun1
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (6 + extraFuel) state2 := hrun2
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (5 + extraFuel) state3 := hrun3
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + extraFuel) state4 := hrun4
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + extraFuel) state5 := hrun5
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + extraFuel) state6 := hrun6
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + extraFuel) state7 := hrun7
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel state8 := hrun8
      _ =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel
            (combineBranchState rightCount leftCode rightCode stack state) := by
              rfl
  · simpa [combineBranchState, pending, restCode, branches, result,
      state1, state2, state3, state4, state5, state6, state7, state8]
      using hstate8

private structure BuildFinished
    (values suffix : List ℕ) (stack : List PendingFrame)
    (state : NPOracleState) : Prop where
  pc : state.pc = 29
  cursor : state.registers 0 = encodeTaggedList suffix
  stackCode : state.registers 2 = encodePendingStack stack
  result : state.registers 3 = encodeBalancedList values
  zero : state.registers 7 = 0
  one : state.registers 9 = 1
  two : state.registers 10 = 2

private theorem emptyBuildState_finished
    (suffix : List ℕ) (stack : List PendingFrame)
    (state : NPOracleState)
    (hcursor : state.registers 0 = encodeTaggedList suffix)
    (hstack : state.registers 2 = encodePendingStack stack)
    (hzero : state.registers 7 = 0)
    (hone : state.registers 9 = 1)
    (htwo : state.registers 10 = 2) :
    BuildFinished [] suffix stack (emptyBuildState state) := by
  constructor <;>
    simp [emptyBuildState, hcursor, hstack, hzero, hone, htwo,
      encodeBalancedList]

private theorem leafBuildState_finished
    (value : ℕ) (suffix : List ℕ) (stack : List PendingFrame)
    (state : NPOracleState)
    (hstack : state.registers 2 = encodePendingStack stack)
    (hzero : state.registers 7 = 0)
    (hone : state.registers 9 = 1)
    (htwo : state.registers 10 = 2) :
    BuildFinished [value] suffix stack
      (leafBuildState value suffix state) := by
  constructor <;>
    simp [leafBuildState, hstack, hzero, hone, htwo,
      encodeBalancedList]

private theorem encodeBalancedList_ne_zero_of_ne_nil
    (values : List ℕ) (hvalues : values ≠ []) :
    encodeBalancedList values ≠ 0 := by
  cases values with
  | nil => exact (hvalues rfl).elim
  | cons value rest =>
      intro hzero
      have hlength :=
        encodeBalancedList_length_le (value :: rest)
      rw [hzero] at hlength
      simp at hlength

private theorem run_buildState
    (values suffix : List ℕ) (stack : List PendingFrame)
    {maximumBits bound extraFuel : ℕ} (state : NPOracleState)
    (hpc : state.pc = 13)
    (hcursor :
      state.registers 0 = encodeTaggedList (values ++ suffix))
    (hcount : state.registers 1 = values.length)
    (hstack : state.registers 2 = encodePendingStack stack)
    (hzero : state.registers 7 = 0)
    (hone : state.registers 9 = 1)
    (htwo : state.registers 10 = 2)
    (hstate : StateBoundedBy bound state)
    (hbound : 1 ≤ bound)
    (hbits :
      natBitLength
          (pairIter (balancedBuildFuel values + extraFuel) bound) ≤
        maximumBits) :
    ∃ finish,
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (balancedBuildFuel values + extraFuel) state =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          extraFuel finish ∧
      BuildFinished values suffix stack finish ∧
      StateBoundedBy (pairIter (balancedBuildFuel values) bound)
        finish := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values suffix stack state bound extraFuel with
  | h length ih =>
      cases values with
      | nil =>
          have hrun :=
            run_emptyBuildState
              (maximumBits := maximumBits) (bound := bound)
              (extraFuel := extraFuel) state hpc
              (by simpa using hcount) hstate (by
                simpa [balancedBuildFuel] using hbits)
          refine ⟨emptyBuildState state, ?_, ?_, ?_⟩
          · simpa [balancedBuildFuel] using hrun.1
          · exact emptyBuildState_finished suffix stack state
              (by simpa using hcursor) hstack hzero hone htwo
          · simpa [balancedBuildFuel] using hrun.2
      | cons first rest =>
          cases rest with
          | nil =>
              have hrun :=
                run_leafBuildState first suffix
                  (maximumBits := maximumBits) (bound := bound)
                  (extraFuel := extraFuel) state hpc
                  (by simpa using hcount) (by simpa using hcursor)
                  hone hstate (by
                    simpa [balancedBuildFuel] using hbits)
              refine ⟨leafBuildState first suffix state, ?_, ?_, ?_⟩
              · simpa [balancedBuildFuel] using hrun.1
              · exact leafBuildState_finished first suffix stack state
                  hstack hzero hone htwo
              · simpa [balancedBuildFuel] using hrun.2
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              let leftFuel := balancedBuildFuel left
              let rightFuel := balancedBuildFuel right
              let rightCount := Nat.shiftRight values.length 1
              let leftCount := Nat.shiftRight (values.length + 1) 1
              let pendingLeft : PendingFrame :=
                { rightCount := right.length, leftCode := 0 }
              let pendingRight : PendingFrame :=
                { rightCount := right.length
                  leftCode := encodeBalancedList left }
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwoValues : 2 ≤ values.length := by
                simp [values]
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLeValues : leftLength ≤ values.length :=
                hleftLtValues.le
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLeValues]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hrightPositive : 0 < right.length := by
                rw [hrightLengthEq]
                dsimp [leftLength]
                omega
              have hrightLeLeft : right.length ≤ left.length := by
                rw [hrightLengthEq, hleftLengthEq]
                dsimp [leftLength]
                omega
              have hleftLt : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length :=
                lt_of_le_of_lt hrightLeLeft hleftLt
              have hsplit : left ++ right = values := by
                exact List.take_append_drop leftLength values
              have hrightCount : rightCount = right.length := by
                dsimp [rightCount]
                rw [Nat.shiftRight_eq_div_pow]
                norm_num
                rw [hrightLengthEq]
                dsimp [leftLength]
                omega
              have hleftCount : leftCount = left.length := by
                dsimp [leftCount]
                rw [Nat.shiftRight_eq_div_pow]
                norm_num
                rw [hleftLengthEq]
              have hbuildFuel :
                  balancedBuildFuel values =
                    29 + leftFuel + rightFuel := by
                dsimp only [values, leftLength, left, right, leftFuel,
                  rightFuel]
                rw [balancedBuildFuel.eq_def]
              have hbitsValues :
                  natBitLength
                      (pairIter
                        (balancedBuildFuel values + extraFuel) bound) ≤
                    maximumBits := by
                simpa only [values] using hbits
              let descend :=
                descendBranchState values.length stack state
              have hdesc :=
                run_descendBranchState values.length stack
                  (maximumBits := maximumBits) (bound := bound)
                  (extraFuel :=
                    leftFuel + (11 + rightFuel + (8 + extraFuel)))
                  state hpc (by simpa [values] using hcount) hstack hzero
                  htwoValues hstate hbound (by
                    rw [show
                      10 +
                          (leftFuel +
                            (11 + rightFuel + (8 + extraFuel))) =
                        29 + leftFuel + rightFuel + extraFuel by omega]
                    rw [← hbuildFuel]
                    exact hbitsValues)
              have hdescBound :
                  StateBoundedBy (pairIter 10 bound) descend := by
                exact hdesc.2
              have hdescPc : descend.pc = 13 := by
                rfl
              have hdescCursor :
                  descend.registers 0 =
                    encodeTaggedList (left ++ (right ++ suffix)) := by
                have happend :
                    left ++ (right ++ suffix) = values ++ suffix := by
                  rw [← List.append_assoc, hsplit]
                simp [descend, descendBranchState, happend, values,
                  hcursor]
              have hdescCount :
                  descend.registers 1 = left.length := by
                change
                  Nat.shiftRight (values.length + 1) 1 = left.length
                exact hleftCount
              have hdescStack :
                  descend.registers 2 =
                    encodePendingStack (pendingLeft :: stack) := by
                change
                  Nat.pair (Nat.pair rightCount 0)
                      (encodePendingStack stack) =
                    encodePendingStack (pendingLeft :: stack)
                simp [pendingLeft, encodePendingFrame, hrightCount]
              have hdescZero : descend.registers 7 = 0 := by
                simp [descend, descendBranchState, hzero]
              have hdescOne : descend.registers 9 = 1 := by
                simp [descend, descendBranchState, hone]
              have hdescTwo : descend.registers 10 = 2 := by
                simp [descend, descendBranchState, htwo]
              have hbitsLeft :
                  natBitLength
                      (pairIter
                        (leftFuel +
                          (11 + rightFuel + (8 + extraFuel)))
                        (pairIter 10 bound)) ≤
                    maximumBits := by
                apply pairIter_cap_suffix
                  (total := balancedBuildFuel values + extraFuel)
                  (consumed := 10)
                  (remaining :=
                    leftFuel + (11 + rightFuel + (8 + extraFuel)))
                  (bound := bound)
                · rw [hbuildFuel]
                  omega
                · exact hbitsValues
              have hleftRun :=
                ih left.length hleftLt
                  (values := left)
                  (suffix := right ++ suffix)
                  (stack := pendingLeft :: stack)
                  (bound := pairIter 10 bound)
                  (extraFuel := 11 + rightFuel + (8 + extraFuel))
                  descend hdescPc hdescCursor hdescCount hdescStack
                  hdescZero hdescOne hdescTwo hdescBound
                  (one_le_pairIter 10 hbound)
                  (by simpa only [leftFuel] using hbitsLeft)
                  rfl
              obtain
                ⟨leftFinish, hrunLeft, hleftFinished, hleftBound⟩ :=
                  hleftRun
              let afterLeftBound :=
                pairIter (10 + leftFuel) bound
              have hleftBound' :
                  StateBoundedBy afterLeftBound leftFinish := by
                dsimp [afterLeftBound]
                rw [pairIter_add]
                simpa only [leftFuel] using hleftBound
              have hbitsResume :
                  natBitLength
                      (pairIter
                        (11 + rightFuel + (8 + extraFuel))
                        afterLeftBound) ≤ maximumBits := by
                dsimp [afterLeftBound]
                apply pairIter_cap_suffix
                  (total := balancedBuildFuel values + extraFuel)
                  (consumed := 10 + leftFuel)
                  (remaining := 11 + rightFuel + (8 + extraFuel))
                  (bound := bound)
                · rw [hbuildFuel]
                  omega
                · exact hbitsValues
              let resume :=
                resumeRightState right.length
                  (encodeBalancedList left) stack leftFinish
              have hresume :=
                run_resumeRightState right.length
                  (encodeBalancedList left) stack
                  (maximumBits := maximumBits)
                  (bound := afterLeftBound)
                  (extraFuel := rightFuel + (8 + extraFuel))
                  leftFinish hleftFinished.pc hleftFinished.stackCode
                  hleftFinished.result hrightPositive hleftBound'
                  (by simpa only [show
                    11 + rightFuel + (8 + extraFuel) =
                      11 + (rightFuel + (8 + extraFuel)) by omega]
                    using hbitsResume)
              let afterResumeBound := pairIter 11 afterLeftBound
              have hresumeBound :
                  StateBoundedBy afterResumeBound resume := by
                exact hresume.2
              have hresumePc : resume.pc = 13 := by
                rfl
              have hresumeCursor :
                  resume.registers 0 =
                    encodeTaggedList (right ++ suffix) := by
                simp [resume, resumeRightState, hleftFinished.cursor]
              have hresumeCount :
                  resume.registers 1 = right.length := by
                rfl
              have hresumeStack :
                  resume.registers 2 =
                    encodePendingStack (pendingRight :: stack) := by
                rfl
              have hresumeZero : resume.registers 7 = 0 := by
                simp [resume, resumeRightState, hleftFinished.zero]
              have hresumeOne : resume.registers 9 = 1 := by
                simp [resume, resumeRightState, hleftFinished.one]
              have hresumeTwo : resume.registers 10 = 2 := by
                simp [resume, resumeRightState, hleftFinished.two]
              have hafterResumeBound :
                  afterResumeBound =
                    pairIter (10 + leftFuel + 11) bound := by
                dsimp only [afterResumeBound, afterLeftBound]
                calc
                  pairIter 11 (pairIter (10 + leftFuel) bound) =
                    pairIter ((10 + leftFuel) + 11) bound :=
                      (pairIter_add (10 + leftFuel) 11 bound).symm
                  _ = pairIter (10 + leftFuel + 11) bound := rfl
              have hbitsRight :
                  natBitLength
                      (pairIter (rightFuel + (8 + extraFuel))
                        afterResumeBound) ≤ maximumBits := by
                rw [hafterResumeBound]
                exact
                  pairIter_cap_suffix
                    (total := balancedBuildFuel values + extraFuel)
                    (consumed := 10 + leftFuel + 11)
                    (remaining := rightFuel + (8 + extraFuel))
                    (bound := bound) (maximumBits := maximumBits)
                    (by
                      rw [hbuildFuel]
                      omega)
                    hbitsValues
              have hrightRun :=
                ih right.length hrightLt
                  (values := right)
                  (suffix := suffix) (stack := pendingRight :: stack)
                  (bound := afterResumeBound)
                  (extraFuel := 8 + extraFuel)
                  resume hresumePc hresumeCursor hresumeCount
                  hresumeStack hresumeZero hresumeOne hresumeTwo
                  hresumeBound
                  (one_le_pairIter 11
                    (one_le_pairIter (10 + leftFuel) hbound))
                  (by simpa only [rightFuel] using hbitsRight)
                  rfl
              obtain
                ⟨rightFinish, hrunRight, hrightFinished,
                  hrightBound⟩ := hrightRun
              let beforeCombineBound :=
                pairIter
                  (10 + leftFuel + 11 + rightFuel) bound
              have hrightBound' :
                  StateBoundedBy beforeCombineBound rightFinish := by
                have heq :
                    beforeCombineBound =
                      pairIter rightFuel afterResumeBound := by
                  dsimp only [beforeCombineBound]
                  rw [show 10 + leftFuel + 11 + rightFuel =
                    (10 + leftFuel + 11) + rightFuel by omega]
                  rw [pairIter_add, ← hafterResumeBound]
                rw [heq]
                exact hrightBound
              have hbitsCombine :
                  natBitLength
                      (pairIter (8 + extraFuel) beforeCombineBound) ≤
                    maximumBits := by
                change
                  natBitLength
                      (pairIter (8 + extraFuel)
                        (pairIter
                          (10 + leftFuel + 11 + rightFuel) bound)) ≤
                    maximumBits
                exact
                  pairIter_cap_suffix
                    (total := balancedBuildFuel values + extraFuel)
                    (consumed := 10 + leftFuel + 11 + rightFuel)
                    (remaining := 8 + extraFuel)
                    (bound := bound) (maximumBits := maximumBits)
                    (by
                      rw [hbuildFuel]
                      omega)
                    hbitsValues
              let combined :=
                combineBranchState right.length
                  (encodeBalancedList left)
                  (encodeBalancedList right) stack rightFinish
              have hcombine :=
                run_combineBranchState right.length
                  (encodeBalancedList left)
                  (encodeBalancedList right) stack
                  (maximumBits := maximumBits)
                  (bound := beforeCombineBound)
                  (extraFuel := extraFuel)
                  rightFinish hrightFinished.pc
                  hrightFinished.stackCode hrightFinished.result
                  hrightFinished.two hrightPositive
                  (encodeBalancedList_ne_zero_of_ne_nil left (by
                    intro hnil
                    rw [hnil] at hleftLengthEq
                    simp at hleftLengthEq
                    omega))
                  hrightBound' hbitsCombine
              have hcombinedFinished :
                  BuildFinished values suffix stack combined := by
                refine
                  { pc := by rfl
                    cursor := ?_
                    stackCode := ?_
                    result := ?_
                    zero := ?_
                    one := ?_
                    two := ?_ }
                · simp [combined, combineBranchState,
                    hrightFinished.cursor]
                · simp [combined, combineBranchState]
                · simp [combined, combineBranchState,
                    values, leftLength, left, right,
                    encodeBalancedList]
                · simp [combined, combineBranchState,
                    hrightFinished.zero]
                · simp [combined, combineBranchState,
                    hrightFinished.one]
                · simp [combined, combineBranchState,
                    hrightFinished.two]
              have hcombinedBound :
                  StateBoundedBy
                    (pairIter (balancedBuildFuel values) bound)
                    combined := by
                have hactual := hcombine.2
                rw [hbuildFuel]
                dsimp [beforeCombineBound] at hactual
                rw [show 29 + leftFuel + rightFuel =
                  (10 + leftFuel + 11 + rightFuel) + 8 by omega]
                rw [pairIter_add]
                exact hactual
              refine ⟨combined, ?_, hcombinedFinished, hcombinedBound⟩
              calc
                runNPOracleProgram taggedToBalancedProgram maximumBits
                    (balancedBuildFuel values + extraFuel) state =
                  runNPOracleProgram taggedToBalancedProgram maximumBits
                    (leftFuel +
                      (11 + rightFuel + (8 + extraFuel)))
                    descend := by
                      rw [hbuildFuel]
                      rw [show
                        29 + leftFuel + rightFuel + extraFuel =
                          10 +
                            (leftFuel +
                              (11 + rightFuel + (8 + extraFuel))) by
                        omega]
                      exact hdesc.1
                _ =
                  runNPOracleProgram taggedToBalancedProgram maximumBits
                    (11 + rightFuel + (8 + extraFuel))
                    leftFinish := by
                      simpa only [leftFuel] using hrunLeft
                _ =
                  runNPOracleProgram taggedToBalancedProgram maximumBits
                    (rightFuel + (8 + extraFuel)) resume := by
                      rw [show
                        11 + rightFuel + (8 + extraFuel) =
                          11 + (rightFuel + (8 + extraFuel)) by omega]
                      exact hresume.1
                _ =
                  runNPOracleProgram taggedToBalancedProgram maximumBits
                    (8 + extraFuel) rightFinish := by
                      simpa only [rightFuel] using hrunRight
                _ =
                  runNPOracleProgram taggedToBalancedProgram maximumBits
                    extraFuel combined := by
                      simpa only [combined] using hcombine.1

theorem run_taggedToBalancedProgram_from
    (inputLength : ℕ) (values : List ℕ) :
    runNPOracleProgram taggedToBalancedProgram
        (taggedToBalancedRegisterBitsFor inputLength values)
        (taggedToBalancedFuel values)
        (initialNPOracleState inputLength (encodeTaggedList values)) =
      some (encodeBalancedList values) := by
  let initialBound := taggedToBalancedInitialBoundFor inputLength values
  let maximumBits := taggedToBalancedRegisterBitsFor inputLength values
  let countSteps := 5 * values.length + 1
  let buildSteps := balancedBuildFuel values
  let postCount := 3 + buildSteps + 2
  let totalFuel := taggedToBalancedFuel values
  let inputCode := encodeTaggedList values
  let initialState :=
    initialNPOracleState inputLength inputCode
  let state1 := (initialState.write 7 0).jump 1
  let state2 := (state1.write 9 1).jump 2
  let state3 := (state2.write 10 2).jump 3
  let state4 := (state3.write 8 inputCode).jump 4
  let state5 := (state4.write 1 0).jump 5
  have htotal :
      totalFuel = 5 + countSteps + postCount := by
    simp [totalFuel, taggedToBalancedFuel, countSteps, postCount,
      buildSteps]
    omega
  have hbitsTotal :
      natBitLength (pairIter totalFuel initialBound) ≤ maximumBits := by
    rfl
  have hbitsAfter :
      ∀ consumed remaining,
        totalFuel = consumed + remaining →
        natBitLength
            (pairIter remaining (pairIter consumed initialBound)) ≤
          maximumBits := by
    intro consumed remaining heq
    exact pairIter_cap_suffix heq hbitsTotal
  have hinitial : StateBoundedBy initialBound initialState := by
    simpa [initialBound, inputCode, initialState] using
      initialState_bounded inputLength values
  have hinitialOne : 1 ≤ initialBound := by
    simp [initialBound, taggedToBalancedInitialBoundFor]
  have hinitialTwo : 2 ≤ initialBound := by
    simp [initialBound, taggedToBalancedInitialBoundFor]
  have hstep1 :=
    runSetClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits)
      (fuel := 4 + countSteps + postCount)
      (bound := initialBound) (pc := 0)
      (register := 7) (value := 0) (next := 1)
      (by rfl) (by rfl) hinitial (Nat.zero_le _) (by
        rw [show
          (4 + countSteps + postCount) + 1 = totalFuel by omega]
        exact hbitsTotal)
  have hrun1 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          totalFuel initialState =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + countSteps + postCount) state1 := by
    rw [htotal]
    rw [show 5 + countSteps + postCount =
      (4 + countSteps + postCount) + 1 by omega]
    simpa [state1] using hstep1.1
  have hstate1 : StateBoundedBy (pairIter 1 initialBound) state1 := by
    simpa [state1, pairIter] using hstep1.2
  have hstep2 :=
    runSetClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits)
      (fuel := 3 + countSteps + postCount)
      (bound := pairIter 1 initialBound) (pc := 1)
      (register := 9) (value := 1) (next := 2)
      (by rfl) (by rfl) hstate1
      (one_le_pairIter 1 hinitialOne) (by
        simpa only [show
          4 + countSteps + postCount =
            (3 + countSteps + postCount) + 1 by omega] using
          hbitsAfter 1 (4 + countSteps + postCount) (by omega))
  have hrun2 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (4 + countSteps + postCount) state1 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + countSteps + postCount) state2 := by
    rw [show 4 + countSteps + postCount =
      (3 + countSteps + postCount) + 1 by omega]
    simpa [state2, state1] using hstep2.1
  have hstate2 : StateBoundedBy (pairIter 2 initialBound) state2 := by
    simpa [state2, state1, pairIter] using hstep2.2
  have htwoAfter2 : 2 ≤ pairIter 2 initialBound :=
    hinitialTwo.trans (value_le_pairIter 2 initialBound)
  have hstep3 :=
    runSetClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits)
      (fuel := 2 + countSteps + postCount)
      (bound := pairIter 2 initialBound) (pc := 2)
      (register := 10) (value := 2) (next := 3)
      (by rfl) (by rfl) hstate2 htwoAfter2 (by
        simpa only [show
          3 + countSteps + postCount =
            (2 + countSteps + postCount) + 1 by omega] using
          hbitsAfter 2 (3 + countSteps + postCount) (by omega))
  have hrun3 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (3 + countSteps + postCount) state2 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + countSteps + postCount) state3 := by
    rw [show 3 + countSteps + postCount =
      (2 + countSteps + postCount) + 1 by omega]
    simpa [state3, state2] using hstep3.1
  have hstate3 : StateBoundedBy (pairIter 3 initialBound) state3 := by
    simpa [state3, state2, pairIter] using hstep3.2
  have hstate3Input : state3.registers 0 = inputCode := by
    simp [state3, state2, state1, initialState, inputCode,
      initialNPOracleState]
  have hstep4 :=
    runCopyClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits)
      (fuel := 1 + countSteps + postCount)
      (bound := pairIter 3 initialBound) (pc := 3)
      (source := 0) (destination := 8) (next := 4)
      (by rfl) (by rfl) hstate3 (by
        simpa only [show
          2 + countSteps + postCount =
            (1 + countSteps + postCount) + 1 by omega] using
          hbitsAfter 3 (2 + countSteps + postCount) (by omega))
  have hrun4 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + countSteps + postCount) state3 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + countSteps + postCount) state4 := by
    rw [show 2 + countSteps + postCount =
      (1 + countSteps + postCount) + 1 by omega]
    simpa [state4, hstate3Input] using hstep4.1
  have hstate4 : StateBoundedBy (pairIter 4 initialBound) state4 := by
    simpa [state4, hstate3Input, pairIter] using hstep4.2
  have hstep5 :=
    runSetClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits)
      (fuel := countSteps + postCount)
      (bound := pairIter 4 initialBound) (pc := 4)
      (register := 1) (value := 0) (next := 5)
      (by rfl) (by rfl) hstate4 (Nat.zero_le _) (by
        simpa only [show
          1 + countSteps + postCount =
            (countSteps + postCount) + 1 by omega] using
          hbitsAfter 4 (1 + countSteps + postCount) (by omega))
  have hrun5 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + countSteps + postCount) state4 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (countSteps + postCount) state5 := by
    rw [show 1 + countSteps + postCount =
      (countSteps + postCount) + 1 by omega]
    simpa [state5, state4] using hstep5.1
  have hstate5 : StateBoundedBy (pairIter 5 initialBound) state5 := by
    simpa [state5, state4, pairIter] using hstep5.2
  let counted := countTaggedState values state5
  have hcountRun :=
    run_countTaggedState values
      (maximumBits := maximumBits) (bound := pairIter 5 initialBound)
      (extraFuel := postCount) state5 (by rfl) (by
        simp [state5, state4, state3, state2, state1, initialState,
          inputCode, initialNPOracleState])
      (by simp [state5, state4, state3, state2, state1])
      hstate5 (one_le_pairIter 5 hinitialOne) (by
        simpa only [countSteps] using
          hbitsAfter 5 (countSteps + postCount) (by omega))
  have hcountedBound :
      StateBoundedBy
        (pairIter countSteps (pairIter 5 initialBound)) counted := by
    simpa only [counted, countSteps] using hcountRun.2
  have hcountedPc : counted.pc = 10 :=
    countTaggedState_pc values state5
  have hcountedCount : counted.registers 1 = values.length := by
    rw [countTaggedState_count]
    simp [state5, state4]
  have hcountedInput : counted.registers 8 = inputCode := by
    rw [countTaggedState_preserves values state5
      (register := 8) (by omega)]
    simp [state5, state4, state3, inputCode]
  have hcountedZero : counted.registers 7 = 0 := by
    rw [countTaggedState_preserves values state5
      (register := 7) (by omega)]
    simp [state5, state4, state3, state2, state1]
  have hcountedOne : counted.registers 9 = 1 := by
    rw [countTaggedState_preserves values state5
      (register := 9) (by omega)]
    simp [state5, state4, state3, state2]
  have hcountedTwo : counted.registers 10 = 2 := by
    rw [countTaggedState_preserves values state5
      (register := 10) (by omega)]
    simp [state5, state4, state3]
  let afterCountBound := pairIter (5 + countSteps) initialBound
  have hcountedBound' : StateBoundedBy afterCountBound counted := by
    dsimp only [afterCountBound]
    rw [pairIter_add]
    exact hcountedBound
  have hbitsPostCount :
      natBitLength (pairIter postCount afterCountBound) ≤ maximumBits := by
    exact hbitsAfter (5 + countSteps) postCount (by omega)
  let restore1 := (counted.write 0 inputCode).jump 11
  let restore2 := (restore1.write 2 0).jump 12
  let buildStart := restore2.jump 13
  have hrestore1 :=
    runCopyClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits)
      (fuel := 2 + buildSteps + 2)
      (bound := afterCountBound) (pc := 10)
      (source := 8) (destination := 0) (next := 11)
      (by rfl) hcountedPc hcountedBound' (by
        simpa [postCount, show
          3 + buildSteps + 2 =
            (2 + buildSteps + 2) + 1 by omega] using hbitsPostCount)
  have hrunRestore1 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          postCount counted =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + buildSteps + 2) restore1 := by
    rw [show postCount = (2 + buildSteps + 2) + 1 by
      simp [postCount]
      omega]
    simpa [restore1, hcountedInput] using hrestore1.1
  have hrestore1Bound :
      StateBoundedBy (pairIter 1 afterCountBound) restore1 := by
    simpa [restore1, hcountedInput, pairIter] using hrestore1.2
  have hrestore2 :=
    runSetClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits)
      (fuel := 1 + buildSteps + 2)
      (bound := pairIter 1 afterCountBound) (pc := 11)
      (register := 2) (value := 0) (next := 12)
      (by rfl) (by rfl) hrestore1Bound (Nat.zero_le _) (by
        have hcap :=
          hbitsAfter (5 + countSteps + 1)
            (2 + buildSteps + 2) (by
              simp [totalFuel, taggedToBalancedFuel, countSteps,
                buildSteps]
              omega)
        have heq :
            pairIter 1 afterCountBound =
              pairIter (5 + countSteps + 1) initialBound := by
          dsimp only [afterCountBound]
          calc
            pairIter 1 (pairIter (5 + countSteps) initialBound) =
                pairIter ((5 + countSteps) + 1) initialBound :=
              (pairIter_add (5 + countSteps) 1 initialBound).symm
            _ = pairIter (5 + countSteps + 1) initialBound := rfl
        rw [heq]
        simpa only [show
          2 + buildSteps + 2 =
            (1 + buildSteps + 2) + 1 by omega] using hcap)
  have hrunRestore2 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (2 + buildSteps + 2) restore1 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + buildSteps + 2) restore2 := by
    rw [show 2 + buildSteps + 2 =
      (1 + buildSteps + 2) + 1 by omega]
    simpa [restore2, restore1] using hrestore2.1
  have hrestore2Bound :
      StateBoundedBy (pairIter 2 afterCountBound) restore2 := by
    simpa [restore2, restore1, pairIter] using hrestore2.2
  have hrestore3 :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits)
      (fuel := buildSteps + 2)
      (bound := pairIter 2 afterCountBound) (pc := 12)
      (register := 7) (zeroTarget := 13) (nonzeroTarget := 13)
      (by rfl) (by rfl) hrestore2Bound
  have hrunRestore3 :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (1 + buildSteps + 2) restore2 =
        runNPOracleProgram taggedToBalancedProgram maximumBits
          (buildSteps + 2) buildStart := by
    rw [show 1 + buildSteps + 2 = (buildSteps + 2) + 1 by omega]
    simpa [buildStart, restore2] using hrestore3.1
  have hbuildStartBound :
      StateBoundedBy (pairIter 3 afterCountBound) buildStart := by
    simpa [buildStart, restore2, pairIter] using hrestore3.2
  have hbuildStartPc : buildStart.pc = 13 := by rfl
  have hbuildStartCursor :
      buildStart.registers 0 = encodeTaggedList (values ++ []) := by
    simp [buildStart, restore2, restore1, inputCode]
  have hbuildStartCount :
      buildStart.registers 1 = values.length := by
    simp [buildStart, restore2, restore1, hcountedCount]
  have hbuildStartStack :
      buildStart.registers 2 = encodePendingStack [] := by
    rfl
  have hbuildStartZero : buildStart.registers 7 = 0 := by
    simp [buildStart, restore2, restore1, hcountedZero]
  have hbuildStartOne : buildStart.registers 9 = 1 := by
    simp [buildStart, restore2, restore1, hcountedOne]
  have hbuildStartTwo : buildStart.registers 10 = 2 := by
    simp [buildStart, restore2, restore1, hcountedTwo]
  let beforeBuildBound :=
    pairIter (5 + countSteps + 3) initialBound
  have hbuildStartBound' :
      StateBoundedBy beforeBuildBound buildStart := by
    have heq :
        beforeBuildBound = pairIter 3 afterCountBound := by
      dsimp only [beforeBuildBound, afterCountBound]
      rw [show 5 + countSteps + 3 =
        (5 + countSteps) + 3 by omega, pairIter_add]
    rw [heq]
    exact hbuildStartBound
  have hbitsBuild :
      natBitLength
          (pairIter (buildSteps + 2) beforeBuildBound) ≤
        maximumBits :=
    hbitsAfter (5 + countSteps + 3) (buildSteps + 2) (by
      simp [totalFuel, taggedToBalancedFuel, countSteps, buildSteps]
      omega)
  have hbuildRun :=
    run_buildState values [] []
      (maximumBits := maximumBits) (bound := beforeBuildBound)
      (extraFuel := 2) buildStart hbuildStartPc hbuildStartCursor
      hbuildStartCount hbuildStartStack hbuildStartZero hbuildStartOne
      hbuildStartTwo hbuildStartBound'
      (one_le_pairIter (5 + countSteps + 3) hinitialOne)
      (by simpa only [buildSteps] using hbitsBuild)
  obtain ⟨finish, hrunBuild, hfinished, hfinishBound⟩ := hbuildRun
  let beforeBranchBound :=
    pairIter (5 + countSteps + 3 + buildSteps) initialBound
  have hfinishBound' :
      StateBoundedBy beforeBranchBound finish := by
    have heq :
        beforeBranchBound =
          pairIter buildSteps beforeBuildBound := by
      dsimp only [beforeBranchBound, beforeBuildBound]
      rw [show 5 + countSteps + 3 + buildSteps =
        (5 + countSteps + 3) + buildSteps by omega, pairIter_add]
    rw [heq]
    simpa only [buildSteps] using hfinishBound
  have hbitsFinal :
      natBitLength (pairIter 2 beforeBranchBound) ≤ maximumBits :=
    hbitsAfter (5 + countSteps + 3 + buildSteps) 2 (by
      simp [totalFuel, taggedToBalancedFuel, countSteps, buildSteps]
      omega)
  let haltState := finish.jump 42
  have hbranch :=
    runBranchZeroClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits) (fuel := 1)
      (bound := beforeBranchBound) (pc := 29) (register := 2)
      (zeroTarget := 42) (nonzeroTarget := 30)
      (by rfl) hfinished.pc hfinishBound'
  have hrunBranch :
      runNPOracleProgram taggedToBalancedProgram maximumBits 2 finish =
        runNPOracleProgram taggedToBalancedProgram maximumBits 1
          haltState := by
    simpa [haltState, hfinished.stackCode] using hbranch.1
  have hhaltBound :
      StateBoundedBy (pairIter 1 beforeBranchBound) haltState := by
    simpa [haltState, hfinished.stackCode, pairIter] using hbranch.2
  have hhalt :=
    runHaltClocked
      (program := taggedToBalancedProgram)
      (maximumBits := maximumBits)
      (bound := pairIter 1 beforeBranchBound)
      (pc := 42) (outputRegister := 3) (by rfl) (by rfl)
      hhaltBound (by simpa [pairIter] using hbitsFinal)
  have hhaltResult :
      runNPOracleProgram taggedToBalancedProgram maximumBits 1 haltState =
        some (encodeBalancedList values) := by
    simpa [haltState, hfinished.result] using hhalt
  calc
    runNPOracleProgram taggedToBalancedProgram
        (taggedToBalancedRegisterBitsFor inputLength values)
        (taggedToBalancedFuel values)
        (initialNPOracleState inputLength (encodeTaggedList values)) =
      runNPOracleProgram taggedToBalancedProgram maximumBits
        totalFuel initialState := by rfl
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits
        (4 + countSteps + postCount) state1 := hrun1
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits
        (3 + countSteps + postCount) state2 := hrun2
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits
        (2 + countSteps + postCount) state3 := hrun3
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits
        (1 + countSteps + postCount) state4 := hrun4
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits
        (countSteps + postCount) state5 := hrun5
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits
        postCount counted := by
          simpa only [counted, countSteps] using hcountRun.1
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits
        (2 + buildSteps + 2) restore1 := hrunRestore1
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits
        (1 + buildSteps + 2) restore2 := hrunRestore2
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits
        (buildSteps + 2) buildStart := hrunRestore3
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits 2 finish := by
        simpa only [buildSteps] using hrunBuild
    _ =
      runNPOracleProgram taggedToBalancedProgram maximumBits 1
        haltState := hrunBranch
    _ = some (encodeBalancedList values) := hhaltResult

theorem run_taggedToBalancedProgram (values : List ℕ) :
    runNPOracleProgram taggedToBalancedProgram
        (taggedToBalancedRegisterBits values)
        (taggedToBalancedFuel values)
        (initialNPOracleState values.length (encodeTaggedList values)) =
      some (encodeBalancedList values) := by
  exact run_taggedToBalancedProgram_from values.length values

end NearCubicWires.CanonicalBalancedBuilder
