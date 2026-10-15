import Proof.Foundations.CanonicalBinaryProgram

/-!
# The exact binomial-coefficient primitive

The symmetric touching-cost sweep compares two conditional expectation scores
after cross-multiplying by binomial fiber sizes, so every executable stage on
that path needs `Nat.choose` as a fixed register-machine program.

The instruction set has no register-amount shift, no multiplication, and no
division, which rules out both the compact "row-as-one-integer" Pascal trick
driven by a variable shift and the multiplicative recurrence
`choose m (k+1) = choose m k * (m-k) / (k+1)`.  This module uses a third route
that needs *only* unit shifts, addition, and saturating subtraction.

Write `width := count + 1` and `base := 2 ^ width`.  Because
`Nat.choose count index ≤ 2 ^ count < base`, the natural number

```text
packedPascalRow count = (base + 1) ^ count
```

is exactly the base-`base` numeral whose digit at position `index` is
`Nat.choose count index`.  The machine builds that numeral by `count`
rounds of `value := value + value * base` — where `value * base` is a loop of
`width` unit left shifts — and then reads digit `position` off by `width *
position` unit right shifts followed by a truncation to the low `width` bits,
which is one round trip through unit shifts and a single subtraction.

Both the packing identity and the digit-extraction identity are proved here
from `add_pow`; nothing is decided numerically and no `Nat.choose` value is
ever tabulated in the proof.
-/

namespace NearCubicWires.CanonicalBinomialProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-! ## §1 The packed Pascal row -/

/-- Split the lowest base-`base` digit off an explicit numeral. -/
private theorem sum_range_shift (coefficients : ℕ → ℕ) (base length : ℕ) :
    (∑ index ∈ Finset.range (length + 1), coefficients index * base ^ index) =
      coefficients 0 +
        base *
          ∑ index ∈ Finset.range length,
            coefficients (index + 1) * base ^ index := by
  rw [Finset.sum_range_succ']
  rw [Finset.mul_sum]
  rw [Nat.add_comm]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro index _
    rw [pow_succ]
    ring

/-- Exact base-`base` digit read-off for an explicit numeral whose digits are
all smaller than the base and vanish beyond a known length. -/
private theorem digitExtract (base : ℕ) (hbase : 0 < base) :
    ∀ (position : ℕ) (coefficients : ℕ → ℕ) (length : ℕ),
      (∀ index, coefficients index < base) →
      (∀ index, length ≤ index → coefficients index = 0) →
      ((∑ index ∈ Finset.range length, coefficients index * base ^ index) /
          base ^ position) % base = coefficients position := by
  intro position
  induction position with
  | zero =>
      intro coefficients length hsmall hvanish
      cases length with
      | zero =>
          simp [hvanish 0 (Nat.le_refl 0)]
      | succ length =>
          rw [sum_range_shift]
          simp only [pow_zero, Nat.div_one]
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt (hsmall 0)
  | succ position inductionHypothesis =>
      intro coefficients length hsmall hvanish
      cases length with
      | zero =>
          simp only [Finset.range_zero, Finset.sum_empty, Nat.zero_div,
            Nat.zero_mod]
          exact (hvanish (position + 1) (Nat.zero_le _)).symm
      | succ length =>
          rw [sum_range_shift]
          rw [show base ^ (position + 1) = base * base ^ position by ring]
          rw [← Nat.div_div_eq_div_mul]
          rw [Nat.add_mul_div_left _ _ hbase]
          rw [Nat.div_eq_of_lt (hsmall 0), Nat.zero_add]
          exact inductionHypothesis (fun index => coefficients (index + 1))
            length (fun index => hsmall (index + 1))
            (fun index hindex => hvanish (index + 1) (by omega))

/-- Digit width of the packed row: one more bit than every entry needs. -/
def binomialWidth (count : ℕ) : ℕ :=
  count + 1

/-- The whole `count`-th Pascal row, packed as one base-`2 ^ binomialWidth`
numeral. -/
def packedPascalRow (count : ℕ) : ℕ :=
  (2 ^ binomialWidth count + 1) ^ count

theorem packedPascalRow_expand (count : ℕ) :
    packedPascalRow count =
      ∑ index ∈ Finset.range (count + 1),
        Nat.choose count index * (2 ^ binomialWidth count) ^ index := by
  unfold packedPascalRow
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro index _
  simp only [one_pow, mul_one, Nat.cast_id]
  ring

/-- **The packing identity.**  Reading digit `position` off the packed row
returns exactly `Nat.choose count position`, for every `position`. -/
theorem packedPascalRow_digit (count position : ℕ) :
    packedPascalRow count / (2 ^ binomialWidth count) ^ position %
        2 ^ binomialWidth count =
      Nat.choose count position := by
  rw [packedPascalRow_expand]
  exact digitExtract (2 ^ binomialWidth count) (Nat.pow_pos (by omega)) position
    (fun index => Nat.choose count index) (count + 1)
    (fun index =>
      lt_of_le_of_lt (Nat.choose_le_two_pow count index)
        (Nat.pow_lt_pow_right (by omega) (by unfold binomialWidth; omega)))
    (fun index hindex => Nat.choose_eq_zero_of_lt (by omega))

/-! ## §2 The fixed program

Register ABI:

* `r0`: paired request `Nat.pair count position`, then the output digit;
* `r1`: native input length, never written;
* `r2`: `count`;
* `r3`: `position`;
* `r4`: `binomialWidth count`, immutable after setup;
* `r5`: the packed row, then its shifted remainder;
* `r6`: outer round counter;
* `r7`: unit-shift counter;
* `r8`: shift scratch.
-/

/-- **The binomial program.**  Five nested counted loops over unit shifts. -/
def binomialProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .copy 2 4 3
  , .increment 4 4
  , .set 5 1 5
  , .copy 2 6 6
  , .branchZero 6 14 7
  , .copy 5 8 8
  , .copy 4 7 9
  , .branchZero 7 12 10
  , .shiftLeft 8 1 8 11
  , .decrement 7 9
  , .add 5 8 5 13
  , .decrement 6 6
  , .copy 3 6 15
  , .branchZero 6 21 16
  , .copy 4 7 17
  , .branchZero 7 20 18
  , .shiftRight 5 1 5 19
  , .decrement 7 17
  , .decrement 6 15
  , .copy 5 8 22
  , .copy 4 7 23
  , .branchZero 7 26 24
  , .shiftRight 8 1 8 25
  , .decrement 7 23
  , .copy 4 7 27
  , .branchZero 7 30 28
  , .shiftLeft 8 1 8 29
  , .decrement 7 27
  , .subtract 5 8 0 31
  , .halt 0
  ]

@[simp] theorem binomialProgram_oracleFree : OracleFree binomialProgram := by
  rfl

/-! ## §3 The two unit-shift loops -/

private theorem shiftLeft_one (value : ℕ) :
    Nat.shiftLeft value 1 = value * 2 := by
  simp [Nat.shiftLeft_eq]

private theorem shiftRight_one (value : ℕ) :
    Nat.shiftRight value 1 = value / 2 := by
  simp [Nat.shiftRight_eq_div_pow]

/-- A counted loop of unit left shifts multiplies its register by a power of
two.  The loop is continuation-parametric so that the four call sites never
expose a concrete state normal form. -/
private theorem run_shiftLeftLoop
    (testPc bodyPc decrementPc exitPc valueRegister maximumBits extra : ℕ)
    (hvalueRegister : valueRegister ≠ 7)
    (htest : binomialProgram[testPc]? = some (.branchZero 7 exitPc bodyPc))
    (hbody :
      binomialProgram[bodyPc]? =
        some (.shiftLeft valueRegister 1 valueRegister decrementPc))
    (hdecrement : binomialProgram[decrementPc]? = some (.decrement 7 testPc)) :
    ∀ (counter value : ℕ) (state : NPOracleState) (result : Option ℕ),
      state.pc = testPc →
      state.registers 7 = counter →
      state.registers valueRegister = value →
      natBitLength counter ≤ maximumBits →
      natBitLength (value * 2 ^ counter) ≤ maximumBits →
      (∀ finalState : NPOracleState,
        finalState.pc = exitPc →
        finalState.registers 7 = 0 →
        finalState.registers valueRegister = value * 2 ^ counter →
        (∀ register, register ≠ 7 → register ≠ valueRegister →
          finalState.registers register = state.registers register) →
        runNPOracleProgram binomialProgram maximumBits extra finalState =
          result) →
      runNPOracleProgram binomialProgram maximumBits
          (3 * counter + 1 + extra) state = result := by
  intro counter
  induction counter with
  | zero =>
      intro value state result hpc hcounter hvalue _ _ hfinish
      rw [show 3 * 0 + 1 + extra = extra + 1 by omega]
      rw [run_branchZero_instruction htest hpc]
      rw [hcounter, if_pos rfl]
      refine hfinish (state.jump exitPc) rfl ?_ ?_ ?_
      · simpa [NPOracleState.jump] using hcounter
      · simpa [NPOracleState.jump] using hvalue
      · intro register _ _
        rfl
  | succ counter inductionHypothesis =>
      intro value state result hpc hcounter hvalue hcounterBits hvalueBits
        hfinish
      have hdoubleLe : value * 2 ≤ value * 2 ^ (counter + 1) := by
        exact Nat.mul_le_mul_left value (by
          have : (2 : ℕ) ^ 1 ≤ 2 ^ (counter + 1) :=
            Nat.pow_le_pow_right (by positivity) (by omega)
          simpa using this)
      have hdoubleBits : natBitLength (value * 2) ≤ maximumBits :=
        (natBitLength_mono hdoubleLe).trans hvalueBits
      have hcounterPredBits : natBitLength counter ≤ maximumBits :=
        (natBitLength_mono (Nat.le_succ counter)).trans hcounterBits
      rw [show 3 * (counter + 1) + 1 + extra = 3 * counter + 1 + extra + 1 + 1 + 1
        by omega]
      rw [run_branchZero_instruction htest hpc]
      rw [hcounter, if_neg (by omega)]
      rw [run_shiftLeft_instruction (value := value * 2) hbody rfl
        (by simp only [NPOracleState.jump]; rw [hvalue, shiftLeft_one])
        hdoubleBits]
      rw [run_decrement_instruction (value := counter) hdecrement rfl
        (by
          simp only [NPOracleState.jump, NPOracleState.write,
            if_neg hvalueRegister.symm]
          rw [hcounter]
          rfl)
        hcounterPredBits]
      refine inductionHypothesis (value * 2) _ result rfl ?_ ?_
        hcounterPredBits ?_ ?_
      · simp [NPOracleState.jump, NPOracleState.write]
      · simp [NPOracleState.jump, NPOracleState.write, hvalueRegister]
      · calc
          natBitLength (value * 2 * 2 ^ counter) =
              natBitLength (value * 2 ^ (counter + 1)) := by
            rw [show value * 2 * 2 ^ counter = value * 2 ^ (counter + 1) by ring]
          _ ≤ maximumBits := hvalueBits
      · intro finalState hfinalPc hfinalCounter hfinalValue hfinalOther
        refine hfinish finalState hfinalPc hfinalCounter ?_ ?_
        · rw [hfinalValue]
          ring
        · intro register hregisterCounter hregisterValue
          rw [hfinalOther register hregisterCounter hregisterValue]
          simp [NPOracleState.jump, NPOracleState.write, hregisterCounter,
            hregisterValue]

/-- A counted loop of unit right shifts divides its register by a power of
two. -/
private theorem run_shiftRightLoop
    (testPc bodyPc decrementPc exitPc valueRegister maximumBits extra : ℕ)
    (hvalueRegister : valueRegister ≠ 7)
    (htest : binomialProgram[testPc]? = some (.branchZero 7 exitPc bodyPc))
    (hbody :
      binomialProgram[bodyPc]? =
        some (.shiftRight valueRegister 1 valueRegister decrementPc))
    (hdecrement : binomialProgram[decrementPc]? = some (.decrement 7 testPc)) :
    ∀ (counter value : ℕ) (state : NPOracleState) (result : Option ℕ),
      state.pc = testPc →
      state.registers 7 = counter →
      state.registers valueRegister = value →
      natBitLength counter ≤ maximumBits →
      natBitLength value ≤ maximumBits →
      (∀ finalState : NPOracleState,
        finalState.pc = exitPc →
        finalState.registers 7 = 0 →
        finalState.registers valueRegister = value / 2 ^ counter →
        (∀ register, register ≠ 7 → register ≠ valueRegister →
          finalState.registers register = state.registers register) →
        runNPOracleProgram binomialProgram maximumBits extra finalState =
          result) →
      runNPOracleProgram binomialProgram maximumBits
          (3 * counter + 1 + extra) state = result := by
  intro counter
  induction counter with
  | zero =>
      intro value state result hpc hcounter hvalue _ _ hfinish
      rw [show 3 * 0 + 1 + extra = extra + 1 by omega]
      rw [run_branchZero_instruction htest hpc]
      rw [hcounter, if_pos rfl]
      refine hfinish (state.jump exitPc) rfl ?_ ?_ ?_
      · simpa [NPOracleState.jump] using hcounter
      · simpa [NPOracleState.jump] using hvalue
      · intro register _ _
        rfl
  | succ counter inductionHypothesis =>
      intro value state result hpc hcounter hvalue hcounterBits hvalueBits
        hfinish
      have hhalfBits : natBitLength (value / 2) ≤ maximumBits :=
        (natBitLength_mono (Nat.div_le_self value 2)).trans hvalueBits
      have hcounterPredBits : natBitLength counter ≤ maximumBits :=
        (natBitLength_mono (Nat.le_succ counter)).trans hcounterBits
      rw [show 3 * (counter + 1) + 1 + extra = 3 * counter + 1 + extra + 1 + 1 + 1
        by omega]
      rw [run_branchZero_instruction htest hpc]
      rw [hcounter, if_neg (by omega)]
      rw [run_shiftRight_instruction (value := value / 2) hbody rfl
        (by simp only [NPOracleState.jump]; rw [hvalue, shiftRight_one])
        hhalfBits]
      rw [run_decrement_instruction (value := counter) hdecrement rfl
        (by
          simp only [NPOracleState.jump, NPOracleState.write,
            if_neg hvalueRegister.symm]
          rw [hcounter]
          rfl)
        hcounterPredBits]
      refine inductionHypothesis (value / 2) _ result rfl ?_ ?_
        hcounterPredBits hhalfBits ?_
      · simp [NPOracleState.jump, NPOracleState.write]
      · simp [NPOracleState.jump, NPOracleState.write, hvalueRegister]
      · intro finalState hfinalPc hfinalCounter hfinalValue hfinalOther
        refine hfinish finalState hfinalPc hfinalCounter ?_ ?_
        · rw [hfinalValue, Nat.div_div_eq_div_mul,
            show 2 * 2 ^ counter = 2 ^ (counter + 1) by ring]
        · intro register hregisterCounter hregisterValue
          rw [hfinalOther register hregisterCounter hregisterValue]
          simp [NPOracleState.jump, NPOracleState.write, hregisterCounter,
            hregisterValue]

/-! ## §4 The two counted outer loops -/

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

/-- The packing loop.  Each round replaces the accumulator `value` by
`value + value * 2 ^ width`, so after `remaining` rounds it holds
`value * (2 ^ width + 1) ^ remaining`. -/
private theorem run_packLoop (width maximumBits extra : ℕ)
    (hwidthBits : natBitLength width ≤ maximumBits) :
    ∀ (remaining accumulator : ℕ) (state : NPOracleState) (result : Option ℕ),
      state.pc = 6 →
      state.registers 4 = width →
      state.registers 5 = accumulator →
      state.registers 6 = remaining →
      natBitLength remaining ≤ maximumBits →
      natBitLength (accumulator * (2 ^ width + 1) ^ remaining) ≤ maximumBits →
      (∀ finalState : NPOracleState,
        finalState.pc = 14 →
        finalState.registers 6 = 0 →
        finalState.registers 5 =
          accumulator * (2 ^ width + 1) ^ remaining →
        finalState.registers 4 = width →
        finalState.registers 3 = state.registers 3 →
        runNPOracleProgram binomialProgram maximumBits extra finalState =
          result) →
      runNPOracleProgram binomialProgram maximumBits
          (remaining * (3 * width + 6) + 1 + extra) state = result := by
  intro remaining
  induction remaining with
  | zero =>
      intro accumulator state result hpc hwidth haccumulator hremaining _ _
        hfinish
      rw [show 0 * (3 * width + 6) + 1 + extra = extra + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hremaining, if_pos rfl]
      refine hfinish (state.jump 14) rfl ?_ ?_ ?_ ?_
      · simpa [NPOracleState.jump] using hremaining
      · simpa [NPOracleState.jump] using haccumulator
      · simpa [NPOracleState.jump] using hwidth
      · rfl
  | succ remaining inductionHypothesis =>
      intro accumulator state result hpc hwidth haccumulator hremaining
        hremainingBits hfinalBits hfinish
      have hpowLe :
          (2 : ℕ) ^ width + 1 ≤ (2 ^ width + 1) ^ (remaining + 1) := by
        calc
          (2 : ℕ) ^ width + 1 = (2 ^ width + 1) ^ 1 := by ring
          _ ≤ (2 ^ width + 1) ^ (remaining + 1) :=
            Nat.pow_le_pow_right (by positivity) (by omega)
      have hstepLe :
          accumulator * (2 ^ width + 1) ≤
            accumulator * (2 ^ width + 1) ^ (remaining + 1) :=
        Nat.mul_le_mul (le_refl accumulator) hpowLe
      have haccumulatorLe :
          accumulator ≤ accumulator * (2 ^ width + 1) ^ (remaining + 1) := by
        calc
          accumulator = accumulator * 1 := by ring
          _ ≤ accumulator * (2 ^ width + 1) ^ (remaining + 1) :=
            Nat.mul_le_mul (le_refl accumulator)
              (le_trans (Nat.le_add_left 1 (2 ^ width)) hpowLe)
      have hshiftLe :
          accumulator * 2 ^ width ≤
            accumulator * (2 ^ width + 1) ^ (remaining + 1) :=
        Nat.mul_le_mul (le_refl accumulator) (le_trans (by omega) hpowLe)
      have haccumulatorBits : natBitLength accumulator ≤ maximumBits :=
        bits_of_le haccumulatorLe hfinalBits
      have hshiftBits :
          natBitLength (accumulator * 2 ^ width) ≤ maximumBits :=
        bits_of_le hshiftLe hfinalBits
      have hstepBits :
          natBitLength (accumulator * (2 ^ width + 1)) ≤ maximumBits :=
        bits_of_le hstepLe hfinalBits
      have hremainingPredBits : natBitLength remaining ≤ maximumBits :=
        bits_of_le (Nat.le_succ remaining) hremainingBits
      rw [show (remaining + 1) * (3 * width + 6) + 1 + extra =
        3 * width + 1 +
            (remaining * (3 * width + 6) + 1 + extra + 1 + 1) + 1 + 1 + 1 by
        ring]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hremaining, if_neg (by omega)]
      rw [run_copy_instruction (value := accumulator) (by rfl) rfl
        (by simpa [NPOracleState.jump] using haccumulator) haccumulatorBits]
      rw [run_copy_instruction (value := width) (by rfl) rfl
        (by
          simp only [NPOracleState.jump, NPOracleState.write]
          simpa using hwidth)
        hwidthBits]
      refine run_shiftLeftLoop 9 10 11 12 8 maximumBits _ (by decide) (by rfl)
        (by rfl) (by rfl) width accumulator _ result rfl ?_ ?_ hwidthBits
        hshiftBits ?_
      · simp [NPOracleState.jump, NPOracleState.write]
      · simp [NPOracleState.jump, NPOracleState.write]
      · intro shiftState hshiftPc hshiftCounter hshiftValue hshiftOther
        have haccumulatorAt : shiftState.registers 5 = accumulator := by
          rw [hshiftOther 5 (by decide) (by decide)]
          simpa [NPOracleState.jump, NPOracleState.write] using haccumulator
        have hwidthAt : shiftState.registers 4 = width := by
          rw [hshiftOther 4 (by decide) (by decide)]
          simpa [NPOracleState.jump, NPOracleState.write] using hwidth
        have hremainingAt : shiftState.registers 6 = remaining + 1 := by
          rw [hshiftOther 6 (by decide) (by decide)]
          simpa [NPOracleState.jump, NPOracleState.write] using hremaining
        have hpositionAt : shiftState.registers 3 = state.registers 3 := by
          rw [hshiftOther 3 (by decide) (by decide)]
          simp [NPOracleState.jump, NPOracleState.write]
        rw [run_add_instruction (value := accumulator * (2 ^ width + 1))
          (by rfl) hshiftPc
          (by rw [haccumulatorAt, hshiftValue]; ring) hstepBits]
        rw [run_decrement_instruction (value := remaining) (by rfl) rfl
          (by
            simp [NPOracleState.jump, NPOracleState.write, hremainingAt])
          hremainingPredBits]
        refine inductionHypothesis (accumulator * (2 ^ width + 1)) _ result rfl
          ?_ ?_ ?_ hremainingPredBits ?_ ?_
        · simp only [NPOracleState.jump, NPOracleState.write]
          simpa using hwidthAt
        · simp [NPOracleState.jump, NPOracleState.write]
        · simp [NPOracleState.jump, NPOracleState.write]
        · calc
            natBitLength
                (accumulator * (2 ^ width + 1) * (2 ^ width + 1) ^ remaining) =
                natBitLength
                  (accumulator * (2 ^ width + 1) ^ (remaining + 1)) := by
              rw [show
                accumulator * (2 ^ width + 1) * (2 ^ width + 1) ^ remaining =
                  accumulator * (2 ^ width + 1) ^ (remaining + 1) by ring]
            _ ≤ maximumBits := hfinalBits
        · intro finalState hfinalPc hfinalRemaining hfinalAccumulator
            hfinalWidth hfinalPosition
          refine hfinish finalState hfinalPc hfinalRemaining ?_ hfinalWidth ?_
          · rw [hfinalAccumulator]
            ring
          · rw [hfinalPosition]
            simp only [NPOracleState.jump, NPOracleState.write]
            simpa using hpositionAt

/-- The extraction loop.  Each round divides the packed row by `2 ^ width`, so
after `remaining` rounds the register holds the row shifted down by
`remaining` whole digits. -/
private theorem run_extractLoop (width maximumBits extra : ℕ)
    (hwidthBits : natBitLength width ≤ maximumBits) :
    ∀ (remaining value : ℕ) (state : NPOracleState) (result : Option ℕ),
      state.pc = 15 →
      state.registers 4 = width →
      state.registers 5 = value →
      state.registers 6 = remaining →
      natBitLength remaining ≤ maximumBits →
      natBitLength value ≤ maximumBits →
      (∀ finalState : NPOracleState,
        finalState.pc = 21 →
        finalState.registers 6 = 0 →
        finalState.registers 5 = value / (2 ^ width) ^ remaining →
        finalState.registers 4 = width →
        runNPOracleProgram binomialProgram maximumBits extra finalState =
          result) →
      runNPOracleProgram binomialProgram maximumBits
          (remaining * (3 * width + 4) + 1 + extra) state = result := by
  intro remaining
  induction remaining with
  | zero =>
      intro value state result hpc hwidth hvalue hremaining _ _ hfinish
      rw [show 0 * (3 * width + 4) + 1 + extra = extra + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hremaining, if_pos rfl]
      refine hfinish (state.jump 21) rfl ?_ ?_ ?_
      · simpa [NPOracleState.jump] using hremaining
      · simpa [NPOracleState.jump] using hvalue
      · simpa [NPOracleState.jump] using hwidth
  | succ remaining inductionHypothesis =>
      intro value state result hpc hwidth hvalue hremaining hremainingBits
        hvalueBits hfinish
      have hshiftBits : natBitLength (value / 2 ^ width) ≤ maximumBits :=
        bits_of_le (Nat.div_le_self value (2 ^ width)) hvalueBits
      have hremainingPredBits : natBitLength remaining ≤ maximumBits :=
        bits_of_le (Nat.le_succ remaining) hremainingBits
      rw [show (remaining + 1) * (3 * width + 4) + 1 + extra =
        3 * width + 1 + (remaining * (3 * width + 4) + 1 + extra + 1) + 1 + 1 by
        ring]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hremaining, if_neg (by omega)]
      rw [run_copy_instruction (value := width) (by rfl) rfl
        (by simpa [NPOracleState.jump] using hwidth) hwidthBits]
      refine run_shiftRightLoop 17 18 19 20 5 maximumBits _ (by decide) (by rfl)
        (by rfl) (by rfl) width value _ result rfl ?_ ?_ hwidthBits hvalueBits
        ?_
      · simp [NPOracleState.jump, NPOracleState.write]
      · simp only [NPOracleState.jump, NPOracleState.write]
        simpa using hvalue
      · intro shiftState hshiftPc hshiftCounter hshiftValue hshiftOther
        have hwidthAt : shiftState.registers 4 = width := by
          rw [hshiftOther 4 (by decide) (by decide)]
          simpa [NPOracleState.jump, NPOracleState.write] using hwidth
        have hremainingAt : shiftState.registers 6 = remaining + 1 := by
          rw [hshiftOther 6 (by decide) (by decide)]
          simpa [NPOracleState.jump, NPOracleState.write] using hremaining
        rw [run_decrement_instruction (value := remaining) (by rfl) hshiftPc
          (by rw [hremainingAt]; rfl) hremainingPredBits]
        refine inductionHypothesis (value / 2 ^ width) _ result rfl ?_ ?_ ?_
          hremainingPredBits hshiftBits ?_
        · simp only [NPOracleState.jump, NPOracleState.write]
          simpa using hwidthAt
        · simp only [NPOracleState.jump, NPOracleState.write]
          simpa using hshiftValue
        · simp [NPOracleState.jump, NPOracleState.write]
        · intro finalState hfinalPc hfinalRemaining hfinalValue hfinalWidth
          refine hfinish finalState hfinalPc hfinalRemaining ?_ hfinalWidth
          rw [hfinalValue, Nat.div_div_eq_div_mul,
            show 2 ^ width * (2 ^ width) ^ remaining =
              (2 ^ width) ^ (remaining + 1) by ring]

/-! ## §5 Public width, clock, and exact execution -/

/-- Public paired ABI: `Nat.pair count position`. -/
def binomialInput (count position : ℕ) : ℕ :=
  Nat.pair count position

/-- Every register value the program ever writes is bounded by this closed
number: the packed row one round beyond its final size. -/
def binomialRegisterBound (count position : ℕ) : ℕ :=
  position + (2 ^ binomialWidth count + 1) ^ binomialWidth count

def binomialBits (count position : ℕ) : ℕ :=
  natBitLength (binomialRegisterBound count position)

def binomialFuel (count position : ℕ) : ℕ :=
  count * (3 * binomialWidth count + 6) +
    position * (3 * binomialWidth count + 4) + 6 * binomialWidth count + 16

private theorem width_le_registerBound (count position : ℕ) :
    binomialWidth count ≤ binomialRegisterBound count position := by
  have hself : (2 : ℕ) ^ binomialWidth count + 1 ≤
      (2 ^ binomialWidth count + 1) ^ binomialWidth count :=
    Nat.le_self_pow (by unfold binomialWidth; omega) _
  have hsmall : binomialWidth count < 2 ^ binomialWidth count :=
    Nat.lt_two_pow_self
  unfold binomialRegisterBound
  omega

private theorem count_le_registerBound (count position : ℕ) :
    count ≤ binomialRegisterBound count position := by
  have hwidth := width_le_registerBound count position
  unfold binomialWidth at hwidth
  omega

private theorem one_le_registerBound (count position : ℕ) :
    1 ≤ binomialRegisterBound count position := by
  have hwidth := width_le_registerBound count position
  unfold binomialWidth at hwidth
  omega

private theorem position_le_registerBound (count position : ℕ) :
    position ≤ binomialRegisterBound count position :=
  Nat.le_add_right _ _

private theorem row_le_registerBound (count position : ℕ) :
    packedPascalRow count ≤ binomialRegisterBound count position := by
  have hmonotone :
      (2 ^ binomialWidth count + 1) ^ count ≤
        (2 ^ binomialWidth count + 1) ^ binomialWidth count :=
    Nat.pow_le_pow_right (by positivity) (by unfold binomialWidth; omega)
  unfold binomialRegisterBound packedPascalRow
  omega

private theorem sub_div_mul (value divisor : ℕ) :
    value - value / divisor * divisor = value % divisor := by
  have hdivision := Nat.div_add_mod value divisor
  have hcommute : value / divisor * divisor = divisor * (value / divisor) :=
    Nat.mul_comm _ _
  omega

set_option maxHeartbeats 800000 in
-- The six setup steps, two counted outer loops, and the low-digit mask are
-- discharged in one chain, so the intermediate machine states stay implicit.
/-- **The exact binomial coefficient, executed.**  One fixed oracle-free
program returns `Nat.choose count position` from the paired ABI, with a closed
width bound and a closed clock. -/
theorem run_binomialProgram (inputLength count position maximumBits : ℕ)
    (hbits : binomialBits count position ≤ maximumBits) :
    runNPOracleProgram binomialProgram maximumBits
        (binomialFuel count position)
        (initialNPOracleState inputLength (binomialInput count position)) =
      some (Nat.choose count position) := by
  have hboundBits :
      natBitLength (binomialRegisterBound count position) ≤ maximumBits :=
    hbits
  have hcountBits : natBitLength count ≤ maximumBits :=
    bits_of_le (count_le_registerBound count position) hboundBits
  have hpositionBits : natBitLength position ≤ maximumBits :=
    bits_of_le (position_le_registerBound count position) hboundBits
  have hwidthBits : natBitLength (binomialWidth count) ≤ maximumBits :=
    bits_of_le (width_le_registerBound count position) hboundBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    bits_of_le (one_le_registerBound count position) hboundBits
  have hrowBits : natBitLength (packedPascalRow count) ≤ maximumBits :=
    bits_of_le (row_le_registerBound count position) hboundBits
  have hshiftedLe :
      packedPascalRow count / (2 ^ binomialWidth count) ^ position ≤
        packedPascalRow count :=
    Nat.div_le_self _ _
  have hshiftedBits :
      natBitLength
          (packedPascalRow count / (2 ^ binomialWidth count) ^ position) ≤
        maximumBits :=
    bits_of_le hshiftedLe hrowBits
  rw [show binomialFuel count position =
      count * (3 * binomialWidth count + 6) + 1 +
            (position * (3 * binomialWidth count + 4) + 1 +
              (6 * binomialWidth count + 7) + 1) +
          1 + 1 + 1 + 1 + 1 + 1 by
    unfold binomialFuel
    ring]
  rw [run_unpairLeft_instruction (value := count) (by rfl) rfl
    (by simp [initialNPOracleState, binomialInput]) hcountBits]
  rw [run_unpairRight_instruction (value := position) (by rfl) rfl
    (by
      simp [initialNPOracleState, binomialInput, NPOracleState.write,
        NPOracleState.jump])
    hpositionBits]
  rw [run_copy_instruction (value := count) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountBits]
  rw [run_increment_instruction (value := binomialWidth count) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, binomialWidth])
    hwidthBits]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  rw [run_copy_instruction (value := count) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountBits]
  refine run_packLoop (binomialWidth count) maximumBits _ hwidthBits count 1 _ _
    rfl ?_ ?_ ?_ hcountBits ?_ ?_
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact bits_of_le (le_of_eq (one_mul _)) hrowBits
  · intro packedState hpackedPc hpackedRemaining hpackedRow hpackedWidth
      hpackedPosition
    have hpackedRowValue :
        packedState.registers 5 = packedPascalRow count := by
      rw [hpackedRow, one_mul]
      rfl
    have hpackedPositionValue : packedState.registers 3 = position := by
      rw [hpackedPosition]
      simp [NPOracleState.write, NPOracleState.jump]
    rw [run_copy_instruction (value := position) (by rfl) hpackedPc
      hpackedPositionValue hpositionBits]
    refine run_extractLoop (binomialWidth count) maximumBits _ hwidthBits
      position (packedPascalRow count) _ _ (by rfl) ?_ ?_ ?_ hpositionBits
      hrowBits ?_
    · simp only [NPOracleState.write, NPOracleState.jump]
      simpa using hpackedWidth
    · simp only [NPOracleState.write, NPOracleState.jump]
      simpa using hpackedRowValue
    · simp [NPOracleState.write, NPOracleState.jump]
    · intro shiftedState hshiftedPc hshiftedRemaining hshiftedValue
        hshiftedWidth
      rw [show 6 * binomialWidth count + 7 =
          3 * binomialWidth count + 1 + (3 * binomialWidth count + 4) + 1 + 1 by
        ring]
      rw [run_copy_instruction
        (value := packedPascalRow count / (2 ^ binomialWidth count) ^ position)
        (by rfl) hshiftedPc hshiftedValue hshiftedBits]
      rw [run_copy_instruction (value := binomialWidth count) (by rfl) rfl
        (by
          simp only [NPOracleState.write, NPOracleState.jump]
          simpa using hshiftedWidth)
        hwidthBits]
      refine run_shiftRightLoop 23 24 25 26 8 maximumBits _ (by decide) (by rfl)
        (by rfl) (by rfl) (binomialWidth count)
        (packedPascalRow count / (2 ^ binomialWidth count) ^ position) _ _
        (by rfl) ?_ ?_ hwidthBits hshiftedBits ?_
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro downState hdownPc hdownCounter hdownValue hdownOther
        have hdownWidth : downState.registers 4 = binomialWidth count := by
          rw [hdownOther 4 (by decide) (by decide)]
          simp only [NPOracleState.write, NPOracleState.jump]
          simpa using hshiftedWidth
        have hdownRemainder :
            downState.registers 5 =
              packedPascalRow count / (2 ^ binomialWidth count) ^ position := by
          rw [hdownOther 5 (by decide) (by decide)]
          simp only [NPOracleState.write, NPOracleState.jump]
          simpa using hshiftedValue
        have hmaskLe :
            packedPascalRow count / (2 ^ binomialWidth count) ^ position /
                  2 ^ binomialWidth count * 2 ^ binomialWidth count ≤
              packedPascalRow count / (2 ^ binomialWidth count) ^ position :=
          Nat.div_mul_le_self _ _
        rw [run_copy_instruction (value := binomialWidth count) (by rfl) hdownPc
          hdownWidth hwidthBits]
        rw [show 3 * binomialWidth count + 3 =
            3 * binomialWidth count + 1 + 2 by
          ring]
        refine run_shiftLeftLoop 27 28 29 30 8 maximumBits _ (by decide)
          (by rfl) (by rfl) (by rfl) (binomialWidth count)
          (packedPascalRow count / (2 ^ binomialWidth count) ^ position /
            2 ^ binomialWidth count) _ _ ?_ ?_ ?_ hwidthBits ?_ ?_
        · rfl
        · simp [NPOracleState.write, NPOracleState.jump]
        · simp only [NPOracleState.write, NPOracleState.jump]
          simpa using hdownValue
        · exact bits_of_le hmaskLe hshiftedBits
        · intro maskState hmaskPc hmaskCounter hmaskValue hmaskOther
          have hmaskRemainder :
              maskState.registers 5 =
                packedPascalRow count /
                  (2 ^ binomialWidth count) ^ position := by
            rw [hmaskOther 5 (by decide) (by decide)]
            simp only [NPOracleState.write, NPOracleState.jump]
            simpa using hdownRemainder
          have hdigitBits :
              natBitLength (Nat.choose count position) ≤ maximumBits := by
            refine bits_of_le ?_ hshiftedBits
            rw [← packedPascalRow_digit count position]
            exact Nat.mod_le _ _
          rw [run_subtract_instruction (value := Nat.choose count position)
            (by rfl) hmaskPc
            (by
              rw [hmaskRemainder, hmaskValue, sub_div_mul,
                packedPascalRow_digit])
            hdigitBits]
          exact run_halt_instruction (fuel := 0)
            (value := Nat.choose count position) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump]) hdigitBits

/-- The same execution stated directly on the pairing constructor, which is
the form every linker stage sees. -/
theorem run_binomialProgram_pair (inputLength count position maximumBits : ℕ)
    (hbits : binomialBits count position ≤ maximumBits) :
    runNPOracleProgram binomialProgram maximumBits
        (binomialFuel count position)
        (initialNPOracleState inputLength (Nat.pair count position)) =
      some (Nat.choose count position) :=
  run_binomialProgram inputLength count position maximumBits hbits

end NearCubicWires.CanonicalBinomialProgram
