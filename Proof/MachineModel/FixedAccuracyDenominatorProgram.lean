import Proof.Foundations.CanonicalBinaryProgram
import Proof.Foundations.ExecutableInterfaces
import Proof.Foundations.Semantics

/-!
# Fixed inverse-polynomial accuracy schedule

The accuracy exponent is fixed before the weak machine is chosen.  This file
therefore compiles that exponent into one oracle-free program computing
`q ^ exponent` from the public arity `q`; there is no run-time function,
certificate, or precomputed denominator in the request ABI.
-/

namespace NearCubicWires.FixedAccuracyDenominatorProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

private theorem state_eq
    (left right : NPOracleState)
    (hpc : left.pc = right.pc)
    (hregisters : ∀ register, left.registers register =
      right.registers register) :
    left = right := by
  cases left with
  | mk leftPc leftRegisters =>
      cases right with
      | mk rightPc rightRegisters =>
          simp only [NPOracleState.mk.injEq] at *
          exact ⟨hpc, funext hregisters⟩

/-- The unique run-time denominator schedule used by the normalized supplier. -/
def fixedTargetDenominator (exponent q : ℕ) : ℕ :=
  q ^ exponent

/-- Public real accuracy is rounded only once, before the program family is
chosen.  The request still carries no exponent or denominator field. -/
noncomputable def compiledAccuracyExponent
    (accuracyExponent : ℝ) : ℕ :=
  ⌈accuracyExponent⌉₊

theorem accuracyExponent_le_compiled
    (accuracyExponent : ℝ) :
    accuracyExponent ≤ (compiledAccuracyExponent accuracyExponent : ℝ) := by
  exact Nat.le_ceil accuracyExponent

/-- Repeated addition and a fixed-exponent outer loop.  All values remain
binary naturals; the loops affect time, not the representation width.

Registers are: input/output `r0`, base `r1`, exponent cursor `r2`, result
`r3`, multiplication cursor `r4`, and addition cursor `r5`. -/
def fixedTargetDenominatorProgram (exponent : ℕ) : NPOracleProgram :=
  [ .copy 0 1 1
  , .set 2 exponent 2
  , .set 3 1 3
  , .branchZero 2 13 4
  , .decrement 2 5
  , .copy 3 4 6
  , .set 3 0 7
  , .branchZero 4 3 8
  , .decrement 4 9
  , .copy 1 5 10
  , .branchZero 5 7 11
  , .decrement 5 12
  , .increment 3 10
  , .copy 3 0 14
  , .halt 0
  ]

@[simp] theorem fixedTargetDenominatorProgram_oracleFree
    (exponent : ℕ) :
    OracleFree (fixedTargetDenominatorProgram exponent) := by
  rfl

@[simp] theorem fixedTargetDenominatorProgram_length
    (exponent : ℕ) :
    (fixedTargetDenominatorProgram exponent).length = 15 := by
  rfl

private def additionFuel : ℕ → ℕ
  | 0 => 1
  | remaining + 1 => 3 + additionFuel remaining

private def multiplicationFuel (base : ℕ) : ℕ → ℕ
  | 0 => 1
  | remaining + 1 =>
      3 + additionFuel base + multiplicationFuel base remaining

private def powerFuel (base : ℕ) : ℕ → ℕ → ℕ
  | _result, 0 => 3
  | result, remaining + 1 =>
      4 + multiplicationFuel base result +
        powerFuel base (result * base) remaining

def fixedTargetDenominatorFuel (exponent q : ℕ) : ℕ :=
  3 + powerFuel q 1 exponent

private def registerBound (exponent q : ℕ) : ℕ :=
  max exponent (max q (max 1 (q ^ exponent))) + 1

def fixedTargetDenominatorBits (exponent q : ℕ) : ℕ :=
  natBitLength (registerBound exponent q)

private theorem boundedBits
    {exponent q value maximumBits : ℕ}
    (hvalue : value ≤ registerBound exponent q)
    (hbits : fixedTargetDenominatorBits exponent q ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

private theorem exponent_le_bound (exponent q : ℕ) :
    exponent ≤ registerBound exponent q := by
  unfold registerBound
  omega

private theorem base_le_bound (exponent q : ℕ) :
    q ≤ registerBound exponent q := by
  unfold registerBound
  omega

private theorem one_le_bound (exponent q : ℕ) :
    1 ≤ registerBound exponent q := by
  unfold registerBound
  omega

private theorem finalPower_le_bound (exponent q : ℕ) :
    q ^ exponent ≤ registerBound exponent q := by
  unfold registerBound
  omega

private theorem partialPower_le_max
    (q processed exponent : ℕ) (hprocessed : processed ≤ exponent) :
    q ^ processed ≤ max 1 (q ^ exponent) := by
  cases q with
  | zero =>
      cases processed <;> simp
  | succ q =>
      exact
        (Nat.pow_le_pow_right (by omega : 0 < q + 1) hprocessed).trans
          (le_max_right _ _)

private theorem partialPower_le_bound
    (q processed exponent : ℕ) (hprocessed : processed ≤ exponent) :
    q ^ processed ≤ registerBound exponent q := by
  exact
    (partialPower_le_max q processed exponent hprocessed).trans <|
      (le_max_right q _).trans <|
        (le_max_right exponent _).trans (Nat.le_add_right _ _)

private theorem additionTrace
    (exponent q accumulator remaining maximumBits extra : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 10)
    (haccumulator : state.registers 3 = accumulator)
    (hremaining : state.registers 5 = remaining)
    (hbound : accumulator + remaining ≤ registerBound exponent q)
    (hbits : fixedTargetDenominatorBits exponent q ≤ maximumBits) :
    runNPOracleProgram (fixedTargetDenominatorProgram exponent) maximumBits
        (additionFuel remaining + extra) state =
      runNPOracleProgram (fixedTargetDenominatorProgram exponent) maximumBits
        extra
        (((state.write 3 (accumulator + remaining)).write 5 0).jump 7) := by
  induction remaining generalizing accumulator state with
  | zero =>
      rw [show additionFuel 0 + extra = extra + 1 by
        simp [additionFuel, Nat.add_comm]]
      rw [run_branchZero_instruction (fuel := extra) (by rfl) hpc]
      rw [hremaining, if_pos rfl]
      congr 2
      apply state_eq
      · simp [NPOracleState.write]
      · intro register
        by_cases hregisterThree : register = 3
        · subst register
          simp [haccumulator]
        · by_cases hregisterFive : register = 5
          · subst register
            simp [hremaining]
          · simp [NPOracleState.write, hregisterThree, hregisterFive]
  | succ remaining inductionHypothesis =>
      have hincrementBits :
          natBitLength (accumulator + 1) ≤ maximumBits := by
        apply boundedBits (hbits := hbits)
        omega
      have hremainingBits :
          natBitLength remaining ≤ maximumBits := by
        apply boundedBits (hbits := hbits)
        omega
      rw [show additionFuel (remaining + 1) + extra =
        (2 + additionFuel remaining + extra) + 1 by
          simp [additionFuel]
          omega]
      rw [run_branchZero_instruction
        (fuel := 2 + additionFuel remaining + extra) (by rfl) hpc]
      rw [hremaining, if_neg (Nat.succ_ne_zero remaining)]
      rw [show 2 + additionFuel remaining + extra =
        (1 + additionFuel remaining + extra) + 1 by omega]
      rw [run_decrement_instruction
        (fuel := 1 + additionFuel remaining + extra)
        (value := remaining) (by rfl) rfl
        (by simp [NPOracleState.jump, hremaining])
        hremainingBits]
      rw [show 1 + additionFuel remaining + extra =
        (additionFuel remaining + extra) + 1 by omega]
      rw [run_increment_instruction
        (fuel := additionFuel remaining + extra)
        (value := accumulator + 1) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, haccumulator])
        hincrementBits]
      rw [inductionHypothesis (accumulator := accumulator + 1)
        (state :=
          ((((state.jump 11).write 5 remaining).jump 12).write 3
            (accumulator + 1)).jump 10)
        rfl
        (by simp)
        (by simp)
        (by omega)]
      congr 2
      apply state_eq
      · simpa [NPOracleState.write, NPOracleState.jump] using hpc.symm
      · intro register
        by_cases hregisterThree : register = 3
        · subst register
          simp [NPOracleState.write]
          omega
        · by_cases hregisterFive : register = 5
          · subst register
            simp [NPOracleState.write]
          · simp [NPOracleState.write, hregisterThree, hregisterFive]

private theorem multiplicationTrace
    (exponent q base accumulator remaining maximumBits extra : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 7)
    (hbase : state.registers 1 = base)
    (haccumulator : state.registers 3 = accumulator)
    (hremaining : state.registers 4 = remaining)
    (hadditionZero : state.registers 5 = 0)
    (hbound :
      accumulator + remaining * base ≤ registerBound exponent q)
    (hremainingBound : remaining ≤ registerBound exponent q)
    (hbaseBound : base ≤ registerBound exponent q)
    (hbits : fixedTargetDenominatorBits exponent q ≤ maximumBits) :
    runNPOracleProgram (fixedTargetDenominatorProgram exponent) maximumBits
        (multiplicationFuel base remaining + extra) state =
      runNPOracleProgram (fixedTargetDenominatorProgram exponent) maximumBits
        extra
        ((((state.write 3 (accumulator + remaining * base)).write 4 0).write
          5 0).jump 3) := by
  induction remaining generalizing accumulator state with
  | zero =>
      rw [show multiplicationFuel base 0 + extra = extra + 1 by
        simp [multiplicationFuel, Nat.add_comm]]
      rw [run_branchZero_instruction (fuel := extra) (by rfl) hpc]
      rw [hremaining, if_pos rfl]
      congr 2
      apply state_eq
      · simp [NPOracleState.write]
      · intro register
        by_cases hregisterThree : register = 3
        · subst register
          simp [haccumulator]
        · by_cases hregisterFour : register = 4
          · subst register
            simp [hremaining]
          · by_cases hregisterFive : register = 5
            · subst register
              simp [hadditionZero]
            · simp [NPOracleState.write, hregisterThree, hregisterFour,
                hregisterFive]
  | succ remaining inductionHypothesis =>
      have hremainingBits :
          natBitLength remaining ≤ maximumBits := by
        exact boundedBits (by omega) hbits
      have hbaseBits :
          natBitLength base ≤ maximumBits :=
        boundedBits hbaseBound hbits
      have hzeroBits : natBitLength 0 ≤ maximumBits :=
        boundedBits (Nat.zero_le _) hbits
      rw [show multiplicationFuel base (remaining + 1) + extra =
        (2 + additionFuel base +
          multiplicationFuel base remaining + extra) + 1 by
            simp [multiplicationFuel]
            omega]
      rw [run_branchZero_instruction
        (fuel := 2 + additionFuel base +
          multiplicationFuel base remaining + extra) (by rfl) hpc]
      rw [hremaining, if_neg (Nat.succ_ne_zero remaining)]
      rw [show 2 + additionFuel base +
          multiplicationFuel base remaining + extra =
        (1 + additionFuel base +
          multiplicationFuel base remaining + extra) + 1 by omega]
      rw [run_decrement_instruction
        (fuel := 1 + additionFuel base +
          multiplicationFuel base remaining + extra)
        (value := remaining) (by rfl) rfl
        (by simp [NPOracleState.jump, hremaining])
        hremainingBits]
      rw [show 1 + additionFuel base +
          multiplicationFuel base remaining + extra =
        (additionFuel base +
          multiplicationFuel base remaining + extra) + 1 by omega]
      rw [run_copy_instruction
        (fuel := additionFuel base +
          multiplicationFuel base remaining + extra)
        (value := base) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hbase])
        hbaseBits]
      rw [show additionFuel base +
          multiplicationFuel base remaining + extra =
        additionFuel base +
          (multiplicationFuel base remaining + extra) by omega]
      rw [additionTrace exponent q accumulator base maximumBits
        (multiplicationFuel base remaining + extra)
        _
        rfl
        (by simp [haccumulator])
        (by simp)
        (by
          calc
            accumulator + base ≤
                accumulator + (remaining + 1) * base := by
                  rw [Nat.succ_mul]
                  omega
            _ ≤ registerBound exponent q := hbound)
        hbits]
      rw [inductionHypothesis (accumulator := accumulator + base)
        (state :=
          (((((((state.jump 8).write 4 remaining).jump 9).write 5 base).jump
            10).write 3 (accumulator + base)).write 5 0).jump 7)
        rfl
        (by simp [hbase])
        (by simp)
        (by simp)
        (by simp)
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            Nat.succ_mul] using hbound)
        (by omega)]
      congr 2
      apply state_eq
      · simpa [NPOracleState.write, NPOracleState.jump] using hpc.symm
      · intro register
        by_cases hregisterThree : register = 3
        · subst register
          simp [NPOracleState.write, Nat.succ_mul, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm]
        · by_cases hregisterFour : register = 4
          · subst register
            simp [NPOracleState.write]
          · by_cases hregisterFive : register = 5
            · subst register
              simp [NPOracleState.write]
            · simp [NPOracleState.write, hregisterThree, hregisterFour,
                hregisterFive]

private theorem powerTrace
    (exponent q processed remaining maximumBits : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 3)
    (hprocessed : processed + remaining = exponent)
    (hbase : state.registers 1 = q)
    (hexponent : state.registers 2 = remaining)
    (hresult : state.registers 3 = q ^ processed)
    (hmultiplicationZero : state.registers 4 = 0)
    (hadditionZero : state.registers 5 = 0)
    (hbits : fixedTargetDenominatorBits exponent q ≤ maximumBits) :
    runNPOracleProgram (fixedTargetDenominatorProgram exponent) maximumBits
        (powerFuel q (q ^ processed) remaining) state =
      some (fixedTargetDenominator exponent q) := by
  induction remaining generalizing processed state with
  | zero =>
      have hprocessedEq : processed = exponent := by
        omega
      have hresultBits :
          natBitLength (q ^ exponent) ≤ maximumBits :=
        boundedBits (finalPower_le_bound exponent q) hbits
      rw [show powerFuel q (q ^ processed) 0 = (1 + 1) + 1 by rfl]
      rw [run_branchZero_instruction (fuel := 2) (by rfl) hpc]
      rw [hexponent, if_pos rfl]
      rw [show 2 = 1 + 1 by rfl]
      rw [run_copy_instruction (fuel := 1)
        (value := q ^ exponent) (by rfl) rfl
        (by
          simpa [NPOracleState.jump, hprocessedEq] using hresult)
        hresultBits]
      exact run_halt_instruction (fuel := 0)
        (value := fixedTargetDenominator exponent q) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump,
          fixedTargetDenominator])
        (by simpa [fixedTargetDenominator] using hresultBits)
  | succ remaining inductionHypothesis =>
      have hremainingBits :
          natBitLength remaining ≤ maximumBits := by
        apply boundedBits (hbits := hbits)
        exact (by
          have : remaining ≤ exponent := by omega
          exact this.trans (exponent_le_bound exponent q))
      have hresultBound :
          q ^ processed ≤ registerBound exponent q :=
        partialPower_le_bound q processed exponent (by omega)
      have hresultBits :
          natBitLength (q ^ processed) ≤ maximumBits :=
        boundedBits hresultBound hbits
      have hzeroBits : natBitLength 0 ≤ maximumBits :=
        boundedBits (Nat.zero_le _) hbits
      have hnextProcessed : processed + 1 + remaining = exponent := by
        omega
      have hnextPowerBound :
          q ^ (processed + 1) ≤ registerBound exponent q :=
        partialPower_le_bound q (processed + 1) exponent (by omega)
      rw [show powerFuel q (q ^ processed) (remaining + 1) =
        (3 + multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining) + 1 by
            simp [powerFuel]
            omega]
      rw [run_branchZero_instruction
        (fuel := 3 + multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining)
        (by rfl) hpc]
      rw [hexponent, if_neg (Nat.succ_ne_zero remaining)]
      rw [show 3 + multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining =
        (2 + multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining) + 1 by omega]
      rw [run_decrement_instruction
        (fuel := 2 + multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining)
        (value := remaining) (by rfl) rfl
        (by simp [NPOracleState.jump, hexponent])
        hremainingBits]
      rw [show 2 + multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining =
        (1 + multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining) + 1 by omega]
      rw [run_copy_instruction
        (fuel := 1 + multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining)
        (value := q ^ processed) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hresult])
        hresultBits]
      rw [show 1 + multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining =
        (multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining) + 1 by omega]
      rw [run_set_instruction
        (fuel := multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining)
        (by rfl) rfl hzeroBits]
      rw [show multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ processed * q) remaining =
        multiplicationFuel q (q ^ processed) +
          powerFuel q (q ^ (processed + 1)) remaining by
            rw [pow_succ]]
      rw [multiplicationTrace exponent q q 0 (q ^ processed) maximumBits
        (powerFuel q (q ^ (processed + 1)) remaining)
        _
        rfl
        (by simp [hbase])
        (by simp)
        (by simp)
        (by simp [hadditionZero])
        (by simpa [pow_succ] using hnextPowerBound)
        hresultBound
        (base_le_bound exponent q)
        hbits]
      apply inductionHypothesis (processed := processed + 1)
      · rfl
      · exact hnextProcessed
      · simp [hbase]
      · simp
      · simp [pow_succ]
      · simp
      · simp

theorem run_fixedTargetDenominatorProgram
    (exponent q maximumBits : ℕ)
    (hbits : fixedTargetDenominatorBits exponent q ≤ maximumBits) :
    runNPOracleProgram (fixedTargetDenominatorProgram exponent) maximumBits
        (fixedTargetDenominatorFuel exponent q)
        (initialNPOracleState q q) =
      some (fixedTargetDenominator exponent q) := by
  have hbaseBits :
      natBitLength q ≤ maximumBits :=
    boundedBits (base_le_bound exponent q) hbits
  have hexponentBits :
      natBitLength exponent ≤ maximumBits :=
    boundedBits (exponent_le_bound exponent q) hbits
  have honeBits :
      natBitLength 1 ≤ maximumBits :=
    boundedBits (one_le_bound exponent q) hbits
  rw [show fixedTargetDenominatorFuel exponent q =
    (2 + powerFuel q 1 exponent) + 1 by
      unfold fixedTargetDenominatorFuel
      omega]
  rw [run_copy_instruction (fuel := 2 + powerFuel q 1 exponent)
    (value := q) (by rfl) rfl
    (by simp [initialNPOracleState]) hbaseBits]
  rw [show 2 + powerFuel q 1 exponent =
    (1 + powerFuel q 1 exponent) + 1 by omega]
  rw [run_set_instruction (fuel := 1 + powerFuel q 1 exponent)
    (by rfl) rfl hexponentBits]
  rw [show 1 + powerFuel q 1 exponent =
    powerFuel q 1 exponent + 1 by omega]
  rw [run_set_instruction (fuel := powerFuel q 1 exponent)
    (by rfl) rfl honeBits]
  simpa using
    powerTrace exponent q 0 exponent maximumBits _
      rfl (by omega)
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      hbits

/-- The supplier's successor denominator is at least the exact inverse-power
denominator required by the headline accuracy. -/
theorem reciprocal_fixedTargetDenominator_succ_le
    (exponent q : ℕ) (hq : 0 < q) :
    (1 : ℝ) / (fixedTargetDenominator exponent q + 1 : ℕ) ≤
      inversePolynomialAdvantage q (exponent : ℝ) := by
  rw [show inversePolynomialAdvantage q (exponent : ℝ) =
      (1 : ℝ) / (q ^ exponent : ℕ) by
    unfold inversePolynomialAdvantage
    calc
      Real.rpow (q : ℝ) (-(exponent : ℝ)) =
          (Real.rpow (q : ℝ) (exponent : ℝ))⁻¹ :=
        Real.rpow_neg (by positivity) _
      _ = ((q : ℝ) ^ exponent)⁻¹ := by
        congr 1
        exact Real.rpow_natCast (q : ℝ) exponent
      _ = (1 : ℝ) / (q ^ exponent : ℕ) := by
        push_cast
        rw [one_div]]
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast
      (Nat.le_add_right (q ^ exponent) 1)

/-- Rounding a public real exponent upward only tightens the failure bound. -/
theorem reciprocal_compiledAccuracyExponent_succ_le
    (accuracyExponent : ℝ) (q : ℕ) (hq : 0 < q) :
    (1 : ℝ) /
        (fixedTargetDenominator
          (compiledAccuracyExponent accuracyExponent) q + 1 : ℕ) ≤
      inversePolynomialAdvantage q accuracyExponent := by
  calc
    (1 : ℝ) /
        (fixedTargetDenominator
          (compiledAccuracyExponent accuracyExponent) q + 1 : ℕ) ≤
        inversePolynomialAdvantage q
          (compiledAccuracyExponent accuracyExponent : ℝ) :=
      reciprocal_fixedTargetDenominator_succ_le
        (compiledAccuracyExponent accuracyExponent) q hq
    _ ≤ inversePolynomialAdvantage q accuracyExponent := by
      unfold inversePolynomialAdvantage
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (Nat.succ_le_iff.mp hq)
      · linarith [accuracyExponent_le_compiled accuracyExponent]

end NearCubicWires.FixedAccuracyDenominatorProgram
