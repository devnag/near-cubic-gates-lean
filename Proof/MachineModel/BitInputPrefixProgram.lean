import Proof.Foundations.CanonicalBinaryProgram
import Proof.Foundations.ExecutableInterfaces
import Proof.Foundations.PolynomialClock

/-!
# Canonical low-bit input projection

Imported evaluators receive the canonical code of their exact input arity.
When a recovered core is padded to a larger public arity, passing the public
code verbatim would leave unconstrained high bits in that evaluator ABI.  This
fixed oracle-free program computes `value % 2 ^ width`; it is the single input
normalizer shared by both recovery branches.
-/

namespace NearCubicWires.BitInputPrefixProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-- The canonical code of the first `width` little-endian bits. -/
def bitInputPrefix (width value : ℕ) : ℕ :=
  value % 2 ^ width

/-- The semantic bit view consumed by an evaluator of the smaller arity. -/
def bitInputPrefixView (width value : ℕ) : BitInput width :=
  fun bit => value.testBit bit.val

theorem bitInputPrefix_eq_encodeView (width value : ℕ) :
    bitInputPrefix width value =
      encodeBitInput (bitInputPrefixView width value) := by
  symm
  calc
    encodeBitInput (bitInputPrefixView width value) =
        encodeBitInput
          (fun bit : Fin width =>
            (value % 2 ^ width).testBit bit.val) := by
      congr 1
      funext bit
      rw [Nat.testBit_mod_two_pow]
      simp [bit.isLt, bitInputPrefixView]
    _ = value % 2 ^ width :=
      encodeBitInput_testBit
        (Nat.mod_lt value (pow_pos (by omega : 0 < 2) width))
    _ = bitInputPrefix width value := rfl

theorem bitInputPrefixView_encodeBitInput
    {inputArity width : ℕ} (input : BitInput inputArity)
    (hwidth : width ≤ inputArity) :
    bitInputPrefixView width (encodeBitInput input) =
      fun bit : Fin width =>
        input ⟨bit.val, bit.isLt.trans_le hwidth⟩ := by
  funext bit
  unfold bitInputPrefixView
  rw [encodeBitInput_eq_ofBits]
  exact Nat.testBit_ofBits_lt input bit.val (bit.isLt.trans_le hwidth)

theorem bitInputPrefix_encodeBitInput
    {inputArity width : ℕ} (input : BitInput inputArity)
    (hwidth : width ≤ inputArity) :
    bitInputPrefix width (encodeBitInput input) =
      encodeBitInput
        (fun bit : Fin width =>
          input ⟨bit.val, bit.isLt.trans_le hwidth⟩) := by
  rw [bitInputPrefix_eq_encodeView,
    bitInputPrefixView_encodeBitInput input hwidth]

/-- Public callable ABI: `pair(width, value)`. -/
def bitInputPrefixInput (width value : ℕ) : ℕ :=
  Nat.pair width value

def bitInputPrefixProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 0 3
  , .branchZero 2 12 4
  , .decrement 2 5
  , .copy 4 5 6
  , .branchZero 5 9 7
  , .decrement 5 8
  , .increment 4 6
  , .testBit 3 2 6 10
  , .branchZero 6 3 11
  , .increment 4 3
  , .copy 4 0 13
  , .halt 0
  ]

@[simp] theorem bitInputPrefixProgram_oracleFree :
    OracleFree bitInputPrefixProgram := by
  rfl

@[simp] theorem bitInputPrefixProgram_length :
    bitInputPrefixProgram.length = 14 := by
  rfl

private def doubleFuel : ℕ → ℕ
  | 0 => 1
  | remaining + 1 => 3 + doubleFuel remaining

private def scanFuel (value : ℕ) : ℕ → ℕ → ℕ
  | _accumulator, 0 => 3
  | accumulator, remaining + 1 =>
      let bit := (value.testBit remaining).toNat
      let next := 2 * accumulator + bit
      5 + doubleFuel accumulator + bit + scanFuel value next remaining

def bitInputPrefixFuel (width value : ℕ) : ℕ :=
  3 + scanFuel value 0 width

private theorem doubleFuel_eq (remaining : ℕ) :
    doubleFuel remaining = 3 * remaining + 1 := by
  induction remaining with
  | zero => rfl
  | succ remaining ih =>
      simp [doubleFuel, ih]
      omega

def registerBound (width value : ℕ) : ℕ :=
  max (bitInputPrefixInput width value) (2 ^ width) + 1

def bitInputPrefixBits (width value : ℕ) : ℕ :=
  natBitLength (registerBound width value)

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

private theorem boundedBits
    {width value candidate maximumBits : ℕ}
    (hcandidate : candidate ≤ registerBound width value)
    (hbits : bitInputPrefixBits width value ≤ maximumBits) :
    natBitLength candidate ≤ maximumBits :=
  (natBitLength_mono hcandidate).trans hbits

private theorem input_le_bound (width value : ℕ) :
    bitInputPrefixInput width value ≤ registerBound width value := by
  unfold registerBound
  omega

private theorem width_le_bound (width value : ℕ) :
    width ≤ registerBound width value := by
  exact
    (Nat.left_le_pair width value).trans
      ((Nat.le_max_left _ _).trans (Nat.le_add_right _ _))

private theorem value_le_bound (width value : ℕ) :
    value ≤ registerBound width value := by
  exact
    (Nat.right_le_pair width value).trans
      ((Nat.le_max_left _ _).trans (Nat.le_add_right _ _))

private theorem power_le_bound (width value : ℕ) :
    2 ^ width ≤ registerBound width value := by
  exact
    (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)

private theorem one_le_bound (width value : ℕ) :
    1 ≤ registerBound width value := by
  unfold registerBound
  omega

private theorem testBit_toNat (value bit : ℕ) :
    (value.testBit bit).toNat = value / 2 ^ bit % 2 := by
  unfold Nat.testBit
  rw [Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (value / 2 ^ bit) with hmod | hmod
  · simp [hmod]
  · simp [hmod]

private theorem prefixStep
    (value accumulator remaining : ℕ) :
    (2 * accumulator + (value.testBit remaining).toNat) *
          2 ^ remaining +
        value % 2 ^ remaining =
      accumulator * 2 ^ (remaining + 1) +
        value % 2 ^ (remaining + 1) := by
  rw [Nat.mod_pow_succ, ← testBit_toNat, pow_succ]
  cases value.testBit remaining <;> simp
  all_goals ring

private theorem accumulator_lt_of_invariant
    {width value accumulator remaining : ℕ}
    (hinvariant :
      accumulator * 2 ^ remaining + value % 2 ^ remaining < 2 ^ width) :
    accumulator < 2 ^ width := by
  have hone : 1 ≤ 2 ^ remaining := Nat.one_le_two_pow
  have haccumulator :
      accumulator ≤ accumulator * 2 ^ remaining :=
    Nat.le_mul_of_pos_right accumulator (by omega)
  exact haccumulator.trans_lt (lt_of_le_of_lt
    (Nat.le_add_right _ _) hinvariant)

private theorem scanFuel_le
    (width value accumulator remaining : ℕ)
    (hremaining : remaining ≤ width)
    (hinvariant :
      accumulator * 2 ^ remaining + value % 2 ^ remaining < 2 ^ width) :
    scanFuel value accumulator remaining ≤
      3 + remaining * (7 + 3 * 2 ^ width) := by
  induction remaining generalizing accumulator with
  | zero =>
      simp [scanFuel]
  | succ remaining ih =>
      let bit := (value.testBit remaining).toNat
      let next := 2 * accumulator + bit
      have hbit : bit ≤ 1 := by
        cases hvalue : value.testBit remaining <;> simp [bit, hvalue]
      have haccumulator :
          accumulator ≤ 2 ^ width :=
        Nat.le_of_lt (accumulator_lt_of_invariant hinvariant)
      have hnextInvariant :
          next * 2 ^ remaining + value % 2 ^ remaining < 2 ^ width := by
        simpa only [next, bit, prefixStep] using hinvariant
      have htail :=
        ih next (by omega) hnextInvariant
      simp only [scanFuel, doubleFuel_eq]
      change
        5 + (3 * accumulator + 1) + bit +
            scanFuel value next remaining ≤
          3 + (remaining + 1) * (7 + 3 * 2 ^ width)
      have hcost :
          5 + (3 * accumulator + 1) + bit ≤
            7 + 3 * 2 ^ width := by
        omega
      calc
        _ ≤
            (5 + (3 * accumulator + 1) + bit) +
              (3 + remaining * (7 + 3 * 2 ^ width)) :=
          Nat.add_le_add_left htail _
        _ ≤
            (7 + 3 * 2 ^ width) +
              (3 + remaining * (7 + 3 * 2 ^ width)) :=
          Nat.add_le_add_right hcost _
        _ = _ := by ring

/-- The unary doubling loop is exponential only in the selected prefix width,
never in the ambient input code.  This is the resource fact used by the final
`E^NP` linker. -/
theorem bitInputPrefixFuel_le (width value : ℕ) :
    bitInputPrefixFuel width value ≤
      6 + width * (7 + 3 * 2 ^ width) := by
  unfold bitInputPrefixFuel
  have hinvariant :
      0 * 2 ^ width + value % 2 ^ width < 2 ^ width := by
    simpa using Nat.mod_lt value (pow_pos (by omega : 0 < 2) width)
  have hscan :=
    Nat.add_le_add_left
      (scanFuel_le width value 0 width le_rfl hinvariant) 3
  omega

theorem bitInputPrefixFuel_le_exponential
    (inputArity width value : ℕ)
    (hpositive : 1 ≤ inputArity) (hwidth : width ≤ inputArity) :
    bitInputPrefixFuel width value ≤ 2 ^ (6 * inputArity) := by
  have hpower :
      2 ^ width ≤ 2 ^ inputArity :=
    Nat.pow_le_pow_right (by omega) hwidth
  have harityPower : inputArity ≤ 2 ^ inputArity :=
    Nat.le_of_lt inputArity.lt_two_pow_self
  have hinner :
      7 + 3 * 2 ^ width ≤ 10 * 2 ^ inputArity := by
    have hone : 1 ≤ 2 ^ inputArity := Nat.one_le_two_pow
    omega
  have hproduct :
      width * (7 + 3 * 2 ^ width) ≤
        10 * 2 ^ (2 * inputArity) := by
    calc
      _ ≤ (2 ^ inputArity) * (10 * 2 ^ inputArity) :=
        Nat.mul_le_mul (hwidth.trans harityPower) hinner
      _ = 10 * 2 ^ (2 * inputArity) := by
        rw [show 2 * inputArity = inputArity + inputArity by omega,
          pow_add]
        ring
  calc
    bitInputPrefixFuel width value ≤
        6 + width * (7 + 3 * 2 ^ width) :=
      bitInputPrefixFuel_le width value
    _ ≤ 6 + 10 * 2 ^ (2 * inputArity) :=
      Nat.add_le_add_left hproduct 6
    _ ≤ 16 * 2 ^ (2 * inputArity) := by
      have hone : 1 ≤ 2 ^ (2 * inputArity) := Nat.one_le_two_pow
      omega
    _ = 2 ^ (4 + 2 * inputArity) := by
      rw [pow_add]
      norm_num
    _ ≤ 2 ^ (6 * inputArity) :=
      Nat.pow_le_pow_right (by omega) (by omega)

theorem bitInputPrefixBits_le_exponential
    (inputArity width value : ℕ)
    (hpositive : 1 ≤ inputArity) (hwidth : width ≤ inputArity)
    (hvalue : value < 2 ^ inputArity) :
    bitInputPrefixBits width value ≤ 2 ^ (6 * inputArity) := by
  have hwidthValue : width < 2 ^ inputArity :=
    hwidth.trans_lt inputArity.lt_two_pow_self
  have hmax :
      max width value + 1 ≤ 2 ^ inputArity := by
    omega
  have hpair :
      bitInputPrefixInput width value < 2 ^ (2 * inputArity) := by
    calc
      Nat.pair width value <
          (max width value + 1) ^ 2 :=
        Nat.pair_lt_max_add_one_sq width value
      _ ≤ (2 ^ inputArity) ^ 2 :=
        Nat.pow_le_pow_left hmax 2
      _ = 2 ^ (2 * inputArity) := by
        rw [← pow_mul]
        congr 1
        omega
  have hpower :
      2 ^ width < 2 ^ (2 * inputArity) := by
    exact
      (Nat.pow_le_pow_right (by omega) hwidth).trans_lt <|
        Nat.pow_lt_pow_right (by omega) (by omega)
  have hbound :
      registerBound width value ≤ 2 ^ (2 * inputArity) := by
    unfold registerBound
    exact Nat.add_one_le_iff.mpr (max_lt hpair hpower)
  have hlength :
      bitInputPrefixBits width value ≤
        2 ^ (2 * inputArity) + 1 :=
    (natBitLength_le_succ (registerBound width value)).trans
      (Nat.add_le_add_right hbound 1)
  have hdouble :
      2 ^ (2 * inputArity) + 1 ≤
        2 ^ (2 * inputArity + 1) := by
    rw [pow_succ]
    have hone : 1 ≤ 2 ^ (2 * inputArity) := Nat.one_le_two_pow
    omega
  exact (hlength.trans hdouble).trans <|
    Nat.pow_le_pow_right (by omega) (by omega)

private theorem doubleTrace
    (width value accumulator remaining maximumBits extra : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 6)
    (haccumulator : state.registers 4 = accumulator)
    (hremaining : state.registers 5 = remaining)
    (hbound : accumulator + remaining ≤ registerBound width value)
    (hbits : bitInputPrefixBits width value ≤ maximumBits) :
    runNPOracleProgram bitInputPrefixProgram maximumBits
        (doubleFuel remaining + extra) state =
      runNPOracleProgram bitInputPrefixProgram maximumBits extra
        (((state.write 4 (accumulator + remaining)).write 5 0).jump 9) := by
  induction remaining generalizing accumulator state with
  | zero =>
      rw [show doubleFuel 0 + extra = extra + 1 by
        simp [doubleFuel, Nat.add_comm]]
      rw [run_branchZero_instruction (fuel := extra) (by rfl) hpc]
      rw [hremaining, if_pos rfl]
      congr 2
      apply state_eq
      · simp [NPOracleState.write]
      · intro register
        by_cases hfour : register = 4
        · subst register
          simp [haccumulator]
        · by_cases hfive : register = 5
          · subst register
            simp [hremaining]
          · simp [NPOracleState.write, hfour, hfive]
  | succ remaining inductionHypothesis =>
      have hremainingBits :
          natBitLength remaining ≤ maximumBits := by
        apply boundedBits (hbits := hbits)
        omega
      have hincrementBits :
          natBitLength (accumulator + 1) ≤ maximumBits := by
        apply boundedBits (hbits := hbits)
        omega
      rw [show doubleFuel (remaining + 1) + extra =
        (2 + doubleFuel remaining + extra) + 1 by
          simp [doubleFuel]
          omega]
      rw [run_branchZero_instruction
        (fuel := 2 + doubleFuel remaining + extra) (by rfl) hpc]
      rw [hremaining, if_neg (Nat.succ_ne_zero remaining)]
      rw [show 2 + doubleFuel remaining + extra =
        (1 + doubleFuel remaining + extra) + 1 by omega]
      rw [run_decrement_instruction
        (fuel := 1 + doubleFuel remaining + extra)
        (value := remaining) (by rfl) rfl
        (by simp [NPOracleState.jump, hremaining])
        hremainingBits]
      rw [show 1 + doubleFuel remaining + extra =
        (doubleFuel remaining + extra) + 1 by omega]
      rw [run_increment_instruction
        (fuel := doubleFuel remaining + extra)
        (value := accumulator + 1) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, haccumulator])
        hincrementBits]
      rw [inductionHypothesis (accumulator := accumulator + 1)
        (state :=
          ((((state.jump 7).write 5 remaining).jump 8).write 4
            (accumulator + 1)).jump 6)
        rfl
        (by simp)
        (by simp)
        (by omega)]
      congr 2
      apply state_eq
      · simpa [NPOracleState.write, NPOracleState.jump] using hpc.symm
      · intro register
        by_cases hfour : register = 4
        · subst register
          simp [NPOracleState.write]
          omega
        · by_cases hfive : register = 5
          · subst register
            simp [NPOracleState.write]
          · simp [NPOracleState.write, hfour, hfive]

private theorem scanTrace
    (width value accumulator remaining maximumBits extra : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 3)
    (hremaining : state.registers 2 = remaining)
    (hvalue : state.registers 3 = value)
    (haccumulator : state.registers 4 = accumulator)
    (hremainingWidth : remaining ≤ width)
    (hinvariant :
      accumulator * 2 ^ remaining + value % 2 ^ remaining < 2 ^ width)
    (hbits : bitInputPrefixBits width value ≤ maximumBits) :
    runNPOracleProgram bitInputPrefixProgram maximumBits
        (scanFuel value accumulator remaining + extra) state =
      some (accumulator * 2 ^ remaining + value % 2 ^ remaining) := by
  induction remaining generalizing accumulator state with
  | zero =>
      have haccumulatorBits :
          natBitLength accumulator ≤ maximumBits := by
        apply boundedBits (hbits := hbits)
        have haccumulatorPower :
            accumulator < 2 ^ width :=
          accumulator_lt_of_invariant hinvariant
        exact (Nat.le_of_lt haccumulatorPower).trans
          (power_le_bound width value)
      rw [show scanFuel value accumulator 0 + extra =
        (2 + extra) + 1 by simp [scanFuel]; omega]
      rw [run_branchZero_instruction
        (fuel := 2 + extra) (by rfl) hpc]
      rw [hremaining, if_pos rfl]
      rw [show 2 + extra = (1 + extra) + 1 by omega]
      rw [run_copy_instruction (fuel := 1 + extra)
        (value := accumulator) (by rfl) rfl
        (by simpa [NPOracleState.jump] using haccumulator)
        haccumulatorBits]
      rw [show 1 + extra = extra + 1 by omega]
      simp [runNPOracleProgram, bitInputPrefixProgram, haccumulatorBits]
      simp [Nat.mod_one]
  | succ remaining inductionHypothesis =>
      let bit := (value.testBit remaining).toNat
      let next := 2 * accumulator + bit
      have hbitLe : bit ≤ 1 := by
        cases hbit : value.testBit remaining <;> simp [bit, hbit]
      have hremainingBits :
          natBitLength remaining ≤ maximumBits := by
        apply boundedBits (hbits := hbits)
        exact
          (Nat.le_of_lt (by omega : remaining < width)).trans
            (width_le_bound width value)
      have haccumulatorPower :
          accumulator < 2 ^ width :=
        accumulator_lt_of_invariant hinvariant
      have haccumulatorBits :
          natBitLength accumulator ≤ maximumBits := by
        apply boundedBits (hbits := hbits)
        exact (Nat.le_of_lt haccumulatorPower).trans
          (power_le_bound width value)
      have hdoubleBound :
          2 * accumulator ≤ registerBound width value := by
        have hnextProduct :
            next * 2 ^ remaining ≤
              next * 2 ^ remaining + value % 2 ^ remaining :=
          Nat.le_add_right _ _
        have hnextInvariant :
            next * 2 ^ remaining + value % 2 ^ remaining < 2 ^ width := by
          simpa only [next, bit, prefixStep] using hinvariant
        have hnextLe :
            next ≤ next * 2 ^ remaining :=
          Nat.le_mul_of_pos_right next (pow_pos (by omega) _)
        have hnextPower : next < 2 ^ width :=
          hnextLe.trans_lt (hnextProduct.trans_lt hnextInvariant)
        exact
          (Nat.le_trans (by simp [next, bit] : 2 * accumulator ≤ next)
            (Nat.le_of_lt hnextPower)).trans (power_le_bound width value)
      have hbitBits : natBitLength bit ≤ maximumBits := by
        apply boundedBits (hbits := hbits)
        exact hbitLe.trans (one_le_bound width value)
      have hnextInvariant :
          next * 2 ^ remaining + value % 2 ^ remaining < 2 ^ width := by
        simpa only [next, bit, prefixStep] using hinvariant
      have hnextBits : natBitLength next ≤ maximumBits := by
        apply boundedBits (hbits := hbits)
        exact
          (Nat.le_of_lt
            (accumulator_lt_of_invariant hnextInvariant)).trans
              (power_le_bound width value)
      cases hbit : value.testBit remaining with
      | false =>
          have hbitZero : bit = 0 := by simp [bit, hbit]
          rw [show scanFuel value accumulator (remaining + 1) + extra =
            (4 + doubleFuel accumulator +
              scanFuel value next remaining + extra) + 1 by
                simp [scanFuel, bit, next, hbit]
                omega]
          rw [run_branchZero_instruction
            (fuel := 4 + doubleFuel accumulator +
              scanFuel value next remaining + extra)
            (by rfl) hpc]
          rw [hremaining, if_neg (Nat.succ_ne_zero remaining)]
          rw [show 4 + doubleFuel accumulator +
              scanFuel value next remaining + extra =
            (3 + doubleFuel accumulator +
              scanFuel value next remaining + extra) + 1 by omega]
          rw [run_decrement_instruction
            (fuel := 3 + doubleFuel accumulator +
              scanFuel value next remaining + extra)
            (value := remaining) (by rfl) rfl
            (by simp [NPOracleState.jump, hremaining])
            hremainingBits]
          rw [show 3 + doubleFuel accumulator +
              scanFuel value next remaining + extra =
            (2 + doubleFuel accumulator +
              scanFuel value next remaining + extra) + 1 by omega]
          rw [run_copy_instruction
            (fuel := 2 + doubleFuel accumulator +
              scanFuel value next remaining + extra)
            (value := accumulator) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, haccumulator])
            haccumulatorBits]
          rw [show 2 + doubleFuel accumulator +
              scanFuel value next remaining + extra =
            doubleFuel accumulator +
              (2 + scanFuel value next remaining + extra) by omega]
          rw [doubleTrace width value accumulator accumulator maximumBits
            (2 + scanFuel value next remaining + extra)
            _
            rfl
            (by simp [NPOracleState.write, NPOracleState.jump, haccumulator])
            (by simp)
            (by simpa [two_mul] using hdoubleBound)
            hbits]
          rw [show 2 + scanFuel value next remaining + extra =
            (1 + scanFuel value next remaining + extra) + 1 by omega]
          rw [run_testBit_instruction
            (fuel := 1 + scanFuel value next remaining + extra)
            (value := 0) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, hvalue, hbit])
            (by simpa [hbitZero] using hbitBits)]
          rw [show 1 + scanFuel value next remaining + extra =
            (scanFuel value next remaining + extra) + 1 by omega]
          rw [run_branchZero_instruction
            (fuel := scanFuel value next remaining + extra)
            (by rfl) rfl]
          rw [if_pos (by simp)]
          let afterCopy :=
            (((state.jump 4).write 2 remaining).jump 5).write 5 accumulator
              |>.jump 6
          let afterDouble :=
            ((afterCopy.write 4 (accumulator + accumulator)).write 5 0).jump 9
          let nextState := ((afterDouble.write 6 0).jump 10).jump 3
          change
            runNPOracleProgram bitInputPrefixProgram maximumBits
                (scanFuel value next remaining + extra) nextState =
              some
                (accumulator * 2 ^ (remaining + 1) +
                  value % 2 ^ (remaining + 1))
          rw [← prefixStep value accumulator remaining]
          simpa only [next, bit, hbit, Bool.toNat_false, Nat.add_zero] using
            inductionHypothesis (accumulator := next) (state := nextState)
              rfl
              (by simp [nextState, afterDouble, afterCopy,
                NPOracleState.write, NPOracleState.jump])
              (by simpa [nextState, afterDouble, afterCopy,
                NPOracleState.write, NPOracleState.jump] using hvalue)
              (by
                simp [nextState, afterDouble, afterCopy, next, bit, hbit,
                  NPOracleState.write, NPOracleState.jump]
                omega)
              (by omega)
              hnextInvariant
      | true =>
          have hbitOne : bit = 1 := by simp [bit, hbit]
          rw [show scanFuel value accumulator (remaining + 1) + extra =
            (5 + doubleFuel accumulator +
              scanFuel value next remaining + extra) + 1 by
                simp [scanFuel, bit, next, hbit]
                omega]
          rw [run_branchZero_instruction
            (fuel := 5 + doubleFuel accumulator +
              scanFuel value next remaining + extra)
            (by rfl) hpc]
          rw [hremaining, if_neg (Nat.succ_ne_zero remaining)]
          rw [show 5 + doubleFuel accumulator +
              scanFuel value next remaining + extra =
            (4 + doubleFuel accumulator +
              scanFuel value next remaining + extra) + 1 by omega]
          rw [run_decrement_instruction
            (fuel := 4 + doubleFuel accumulator +
              scanFuel value next remaining + extra)
            (value := remaining) (by rfl) rfl
            (by simp [NPOracleState.jump, hremaining])
            hremainingBits]
          rw [show 4 + doubleFuel accumulator +
              scanFuel value next remaining + extra =
            (3 + doubleFuel accumulator +
              scanFuel value next remaining + extra) + 1 by omega]
          rw [run_copy_instruction
            (fuel := 3 + doubleFuel accumulator +
              scanFuel value next remaining + extra)
            (value := accumulator) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, haccumulator])
            haccumulatorBits]
          rw [show 3 + doubleFuel accumulator +
              scanFuel value next remaining + extra =
            doubleFuel accumulator +
              (3 + scanFuel value next remaining + extra) by omega]
          rw [doubleTrace width value accumulator accumulator maximumBits
            (3 + scanFuel value next remaining + extra)
            _
            rfl
            (by simp [NPOracleState.write, NPOracleState.jump, haccumulator])
            (by simp)
            (by simpa [two_mul] using hdoubleBound)
            hbits]
          rw [show 3 + scanFuel value next remaining + extra =
            (2 + scanFuel value next remaining + extra) + 1 by omega]
          rw [run_testBit_instruction
            (fuel := 2 + scanFuel value next remaining + extra)
            (value := 1) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, hvalue, hbit])
            (by simpa [hbitOne] using hbitBits)]
          rw [show 2 + scanFuel value next remaining + extra =
            (1 + scanFuel value next remaining + extra) + 1 by omega]
          rw [run_branchZero_instruction
            (fuel := 1 + scanFuel value next remaining + extra)
            (by rfl) rfl]
          rw [if_neg (by simp)]
          rw [show 1 + scanFuel value next remaining + extra =
            (scanFuel value next remaining + extra) + 1 by omega]
          rw [run_increment_instruction
            (fuel := scanFuel value next remaining + extra)
            (value := next) (by rfl) rfl
            (by
              simp [NPOracleState.write, NPOracleState.jump, next, bit, hbit]
              omega)
            hnextBits]
          let afterCopy :=
            (((state.jump 4).write 2 remaining).jump 5).write 5 accumulator
              |>.jump 6
          let afterDouble :=
            ((afterCopy.write 4 (accumulator + accumulator)).write 5 0).jump 9
          let nextState :=
            ((((afterDouble.write 6 1).jump 10).jump 11).write 4 next).jump 3
          change
            runNPOracleProgram bitInputPrefixProgram maximumBits
                (scanFuel value next remaining + extra) nextState =
              some
                (accumulator * 2 ^ (remaining + 1) +
                  value % 2 ^ (remaining + 1))
          rw [← prefixStep value accumulator remaining]
          simpa only [next, bit, hbit, Bool.toNat_true] using
            inductionHypothesis (accumulator := next) (state := nextState)
              rfl
              (by simp [nextState, afterDouble, afterCopy,
                NPOracleState.write, NPOracleState.jump])
              (by simpa [nextState, afterDouble, afterCopy,
                NPOracleState.write, NPOracleState.jump] using hvalue)
              (by simp [nextState, afterDouble, afterCopy,
                NPOracleState.write, NPOracleState.jump])
              (by omega)
              hnextInvariant

theorem run_bitInputPrefixProgram
    (inputLength width value maximumBits extra : ℕ)
    (hbits : bitInputPrefixBits width value ≤ maximumBits) :
    runNPOracleProgram bitInputPrefixProgram maximumBits
        (bitInputPrefixFuel width value + extra)
        (initialNPOracleState inputLength (bitInputPrefixInput width value)) =
      some (bitInputPrefix width value) := by
  let initial :=
    initialNPOracleState inputLength (bitInputPrefixInput width value)
  have hinputBits :
      natBitLength (bitInputPrefixInput width value) ≤ maximumBits :=
    boundedBits (input_le_bound width value) hbits
  have hwidthBits : natBitLength width ≤ maximumBits :=
    boundedBits (width_le_bound width value) hbits
  have hvalueBits : natBitLength value ≤ maximumBits :=
    boundedBits (value_le_bound width value) hbits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    boundedBits (Nat.zero_le _) hbits
  rw [show bitInputPrefixFuel width value + extra =
    (2 + scanFuel value 0 width + extra) + 1 by
      simp [bitInputPrefixFuel]
      omega]
  rw [run_unpairLeft_instruction
    (fuel := 2 + scanFuel value 0 width + extra)
    (value := width) (by rfl) rfl
    (by simp [initialNPOracleState, bitInputPrefixInput])
    hwidthBits]
  rw [show 2 + scanFuel value 0 width + extra =
    (1 + scanFuel value 0 width + extra) + 1 by omega]
  rw [run_unpairRight_instruction
    (fuel := 1 + scanFuel value 0 width + extra)
    (value := value) (by rfl) rfl
    (by simp [initialNPOracleState, bitInputPrefixInput,
      NPOracleState.write, NPOracleState.jump])
    hvalueBits]
  rw [show 1 + scanFuel value 0 width + extra =
    (scanFuel value 0 width + extra) + 1 by omega]
  rw [run_set_instruction
    (fuel := scanFuel value 0 width + extra)
    (by rfl) rfl hzeroBits]
  have hinvariant :
      0 * 2 ^ width + value % 2 ^ width < 2 ^ width :=
    by
      simpa using Nat.mod_lt value (pow_pos (by omega : 0 < 2) width)
  let scanState :=
    (((((initial.write 2 width).jump 1).write 3 value).jump 2).write 4 0).jump 3
  simpa [bitInputPrefix] using
    scanTrace width value 0 width maximumBits extra
      scanState
      rfl
      (by simp [scanState, NPOracleState.write, NPOracleState.jump])
      (by simp [scanState, NPOracleState.write, NPOracleState.jump])
      (by simp [scanState, NPOracleState.write, NPOracleState.jump])
      le_rfl
      hinvariant
      hbits

end NearCubicWires.BitInputPrefixProgram
