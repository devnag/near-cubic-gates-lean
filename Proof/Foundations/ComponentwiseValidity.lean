import Proof.Foundations.ComponentwiseTransfer

/-!
# Pointwise algebra for the componentwise validity test

These lemmas are the local, source-independent core of Appendix C.10.1.
Auxiliary coordinates are rounded at one half, systematic coordinates are
rounded to their prescribed encoding bit, and signed two-literal clauses use
one common polynomial representation.
-/

namespace NearCubicWires.ComponentwiseValidity

open Finset
open scoped BigOperators
open NearCubicWires

noncomputable def roundBit (value : ℝ) : Bool :=
  decide (1 / 2 ≤ value)

def booleanityPenalty (value : ℝ) : ℝ :=
  value ^ 2 * (1 - value) ^ 2

def systematicPenalty (expected : Bool) (value : ℝ) : ℝ :=
  (bitAsReal expected - value) ^ 2

def validityPenalty (constraint : Option Bool) (value : ℝ) : ℝ :=
  match constraint with
  | none => booleanityPenalty value
  | some expected => systematicPenalty expected value

noncomputable def validityRound
    (constraint : Option Bool) (value : ℝ) : Bool :=
  match constraint with
  | none => roundBit value
  | some expected => expected

def literalValue (negative : Bool) (value : ℝ) : ℝ :=
  if negative then 1 - value else value

def clauseValue (leftNegative rightNegative : Bool)
    (left right : ℝ) : ℝ :=
  let leftLiteral := literalValue leftNegative left
  let rightLiteral := literalValue rightNegative right
  leftLiteral + rightLiteral - leftLiteral * rightLiteral

@[simp] theorem bitAsReal_roundBit_of_ge (value : ℝ)
    (hvalue : 1 / 2 ≤ value) :
    bitAsReal (roundBit value) = 1 := by
  have hvalue' : (2 : ℝ)⁻¹ ≤ value := by
    simpa only [one_div] using hvalue
  simp [roundBit, hvalue', bitAsReal]

@[simp] theorem bitAsReal_roundBit_of_lt (value : ℝ)
    (hvalue : value < 1 / 2) :
    bitAsReal (roundBit value) = 0 := by
  have hvalue' : value < (2 : ℝ)⁻¹ := by
    simpa only [one_div] using hvalue
  simp [roundBit, not_le.mpr hvalue', bitAsReal]

theorem roundBit_distance_sq_le_penalty (value : ℝ) :
    (value - bitAsReal (roundBit value)) ^ 2 ≤
      4 * booleanityPenalty value := by
  by_cases hvalue : 1 / 2 ≤ value
  · rw [bitAsReal_roundBit_of_ge value hvalue]
    unfold booleanityPenalty
    have hfactor :
        4 * (value ^ 2 * (1 - value) ^ 2) - (value - 1) ^ 2 =
          (value - 1) ^ 2 * (4 * value ^ 2 - 1) := by
      ring
    have hsecond : 0 ≤ 4 * value ^ 2 - 1 := by
      nlinarith [sq_nonneg value]
    have hproduct :
        0 ≤ (value - 1) ^ 2 * (4 * value ^ 2 - 1) :=
      mul_nonneg (sq_nonneg _) hsecond
    nlinarith
  · have hlt : value < 1 / 2 := lt_of_not_ge hvalue
    rw [bitAsReal_roundBit_of_lt value hlt]
    unfold booleanityPenalty
    have hfactor :
        4 * (value ^ 2 * (1 - value) ^ 2) - value ^ 2 =
          value ^ 2 * (4 * (1 - value) ^ 2 - 1) := by
      ring
    have hsecond : 0 ≤ 4 * (1 - value) ^ 2 - 1 := by
      nlinarith [sq_nonneg (1 - value)]
    have hproduct :
        0 ≤ value ^ 2 * (4 * (1 - value) ^ 2 - 1) :=
      mul_nonneg (sq_nonneg _) hsecond
    nlinarith

theorem booleanityPenalty_nonnegative (value : ℝ) :
    0 ≤ booleanityPenalty value := by
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- A nearby Boolean value makes the auxiliary validity penalty no larger
than its pointwise `ℓ₁` error. -/
theorem booleanityPenalty_le_distance
    (expected : Bool) (value : ℝ)
    (hzero : 0 ≤ value) (hone : value ≤ 1) :
    booleanityPenalty value ≤ |value - bitAsReal expected| := by
  have hleft : value ^ 2 ≤ value := by nlinarith
  have hright : (1 - value) ^ 2 ≤ 1 - value := by nlinarith
  have hleftNonnegative : 0 ≤ value ^ 2 := sq_nonneg _
  have hrightNonnegative : 0 ≤ (1 - value) ^ 2 := sq_nonneg _
  cases expected with
  | false =>
      rw [show bitAsReal false = 0 by rfl, sub_zero, abs_of_nonneg hzero]
      unfold booleanityPenalty
      calc
        value ^ 2 * (1 - value) ^ 2 ≤ value ^ 2 * 1 := by
          gcongr
          nlinarith
        _ = value ^ 2 := by ring
        _ ≤ value := hleft
  | true =>
      have habs : |value - bitAsReal true| = 1 - value := by
        rw [show bitAsReal true = 1 by rfl,
          abs_of_nonpos (sub_nonpos.mpr hone)]
        ring
      rw [habs]
      unfold booleanityPenalty
      calc
        value ^ 2 * (1 - value) ^ 2 ≤ 1 * (1 - value) ^ 2 := by
          gcongr
          nlinarith
        _ = (1 - value) ^ 2 := by ring
        _ ≤ 1 - value := hright

theorem systematicPenalty_eq_distance_sq
    (expected : Bool) (value : ℝ) :
    systematicPenalty expected value =
      (value - bitAsReal expected) ^ 2 := by
  unfold systematicPenalty
  ring

theorem systematicPenalty_le_distance
    (expected : Bool) (value : ℝ)
    (hzero : 0 ≤ value) (hone : value ≤ 1) :
    systematicPenalty expected value ≤
      |value - bitAsReal expected| := by
  rw [systematicPenalty_eq_distance_sq]
  cases expected with
  | false =>
      rw [show bitAsReal false = 0 by rfl, sub_zero, abs_of_nonneg hzero]
      nlinarith
  | true =>
      have habs : |value - bitAsReal true| = 1 - value := by
        rw [show bitAsReal true = 1 by rfl,
          abs_of_nonpos (sub_nonpos.mpr hone)]
        ring
      rw [habs]
      change (value - 1) ^ 2 ≤ 1 - value
      nlinarith

theorem validityRound_distance_sq_le
    (constraint : Option Bool) (value : ℝ) :
    (value - bitAsReal (validityRound constraint value)) ^ 2 ≤
      4 * validityPenalty constraint value := by
  cases constraint with
  | none =>
      exact roundBit_distance_sq_le_penalty value
  | some expected =>
      simp only [validityRound, validityPenalty]
      rw [systematicPenalty_eq_distance_sq]
      nlinarith [sq_nonneg (value - bitAsReal expected)]

theorem validityPenalty_le_nearby_distance
    (constraint : Option Bool) (nearby : Bool) (value : ℝ)
    (hzero : 0 ≤ value) (hone : value ≤ 1)
    (hsystematic :
      ∀ expected, constraint = some expected → nearby = expected) :
    validityPenalty constraint value ≤
      |value - bitAsReal nearby| := by
  cases constraint with
  | none =>
      exact booleanityPenalty_le_distance nearby value hzero hone
  | some expected =>
      have hnearby : nearby = expected :=
        hsystematic expected rfl
      subst nearby
      exact systematicPenalty_le_distance expected value hzero hone

@[simp] theorem literalValue_bitAsReal
    (negative value : Bool) :
    literalValue negative (bitAsReal value) =
      bitAsReal (xor negative value) := by
  cases negative <;> cases value <;>
    norm_num [literalValue, bitAsReal]

theorem literalValue_sub (negative : Bool) (left right : ℝ) :
    literalValue negative left - literalValue negative right =
      (if negative then -(left - right) else left - right) := by
  cases negative
  · simp [literalValue]
  · simp [literalValue]

@[simp] theorem abs_literalValue_sub
    (negative : Bool) (left right : ℝ) :
    |literalValue negative left - literalValue negative right| =
      |left - right| := by
  rw [literalValue_sub]
  cases negative
  · rfl
  · simp [abs_sub_comm]

/-- Three-term triangle inequality in the exact shape used after expanding a
two-literal clause. -/
theorem abs_add_add_le (left middle right : ℝ) :
    |left + middle + right| ≤ |left| + |middle| + |right| := by
  calc
    |left + middle + right| ≤ |left + middle| + |right| :=
      abs_add_le _ _
    _ ≤ (|left| + |middle|) + |right| :=
      add_le_add (abs_add_le left middle) le_rfl

theorem clauseValue_sub_le
    (leftNegative rightNegative : Bool)
    (left right roundedLeft roundedRight : ℝ) :
    |clauseValue leftNegative rightNegative left right -
        clauseValue leftNegative rightNegative roundedLeft roundedRight| ≤
      |left - roundedLeft| + |right - roundedRight| +
        |left * right - roundedLeft * roundedRight| := by
  cases leftNegative <;> cases rightNegative
  · have h := abs_add_add_le
      (left - roundedLeft) (right - roundedRight)
      (-(left * right - roundedLeft * roundedRight))
    calc
      |clauseValue false false left right -
          clauseValue false false roundedLeft roundedRight| =
          |(left - roundedLeft) + (right - roundedRight) +
            (-(left * right - roundedLeft * roundedRight))| := by
        congr 1
        simp [clauseValue, literalValue]
        ring
      _ ≤ _ := by simpa only [abs_neg] using h
  · have h := abs_add_add_le
      0 (-(right - roundedRight))
      (left * right - roundedLeft * roundedRight)
    have hshort :
        |-(right - roundedRight) +
            (left * right - roundedLeft * roundedRight)| ≤
          |right - roundedRight| +
            |left * right - roundedLeft * roundedRight| := by
      simpa only [zero_add, abs_neg, abs_zero] using h
    calc
      |clauseValue false true left right -
          clauseValue false true roundedLeft roundedRight| =
          |-(right - roundedRight) +
            (left * right - roundedLeft * roundedRight)| := by
        congr 1
        simp [clauseValue, literalValue]
        ring
      _ ≤ _ := hshort
      _ ≤ _ := by
        linarith [abs_nonneg (left - roundedLeft)]
  · have h := abs_add_add_le
      (-(left - roundedLeft)) 0
      (left * right - roundedLeft * roundedRight)
    have hshort :
        |-(left - roundedLeft) +
            (left * right - roundedLeft * roundedRight)| ≤
          |left - roundedLeft| +
            |left * right - roundedLeft * roundedRight| := by
      simpa only [add_zero, abs_neg, abs_zero] using h
    calc
      |clauseValue true false left right -
          clauseValue true false roundedLeft roundedRight| =
          |-(left - roundedLeft) +
            (left * right - roundedLeft * roundedRight)| := by
        congr 1
        simp [clauseValue, literalValue]
        ring
      _ ≤ _ := hshort
      _ ≤ _ := by
        linarith [abs_nonneg (right - roundedRight)]
  · have hshort :
        |-(left * right - roundedLeft * roundedRight)| ≤
          |left * right - roundedLeft * roundedRight| := by
      rw [abs_neg]
    calc
      |clauseValue true true left right -
          clauseValue true true roundedLeft roundedRight| =
          |-(left * right - roundedLeft * roundedRight)| := by
        congr 1
        simp [clauseValue, literalValue]
        ring
      _ ≤ _ := hshort
      _ ≤ _ := by
        linarith [abs_nonneg (left - roundedLeft),
          abs_nonneg (right - roundedRight)]

theorem abs_product_sub_le
    (left right roundedLeft roundedRight : ℝ) :
    |left * right - roundedLeft * roundedRight| ≤
      |left| * |right - roundedRight| +
        |roundedRight| * |left - roundedLeft| := by
  have hdecompose :
      left * right - roundedLeft * roundedRight =
        left * (right - roundedRight) +
          roundedRight * (left - roundedLeft) := by
    ring
  rw [hdecompose]
  calc
    |left * (right - roundedRight) +
        roundedRight * (left - roundedLeft)|
        ≤ |left * (right - roundedRight)| +
            |roundedRight * (left - roundedLeft)| := abs_add_le _ _
    _ = |left| * |right - roundedRight| +
          |roundedRight| * |left - roundedLeft| := by
      rw [abs_mul, abs_mul]

theorem bitAsReal_abs_le_one (value : Bool) :
    |bitAsReal value| ≤ 1 := by
  cases value <;> norm_num [bitAsReal]

/-- Finite Cauchy--Schwarz in normalized expectation form. -/
theorem expect_abs_mul_le_sqrt
    {ι : Type} (index : Finset ι)
    (left right : ι → ℝ) :
    (𝔼 i ∈ index, |left i| * |right i|) ≤
      Real.sqrt (𝔼 i ∈ index, left i ^ 2) *
        Real.sqrt (𝔼 i ∈ index, right i ^ 2) := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq index
      (fun i => |left i|) (fun i => |right i|)
  have hnonnegative :
      0 ≤ (𝔼 i ∈ index, |left i| * |right i|) :=
    Finset.expect_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsqrt :
      (𝔼 i ∈ index, |left i| * |right i|) ≤
        Real.sqrt
          ((𝔼 i ∈ index, left i ^ 2) *
            (𝔼 i ∈ index, right i ^ 2)) := by
    apply (Real.le_sqrt hnonnegative (by positivity)).2
    simpa only [sq_abs] using h
  calc
    (𝔼 i ∈ index, |left i| * |right i|) ≤
        Real.sqrt
          ((𝔼 i ∈ index, left i ^ 2) *
            (𝔼 i ∈ index, right i ^ 2)) := hsqrt
    _ = Real.sqrt (𝔼 i ∈ index, left i ^ 2) *
        Real.sqrt (𝔼 i ∈ index, right i ^ 2) := by
      rw [Real.sqrt_mul (by positivity)]

theorem expect_abs_le_sqrt
    {ι : Type} (index : Finset ι) (hne : index.Nonempty)
    (value : ι → ℝ) :
    (𝔼 i ∈ index, |value i|) ≤
      Real.sqrt (𝔼 i ∈ index, value i ^ 2) := by
  have h := expect_abs_mul_le_sqrt index value (fun _ => 1)
  simpa [Finset.expect_const hne] using h

/-- Validity completeness for a `[0,1]` proof near a Boolean proof that
respects every prescribed systematic coordinate. -/
theorem validityPenalty_mean_le
    {ι : Type} (index : Finset ι)
    (constraint : ι → Option Bool) (value : ι → ℝ)
    (nearby : ι → Bool) (zeta : ℝ)
    (hvalue : ∀ i ∈ index, 0 ≤ value i ∧ value i ≤ 1)
    (hsystematic : ∀ i ∈ index, ∀ expected,
      constraint i = some expected → nearby i = expected)
    (hdistance :
      (𝔼 i ∈ index, |value i - bitAsReal (nearby i)|) ≤ zeta) :
    (𝔼 i ∈ index, validityPenalty (constraint i) (value i)) ≤ zeta := by
  exact (Finset.expect_le_expect fun i hi =>
    validityPenalty_le_nearby_distance
      (constraint i) (nearby i) (value i)
      (hvalue i hi).1 (hvalue i hi).2
      (hsystematic i hi)).trans hdistance

/-- Passing validity controls the total mean-square rounding error. -/
theorem validityRound_meanSquare_le
    {ι : Type} (index : Finset ι)
    (constraint : ι → Option Bool) (value : ι → ℝ) :
    (𝔼 i ∈ index,
        (value i - bitAsReal (validityRound (constraint i) (value i))) ^ 2) ≤
      4 * (𝔼 i ∈ index, validityPenalty (constraint i) (value i)) := by
  calc
    (𝔼 i ∈ index,
        (value i - bitAsReal (validityRound (constraint i) (value i))) ^ 2) ≤
        𝔼 i ∈ index, 4 * validityPenalty (constraint i) (value i) :=
      Finset.expect_le_expect fun i _ =>
        validityRound_distance_sq_le (constraint i) (value i)
    _ = 4 * (𝔼 i ∈ index,
        validityPenalty (constraint i) (value i)) := by
      rw [Finset.mul_expect]

theorem validityRound_meanSquare_le_twelve
    {ι : Type} (index : Finset ι)
    (constraint : ι → Option Bool) (value : ι → ℝ) (zeta : ℝ)
    (hpenalty :
      (𝔼 i ∈ index, validityPenalty (constraint i) (value i)) ≤
        3 * zeta) :
    (𝔼 i ∈ index,
        (value i - bitAsReal (validityRound (constraint i) (value i))) ^ 2) ≤
      12 * zeta := by
  calc
    _ ≤ 4 * (𝔼 i ∈ index,
        validityPenalty (constraint i) (value i)) :=
      validityRound_meanSquare_le index constraint value
    _ ≤ 4 * (3 * zeta) :=
      mul_le_mul_of_nonneg_left hpenalty (by norm_num)
    _ = 12 * zeta := by ring

/-- The C.10.1 clause ledger.  A second-moment bound of four on the real
coordinate and mean-square rounding error `delta²` on both coordinates imply
the advertised (slightly slack) `6·delta` mean clause error. -/
theorem clauseMean_distance_le_six
    {ι : Type} (index : Finset ι) (hne : index.Nonempty)
    (leftNegative rightNegative : ι → Bool)
    (left right : ι → ℝ) (roundedLeft roundedRight : ι → Bool)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hleftSecond :
      (𝔼 i ∈ index, left i ^ 2) ≤ 4)
    (hleftDistance :
      (𝔼 i ∈ index,
        (left i - bitAsReal (roundedLeft i)) ^ 2) ≤ delta ^ 2)
    (hrightDistance :
      (𝔼 i ∈ index,
        (right i - bitAsReal (roundedRight i)) ^ 2) ≤ delta ^ 2) :
    (𝔼 i ∈ index,
      |clauseValue (leftNegative i) (rightNegative i) (left i) (right i) -
        clauseValue (leftNegative i) (rightNegative i)
          (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))|) ≤
      6 * delta := by
  let leftError : ι → ℝ :=
    fun i => left i - bitAsReal (roundedLeft i)
  let rightError : ι → ℝ :=
    fun i => right i - bitAsReal (roundedRight i)
  have hleftAbs :
      (𝔼 i ∈ index, |leftError i|) ≤ delta := by
    calc
      (𝔼 i ∈ index, |leftError i|) ≤
          Real.sqrt (𝔼 i ∈ index, leftError i ^ 2) :=
        expect_abs_le_sqrt index hne leftError
      _ ≤ Real.sqrt (delta ^ 2) := by
        apply Real.sqrt_le_sqrt
        simpa [leftError] using hleftDistance
      _ = delta := Real.sqrt_sq hdelta
  have hrightAbs :
      (𝔼 i ∈ index, |rightError i|) ≤ delta := by
    calc
      (𝔼 i ∈ index, |rightError i|) ≤
          Real.sqrt (𝔼 i ∈ index, rightError i ^ 2) :=
        expect_abs_le_sqrt index hne rightError
      _ ≤ Real.sqrt (delta ^ 2) := by
        apply Real.sqrt_le_sqrt
        simpa [rightError] using hrightDistance
      _ = delta := Real.sqrt_sq hdelta
  have hproduct :
      (𝔼 i ∈ index, |left i| * |rightError i|) ≤ 2 * delta := by
    calc
      (𝔼 i ∈ index, |left i| * |rightError i|) ≤
          Real.sqrt (𝔼 i ∈ index, left i ^ 2) *
            Real.sqrt (𝔼 i ∈ index, rightError i ^ 2) :=
        expect_abs_mul_le_sqrt index left rightError
      _ ≤ Real.sqrt 4 * Real.sqrt (delta ^ 2) := by
        apply mul_le_mul
        · exact Real.sqrt_le_sqrt hleftSecond
        · apply Real.sqrt_le_sqrt
          simpa [rightError] using hrightDistance
        · positivity
        · positivity
      _ = 2 * delta := by
        rw [Real.sqrt_sq hdelta]
        norm_num
  have hpoint : ∀ i ∈ index,
      |clauseValue (leftNegative i) (rightNegative i) (left i) (right i) -
          clauseValue (leftNegative i) (rightNegative i)
            (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))| ≤
        |leftError i| + |leftError i| + |rightError i| +
          |left i| * |rightError i| := by
    intro i _hi
    have hclause :=
      clauseValue_sub_le (leftNegative i) (rightNegative i)
        (left i) (right i)
        (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))
    have hproductPoint :=
      abs_product_sub_le
        (left i) (right i)
        (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))
    have hrounded :
        |bitAsReal (roundedRight i)| * |leftError i| ≤
          |leftError i| := by
      have hnonnegative : 0 ≤ |leftError i| := abs_nonneg _
      calc
        |bitAsReal (roundedRight i)| * |leftError i| ≤
            1 * |leftError i| :=
          mul_le_mul_of_nonneg_right
            (bitAsReal_abs_le_one (roundedRight i)) hnonnegative
        _ = |leftError i| := one_mul _
    change
      |clauseValue (leftNegative i) (rightNegative i) (left i) (right i) -
          clauseValue (leftNegative i) (rightNegative i)
            (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))| ≤
        |left i - bitAsReal (roundedLeft i)| +
          |left i - bitAsReal (roundedLeft i)| +
          |right i - bitAsReal (roundedRight i)| +
          |left i| * |right i - bitAsReal (roundedRight i)|
    calc
      _ ≤ |left i - bitAsReal (roundedLeft i)| +
          |right i - bitAsReal (roundedRight i)| +
          |left i * right i -
            bitAsReal (roundedLeft i) * bitAsReal (roundedRight i)| :=
        hclause
      _ ≤ |left i - bitAsReal (roundedLeft i)| +
          |right i - bitAsReal (roundedRight i)| +
          (|left i| * |right i - bitAsReal (roundedRight i)| +
            |bitAsReal (roundedRight i)| *
              |left i - bitAsReal (roundedLeft i)|) := by
        gcongr
      _ ≤ _ := by
        have := hrounded
        dsimp [leftError, rightError] at this
        linarith
  calc
    (𝔼 i ∈ index,
        |clauseValue (leftNegative i) (rightNegative i) (left i) (right i) -
          clauseValue (leftNegative i) (rightNegative i)
            (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))|) ≤
        𝔼 i ∈ index,
          (|leftError i| + |leftError i| + |rightError i| +
            |left i| * |rightError i|) :=
      Finset.expect_le_expect hpoint
    _ = (𝔼 i ∈ index, |leftError i|) +
          (𝔼 i ∈ index, |leftError i|) +
          (𝔼 i ∈ index, |rightError i|) +
          (𝔼 i ∈ index, |left i| * |rightError i|) := by
      simp only [Finset.expect_add_distrib]
    _ ≤ 6 * delta := by linarith

/-- Aggregated C.10.1 form.  The validity test controls the mean-square error
over both positions jointly, rather than requiring a separate bound for each
position.  The weighted Cauchy--Schwarz step below retains the manuscript's
constant `6`. -/
theorem clauseMean_distance_le_six_of_combined
    {ι : Type} (index : Finset ι) (hne : index.Nonempty)
    (leftNegative rightNegative : ι → Bool)
    (left right : ι → ℝ) (roundedLeft roundedRight : ι → Bool)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hleftSecond :
      (𝔼 i ∈ index, left i ^ 2) ≤ 4)
    (hcombinedDistance :
      (𝔼 i ∈ index,
          (left i - bitAsReal (roundedLeft i)) ^ 2) +
        (𝔼 i ∈ index,
          (right i - bitAsReal (roundedRight i)) ^ 2) ≤
        2 * delta ^ 2) :
    (𝔼 i ∈ index,
      |clauseValue (leftNegative i) (rightNegative i) (left i) (right i) -
        clauseValue (leftNegative i) (rightNegative i)
          (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))|) ≤
      6 * delta := by
  let leftError : ι → ℝ :=
    fun i => left i - bitAsReal (roundedLeft i)
  let rightError : ι → ℝ :=
    fun i => right i - bitAsReal (roundedRight i)
  let leftSquare : ℝ := 𝔼 i ∈ index, leftError i ^ 2
  let rightSquare : ℝ := 𝔼 i ∈ index, rightError i ^ 2
  have hleftSquareNonnegative : 0 ≤ leftSquare := by
    exact Finset.expect_nonneg fun i _ => sq_nonneg (leftError i)
  have hrightSquareNonnegative : 0 ≤ rightSquare := by
    exact Finset.expect_nonneg fun i _ => sq_nonneg (rightError i)
  let leftRoot := Real.sqrt leftSquare
  let rightRoot := Real.sqrt rightSquare
  have hleftRootNonnegative : 0 ≤ leftRoot := Real.sqrt_nonneg _
  have hrightRootNonnegative : 0 ≤ rightRoot := Real.sqrt_nonneg _
  have hleftRootSquare : leftRoot ^ 2 = leftSquare := by
    exact Real.sq_sqrt hleftSquareNonnegative
  have hrightRootSquare : rightRoot ^ 2 = rightSquare := by
    exact Real.sq_sqrt hrightSquareNonnegative
  have hcombined :
      leftSquare + rightSquare ≤ 2 * delta ^ 2 := by
    simpa [leftSquare, rightSquare, leftError, rightError] using
      hcombinedDistance
  have hleftAbs :
      (𝔼 i ∈ index, |leftError i|) ≤ leftRoot := by
    exact expect_abs_le_sqrt index hne leftError
  have hrightAbs :
      (𝔼 i ∈ index, |rightError i|) ≤ rightRoot := by
    exact expect_abs_le_sqrt index hne rightError
  have hproduct :
      (𝔼 i ∈ index, |left i| * |rightError i|) ≤
        2 * rightRoot := by
    calc
      (𝔼 i ∈ index, |left i| * |rightError i|) ≤
          Real.sqrt (𝔼 i ∈ index, left i ^ 2) *
            Real.sqrt (𝔼 i ∈ index, rightError i ^ 2) :=
        expect_abs_mul_le_sqrt index left rightError
      _ ≤ Real.sqrt 4 * Real.sqrt rightSquare := by
        apply mul_le_mul
        · exact Real.sqrt_le_sqrt hleftSecond
        · exact le_rfl
        · positivity
        · positivity
      _ = 2 * rightRoot := by
        norm_num [rightRoot, rightSquare]
  have hweighted : 2 * leftRoot + 3 * rightRoot ≤ 6 * delta := by
    have hcauchy :
        (2 * leftRoot + 3 * rightRoot) ^ 2 ≤
          13 * (leftRoot ^ 2 + rightRoot ^ 2) := by
      nlinarith [sq_nonneg (3 * leftRoot - 2 * rightRoot)]
    have hcombinedRoots :
        leftRoot ^ 2 + rightRoot ^ 2 ≤ 2 * delta ^ 2 := by
      simpa only [hleftRootSquare, hrightRootSquare] using hcombined
    have hsquare :
        (2 * leftRoot + 3 * rightRoot) ^ 2 ≤ (6 * delta) ^ 2 := by
      calc
        _ ≤ 13 * (leftRoot ^ 2 + rightRoot ^ 2) := hcauchy
        _ ≤ 13 * (2 * delta ^ 2) := by gcongr
        _ ≤ (6 * delta) ^ 2 := by nlinarith [sq_nonneg delta]
    have hleftSide : 0 ≤ 2 * leftRoot + 3 * rightRoot := by positivity
    have hrightSide : 0 ≤ 6 * delta := by positivity
    nlinarith
  have hpoint : ∀ i ∈ index,
      |clauseValue (leftNegative i) (rightNegative i) (left i) (right i) -
          clauseValue (leftNegative i) (rightNegative i)
            (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))| ≤
        |leftError i| + |leftError i| + |rightError i| +
          |left i| * |rightError i| := by
    intro i _hi
    have hclause :=
      clauseValue_sub_le (leftNegative i) (rightNegative i)
        (left i) (right i)
        (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))
    have hproductPoint :=
      abs_product_sub_le
        (left i) (right i)
        (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))
    have hrounded :
        |bitAsReal (roundedRight i)| * |leftError i| ≤
          |leftError i| := by
      calc
        |bitAsReal (roundedRight i)| * |leftError i| ≤
            1 * |leftError i| :=
          mul_le_mul_of_nonneg_right
            (bitAsReal_abs_le_one (roundedRight i)) (abs_nonneg _)
        _ = |leftError i| := one_mul _
    change
      |clauseValue (leftNegative i) (rightNegative i) (left i) (right i) -
          clauseValue (leftNegative i) (rightNegative i)
            (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))| ≤
        |left i - bitAsReal (roundedLeft i)| +
          |left i - bitAsReal (roundedLeft i)| +
          |right i - bitAsReal (roundedRight i)| +
          |left i| * |right i - bitAsReal (roundedRight i)|
    calc
      _ ≤ |left i - bitAsReal (roundedLeft i)| +
          |right i - bitAsReal (roundedRight i)| +
          |left i * right i -
            bitAsReal (roundedLeft i) * bitAsReal (roundedRight i)| :=
        hclause
      _ ≤ |left i - bitAsReal (roundedLeft i)| +
          |right i - bitAsReal (roundedRight i)| +
          (|left i| * |right i - bitAsReal (roundedRight i)| +
            |bitAsReal (roundedRight i)| *
              |left i - bitAsReal (roundedLeft i)|) := by
        gcongr
      _ ≤ _ := by
        have := hrounded
        dsimp [leftError, rightError] at this
        linarith
  calc
    (𝔼 i ∈ index,
        |clauseValue (leftNegative i) (rightNegative i) (left i) (right i) -
          clauseValue (leftNegative i) (rightNegative i)
            (bitAsReal (roundedLeft i)) (bitAsReal (roundedRight i))|) ≤
        𝔼 i ∈ index,
          (|leftError i| + |leftError i| + |rightError i| +
            |left i| * |rightError i|) :=
      Finset.expect_le_expect hpoint
    _ = 2 * (𝔼 i ∈ index, |leftError i|) +
          (𝔼 i ∈ index, |rightError i|) +
          (𝔼 i ∈ index, |left i| * |rightError i|) := by
      simp only [Finset.expect_add_distrib]
      ring
    _ ≤ 2 * leftRoot + rightRoot + 2 * rightRoot := by
      gcongr
    _ ≤ 6 * delta := by linarith

/-! ## Acceptance-gap ledger -/

/-- The fixed real-valued margins used by the C.10 verifier.  Separating the
outer-PCP error, validity-rounding loss, and supplier-estimation error prevents
any one of them from being silently charged twice or omitted. -/
structure SoundnessParameters where
  completeness : ℝ
  soundness : ℝ
  zeta : ℝ
  outerError : ℝ
  estimationError : ℝ
  zetaNonnegative : 0 ≤ zeta
  outerErrorNonnegative : 0 ≤ outerError
  estimationErrorNonnegative : 0 ≤ estimationError
  gap : soundness < completeness
  reserve :
    outerError + 6 * Real.sqrt (12 * zeta) + estimationError <
      (completeness - soundness) / 2

noncomputable def SoundnessParameters.acceptanceThreshold
    (parameters : SoundnessParameters) : ℝ :=
  (parameters.completeness + parameters.soundness) / 2

/-- Final numerical contradiction in C.10.1.  The rounded Boolean proof pays
outer-PCP/PCPP soundness, the real proof pays the proved `6·sqrt(12ζ)` clause
ledger, and the decoded supplier result pays its own error exactly once. -/
theorem estimate_lt_acceptanceThreshold
    (parameters : SoundnessParameters)
    (roundedMean realMean estimate : ℝ)
    (hrounded :
      roundedMean ≤ parameters.soundness + parameters.outerError)
    (hreal :
      |realMean - roundedMean| ≤
        6 * Real.sqrt (12 * parameters.zeta))
    (hestimate :
      |estimate - realMean| ≤ parameters.estimationError) :
    estimate < parameters.acceptanceThreshold := by
  have hrealUpper :
      realMean - roundedMean ≤
        6 * Real.sqrt (12 * parameters.zeta) :=
    (abs_le.mp hreal).2
  have hestimateUpper :
      estimate - realMean ≤ parameters.estimationError :=
    (abs_le.mp hestimate).2
  unfold SoundnessParameters.acceptanceThreshold
  linarith [parameters.reserve]

theorem rejects_at_acceptanceThreshold
    (parameters : SoundnessParameters)
    (roundedMean realMean estimate : ℝ)
    (hrounded :
      roundedMean ≤ parameters.soundness + parameters.outerError)
    (hreal :
      |realMean - roundedMean| ≤
        6 * Real.sqrt (12 * parameters.zeta))
    (hestimate :
      |estimate - realMean| ≤ parameters.estimationError) :
    ¬parameters.acceptanceThreshold ≤ estimate := by
  exact not_le.mpr
    (estimate_lt_acceptanceThreshold parameters roundedMean realMean estimate
      hrounded hreal hestimate)

end NearCubicWires.ComponentwiseValidity
