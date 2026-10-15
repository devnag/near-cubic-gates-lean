import Mathlib

/-!
# Local finite algebra for the threshold AND-four supplier

This file proves representation identities used by Appendices A--B.  It does
not formalize the asymptotic rectangular product, expander estimate, or prime
density theorem.  There are no declarations by `postulate` and no incomplete
proofs.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.ThresholdCompiler

def bitInt (b : Bool) : ℤ := if b then 1 else 0

def positiveResidual (x c : Bool) : ℤ :=
  (1 - bitInt c) * bitInt x

def negativeResidual (x c : Bool) : ℤ :=
  bitInt c * (1 - bitInt x)

theorem residualIntegerIdentity (x c : Bool) :
    bitInt x = bitInt c + positiveResidual x c - negativeResidual x c := by
  cases x <;> cases c <;> decide

theorem weightedResidualIdentity {n : ℕ}
    (w : Fin n → ℤ) (x c : Fin n → Bool) :
    (∑ i, w i * bitInt (x i)) =
      (∑ i, w i * bitInt (c i))
        + (∑ i, w i * positiveResidual (x i) (c i))
        - (∑ i, w i * negativeResidual (x i) (c i)) := by
  calc
    (∑ i, w i * bitInt (x i)) =
        ∑ i, w i *
          (bitInt (c i) + positiveResidual (x i) (c i) -
            negativeResidual (x i) (c i)) := by
          apply sum_congr rfl
          intro i _
          rw [residualIntegerIdentity]
    _ = (∑ i, w i * bitInt (c i))
          + (∑ i, w i * positiveResidual (x i) (c i))
          - (∑ i, w i * negativeResidual (x i) (c i)) := by
        simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]

theorem exactCutDifference (score theta : ℤ) :
    (if score = theta then 1 else 0 : ℤ) =
      (if score ≥ theta then 1 else 0) -
      (if score ≥ theta + 1 then 1 else 0) := by
  by_cases h : score = theta
  · subst score
    simp
  · by_cases hlo : score < theta
    · have hnext : score < theta + 1 := by omega
      simp [h, not_le.mpr hlo, not_le.mpr hnext]
    · have hge : score ≥ theta := le_of_not_gt hlo
      have hstrict : theta < score := lt_of_le_of_ne hge (Ne.symm h)
      have hnext : score ≥ theta + 1 := Int.add_one_le_iff.mpr hstrict
      simp [h, hge, hnext]

theorem exactEquationChildrenAreDisjoint
    {ι : Type} [DecidableEq ι] (targets : Finset ι) (value : ι) :
    (∑ target ∈ targets, if value = target then 1 else 0) =
      if value ∈ targets then 1 else 0 := by
  by_cases h : value ∈ targets
  · rw [if_pos h]
    rw [sum_eq_single value]
    · simp
    · intro b hb hne
      simp [Ne.symm hne]
    · simp [h]
  · rw [if_neg h]
    apply sum_eq_zero
    intro target htarget
    simp only [ite_eq_right_iff]
    intro heq
    subst target
    exact (h htarget).elim

/-- The odd tag in the corrected CW crossing child simultaneously forces the
selected Boolean literal to be one and the partial score to hit its exact
target.  This is the parity step in Appendix A.12.0, equation (A.12.0c). -/
theorem oddTaggedEquation (score target : ℤ) (z : Bool) :
    2 * score + bitInt z = 2 * target + 1 ↔ z = true ∧ score = target := by
  cases z
  · simp [bitInt]
    omega
  · simp [bitInt]

theorem xorScalarDecomposition (q₁ q₂ : Bool) :
    bitInt (xor q₁ q₂) = (bitInt q₁ + bitInt q₂) % 2 := by
  cases q₁ <;> cases q₂ <;> decide

theorem andFourProduct (q₁ q₂ q₃ q₄ : Bool) :
    bitInt (q₁ && q₂ && q₃ && q₄) =
      bitInt q₁ * bitInt q₂ * bitInt q₃ * bitInt q₄ := by
  cases q₁ <;> cases q₂ <;> cases q₃ <;> cases q₄ <;> decide

theorem trueEquationPassesEveryModulus (modulus : ℤ) :
    (0 : ℤ) % modulus = 0 := by
  simp

theorem nondivisorRejectsFalseEquation (difference prime : ℤ)
    (h : ¬ prime ∣ difference) : difference % prime ≠ 0 := by
  exact fun hz => h (Int.dvd_iff_emod_eq_zero.mpr hz)

theorem boundedMultipleIsZero (base digit : ℤ)
    (hbase : 0 < base) (hlower : -base < digit) (hupper : digit < base)
    (hdiv : base ∣ digit) : digit = 0 := by
  rcases hdiv with ⟨multiple, rfl⟩
  rcases lt_trichotomy multiple 0 with hneg | hzero | hpos
  · have hmultiple : multiple ≤ -1 := by omega
    have : base * multiple ≤ -base := by nlinarith
    omega
  · simp [hzero]
  · have hmultiple : 1 ≤ multiple := by omega
    have : base ≤ base * multiple := by nlinarith
    omega

/-- Mixed-radix stacking of four bounded equation differences cannot cancel.
The manuscript uses a larger safety margin; strict magnitude below the radix
already suffices for injectivity. -/
theorem fourEquationStackInjective
    (base d₀ d₁ d₂ d₃ : ℤ)
    (hbase : 0 < base)
    (h₀l : -base < d₀) (h₀u : d₀ < base)
    (h₁l : -base < d₁) (h₁u : d₁ < base)
    (h₂l : -base < d₂) (h₂u : d₂ < base)
    (_h₃l : -base < d₃) (_h₃u : d₃ < base)
    (hstack : d₀ + base * d₁ + base ^ 2 * d₂ + base ^ 3 * d₃ = 0) :
    d₀ = 0 ∧ d₁ = 0 ∧ d₂ = 0 ∧ d₃ = 0 := by
  have hbaseNe : base ≠ 0 := ne_of_gt hbase
  have hdiv₀ : base ∣ d₀ := by
    refine ⟨-(d₁ + base * d₂ + base ^ 2 * d₃), ?_⟩
    calc
      d₀ = -(base * d₁ + base ^ 2 * d₂ + base ^ 3 * d₃) := by linarith
      _ = base * (-(d₁ + base * d₂ + base ^ 2 * d₃)) := by ring
  have hd₀ : d₀ = 0 := boundedMultipleIsZero base d₀ hbase h₀l h₀u hdiv₀
  have hstack₁ : d₁ + base * d₂ + base ^ 2 * d₃ = 0 := by
    have hmul : base * (d₁ + base * d₂ + base ^ 2 * d₃) = 0 := by
      rw [hd₀] at hstack
      ring_nf at hstack ⊢
      exact hstack
    exact (mul_eq_zero.mp hmul).resolve_left hbaseNe
  have hdiv₁ : base ∣ d₁ := by
    refine ⟨-(d₂ + base * d₃), ?_⟩
    calc
      d₁ = -(base * d₂ + base ^ 2 * d₃) := by linarith
      _ = base * (-(d₂ + base * d₃)) := by ring
  have hd₁ : d₁ = 0 := boundedMultipleIsZero base d₁ hbase h₁l h₁u hdiv₁
  have hstack₂ : d₂ + base * d₃ = 0 := by
    rw [hd₁] at hstack₁
    have hmul : base * (d₂ + base * d₃) = 0 := by
      ring_nf at hstack₁ ⊢
      exact hstack₁
    exact (mul_eq_zero.mp hmul).resolve_left hbaseNe
  have hdiv₂ : base ∣ d₂ := by
    exact ⟨-d₃, by linarith⟩
  have hd₂ : d₂ = 0 := boundedMultipleIsZero base d₂ hbase h₂l h₂u hdiv₂
  have hd₃ : d₃ = 0 := by
    rw [hd₂] at hstack₂
    have hmul : base * d₃ = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hbaseNe
  exact ⟨hd₀, hd₁, hd₂, hd₃⟩

/-- The full occurrence lift, indexed so `j = 0` is the singleton layer. -/
def binLiftFull (t : ℕ) : ℤ :=
  ∑ j ∈ range t, (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ)

/-- The occurrence lift truncated after subset size `q`. -/
def binLift (q t : ℕ) : ℤ :=
  ∑ j ∈ range (min q t), (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ)

theorem twoMulBinLiftFull (t : ℕ) :
    2 * binLiftFull t = 1 - (-1 : ℤ) ^ t := by
  have hbinom :
      (-1 : ℤ) ^ t =
        ∑ m ∈ range (t + 1), (-2 : ℤ) ^ m * (t.choose m : ℤ) := by
    simpa using (add_pow (-2 : ℤ) 1 t)
  rw [sum_range_succ'] at hbinom
  have htail :
      (∑ j ∈ range t,
          (-2 : ℤ) ^ (j + 1) * (t.choose (j + 1) : ℤ)) =
        -2 * binLiftFull t := by
    simp only [binLiftFull, pow_succ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [htail] at hbinom
  norm_num at hbinom ⊢
  omega

theorem binLiftFullEven (t : ℕ) (ht : Even t) : binLiftFull t = 0 := by
  have h := twoMulBinLiftFull t
  have hpow : (-1 : ℤ) ^ t = 1 := ht.neg_one_pow
  rw [hpow] at h
  omega

theorem binLiftFullOdd (t : ℕ) (ht : Odd t) : binLiftFull t = 1 := by
  have h := twoMulBinLiftFull t
  have hpow : (-1 : ℤ) ^ t = -1 := ht.neg_one_pow
  rw [hpow] at h
  omega

theorem omittedBinLiftTermModEqZero
    (q j t : ℕ) (h : q ≤ j) :
    (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ) ≡ 0 [ZMOD (2 : ℤ) ^ q] := by
  apply Int.modEq_zero_iff_dvd.mpr
  have hp : (2 : ℤ) ^ q ∣ (2 : ℤ) ^ j := pow_dvd_pow 2 h
  have hn : (2 : ℤ) ^ q ∣ (-2 : ℤ) ^ j := by
    rw [show (-2 : ℤ) = (-1 : ℤ) * 2 by norm_num, mul_pow]
    exact dvd_mul_of_dvd_right hp _
  exact dvd_mul_of_dvd_left hn _

theorem binLiftModEqFull (q t : ℕ) :
    binLift q t ≡ binLiftFull t [ZMOD (2 : ℤ) ^ q] := by
  rcases le_total q t with hqt | htq
  · have hadd : q + (t - q) = t := Nat.add_sub_of_le hqt
    have htail :
        (∑ i ∈ range (t - q),
            (-2 : ℤ) ^ (q + i) * (t.choose (q + i + 1) : ℤ)) ≡
          0 [ZMOD (2 : ℤ) ^ q] := by
      simpa using Int.ModEq.sum (s := range (t - q)) (fun i _ =>
        omittedBinLiftTermModEqZero q (q + i) t (Nat.le_add_right q i))
    unfold binLift binLiftFull
    rw [Nat.min_eq_left hqt]
    have hsplit := sum_range_add
      (fun j => (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ)) q (t - q)
    rw [hadd] at hsplit
    rw [hsplit]
    have hhead :
        (∑ j ∈ range q,
            (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ)) ≡
          (∑ j ∈ range q,
            (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ))
          [ZMOD (2 : ℤ) ^ q] := Int.ModEq.rfl
    simpa using (hhead.add htail).symm
  · unfold binLift binLiftFull
    rw [Nat.min_eq_right htq]

theorem binLiftModEqParity (q t : ℕ) :
    binLift q t ≡ ((t % 2 : ℕ) : ℤ) [ZMOD (2 : ℤ) ^ q] := by
  rcases Nat.even_or_odd t with ht | ht
  · have hfull := binLiftModEqFull q t
    rw [binLiftFullEven t ht] at hfull
    have hmod : t % 2 = 0 := Nat.even_iff.mp ht
    simpa [hmod] using hfull
  · have hfull := binLiftModEqFull q t
    rw [binLiftFullOdd t ht] at hfull
    have hmod : t % 2 = 1 := Nat.odd_iff.mp ht
    simpa [hmod] using hfull

theorem signedSliceRecombine
    {ι τ : Type} [Fintype ι] [Fintype τ]
    (a b : ι → ℤ) (plus minus : τ → ι → ℤ) (place : τ → ℤ)
    (ha : ∀ i, a i = ∑ t, place t * (plus t i - minus t i)) :
    (∑ i, a i * b i) =
      ∑ t, place t *
        ((∑ i, plus t i * b i) - (∑ i, minus t i * b i)) := by
  simp_rw [ha]
  calc
    (∑ i, (∑ t, place t * (plus t i - minus t i)) * b i) =
        ∑ i, ∑ t, (place t * (plus t i - minus t i)) * b i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
    _ = ∑ t, ∑ i, (place t * (plus t i - minus t i)) * b i := by
          rw [Finset.sum_comm]
    _ = ∑ t, place t *
        ((∑ i, plus t i * b i) - (∑ i, minus t i * b i)) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

/-! ## The executable corrected first-crossing compiler

The declarations below are the kernel-checked counterpart of
`reference_compiler.erratum_safe_disjoint_children`.  In particular, the
compiler traverses bit levels and variables in descending order, starts from
the explicit zero sentinel, permits a zero quotient, and expands complemented
literals only after constructing the nonnegative crossing equation.
-/

/-- An exact integer equation over `n` Boolean variables. -/
structure ExactEquation (n : ℕ) where
  weights : Fin n → ℤ
  target : ℤ

namespace ExactEquation

def Holds {n : ℕ} (equation : ExactEquation n) (x : Fin n → Bool) : Prop :=
  (∑ i, equation.weights i * bitInt (x i)) = equation.target

instance {n : ℕ} (equation : ExactEquation n) (x : Fin n → Bool) :
    Decidable (equation.Holds x) := by
  unfold Holds
  infer_instance

end ExactEquation

def signedLiteral (weight : ℤ) (x : Bool) : Bool :=
  if weight < 0 then !x else x

def magnitude (weight : ℤ) : ℕ := weight.natAbs

def negativeMass {n : ℕ} (weights : Fin n → ℤ) : ℤ :=
  ∑ i, if weights i < 0 then (magnitude (weights i) : ℤ) else 0

def shiftedTarget {n : ℕ} (weights : Fin n → ℤ) (target : ℤ) : ℤ :=
  target + negativeMass weights

def totalMagnitude {n : ℕ} (weights : Fin n → ℤ) : ℕ :=
  ∑ i, magnitude (weights i)

def maximumMagnitude {n : ℕ} (weights : Fin n → ℤ) : ℕ :=
  Finset.univ.sup fun i => magnitude (weights i)

/-- Python's `max(1, max((*magnitudes, shifted_target)).bit_length())`. -/
def crossingLevelCount {n : ℕ} (weights : Fin n → ℤ) (target : ℤ) : ℕ :=
  max 1 (Nat.size (max (maximumMagnitude weights) (shiftedTarget weights target).toNat))

def strictThresholdHolds {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool) : Prop :=
  target < ∑ i, weights i * bitInt (x i)

instance {n : ℕ} (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool) :
    Decidable (strictThresholdHolds weights target x) := by
  unfold strictThresholdHolds
  infer_instance

def literalScore {n : ℕ}
    (coefficients : Fin n → ℕ) (weights : Fin n → ℤ) (x : Fin n → Bool) : ℕ :=
  ∑ i, coefficients i * (signedLiteral (weights i) (x i)).toNat

def addCrossingBit {n : ℕ}
    (coefficients : Fin n → ℕ) (selected : Fin n) (bit : ℕ) : Fin n → ℕ :=
  fun i => coefficients i + if i = selected then 2 ^ bit else 0

def negativeLiteralOffset {n : ℕ}
    (weights : Fin n → ℤ) (literalWeights : Fin n → ℤ) : ℤ :=
  ∑ i, if weights i < 0 then literalWeights i else 0

def expandLiteralEquation {n : ℕ}
    (weights : Fin n → ℤ) (literalWeights : Fin n → ℤ)
    (literalTarget : ℤ) : ExactEquation n where
  weights i := if weights i < 0 then -literalWeights i else literalWeights i
  target := literalTarget - negativeLiteralOffset weights literalWeights

/-- The corrected odd-tag child (A.12.0c), after signed-literal expansion. -/
def crossingChild {n : ℕ}
    (weights : Fin n → ℤ) (shifted : ℕ) (coefficients : Fin n → ℕ)
    (selected : Fin n) (bit : ℕ) : ExactEquation n :=
  let literalWeights : Fin n → ℤ :=
    fun i => 2 * (coefficients i : ℤ) + if i = selected then 1 else 0
  let place : ℕ := 2 ^ bit
  let literalTarget : ℤ :=
    2 * (place : ℤ) * ((shifted / place + 1 : ℕ) : ℤ) + 1
  expandLiteralEquation weights literalWeights literalTarget

structure CrossingState (n : ℕ) where
  coefficients : Fin n → ℕ
  children : List (ExactEquation n)

def compileCrossingLevel {n : ℕ}
    (weights : Fin n → ℤ) (shifted bit : ℕ) :
    List (Fin n) → CrossingState n → CrossingState n
  | [], state => state
  | selected :: remaining, state =>
      if (magnitude (weights selected)).testBit bit then
        let next := addCrossingBit state.coefficients selected bit
        let child := crossingChild weights shifted next selected bit
        compileCrossingLevel weights shifted bit remaining
          ⟨next, state.children ++ [child]⟩
      else
        compileCrossingLevel weights shifted bit remaining state

/-- Descending recursion makes the visitation order
`(n,L),...,(1,L),(n,L-1),...,(1,1)` exactly as in (A.12.0a). -/
def compileCrossingLevels {n : ℕ}
    (weights : Fin n → ℤ) (shifted : ℕ) :
    ℕ → CrossingState n → CrossingState n
  | 0, state => state
  | bit + 1, state =>
      let afterLevel := compileCrossingLevel weights shifted bit
        (List.finRange n).reverse state
      compileCrossingLevels weights shifted bit afterLevel

def zeroEquation (n : ℕ) (target : ℤ) : ExactEquation n where
  weights := fun _ => 0
  target := target

/-- Executable port of the erratum-safe disjoint-child compiler.

The two constant branches deliberately return one equation (`0=0` or
`0=1`), keeping the output representation uniform and nonempty.
-/
def erratumSafeDisjointChildren {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) : List (ExactEquation n) :=
  let shifted := shiftedTarget weights target
  if shifted < 0 then
    [zeroEquation n 0]
  else if totalMagnitude weights ≤ shifted then
    [zeroEquation n 1]
  else
    let initial : CrossingState n := ⟨fun _ => 0, []⟩
    (compileCrossingLevels weights shifted.toNat
      (crossingLevelCount weights target) initial).children

def acceptanceMass {n : ℕ}
    (children : List (ExactEquation n)) (x : Fin n → Bool) : ℤ :=
  (children.map fun child => if child.Holds x then (1 : ℤ) else 0).sum

def acceptanceCount {n : ℕ}
    (children : List (ExactEquation n)) (x : Fin n → Bool) : ℕ :=
  (children.map fun child => if child.Holds x then 1 else 0).sum

def acceptsAny {n : ℕ}
    (children : List (ExactEquation n)) (x : Fin n → Bool) : Bool :=
  children.any fun child => decide (child.Holds x)

@[simp] theorem bitInt_eq_toNat (b : Bool) : bitInt b = b.toNat := by
  cases b <;> rfl

theorem signedLiteralPointwise (weight : ℤ) (x : Bool) :
    weight * bitInt x =
      (magnitude weight : ℤ) * bitInt (signedLiteral weight x) -
        (if weight < 0 then (magnitude weight : ℤ) else 0) := by
  by_cases hweight : weight < 0
  · have habs : (magnitude weight : ℤ) = -weight := by
      simp [magnitude, abs_of_neg hweight]
    cases x <;> simp [signedLiteral, hweight, bitInt, habs]
  · have hnonneg : 0 ≤ weight := le_of_not_gt hweight
    have habs : (magnitude weight : ℤ) = weight := by
      simp [magnitude, abs_of_nonneg hnonneg]
    cases x <;> simp [signedLiteral, hweight, bitInt, habs]

/-- Signed-literal substitution is exact for every integer weight, including
zero and negative weights. -/
theorem signedLiteralScoreIdentity {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool) :
    (∑ i, weights i * bitInt (x i)) - target =
      (∑ i, (magnitude (weights i) : ℤ) *
        bitInt (signedLiteral (weights i) (x i))) -
        shiftedTarget weights target := by
  simp only [shiftedTarget, negativeMass]
  have hsum :
      (∑ i, weights i * bitInt (x i)) =
        (∑ i, (magnitude (weights i) : ℤ) *
          bitInt (signedLiteral (weights i) (x i))) -
          ∑ i, if weights i < 0 then (magnitude (weights i) : ℤ) else 0 := by
    calc
      (∑ i, weights i * bitInt (x i)) =
          ∑ i, ((magnitude (weights i) : ℤ) *
            bitInt (signedLiteral (weights i) (x i)) -
              if weights i < 0 then (magnitude (weights i) : ℤ) else 0) := by
            apply sum_congr rfl
            intro i _
            exact signedLiteralPointwise (weights i) (x i)
      _ = (∑ i, (magnitude (weights i) : ℤ) *
            bitInt (signedLiteral (weights i) (x i))) -
            ∑ i, if weights i < 0 then (magnitude (weights i) : ℤ) else 0 := by
          rw [sum_sub_distrib]
  linarith

theorem literalExpansionPointwise
    (weight literalWeight : ℤ) (x : Bool) :
    literalWeight * bitInt (signedLiteral weight x) =
      (if weight < 0 then -literalWeight else literalWeight) * bitInt x +
        (if weight < 0 then literalWeight else 0) := by
  by_cases hweight : weight < 0 <;>
    cases x <;> simp [signedLiteral, hweight, bitInt]

theorem literalExpansionIdentity {n : ℕ}
    (weights literalWeights : Fin n → ℤ) (x : Fin n → Bool) :
    (∑ i, literalWeights i * bitInt (signedLiteral (weights i) (x i))) =
      (∑ i, (if weights i < 0 then -literalWeights i else literalWeights i) *
        bitInt (x i)) + negativeLiteralOffset weights literalWeights := by
  simp only [negativeLiteralOffset]
  calc
    (∑ i, literalWeights i * bitInt (signedLiteral (weights i) (x i))) =
        ∑ i, ((if weights i < 0 then -literalWeights i else literalWeights i) *
          bitInt (x i) + if weights i < 0 then literalWeights i else 0) := by
      apply sum_congr rfl
      intro i _
      exact literalExpansionPointwise (weights i) (literalWeights i) (x i)
    _ = (∑ i, (if weights i < 0 then -literalWeights i else literalWeights i) *
          bitInt (x i)) +
          ∑ i, if weights i < 0 then literalWeights i else 0 := by
      rw [sum_add_distrib]

theorem expandLiteralEquation_holds_iff {n : ℕ}
    (weights literalWeights : Fin n → ℤ) (literalTarget : ℤ)
    (x : Fin n → Bool) :
    (expandLiteralEquation weights literalWeights literalTarget).Holds x ↔
      (∑ i, literalWeights i *
        bitInt (signedLiteral (weights i) (x i))) = literalTarget := by
  unfold ExactEquation.Holds expandLiteralEquation
  rw [literalExpansionIdentity]
  simp only [negativeLiteralOffset]
  constructor <;> intro h <;> linarith

theorem literalScore_addCrossingBit {n : ℕ}
    (coefficients : Fin n → ℕ) (weights : Fin n → ℤ) (x : Fin n → Bool)
    (selected : Fin n) (bit : ℕ) :
    literalScore (addCrossingBit coefficients selected bit) weights x =
      literalScore coefficients weights x +
        2 ^ bit * (signedLiteral (weights selected) (x selected)).toNat := by
  unfold literalScore addCrossingBit
  simp_rw [add_mul, sum_add_distrib]
  congr 1
  simp

theorem oddTaggedScoreIdentity {n : ℕ}
    (coefficients : Fin n → ℕ) (weights : Fin n → ℤ) (x : Fin n → Bool)
    (selected : Fin n) :
    (∑ i, (2 * (coefficients i : ℤ) + if i = selected then 1 else 0) *
      bitInt (signedLiteral (weights i) (x i))) =
      2 * (literalScore coefficients weights x : ℤ) +
        bitInt (signedLiteral (weights selected) (x selected)) := by
  simp only [literalScore, bitInt_eq_toNat, add_mul, sum_add_distrib]
  push_cast
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte,
    add_left_inj]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  ring

/-- Arithmetic heart of the corrected crossing child.  The quotient is
allowed to be zero; the only required fact is that the prior score is a
multiple of the current power-of-two place. -/
theorem exactNatCrossing
    (prior target place : ℕ) (z : Bool) (hplace : 0 < place)
    (hdiv : place ∣ prior) :
    2 * (prior + place * z.toNat) + z.toNat =
        2 * place * (target / place + 1) + 1 ↔
      prior ≤ target ∧ target < prior + place * z.toNat := by
  rcases hdiv with ⟨k, rfl⟩
  cases z
  · simp only [Bool.toNat_false, mul_zero, add_zero]
    constructor <;> intro h
    · have hmod := congrArg (fun value : ℕ => value % 2) h
      norm_num [Nat.add_mod, Nat.mul_mod] at hmod
    · exact ((Nat.not_lt_of_ge h.1) h.2).elim
  · simp only [Bool.toNat_true, mul_one]
    constructor
    · intro heq
      have hquotient : target / place = k := by
        nlinarith
      have hlower : k * place ≤ target := by
        apply (Nat.le_div_iff_mul_le hplace).mp
        omega
      have hupper : target < (k + 1) * place := by
        apply (Nat.div_lt_iff_lt_mul hplace).mp
        omega
      constructor <;> nlinarith
    · rintro ⟨hlower, hupper⟩
      have hquotient : target / place = k := by
        apply Nat.div_eq_of_lt_le
        · nlinarith
        · nlinarith
      rw [hquotient]
      ring

theorem crossingChild_holds_iff {n : ℕ}
    (weights : Fin n → ℤ) (shifted : ℕ) (coefficients : Fin n → ℕ)
    (selected : Fin n) (bit : ℕ) (x : Fin n → Bool)
    (hdiv : 2 ^ bit ∣ literalScore coefficients weights x)
    (hcontribution :
      2 ^ bit * (signedLiteral (weights selected) (x selected)).toNat ≤
        literalScore coefficients weights x) :
    (crossingChild weights shifted coefficients selected bit).Holds x ↔
      let previous :=
        literalScore coefficients weights x -
          2 ^ bit * (signedLiteral (weights selected) (x selected)).toNat
      previous ≤ shifted ∧ shifted < literalScore coefficients weights x := by
  let z := signedLiteral (weights selected) (x selected)
  let place := 2 ^ bit
  have hplace : 0 < place := pow_pos (by omega) _
  have hscore :
      (∑ i, (2 * (coefficients i : ℤ) + if i = selected then 1 else 0) *
        bitInt (signedLiteral (weights i) (x i))) =
        2 * (literalScore coefficients weights x : ℤ) + bitInt z := by
    simpa [z] using oddTaggedScoreIdentity coefficients weights x selected
  rw [show crossingChild weights shifted coefficients selected bit =
      expandLiteralEquation weights
        (fun i => 2 * (coefficients i : ℤ) + if i = selected then 1 else 0)
        (2 * (place : ℤ) * ((shifted / place + 1 : ℕ) : ℤ) + 1) by
      rfl]
  rw [expandLiteralEquation_holds_iff, hscore]
  dsimp only
  have hdecompose :
      literalScore coefficients weights x =
        (literalScore coefficients weights x - place * z.toNat) +
          place * z.toNat := (Nat.sub_add_cancel hcontribution).symm
  have hpriorDiv :
      place ∣ literalScore coefficients weights x - place * z.toNat := by
    apply Nat.dvd_sub hdiv
    exact dvd_mul_right place z.toNat
  have hcross := exactNatCrossing
    (literalScore coefficients weights x - place * z.toNat)
    shifted place z hplace hpriorDiv
  rw [← hdecompose] at hcross
  have hcrossZ :
      ((2 * literalScore coefficients weights x + z.toNat : ℕ) : ℤ) =
          ((2 * place * (shifted / place + 1) + 1 : ℕ) : ℤ) ↔
        literalScore coefficients weights x - place * z.toNat ≤ shifted ∧
          shifted < literalScore coefficients weights x := by
    exact_mod_cast hcross
  simpa [z, place, bitInt_eq_toNat] using hcrossZ

def thresholdIndicator (score target : ℕ) : ℤ :=
  if target < score then 1 else 0

theorem crossingIndicatorDifference
    (previous current target : ℕ) (hmonotone : previous ≤ current) :
    (if previous ≤ target ∧ target < current then (1 : ℤ) else 0) =
      thresholdIndicator current target - thresholdIndicator previous target := by
  unfold thresholdIndicator
  by_cases hprevious : target < previous
  · have hcurrent : target < current := lt_of_lt_of_le hprevious hmonotone
    simp [hprevious, hcurrent, not_le.mpr hprevious]
  · have hpreviousLe : previous ≤ target := le_of_not_gt hprevious
    by_cases hcurrent : target < current
    · simp [hprevious, hcurrent, hpreviousLe]
    · simp [hprevious, hcurrent]

@[simp] theorem acceptanceMass_nil {n : ℕ} (x : Fin n → Bool) :
    acceptanceMass [] x = 0 := rfl

theorem acceptanceMass_append {n : ℕ}
    (left right : List (ExactEquation n)) (x : Fin n → Bool) :
    acceptanceMass (left ++ right) x =
      acceptanceMass left x + acceptanceMass right x := by
  simp [acceptanceMass, List.map_append, List.sum_append]

@[simp] theorem acceptanceMass_singleton {n : ℕ}
    (child : ExactEquation n) (x : Fin n → Bool) :
    acceptanceMass [child] x = if child.Holds x then 1 else 0 := by
  simp [acceptanceMass]

theorem literalScore_monotone_addCrossingBit {n : ℕ}
    (coefficients : Fin n → ℕ) (weights : Fin n → ℤ) (x : Fin n → Bool)
    (selected : Fin n) (bit : ℕ) :
    literalScore coefficients weights x ≤
      literalScore (addCrossingBit coefficients selected bit) weights x := by
  rw [literalScore_addCrossingBit]
  omega

/-- Each level telescopes exactly from its incoming threshold indicator to
its outgoing one.  This theorem is independent of the variable order; the
descending order is fixed by the executable definition above. -/
theorem compileCrossingLevel_mass {n : ℕ}
    (weights : Fin n → ℤ) (shifted bit : ℕ) (selected : List (Fin n))
    (state : CrossingState n) (x : Fin n → Bool)
    (hdiv : 2 ^ bit ∣ literalScore state.coefficients weights x) :
    let result := compileCrossingLevel weights shifted bit selected state
    acceptanceMass result.children x - acceptanceMass state.children x =
      thresholdIndicator (literalScore result.coefficients weights x) shifted -
        thresholdIndicator (literalScore state.coefficients weights x) shifted := by
  induction selected generalizing state with
  | nil =>
      simp [compileCrossingLevel]
  | cons selected remaining ih =>
      simp only [compileCrossingLevel]
      by_cases hactive : (magnitude (weights selected)).testBit bit = true
      · simp only [hactive]
        let next := addCrossingBit state.coefficients selected bit
        let child := crossingChild weights shifted next selected bit
        let nextState : CrossingState n := ⟨next, state.children ++ [child]⟩
        have hscore :
            literalScore next weights x =
              literalScore state.coefficients weights x +
                2 ^ bit *
                  (signedLiteral (weights selected) (x selected)).toNat := by
          simpa [next] using
            literalScore_addCrossingBit state.coefficients weights x selected bit
        have hnextDiv : 2 ^ bit ∣ literalScore next weights x := by
          rw [hscore]
          exact Nat.dvd_add hdiv (dvd_mul_right (2 ^ bit) _)
        have hcontribution :
            2 ^ bit * (signedLiteral (weights selected) (x selected)).toNat ≤
              literalScore next weights x := by
          rw [hscore]
          omega
        have hchild :
            child.Holds x ↔
              literalScore state.coefficients weights x ≤ shifted ∧
                shifted < literalScore next weights x := by
          have h := crossingChild_holds_iff weights shifted next selected bit x
            hnextDiv hcontribution
          dsimp [child] at h ⊢
          rw [h]
          rw [hscore]
          omega
        have hstep :
            (if child.Holds x then (1 : ℤ) else 0) =
              thresholdIndicator (literalScore next weights x) shifted -
                thresholdIndicator
                  (literalScore state.coefficients weights x) shifted := by
          rw [if_congr hchild rfl rfl]
          exact crossingIndicatorDifference _ _ _
            (literalScore_monotone_addCrossingBit
              state.coefficients weights x selected bit)
        have htail := ih nextState hnextDiv
        dsimp [nextState] at htail
        simp only [acceptanceMass_append, acceptanceMass_singleton] at htail
        dsimp [next, child] at htail hstep ⊢
        linarith
      · simp only [hactive, Bool.false_eq]
        exact ih state hdiv

theorem compileCrossingLevel_score_divisible {n : ℕ}
    (weights : Fin n → ℤ) (shifted bit : ℕ) (selected : List (Fin n))
    (state : CrossingState n) (x : Fin n → Bool)
    (hdiv : 2 ^ bit ∣ literalScore state.coefficients weights x) :
    2 ^ bit ∣ literalScore
      (compileCrossingLevel weights shifted bit selected state).coefficients weights x := by
  induction selected generalizing state with
  | nil => simpa [compileCrossingLevel] using hdiv
  | cons selected remaining ih =>
      simp only [compileCrossingLevel]
      by_cases hactive : (magnitude (weights selected)).testBit bit = true
      · simp only [hactive]
        apply ih
        rw [literalScore_addCrossingBit]
        exact Nat.dvd_add hdiv (dvd_mul_right (2 ^ bit) _)
      · simp only [hactive]
        exact ih state hdiv

theorem compileCrossingLevel_coefficients {n : ℕ}
    (weights : Fin n → ℤ) (shifted bit : ℕ) (selected : List (Fin n))
    (state : CrossingState n) (hnodup : selected.Nodup) (i : Fin n) :
    (compileCrossingLevel weights shifted bit selected state).coefficients i =
      state.coefficients i +
        if i ∈ selected ∧ (magnitude (weights i)).testBit bit = true
        then 2 ^ bit else 0 := by
  induction selected generalizing state with
  | nil => simp [compileCrossingLevel]
  | cons selected remaining ih =>
      have hselected : selected ∉ remaining := (List.nodup_cons.mp hnodup).1
      have hremaining : remaining.Nodup := (List.nodup_cons.mp hnodup).2
      simp only [compileCrossingLevel]
      by_cases hactive : (magnitude (weights selected)).testBit bit = true
      · rw [if_pos hactive]
        rw [ih _ hremaining]
        by_cases hi : i = selected
        · subst i
          simp [addCrossingBit, hselected, hactive]
        · simp [addCrossingBit, hi]
      · rw [if_neg hactive]
        rw [ih _ hremaining]
        by_cases hi : i = selected
        · subst i
          simp [hselected, hactive]
        · simp [hi]

theorem compileCrossingLevel_all_coefficients {n : ℕ}
    (weights : Fin n → ℤ) (shifted bit : ℕ) (state : CrossingState n)
    (i : Fin n) :
    (compileCrossingLevel weights shifted bit (List.finRange n).reverse state).coefficients i =
      state.coefficients i +
        if (magnitude (weights i)).testBit bit then 2 ^ bit else 0 := by
  rw [compileCrossingLevel_coefficients weights shifted bit (List.finRange n).reverse state
    (List.nodup_reverse.mpr (List.nodup_finRange n)) i]
  simp

theorem testBit_toNat (value bit : ℕ) :
    (value.testBit bit).toNat = value / 2 ^ bit % 2 := by
  unfold Nat.testBit
  rw [Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (value / 2 ^ bit) with hmod | hmod
  · simp [hmod]
  · simp [hmod]

def lowBits (value levels : ℕ) : ℕ := value % 2 ^ levels

theorem lowBits_succ (value bit : ℕ) :
    lowBits value (bit + 1) =
      lowBits value bit +
        if value.testBit bit then 2 ^ bit else 0 := by
  unfold lowBits
  rw [Nat.mod_pow_succ, ← testBit_toNat]
  cases value.testBit bit <;> simp [mul_comm]

theorem compileCrossingLevels_coefficients {n : ℕ}
    (weights : Fin n → ℤ) (shifted levels : ℕ) (state : CrossingState n)
    (i : Fin n) :
    (compileCrossingLevels weights shifted levels state).coefficients i =
      state.coefficients i + lowBits (magnitude (weights i)) levels := by
  induction levels generalizing state with
  | zero => simp [compileCrossingLevels, lowBits, Nat.mod_one]
  | succ bit ih =>
      let afterLevel := compileCrossingLevel weights shifted bit
        (List.finRange n).reverse state
      change
        (compileCrossingLevels weights shifted bit afterLevel).coefficients i =
          state.coefficients i + lowBits (magnitude (weights i)) (bit + 1)
      rw [ih, compileCrossingLevel_all_coefficients, lowBits_succ]
      split <;> omega

theorem compileCrossingLevels_mass {n : ℕ}
    (weights : Fin n → ℤ) (shifted levels : ℕ) (state : CrossingState n)
    (x : Fin n → Bool)
    (hdiv : 2 ^ levels ∣ literalScore state.coefficients weights x) :
    let result := compileCrossingLevels weights shifted levels state
    acceptanceMass result.children x - acceptanceMass state.children x =
      thresholdIndicator (literalScore result.coefficients weights x) shifted -
        thresholdIndicator (literalScore state.coefficients weights x) shifted := by
  induction levels generalizing state with
  | zero =>
      simp [compileCrossingLevels]
  | succ bit ih =>
      let afterLevel := compileCrossingLevel weights shifted bit
        (List.finRange n).reverse state
      change
        acceptanceMass
            (compileCrossingLevels weights shifted bit afterLevel).children x -
            acceptanceMass state.children x =
          thresholdIndicator
              (literalScore
                (compileCrossingLevels weights shifted bit afterLevel).coefficients
                weights x)
              shifted -
            thresholdIndicator (literalScore state.coefficients weights x) shifted
      have hpower : 2 ^ bit ∣ 2 ^ (bit + 1) := pow_dvd_pow 2 (Nat.le_succ bit)
      have hstartDiv : 2 ^ bit ∣ literalScore state.coefficients weights x :=
        dvd_trans hpower hdiv
      have hlevel := compileCrossingLevel_mass weights shifted bit
        (List.finRange n).reverse state x hstartDiv
      have hafterDiv := compileCrossingLevel_score_divisible weights shifted bit
        (List.finRange n).reverse state x hstartDiv
      have htail := ih afterLevel hafterDiv
      dsimp [afterLevel] at hlevel htail
      linarith

theorem magnitude_lt_crossingPower {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (i : Fin n) :
    magnitude (weights i) < 2 ^ crossingLevelCount weights target := by
  have hmagnitude : magnitude (weights i) ≤ maximumMagnitude weights :=
    Finset.le_sup (s := Finset.univ)
      (f := fun j => magnitude (weights j)) (Finset.mem_univ i)
  have hparameter :
      magnitude (weights i) ≤
        max (maximumMagnitude weights) (shiftedTarget weights target).toNat :=
    hmagnitude.trans (Nat.le_max_left _ _)
  have hsize :
      Nat.size (magnitude (weights i)) ≤
        Nat.size (max (maximumMagnitude weights) (shiftedTarget weights target).toNat) :=
    Nat.size_le_size hparameter
  apply Nat.size_le.mp
  exact hsize.trans (Nat.le_max_right _ _)

theorem lowBits_crossingLevelCount {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (i : Fin n) :
    lowBits (magnitude (weights i)) (crossingLevelCount weights target) =
      magnitude (weights i) := by
  unfold lowBits
  exact Nat.mod_eq_of_lt (magnitude_lt_crossingPower weights target i)

theorem compiledCrossingCoefficients {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (i : Fin n) :
    let initial : CrossingState n := ⟨fun _ => 0, []⟩
    (compileCrossingLevels weights (shiftedTarget weights target).toNat
      (crossingLevelCount weights target) initial).coefficients i =
        magnitude (weights i) := by
  intro initial
  rw [compileCrossingLevels_coefficients, lowBits_crossingLevelCount]
  simp [initial]

theorem compiledCrossingScore {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool) :
    let initial : CrossingState n := ⟨fun _ => 0, []⟩
    literalScore
      (compileCrossingLevels weights (shiftedTarget weights target).toNat
        (crossingLevelCount weights target) initial).coefficients weights x =
      ∑ i, magnitude (weights i) *
        (signedLiteral (weights i) (x i)).toNat := by
  intro initial
  unfold literalScore
  apply sum_congr rfl
  intro i _
  rw [compiledCrossingCoefficients]

theorem compiledCrossingMass {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool) :
    let initial : CrossingState n := ⟨fun _ => 0, []⟩
    let result := compileCrossingLevels weights (shiftedTarget weights target).toNat
      (crossingLevelCount weights target) initial
    acceptanceMass result.children x =
      thresholdIndicator
        (∑ i, magnitude (weights i) *
          (signedLiteral (weights i) (x i)).toNat)
        (shiftedTarget weights target).toNat := by
  intro initial result
  have hzero : literalScore initial.coefficients weights x = 0 := by
    simp [initial, literalScore]
  have hmass := compileCrossingLevels_mass weights
    (shiftedTarget weights target).toNat (crossingLevelCount weights target)
    initial x (hzero ▸ dvd_zero (2 ^ crossingLevelCount weights target))
  dsimp [initial, result] at hmass ⊢
  rw [compiledCrossingScore] at hmass
  simpa [acceptanceMass, thresholdIndicator, literalScore] using hmass

theorem strictThreshold_iff_shiftedLiteral {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool)
    (hshifted : 0 ≤ shiftedTarget weights target) :
    strictThresholdHolds weights target x ↔
      (shiftedTarget weights target).toNat <
        ∑ i, magnitude (weights i) *
          (signedLiteral (weights i) (x i)).toNat := by
  have hidentity := signedLiteralScoreIdentity weights target x
  have hshiftedCast :
      ((shiftedTarget weights target).toNat : ℤ) =
        shiftedTarget weights target := Int.toNat_of_nonneg hshifted
  have hsumCast :
      ((∑ i, magnitude (weights i) *
          (signedLiteral (weights i) (x i)).toNat : ℕ) : ℤ) =
        ∑ i, (magnitude (weights i) : ℤ) *
          bitInt (signedLiteral (weights i) (x i)) := by
    simp [bitInt_eq_toNat]
  unfold strictThresholdHolds
  constructor
  · intro hstrict
    have hpositive :
        0 < (∑ i, (magnitude (weights i) : ℤ) *
          bitInt (signedLiteral (weights i) (x i))) -
            shiftedTarget weights target := by
      rw [← hidentity]
      omega
    have hcast :
        ((shiftedTarget weights target).toNat : ℤ) <
          ((∑ i, magnitude (weights i) *
            (signedLiteral (weights i) (x i)).toNat : ℕ) : ℤ) := by
      rw [hshiftedCast, hsumCast]
      omega
    exact_mod_cast hcast
  · intro hstrict
    have hcast :
        ((shiftedTarget weights target).toNat : ℤ) <
          ((∑ i, magnitude (weights i) *
            (signedLiteral (weights i) (x i)).toNat : ℕ) : ℤ) := by
      exact_mod_cast hstrict
    rw [hshiftedCast, hsumCast] at hcast
    have hpositive :
        0 < (∑ i, weights i * bitInt (x i)) - target := by
      rw [hidentity]
      omega
    omega

theorem literalMagnitudeScore_le_total {n : ℕ}
    (weights : Fin n → ℤ) (x : Fin n → Bool) :
    (∑ i, magnitude (weights i) *
      (signedLiteral (weights i) (x i)).toNat) ≤ totalMagnitude weights := by
  unfold totalMagnitude
  apply sum_le_sum
  intro i _
  have hbit :
      (signedLiteral (weights i) (x i)).toNat ≤ 1 := by
    cases signedLiteral (weights i) (x i) <;> decide
  nlinarith

theorem strictThreshold_of_shiftedTarget_neg {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool)
    (hshifted : shiftedTarget weights target < 0) :
    strictThresholdHolds weights target x := by
  have hidentity := signedLiteralScoreIdentity weights target x
  have hnonnegative :
      0 ≤ ∑ i, (magnitude (weights i) : ℤ) *
        bitInt (signedLiteral (weights i) (x i)) := by
    apply sum_nonneg
    intro i _
    apply mul_nonneg
    · omega
    · cases signedLiteral (weights i) (x i) <;> decide
  unfold strictThresholdHolds
  omega

theorem not_strictThreshold_of_total_le_shifted {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool)
    (hshifted : 0 ≤ shiftedTarget weights target)
    (htotal : (totalMagnitude weights : ℤ) ≤ shiftedTarget weights target) :
    ¬strictThresholdHolds weights target x := by
  rw [strictThreshold_iff_shiftedLiteral weights target x hshifted]
  have htotalNat :
      totalMagnitude weights ≤ (shiftedTarget weights target).toNat := by
    rw [← Int.ofNat_le]
    simpa [Int.toNat_of_nonneg hshifted] using htotal
  exact Nat.not_lt_of_ge
    ((literalMagnitudeScore_le_total weights x).trans htotalNat)

/-- Total semantic correctness of the executable compiler, for arbitrary
arity and arbitrary integer weights.  The integer-valued mass is exactly zero
or one, so this theorem simultaneously proves equivalence and disjointness. -/
theorem erratumSafeDisjointChildren_mass {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool) :
    acceptanceMass (erratumSafeDisjointChildren weights target) x =
      if strictThresholdHolds weights target x then 1 else 0 := by
  by_cases hnegative : shiftedTarget weights target < 0
  · have hstrict := strictThreshold_of_shiftedTarget_neg weights target x hnegative
    simp [erratumSafeDisjointChildren, hnegative, hstrict, acceptanceMass,
      zeroEquation, ExactEquation.Holds]
  · have hnonnegative : 0 ≤ shiftedTarget weights target := le_of_not_gt hnegative
    by_cases hconstant :
        (totalMagnitude weights : ℤ) ≤ shiftedTarget weights target
    · have hreject :=
        not_strictThreshold_of_total_le_shifted weights target x hnonnegative hconstant
      simp [erratumSafeDisjointChildren, hnegative, hconstant, hreject,
        acceptanceMass, zeroEquation, ExactEquation.Holds]
    · have hsemantic :=
        strictThreshold_iff_shiftedLiteral weights target x hnonnegative
      rw [erratumSafeDisjointChildren]
      simp only [hnegative, hconstant, ↓reduceIte]
      rw [compiledCrossingMass]
      unfold thresholdIndicator
      split
      · rename_i haccepts
        simp [hsemantic.mpr haccepts]
      · rename_i hrejects
        have hreject : ¬strictThresholdHolds weights target x :=
          fun h => hrejects (hsemantic.mp h)
        simp [hreject]

@[simp] theorem acceptanceMass_cons {n : ℕ}
    (child : ExactEquation n) (children : List (ExactEquation n))
    (x : Fin n → Bool) :
    acceptanceMass (child :: children) x =
      acceptanceMass children x + if child.Holds x then 1 else 0 := by
  simp [acceptanceMass, add_comm]

@[simp] theorem acceptanceCount_cons {n : ℕ}
    (child : ExactEquation n) (children : List (ExactEquation n))
    (x : Fin n → Bool) :
    acceptanceCount (child :: children) x =
      acceptanceCount children x + if child.Holds x then 1 else 0 := by
  simp [acceptanceCount, add_comm]

theorem acceptanceMass_eq_count {n : ℕ}
    (children : List (ExactEquation n)) (x : Fin n → Bool) :
    acceptanceMass children x = (acceptanceCount children x : ℤ) := by
  induction children with
  | nil => rfl
  | cons child children ih =>
      rw [acceptanceMass_cons, acceptanceCount_cons, ih]
      by_cases hchild : child.Holds x <;> simp [hchild]

theorem erratumSafeDisjointChildren_count {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool) :
    acceptanceCount (erratumSafeDisjointChildren weights target) x =
      if strictThresholdHolds weights target x then 1 else 0 := by
  have hmass := erratumSafeDisjointChildren_mass weights target x
  rw [acceptanceMass_eq_count] at hmass
  exact_mod_cast hmass

theorem acceptanceCount_pos_iff_exists {n : ℕ}
    (children : List (ExactEquation n)) (x : Fin n → Bool) :
    0 < acceptanceCount children x ↔
      ∃ child ∈ children, child.Holds x := by
  induction children with
  | nil => simp [acceptanceCount]
  | cons child children ih =>
      by_cases hchild : child.Holds x
      · simp [hchild]
      · simp [hchild, ih]

theorem erratumSafeDisjointChildren_any_iff {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool) :
    acceptsAny (erratumSafeDisjointChildren weights target) x = true ↔
      strictThresholdHolds weights target x := by
  rw [acceptsAny, List.any_eq_true]
  constructor
  · rintro ⟨child, hmem, hchild⟩
    have hholds : child.Holds x := of_decide_eq_true hchild
    have hpositive :
        0 < acceptanceCount (erratumSafeDisjointChildren weights target) x :=
      (acceptanceCount_pos_iff_exists _ _).mpr ⟨child, hmem, hholds⟩
    rw [erratumSafeDisjointChildren_count] at hpositive
    by_contra hreject
    simp [hreject] at hpositive
  · intro hstrict
    have hpositive :
        0 < acceptanceCount (erratumSafeDisjointChildren weights target) x := by
      rw [erratumSafeDisjointChildren_count]
      simp [hstrict]
    rcases (acceptanceCount_pos_iff_exists _ _).mp hpositive with
      ⟨child, hmem, hholds⟩
    exact ⟨child, hmem, decide_eq_true hholds⟩

theorem one_le_acceptanceCount_of_mem {n : ℕ}
    {children : List (ExactEquation n)} {child : ExactEquation n}
    (x : Fin n → Bool) (hmem : child ∈ children) (hholds : child.Holds x) :
    1 ≤ acceptanceCount children x := by
  have hpositive := (acceptanceCount_pos_iff_exists children x).mpr
    ⟨child, hmem, hholds⟩
  omega

theorem pairwise_disjoint_of_acceptanceCount_le_one {n : ℕ}
    (children : List (ExactEquation n)) (x : Fin n → Bool)
    (hle : acceptanceCount children x ≤ 1) :
    children.Pairwise fun left right => ¬(left.Holds x ∧ right.Holds x) := by
  induction children with
  | nil => simp
  | cons child children ih =>
      rw [List.pairwise_cons]
      have htailLe : acceptanceCount children x ≤ 1 := by
        rw [acceptanceCount_cons] at hle
        split at hle <;> omega
      refine ⟨?_, ih htailLe⟩
      intro other hmem hboth
      have htailPositive :=
        one_le_acceptanceCount_of_mem x hmem hboth.2
      have hchild : child.Holds x := hboth.1
      rw [acceptanceCount_cons] at hle
      simp [hchild] at hle
      omega

theorem erratumSafeDisjointChildren_pairwise {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (x : Fin n → Bool) :
    (erratumSafeDisjointChildren weights target).Pairwise
      fun left right => ¬(left.Holds x ∧ right.Holds x) := by
  apply pairwise_disjoint_of_acceptanceCount_le_one
  rw [erratumSafeDisjointChildren_count]
  split <;> omega

theorem compileCrossingLevel_length {n : ℕ}
    (weights : Fin n → ℤ) (shifted bit : ℕ) (selected : List (Fin n))
    (state : CrossingState n) :
    (compileCrossingLevel weights shifted bit selected state).children.length ≤
      state.children.length + selected.length := by
  induction selected generalizing state with
  | nil => simp [compileCrossingLevel]
  | cons selected remaining ih =>
      simp only [compileCrossingLevel]
      split
      · have h := ih
          { coefficients := addCrossingBit state.coefficients selected bit
            children := state.children ++
              [crossingChild weights shifted
                (addCrossingBit state.coefficients selected bit) selected bit] }
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        omega
      · have h := ih state
        simp only [List.length_cons] at h ⊢
        omega

theorem compileCrossingLevels_length {n : ℕ}
    (weights : Fin n → ℤ) (shifted levels : ℕ) (state : CrossingState n) :
    (compileCrossingLevels weights shifted levels state).children.length ≤
      state.children.length + n * levels := by
  induction levels generalizing state with
  | zero => simp [compileCrossingLevels]
  | succ bit ih =>
      let afterLevel := compileCrossingLevel weights shifted bit
        (List.finRange n).reverse state
      change
        (compileCrossingLevels weights shifted bit afterLevel).children.length ≤
          state.children.length + n * (bit + 1)
      have hlevel := compileCrossingLevel_length weights shifted bit
        (List.finRange n).reverse state
      have htail := ih afterLevel
      dsimp [afterLevel] at hlevel htail ⊢
      simp only [List.length_reverse, List.length_finRange] at hlevel
      rw [Nat.mul_succ]
      omega

theorem erratumSafeDisjointChildren_length {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) :
    (erratumSafeDisjointChildren weights target).length ≤
      max 1 (n * crossingLevelCount weights target) := by
  by_cases hnegative : shiftedTarget weights target < 0
  · simp [erratumSafeDisjointChildren, hnegative]
  · by_cases hconstant :
        (totalMagnitude weights : ℤ) ≤ shiftedTarget weights target
    · simp [erratumSafeDisjointChildren, hnegative, hconstant]
    · rw [erratumSafeDisjointChildren]
      simp only [hnegative, hconstant, ↓reduceIte]
      have h := compileCrossingLevels_length weights
        (shiftedTarget weights target).toNat
        (crossingLevelCount weights target)
        (⟨fun _ => 0, []⟩ : CrossingState n)
      simpa using h.trans (Nat.le_max_right _ _)

theorem erratumSafeDisjointChildren_true_constant {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ)
    (hnegative : shiftedTarget weights target < 0) :
    erratumSafeDisjointChildren weights target = [zeroEquation n 0] := by
  simp [erratumSafeDisjointChildren, hnegative]

theorem erratumSafeDisjointChildren_false_constant {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ)
    (hnonnegative : 0 ≤ shiftedTarget weights target)
    (htotal : (totalMagnitude weights : ℤ) ≤ shiftedTarget weights target) :
    erratumSafeDisjointChildren weights target = [zeroEquation n 1] := by
  simp [erratumSafeDisjointChildren, not_lt.mpr hnonnegative, htotal]

theorem constantBranches_nonempty {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ)
    (hconstant :
      shiftedTarget weights target < 0 ∨
        (0 ≤ shiftedTarget weights target ∧
          (totalMagnitude weights : ℤ) ≤ shiftedTarget weights target)) :
    (erratumSafeDisjointChildren weights target).length = 1 := by
  rcases hconstant with hnegative | ⟨hnonnegative, htotal⟩
  · rw [erratumSafeDisjointChildren_true_constant weights target hnegative]
    rfl
  · rw [erratumSafeDisjointChildren_false_constant weights target hnonnegative htotal]
    rfl

/-- Explicitly records the erratum's legal `Q_b = 0` case. -/
theorem zeroQuotientCrossing
    (prior target place : ℕ) (z : Bool) (hplace : 0 < place)
    (htarget : target < place) (hdiv : place ∣ prior) :
    2 * (prior + place * z.toNat) + z.toNat = 2 * place + 1 ↔
      prior ≤ target ∧ target < prior + place * z.toNat := by
  have hquotient : target / place = 0 := Nat.div_eq_of_lt htarget
  simpa [hquotient] using exactNatCrossing prior target place z hplace hdiv

def EquationWithin {n : ℕ} (bound : ℕ) (equation : ExactEquation n) : Prop :=
  (∀ i, |equation.weights i| ≤ (bound : ℤ)) ∧
    |equation.target| ≤ (bound : ℤ)

/-- A deliberately simple global envelope.  It is polynomial in the explicit
output size and dominates both the literal equation and the signed expansion. -/
def compilerParameterBound {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) : ℕ :=
  let levels := crossingLevelCount weights target
  let slots := n * levels
  let place := 2 ^ levels
  let coefficient := slots * place
  let literalWeight := 2 * coefficient + 1
  2 * ((shiftedTarget weights target).toNat + place) + 1 +
    n * literalWeight

theorem crossingChild_within {n : ℕ}
    (weights : Fin n → ℤ) (shifted : ℕ) (coefficients : Fin n → ℕ)
    (selected : Fin n) (bit coefficientBound placeBound : ℕ)
    (hcoefficients : ∀ i, coefficients i ≤ coefficientBound)
    (hplace : 2 ^ bit ≤ placeBound) :
    EquationWithin
      (2 * (shifted + placeBound) + 1 + n * (2 * coefficientBound + 1))
      (crossingChild weights shifted coefficients selected bit) := by
  let literalWeights : Fin n → ℤ :=
    fun i => 2 * (coefficients i : ℤ) + if i = selected then 1 else 0
  let place := 2 ^ bit
  let literalTarget : ℤ :=
    2 * (place : ℤ) * ((shifted / place + 1 : ℕ) : ℤ) + 1
  let weightBound : ℕ := 2 * coefficientBound + 1
  let targetBound : ℕ := 2 * (shifted + placeBound) + 1
  have hliteralWeight (i : Fin n) :
      0 ≤ literalWeights i ∧ literalWeights i ≤ (weightBound : ℤ) := by
    dsimp [literalWeights, weightBound]
    have hi := hcoefficients i
    split <;> norm_cast <;> omega
  have hplacePositive : 0 < place := pow_pos (by omega) _
  have hplaceQuotient : place * (shifted / place) ≤ shifted := by
    simpa [mul_comm] using Nat.div_mul_le_self shifted place
  have hliteralTarget :
      0 ≤ literalTarget ∧ literalTarget ≤ (targetBound : ℤ) := by
    dsimp [literalTarget, targetBound]
    constructor
    · positivity
    · have hmul :
          place * (shifted / place + 1) ≤ shifted + placeBound := by
        rw [mul_add, mul_one]
        exact Nat.add_le_add hplaceQuotient hplace
      norm_cast
      nlinarith
  have hoffsetNonnegative :
      0 ≤ negativeLiteralOffset weights literalWeights := by
    unfold negativeLiteralOffset
    apply sum_nonneg
    intro i _
    split
    · exact (hliteralWeight i).1
    · omega
  have hoffsetUpper :
      negativeLiteralOffset weights literalWeights ≤ (n * weightBound : ℕ) := by
    unfold negativeLiteralOffset
    calc
      (∑ i, if weights i < 0 then literalWeights i else 0) ≤
          ∑ _i : Fin n, (weightBound : ℤ) := by
        apply sum_le_sum
        intro i _
        split
        · exact (hliteralWeight i).2
        · positivity
      _ = (n * weightBound : ℕ) := by
        push_cast
        simp
  have hn : 1 ≤ n := by
    exact Nat.one_le_iff_ne_zero.mpr fun hnzero => by
      subst n
      exact Fin.elim0 selected
  have hweightWithin :
      (weightBound : ℤ) ≤
        (2 * (shifted + placeBound) + 1 + n * weightBound : ℕ) := by
    norm_cast
    have : weightBound ≤ n * weightBound := by nlinarith
    omega
  constructor
  · intro i
    rw [show (crossingChild weights shifted coefficients selected bit).weights i =
        if weights i < 0 then -literalWeights i else literalWeights i by rfl]
    split
    · rw [abs_neg, abs_of_nonneg (hliteralWeight i).1]
      exact (hliteralWeight i).2.trans hweightWithin
    · rw [abs_of_nonneg (hliteralWeight i).1]
      exact (hliteralWeight i).2.trans hweightWithin
  · rw [show (crossingChild weights shifted coefficients selected bit).target =
      literalTarget - negativeLiteralOffset weights literalWeights by rfl]
    rw [abs_le]
    constructor
    · have : -((targetBound + n * weightBound : ℕ) : ℤ) ≤
          literalTarget - negativeLiteralOffset weights literalWeights := by
        calc
          -((targetBound + n * weightBound : ℕ) : ℤ) ≤
              -((n * weightBound : ℕ) : ℤ) := by
                push_cast
                omega
          _ ≤ -negativeLiteralOffset weights literalWeights :=
            neg_le_neg hoffsetUpper
          _ ≤ literalTarget - negativeLiteralOffset weights literalWeights := by
            linarith [hliteralTarget.1]
      simpa [targetBound, weightBound, add_assoc] using this
    · have : literalTarget - negativeLiteralOffset weights literalWeights ≤
          ((targetBound + n * weightBound : ℕ) : ℤ) := by
        calc
          literalTarget - negativeLiteralOffset weights literalWeights ≤ literalTarget := by
            linarith [hoffsetNonnegative]
          _ ≤ (targetBound : ℤ) := hliteralTarget.2
          _ ≤ ((targetBound + n * weightBound : ℕ) : ℤ) := by
            push_cast
            omega
      simpa [targetBound, weightBound, add_assoc] using this

theorem compileCrossingLevel_within {n : ℕ}
    (weights : Fin n → ℤ) (shifted bit : ℕ) (selected : List (Fin n))
    (state : CrossingState n) (placeBound totalSlots processed : ℕ)
    (hplace : 2 ^ bit ≤ placeBound)
    (hslots : processed + selected.length ≤ totalSlots)
    (hcoefficients :
      ∀ i, state.coefficients i ≤ processed * placeBound)
    (hchildren :
      ∀ child ∈ state.children,
        EquationWithin
          (2 * (shifted + placeBound) + 1 +
            n * (2 * (totalSlots * placeBound) + 1))
          child) :
    let result := compileCrossingLevel weights shifted bit selected state
    (∀ i, result.coefficients i ≤
      (processed + selected.length) * placeBound) ∧
    ∀ child ∈ result.children,
      EquationWithin
        (2 * (shifted + placeBound) + 1 +
          n * (2 * (totalSlots * placeBound) + 1))
        child := by
  induction selected generalizing state processed with
  | nil =>
      simp only [compileCrossingLevel, List.length_nil, add_zero]
      exact ⟨hcoefficients, hchildren⟩
  | cons selected remaining ih =>
      simp only [compileCrossingLevel]
      have hnextSlots : processed + 1 + remaining.length ≤ totalSlots := by
        simp only [List.length_cons] at hslots
        omega
      by_cases hactive : (magnitude (weights selected)).testBit bit = true
      · rw [if_pos hactive]
        let next := addCrossingBit state.coefficients selected bit
        let child := crossingChild weights shifted next selected bit
        let nextState : CrossingState n := ⟨next, state.children ++ [child]⟩
        have hnextCoefficients :
            ∀ i, next i ≤ (processed + 1) * placeBound := by
          intro i
          dsimp [next, addCrossingBit]
          split
          · nlinarith [hcoefficients i]
          · nlinarith [hcoefficients i]
        have hnextGlobal :
            ∀ i, next i ≤ totalSlots * placeBound := by
          intro i
          exact (hnextCoefficients i).trans
            (Nat.mul_le_mul_right placeBound
              (Nat.le_of_add_right_le hnextSlots))
        have hchild :
            EquationWithin
              (2 * (shifted + placeBound) + 1 +
                n * (2 * (totalSlots * placeBound) + 1))
              child := by
          dsimp [child]
          exact crossingChild_within weights shifted next selected bit
            (totalSlots * placeBound) placeBound hnextGlobal hplace
        have hnextChildren :
            ∀ candidate ∈ nextState.children,
              EquationWithin
                (2 * (shifted + placeBound) + 1 +
                  n * (2 * (totalSlots * placeBound) + 1))
                candidate := by
          intro candidate hmem
          dsimp [nextState] at hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hchildren candidate hmem
          · simp only [List.mem_singleton] at hmem
            subst candidate
            exact hchild
        have hresult := ih nextState (processed + 1)
          hnextSlots hnextCoefficients hnextChildren
        dsimp [nextState, next, child] at hresult ⊢
        refine ⟨?_, hresult.2⟩
        intro i
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult.1 i
      · rw [if_neg hactive]
        have hnextCoefficients :
            ∀ i, state.coefficients i ≤ (processed + 1) * placeBound := by
          intro i
          exact (hcoefficients i).trans (Nat.mul_le_mul_right placeBound (Nat.le_succ _))
        have hresult := ih state (processed + 1)
          hnextSlots hnextCoefficients hchildren
        refine ⟨?_, hresult.2⟩
        intro i
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult.1 i

theorem compileCrossingLevels_within {n : ℕ}
    (weights : Fin n → ℤ) (shifted levels : ℕ) (state : CrossingState n)
    (placeBound totalSlots processed : ℕ)
    (hplaces : ∀ bit < levels, 2 ^ bit ≤ placeBound)
    (hslots : processed + n * levels ≤ totalSlots)
    (hcoefficients :
      ∀ i, state.coefficients i ≤ processed * placeBound)
    (hchildren :
      ∀ child ∈ state.children,
        EquationWithin
          (2 * (shifted + placeBound) + 1 +
            n * (2 * (totalSlots * placeBound) + 1))
          child) :
    let result := compileCrossingLevels weights shifted levels state
    (∀ i, result.coefficients i ≤
      (processed + n * levels) * placeBound) ∧
    ∀ child ∈ result.children,
      EquationWithin
        (2 * (shifted + placeBound) + 1 +
          n * (2 * (totalSlots * placeBound) + 1))
        child := by
  induction levels generalizing state processed with
  | zero =>
      simp only [compileCrossingLevels, mul_zero, add_zero]
      exact ⟨hcoefficients, hchildren⟩
  | succ bit ih =>
      let afterLevel := compileCrossingLevel weights shifted bit
        (List.finRange n).reverse state
      have hlevelSlots :
          processed + (List.finRange n).reverse.length ≤ totalSlots := by
        simp only [List.length_reverse, List.length_finRange]
        have : processed + n ≤ processed + n * (bit + 1) := by
          rw [Nat.mul_succ]
          omega
        exact this.trans hslots
      have hlevel := compileCrossingLevel_within weights shifted bit
        (List.finRange n).reverse state placeBound totalSlots processed
        (hplaces bit (Nat.lt_succ_self bit)) hlevelSlots hcoefficients hchildren
      have htailSlots : processed + n + n * bit ≤ totalSlots := by
        rw [Nat.mul_succ] at hslots
        omega
      have htail := ih afterLevel (processed + n)
        (fun lower hlower => hplaces lower (hlower.trans (Nat.lt_succ_self bit)))
        htailSlots
        (by
          intro i
          simpa using hlevel.1 i)
        hlevel.2
      dsimp [afterLevel] at htail ⊢
      simpa [compileCrossingLevels, Nat.mul_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using htail

theorem compilerParameterBound_pos {n : ℕ}
  (weights : Fin n → ℤ) (target : ℤ) :
    0 < compilerParameterBound weights target := by
  unfold compilerParameterBound
  positivity

/-- Every emitted coefficient and target is inside one explicit global
envelope, including both constant branches and signed-literal expansion. -/
theorem erratumSafeDisjointChildren_parameters {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) :
    ∀ child ∈ erratumSafeDisjointChildren weights target,
      EquationWithin (compilerParameterBound weights target) child := by
  intro child hmem
  by_cases hnegative : shiftedTarget weights target < 0
  · rw [erratumSafeDisjointChildren_true_constant weights target hnegative] at hmem
    simp only [List.mem_singleton] at hmem
    subst child
    constructor
    · intro i
      simp [zeroEquation]
    · simp [zeroEquation]
  · have hnonnegative : 0 ≤ shiftedTarget weights target := le_of_not_gt hnegative
    by_cases hconstant :
        (totalMagnitude weights : ℤ) ≤ shiftedTarget weights target
    · rw [erratumSafeDisjointChildren_false_constant weights target
        hnonnegative hconstant] at hmem
      simp only [List.mem_singleton] at hmem
      subst child
      constructor
      · intro i
        simp [zeroEquation]
      · change (1 : ℤ) ≤ (compilerParameterBound weights target : ℕ)
        exact_mod_cast compilerParameterBound_pos weights target
    · rw [erratumSafeDisjointChildren] at hmem
      simp only [hnegative, hconstant, ↓reduceIte] at hmem
      let levels := crossingLevelCount weights target
      let place := 2 ^ levels
      let slots := n * levels
      let initial : CrossingState n := ⟨fun _ => 0, []⟩
      have hplaces : ∀ bit < levels, 2 ^ bit ≤ place := by
        intro bit hbit
        exact Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hbit)
      have hcompiled := compileCrossingLevels_within weights
        (shiftedTarget weights target).toNat levels initial place slots 0
        hplaces (by simp [slots])
        (by intro i; simp [initial])
        (by intro candidate hcand; simp [initial] at hcand)
      have hbound := hcompiled.2 child
      dsimp [initial, levels, place, slots] at hbound hmem
      have := hbound hmem
      simpa [compilerParameterBound] using this

/-- Maximum magnitude appearing in the explicit input, with one as the
zero-input sentinel. -/
def compilerInputHeight {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) : ℕ :=
  max 1 (max (maximumMagnitude weights) (shiftedTarget weights target).toNat)

theorem compilerInputHeight_pos {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) :
    0 < compilerInputHeight weights target := by
  unfold compilerInputHeight
  omega

/-- The executable loop count is exactly the binary encoding length of the
largest normalized input parameter. -/
theorem crossingLevelCount_eq_inputSize {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) :
    crossingLevelCount weights target =
      Nat.size (compilerInputHeight weights target) := by
  let parameter :=
    max (maximumMagnitude weights) (shiftedTarget weights target).toNat
  by_cases hzero : parameter = 0
  · simp [crossingLevelCount, compilerInputHeight, parameter, hzero]
  · have hparameter : 1 ≤ parameter := Nat.one_le_iff_ne_zero.mpr hzero
    have hsize : 1 ≤ Nat.size parameter := by
      exact (Nat.size_pos.mpr (Nat.zero_lt_of_ne_zero hzero))
    simp [crossingLevelCount, compilerInputHeight, parameter,
      Nat.max_eq_right hparameter, Nat.max_eq_right hsize]

theorem erratumSafeDisjointChildren_encodingLength {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) :
    (erratumSafeDisjointChildren weights target).length ≤
      max 1 (n * Nat.size (compilerInputHeight weights target)) := by
  simpa [crossingLevelCount_eq_inputSize] using
    erratumSafeDisjointChildren_length weights target

/-- A kernel-visible polynomial/output-size bridge for the value envelope.
Consequently its binary encoding length is at most the size of the right-hand
side, which is one input-height factor times a polynomial in `n` and its bit
length. -/
theorem compilerParameterBound_le_encodingEnvelope {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) :
    compilerParameterBound weights target ≤
      (2 * n * n * Nat.size (compilerInputHeight weights target) + n + 5) *
        2 ^ Nat.size (compilerInputHeight weights target) := by
  let height := compilerInputHeight weights target
  let levels := Nat.size height
  let place := 2 ^ levels
  have hshifted :
      (shiftedTarget weights target).toNat ≤ height := by
    dsimp [height, compilerInputHeight]
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hheight : height < place := by
    dsimp [place, levels]
    exact Nat.size_le.mp le_rfl
  have hplace : 1 ≤ place := by
    dsimp [place]
    exact Nat.one_le_two_pow
  have hlevels :
      crossingLevelCount weights target = levels := by
    simpa [levels, height] using crossingLevelCount_eq_inputSize weights target
  unfold compilerParameterBound
  rw [hlevels]
  dsimp [levels, place] at hshifted hheight hplace ⊢
  nlinarith

theorem compilerParameterBitLength_le_encodingEnvelope {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) :
    Nat.size (compilerParameterBound weights target) ≤
      Nat.size
        ((2 * n * n * Nat.size (compilerInputHeight weights target) + n + 5) *
          2 ^ Nat.size (compilerInputHeight weights target)) :=
  Nat.size_le_size (compilerParameterBound_le_encodingEnvelope weights target)

end NearCubicWires.ThresholdCompiler
