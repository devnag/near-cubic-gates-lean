import Proof.Circuits.AggregateSemanticStage
import Proof.Circuits.ComponentwisePolynomial
import Proof.Supplier.SupplierEstimator

/-!
# The linearity expansion of the aggregate clause mean

`AggregateSemanticStage` closes the corrected semantic stage down to one
obligation, `AggregateEstimateAccurate`: the machine must produce a number
within `estimationError` of

```text
mu = E_{i,u} F_i(T(u))
```

where `F_i` is the manuscript's degree-two arithmetization of PCPP clause `i`
and `T(u)` is the proof vector recovered from the guessed legal circuit sum at
PCPP input `u`.  This module builds the bridge from the supplier estimator's
per-request conjunction probabilities to that one number, which is Appendix
C.10's sentence "the machine estimates `mu` **by expanding it into AND-four
supplier calls**".

## §0 What the expansion produces

Three structures compose, and each of them is *linear*:

* the guessed sum is `D = sum_a alpha_a C_a`, linear in its atoms;
* fixing a clause address and a side is a **literal restriction** of every
  atom (`SliceRestricts` below), so on each occurrence slice the guess is one
  linear polynomial in circuits of the supplier's own family at arity `n`;
* the recovered proof coordinate is the **occurrence-fibre average** of the
  signed slice readings, again linear.

Only the clause polynomial `L + R - L*R` is nonlinear, and it is nonlinear of
degree exactly two.  Consequently **every** monomial of the expansion carries
at most two restricted atoms: the conjunctions that arise are the empty
conjunction (the constant, `conjunctionProbability evaluate []` = 1),
singletons `[C]`, and pairs `[C, C']`.  All three are inside the supplier's
`circuits.length <= 4` ABI, so no shape the expansion produces is outside what
`SharedNormalizedEstimator` can express.  The four-atom conjunctions of the
manuscript come from the *validity* side (`T^2 (1-T)^2`), which the seam
charges separately; the estimated clause mean itself never needs more than a
pair.

## §1 The bookkeeping

`ComponentwisePolynomial` already owns the monomial calculus: `clausePolynomial`
is the degree-two clause, `literalPolynomial` is the sign, `CircuitPolynomial.mul`
appends factor lists, and `estimatedMean_error_le` is the componentwise error
ledger.  Only one constructor is missing — a *finite* sum of polynomials, needed
by the occurrence fibre and by the clause-index average — and §1 supplies it.

## §2 The expansion

`aggregateClausePolynomial` is the composite, and
`aggregateClauseMean_eq_sum_conjunctionProbability` is the exact algebraic
identity: the aggregate clause mean *is* the coefficient-weighted sum of
conjunction probabilities of restricted atom lists of length at most two.

## §3 The coefficient mass

`clauseMassCap` is the manuscript's `Lambda_0`: with per-slice coefficient mass
at most `Lambda`, the aggregate expansion has coefficient mass at most
`(2 + Lambda)^2 + 2 * (2 + Lambda)`.  The two additive `1`s are the two signs —
the occurrence table stores the *signed* literal value, and the clause
polynomial re-applies the sign — and the square is the single product.  In the
manuscript's notation `Lambda_0 <= 4 * augmented^2 + 4 * augmented`, comfortably
inside the published `augmented^4`.

## §4 The recombination and the numeric dial

`aggregateEstimate_error_le_of_expansion` is `componentwise_real_error` at
`error := rows.failure`, `mass := Lambda_0`;
`aggregate_estimatedMean_error_le` is its instance at the concrete expansion.
`massCap_advantage_le_estimationError` is the numeric dial: at the published
request `D > 4R + 10` of Appendix C.3/A.8, the inverse-polynomial supplier
advantage times `Lambda_0(q)` is eventually below any fixed positive
`estimationError`.

## §5 The stage

`aggregateEstimateAccurate_of_expansion` discharges
`AggregateSemanticStage.AggregateEstimateAccurate`, and the two stage-side
corollaries put the completeness comparison and the soundness contradiction
each behind one named hypothesis about the executed supplier aggregation.
-/

namespace NearCubicWires.AggregateClauseExpansion

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.AggregateSemanticStage
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.OccurrenceSliceTransport
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

/-! ## §1 Finite sums of circuit polynomials -/

/-- Concatenating monomial lists adds polynomials.  This is the finite-sum
constructor the occurrence fibre and the clause-index average both need;
`CircuitPolynomial.add` is its two-element case. -/
def polynomialSumList {Atom : Type} {degree : ℕ}
    (polynomials : List (CircuitPolynomial Atom degree)) :
    CircuitPolynomial Atom degree where
  monomials := polynomials.flatMap fun polynomial => polynomial.monomials

theorem polynomialSumList_value {Atom : Type} {degree q : ℕ}
    (evaluate : Atom → BitInput q → Bool)
    (polynomials : List (CircuitPolynomial Atom degree))
    (input : BitInput q) :
    (polynomialSumList polynomials).value evaluate input =
      (polynomials.map fun polynomial =>
        polynomial.value evaluate input).sum := by
  change
    (((polynomials.flatMap fun polynomial => polynomial.monomials).map
        fun monomial => monomial.value evaluate input).sum) =
      (polynomials.map fun polynomial =>
        polynomial.value evaluate input).sum
  induction polynomials with
  | nil => rfl
  | cons polynomial polynomials inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, inductionHypothesis]
      rfl

theorem polynomialSumList_coefficientMass {Atom : Type} {degree : ℕ}
    (polynomials : List (CircuitPolynomial Atom degree)) :
    (polynomialSumList polynomials).coefficientMass =
      (polynomials.map fun polynomial =>
        polynomial.coefficientMass).sum := by
  change
    (((polynomials.flatMap fun polynomial => polynomial.monomials).map
        fun monomial => |monomial.coefficient|).sum) =
      (polynomials.map fun polynomial => polynomial.coefficientMass).sum
  induction polynomials with
  | nil => rfl
  | cons polynomial polynomials inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, inductionHypothesis]
      rfl

/-- Sum a family of polynomials over a finite index set. -/
noncomputable def polynomialFinsetSum {Atom : Type} {degree : ℕ} {ι : Type}
    (index : Finset ι) (polynomial : ι → CircuitPolynomial Atom degree) :
    CircuitPolynomial Atom degree :=
  polynomialSumList (index.toList.map polynomial)

theorem polynomialFinsetSum_value {Atom : Type} {degree q : ℕ} {ι : Type}
    (evaluate : Atom → BitInput q → Bool) (index : Finset ι)
    (polynomial : ι → CircuitPolynomial Atom degree) (input : BitInput q) :
    (polynomialFinsetSum index polynomial).value evaluate input =
      ∑ i ∈ index, (polynomial i).value evaluate input := by
  rw [polynomialFinsetSum, polynomialSumList_value, List.map_map]
  exact Finset.sum_map_toList index
    (fun i => (polynomial i).value evaluate input)

theorem polynomialFinsetSum_coefficientMass {Atom : Type} {degree : ℕ}
    {ι : Type} (index : Finset ι)
    (polynomial : ι → CircuitPolynomial Atom degree) :
    (polynomialFinsetSum index polynomial).coefficientMass =
      ∑ i ∈ index, (polynomial i).coefficientMass := by
  rw [polynomialFinsetSum, polynomialSumList_coefficientMass, List.map_map]
  exact Finset.sum_map_toList index
    (fun i => (polynomial i).coefficientMass)

theorem coefficientMass_nonneg {Atom : Type} {degree : ℕ}
    (polynomial : CircuitPolynomial Atom degree) :
    0 ≤ polynomial.coefficientMass := by
  refine List.sum_nonneg ?_
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨monomial, _, hcoefficient⟩
  rw [← hcoefficient]
  exact abs_nonneg _

/-! ## §2 The expansion

The three linear layers, then the single degree-two clause. -/

def SliceRestricts {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice :
      Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1) : Prop :=
  ∀ (input : BitInput n) (slot : Fin (2 ^ pcpp.clauseBits) × Bool),
    (slice slot).value evaluate input = sliceGuess pcpp guess input slot

/-- The signed coordinate reading of one clause occurrence, as a linear
polynomial in the restricted atoms.  The occurrence table stores the *literal*
value, so a negative literal is read back complemented. -/
def occurrenceSlotPolynomial {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool) : CircuitPolynomial Atom 1 :=
  literalPolynomial (literalNegated (occurrenceLiteral pcpp slot)) (slice slot)

/-- The proof coordinate the verifier reads back: the occurrence-fibre average
of the signed coordinate readings.  Coordinates named by no occurrence get the
zero polynomial, matching `occurrenceProofValue`. -/
noncomputable def occurrenceCoordinatePolynomial {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    CircuitPolynomial Atom 1 :=
  CircuitPolynomial.scale
    (1 / ((occurrenceFiber (occurrenceVariable pcpp) coordinate).card : ℚ))
    (polynomialFinsetSum (occurrenceFiber (occurrenceVariable pcpp) coordinate)
      (occurrenceSlotPolynomial pcpp slice))

/-- The manuscript's `F_i`: the degree-two arithmetization of clause `i`,
evaluated at the recovered proof coordinates. -/
noncomputable def clauseIndexPolynomial {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (index : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 2 :=
  clausePolynomial (literalNegated (pcpp.clauses index).left)
    (literalNegated (pcpp.clauses index).right)
    (occurrenceCoordinatePolynomial pcpp slice
      (literalIndex (pcpp.clauses index).left))
    (occurrenceCoordinatePolynomial pcpp slice
      (literalIndex (pcpp.clauses index).right))

/-- **The aggregate clause polynomial.**  One degree-two monomial list whose
uniform mean over the PCPP input cube is exactly the estimated quantity
`mu = E_{i,u} F_i(T(u))`. -/
noncomputable def aggregateClausePolynomial {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1) :
    CircuitPolynomial Atom 2 :=
  CircuitPolynomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ))
    (polynomialFinsetSum (univ : Finset (Fin (2 ^ pcpp.clauseBits)))
      (clauseIndexPolynomial pcpp slice))

/-- **Every conjunction the expansion requests has at most two atoms**, hence
at most the four the supplier ABI accepts.  This is a property of the type: the
clause is degree two. -/
theorem aggregateClausePolynomial_factors_length_le_four {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (monomial : CircuitMonomial Atom 2)
    (_hmonomial :
      monomial ∈ (aggregateClausePolynomial pcpp slice).monomials) :
    monomial.factors.length ≤ 4 :=
  monomial.degree_le.trans (by norm_num)

theorem occurrenceSlotPolynomial_value {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice)
    (input : BitInput n) (slot : Fin (2 ^ pcpp.clauseBits) × Bool) :
    (occurrenceSlotPolynomial pcpp slice slot).value evaluate input =
      occurrenceCoordinateValue pcpp (sliceGuess pcpp guess input) slot := by
  rw [occurrenceSlotPolynomial, literalPolynomial_value, hslice input slot]
  rfl

theorem occurrenceCoordinatePolynomial_value {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice)
    (input : BitInput n)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (occurrenceCoordinatePolynomial pcpp slice coordinate).value evaluate
        input =
      recoveredProofValue pcpp guess input coordinate := by
  rw [occurrenceCoordinatePolynomial, CircuitPolynomial.scale_value,
    polynomialFinsetSum_value]
  rw [Finset.sum_congr rfl fun slot _ =>
    occurrenceSlotPolynomial_value pcpp evaluate guess slice hslice input slot]
  change
    ((1 / ((occurrenceFiber (occurrenceVariable pcpp) coordinate).card : ℚ) :
        ℚ) : ℝ) *
        ∑ slot ∈ occurrenceFiber (occurrenceVariable pcpp) coordinate,
          occurrenceCoordinateValue pcpp (sliceGuess pcpp guess input) slot =
      meanOn (occurrenceFiber (occurrenceVariable pcpp) coordinate)
        (occurrenceCoordinateValue pcpp (sliceGuess pcpp guess input))
  rw [meanOn]
  push_cast
  ring

theorem clauseIndexPolynomial_value {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice)
    (input : BitInput n) (index : Fin (2 ^ pcpp.clauseBits)) :
    (clauseIndexPolynomial pcpp slice index).value evaluate input =
      clauseRealValue (pcpp.clauses index)
        (recoveredProofValue pcpp guess input) := by
  rw [clauseIndexPolynomial, clausePolynomial_value,
    occurrenceCoordinatePolynomial_value pcpp evaluate guess slice hslice input,
    occurrenceCoordinatePolynomial_value pcpp evaluate guess slice hslice input]
  rfl

theorem aggregateClausePolynomial_value {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice)
    (input : BitInput n) :
    (aggregateClausePolynomial pcpp slice).value evaluate input =
      clauseMean pcpp (recoveredProofValue pcpp guess input) := by
  rw [aggregateClausePolynomial, CircuitPolynomial.scale_value,
    polynomialFinsetSum_value]
  rw [Finset.sum_congr rfl fun index _ =>
    clauseIndexPolynomial_value pcpp evaluate guess slice hslice input index]
  rw [clauseMean, Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-- **The semantic expansion theorem.**  The aggregate clause mean of the proof
family recovered from a guessed legal circuit sum is the exact mean of the
degree-two aggregate clause polynomial in the restricted atoms. -/
theorem aggregateClauseMean_eq_exactMean {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice) :
    aggregateClauseMean pcpp
        (fun input => recoveredProofValue pcpp guess input) =
      (aggregateClausePolynomial pcpp slice).exactMean evaluate := by
  rw [CircuitPolynomial.exactMean_eq_uniformMean,
    CircuitPolynomial.uniformMean, aggregateClauseMean]
  exact Finset.expect_congr rfl fun input _ =>
    (aggregateClausePolynomial_value pcpp evaluate guess slice hslice
      input).symm

/-- **The expansion, fully unfolded.**  Each summand is exactly the quantity a
`SharedNormalizedEstimator` request returns: `conjunctionProbability evaluate`
of a list of at most two restricted atoms. -/
theorem aggregateClauseMean_eq_sum_conjunctionProbability {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice) :
    aggregateClauseMean pcpp
        (fun input => recoveredProofValue pcpp guess input) =
      ((aggregateClausePolynomial pcpp slice).monomials.map
        fun monomial =>
          (monomial.coefficient : ℝ) *
            conjunctionProbability evaluate monomial.factors).sum :=
  aggregateClauseMean_eq_exactMean pcpp evaluate guess slice hslice

/-! ## §3 The coefficient mass

`Lambda_0` in the manuscript's notation.  Two signs and one product. -/

/-- **The coefficient-mass cap.**  With per-slice coefficient mass at most
`mass`, the aggregate expansion has coefficient mass at most this.  The two
additive `2`s are the two signs the expansion applies (the occurrence table
stores the signed literal; the clause polynomial re-applies the sign), and the
square is the single degree-two product. -/
def clauseMassCap (mass : ℚ) : ℚ := (2 + mass) ^ 2 + 2 * (2 + mass)

theorem occurrenceSlotPolynomial_coefficientMass_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (mass : ℚ) (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool) :
    (occurrenceSlotPolynomial pcpp slice slot).coefficientMass ≤ 1 + mass := by
  rw [occurrenceSlotPolynomial, literalPolynomial_coefficientMass]
  have hslot := hmass slot
  cases literalNegated (occurrenceLiteral pcpp slot) with
  | false => simpa using by linarith
  | true => simpa using by linarith

theorem occurrenceCoordinatePolynomial_coefficientMass_le {Atom : Type}
    {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (occurrenceCoordinatePolynomial pcpp slice coordinate).coefficientMass ≤
      1 + mass := by
  classical
  rw [occurrenceCoordinatePolynomial, CircuitPolynomial.scale_coefficientMass,
    polynomialFinsetSum_coefficientMass]
  set fiber := occurrenceFiber (occurrenceVariable pcpp) coordinate with hfiber
  have hbound :
      (∑ slot ∈ fiber,
          (occurrenceSlotPolynomial pcpp slice slot).coefficientMass) ≤
        (fiber.card : ℚ) * (1 + mass) := by
    calc
      (∑ slot ∈ fiber,
          (occurrenceSlotPolynomial pcpp slice slot).coefficientMass) ≤
          ∑ _slot ∈ fiber, (1 + mass) :=
        Finset.sum_le_sum fun slot _ =>
          occurrenceSlotPolynomial_coefficientMass_le pcpp slice mass hmass slot
      _ = (fiber.card : ℚ) * (1 + mass) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos fiber.card with hcard | hcard
  · have hempty : fiber = ∅ := Finset.card_eq_zero.mp hcard
    rw [hempty]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero,
      mul_zero, div_zero, abs_zero]
    linarith
  · have hpositive : (0 : ℚ) < (fiber.card : ℚ) := by
      exact_mod_cast hcard
    have habs : |1 / (fiber.card : ℚ)| = 1 / (fiber.card : ℚ) :=
      abs_of_nonneg (by positivity)
    rw [habs]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpositive]
    calc
      (∑ slot ∈ fiber,
          (occurrenceSlotPolynomial pcpp slice slot).coefficientMass) ≤
          (fiber.card : ℚ) * (1 + mass) := hbound
      _ = (1 + mass) * (fiber.card : ℚ) := by ring

theorem clauseIndexPolynomial_coefficientMass_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass)
    (index : Fin (2 ^ pcpp.clauseBits)) :
    (clauseIndexPolynomial pcpp slice index).coefficientMass ≤
      clauseMassCap mass := by
  rw [clauseIndexPolynomial, clausePolynomial_coefficientMass, clauseMassCap]
  have hside :
      ∀ (negative : Bool)
        (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)),
        (literalPolynomial negative
              (occurrenceCoordinatePolynomial pcpp slice
                coordinate)).coefficientMass ≤ 2 + mass := by
    intro negative coordinate
    have hcoordinate :=
      occurrenceCoordinatePolynomial_coefficientMass_le pcpp slice mass
        hmassNonneg hmass coordinate
    rw [literalPolynomial_coefficientMass]
    cases negative with
    | false => simpa using by linarith
    | true => simpa using by linarith
  have hleft :=
    hside (literalNegated (pcpp.clauses index).left)
      (literalIndex (pcpp.clauses index).left)
  have hright :=
    hside (literalNegated (pcpp.clauses index).right)
      (literalIndex (pcpp.clauses index).right)
  have hleftNonneg :
      (0 : ℚ) ≤
        (literalPolynomial (literalNegated (pcpp.clauses index).left)
          (occurrenceCoordinatePolynomial pcpp slice
            (literalIndex (pcpp.clauses index).left))).coefficientMass :=
    coefficientMass_nonneg _
  have hrightNonneg :
      (0 : ℚ) ≤
        (literalPolynomial (literalNegated (pcpp.clauses index).right)
          (occurrenceCoordinatePolynomial pcpp slice
            (literalIndex (pcpp.clauses index).right))).coefficientMass :=
    coefficientMass_nonneg _
  nlinarith

theorem aggregateClausePolynomial_coefficientMass_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass) :
    (aggregateClausePolynomial pcpp slice).coefficientMass ≤
      clauseMassCap mass := by
  classical
  rw [aggregateClausePolynomial, CircuitPolynomial.scale_coefficientMass,
    polynomialFinsetSum_coefficientMass]
  have hpositive : (0 : ℚ) < ((2 ^ pcpp.clauseBits : ℕ) : ℚ) := by
    positivity
  have habs :
      |1 / (2 ^ pcpp.clauseBits : ℚ)| = 1 / (2 ^ pcpp.clauseBits : ℚ) :=
    abs_of_nonneg (by positivity)
  have hbound :
      (∑ index ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
          (clauseIndexPolynomial pcpp slice index).coefficientMass) ≤
        (2 ^ pcpp.clauseBits : ℚ) * clauseMassCap mass := by
    calc
      (∑ index ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
          (clauseIndexPolynomial pcpp slice index).coefficientMass) ≤
          ∑ _index ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
            clauseMassCap mass :=
        Finset.sum_le_sum fun index _ =>
          clauseIndexPolynomial_coefficientMass_le pcpp slice mass hmassNonneg
            hmass index
      _ = (2 ^ pcpp.clauseBits : ℚ) * clauseMassCap mass := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_fin]
        push_cast
        ring
  rw [habs, div_mul_eq_mul_div, one_mul,
    div_le_iff₀ (by positivity : (0 : ℚ) < (2 ^ pcpp.clauseBits : ℚ))]
  calc
    (∑ index ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
        (clauseIndexPolynomial pcpp slice index).coefficientMass) ≤
        (2 ^ pcpp.clauseBits : ℚ) * clauseMassCap mass := hbound
    _ = clauseMassCap mass * (2 ^ pcpp.clauseBits : ℚ) := by ring

/-! ## §4 The recombination

`componentwise_real_error` at `error := rows.failure`, `mass := Lambda_0`. -/

/-- **The recombination, in the componentwise ledger's own shape.**  Any finite
expansion of the aggregate clause mean into coefficient-weighted conjunction
probabilities transports the supplier's per-request failure parameter into an
error on the single estimated number, multiplied by the coefficient mass.  This
is `ComponentwiseTransfer.componentwise_real_error`. -/
theorem aggregateEstimate_error_le_of_expansion {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    {ι : Type} (index : Finset ι) (coefficient : ι → ℝ)
    (circuits : ι → List Atom) (estimate : ι → ℝ) (failure mass : ℝ)
    (hfailure : 0 ≤ failure)
    (hpoint : ∀ i ∈ index,
      |estimate i - conjunctionProbability evaluate (circuits i)| ≤ failure)
    (hmass : (∑ i ∈ index, |coefficient i|) ≤ mass)
    (hexpansion :
      aggregateClauseMean pcpp value =
        ∑ i ∈ index,
          coefficient i * conjunctionProbability evaluate (circuits i)) :
    |(∑ i ∈ index, coefficient i * estimate i) -
        aggregateClauseMean pcpp value| ≤ failure * mass := by
  rw [hexpansion]
  exact componentwise_real_error index coefficient
    (fun i => conjunctionProbability evaluate (circuits i)) estimate failure
    mass hfailure hpoint hmass

private theorem list_map_sum_eq_finsetSum {α β : Type} [AddCommMonoid β]
    (values : List α) (map : α → β) :
    (values.map map).sum = ∑ i : Fin values.length, map values[i] := by
  induction values with
  | nil => simp
  | cons value values inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Fin.sum_univ_succ, inductionHypothesis]
      rfl

/-- **The recombination at the concrete expansion, indexed by a `Finset`.**
Every monomial of the aggregate clause polynomial contributes one supplier
request; the sum of the estimates is within `failure * Lambda_0` of the
aggregate clause mean. -/
theorem aggregate_finsetEstimate_error_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice)
    (estimate : List Atom → ℝ) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |estimate circuits - conjunctionProbability evaluate circuits| ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass) :
    |(∑ i : Fin (aggregateClausePolynomial pcpp slice).monomials.length,
          (((aggregateClausePolynomial pcpp slice).monomials[i]).coefficient :
              ℝ) *
            estimate
              (((aggregateClausePolynomial pcpp slice).monomials[i]).factors)) -
        aggregateClauseMean pcpp
          (fun input => recoveredProofValue pcpp guess input)| ≤
      failure * (clauseMassCap mass : ℝ) := by
  classical
  refine aggregateEstimate_error_le_of_expansion pcpp evaluate
    (fun input => recoveredProofValue pcpp guess input)
    (univ : Finset (Fin (aggregateClausePolynomial pcpp slice).monomials.length))
    (fun i =>
      (((aggregateClausePolynomial pcpp slice).monomials[i]).coefficient : ℝ))
    (fun i => ((aggregateClausePolynomial pcpp slice).monomials[i]).factors)
    (fun i =>
      estimate (((aggregateClausePolynomial pcpp slice).monomials[i]).factors))
    failure (clauseMassCap mass : ℝ) hfailure (fun i _ => hpoint _) ?_ ?_
  · have hmassBound :
        (aggregateClausePolynomial pcpp slice).coefficientMass ≤
          clauseMassCap mass :=
      aggregateClausePolynomial_coefficientMass_le pcpp slice mass hmassNonneg
        hmass
    have hindexed :
        (aggregateClausePolynomial pcpp slice).coefficientMass =
          ∑ i : Fin (aggregateClausePolynomial pcpp slice).monomials.length,
            |((aggregateClausePolynomial pcpp slice).monomials[i]).coefficient| := by
      exact list_map_sum_eq_finsetSum
        (aggregateClausePolynomial pcpp slice).monomials
        (fun monomial => |monomial.coefficient|)
    rw [hindexed] at hmassBound
    exact_mod_cast hmassBound
  · rw [aggregateClauseMean_eq_sum_conjunctionProbability pcpp evaluate guess
      slice hslice]
    exact list_map_sum_eq_finsetSum
      (aggregateClausePolynomial pcpp slice).monomials
      (fun monomial =>
        (monomial.coefficient : ℝ) *
          conjunctionProbability evaluate monomial.factors)

/-- **The recombination in the estimator's own list shape.**  This is the same
statement through `CircuitPolynomial.estimatedMean`, which is the object the
executed supplier aggregation fills in monomial order. -/
theorem aggregate_estimatedMean_error_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice)
    (estimate : List Atom → ℚ) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |(estimate circuits : ℝ) -
        conjunctionProbability evaluate circuits| ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass) :
    |(aggregateClausePolynomial pcpp slice).estimatedMean estimate -
        aggregateClauseMean pcpp
          (fun input => recoveredProofValue pcpp guess input)| ≤
      failure * (clauseMassCap mass : ℝ) := by
  rw [aggregateClauseMean_eq_exactMean pcpp evaluate guess slice hslice]
  refine le_trans
    (estimatedMean_error_le evaluate estimate
      (aggregateClausePolynomial pcpp slice) failure
      (fun monomial _ => hpoint monomial.factors)) ?_
  refine mul_le_mul_of_nonneg_left ?_ hfailure
  exact_mod_cast
    aggregateClausePolynomial_coefficientMass_le pcpp slice mass hmassNonneg
      hmass

/-! ## §5 The numeric dial

Appendix C.3 requests `D > 4R + 10` from the supplier, where `R` bounds the
coefficient-mass exponent and `D` the accuracy exponent.  At that request the
propagated error of the expansion is eventually below any fixed positive
`estimationError`. -/

/-- **The published dial.**  With coefficient mass at most `q ^ massExponent`
and the manuscript's request `4 * massExponent + 10 <= accuracyExponent`, the
propagated error `Lambda_0(q) * inversePolynomialAdvantage q accuracyExponent`
is at most `estimationError` for every
`q >= ceil (15 / estimationError) + 1`. -/
private theorem inversePolynomialAdvantage_eq_rpow (q : ℕ) (exponent : ℝ) :
    inversePolynomialAdvantage q exponent = (q : ℝ) ^ (-exponent) := rfl

theorem massCap_advantage_le_estimationError
    (massExponent accuracyExponent estimationError : ℝ)
    (hmassExponent : 0 ≤ massExponent) (herror : 0 < estimationError)
    (hdial : 4 * massExponent + 10 ≤ accuracyExponent)
    (q : ℕ) (honset : ⌈15 / estimationError⌉₊ + 1 ≤ q)
    (mass : ℝ) (hmassNonneg : 0 ≤ mass)
    (hmassBound : mass ≤ (q : ℝ) ^ massExponent) :
    ((2 + mass) ^ 2 + 2 * (2 + mass)) *
        inversePolynomialAdvantage q accuracyExponent ≤ estimationError := by
  rw [inversePolynomialAdvantage_eq_rpow]
  have hqNat : 1 ≤ q := by omega
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqNat
  have hqPositive : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq
  set scale : ℝ := (q : ℝ) ^ massExponent with hscale
  have hscaleOne : (1 : ℝ) ≤ scale := by
    rw [hscale]
    exact Real.one_le_rpow hq hmassExponent
  have hcap :
      (2 + mass) ^ 2 + 2 * (2 + mass) ≤ 15 * (scale * scale) := by
    nlinarith
  have hsquare :
      scale * scale = (q : ℝ) ^ (2 * massExponent) := by
    rw [hscale, ← Real.rpow_add hqPositive]
    ring_nf
  have hadvantage :
      (q : ℝ) ^ (2 * massExponent) * (q : ℝ) ^ (-accuracyExponent) ≤
        (q : ℝ) ^ (-10 : ℝ) := by
    rw [← Real.rpow_add hqPositive]
    exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hten : (q : ℝ) ^ (-10 : ℝ) = ((q : ℝ) ^ (10 : ℕ))⁻¹ := by
    rw [show (-10 : ℝ) = -((10 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (le_of_lt hqPositive), Real.rpow_natCast]
  have hpow : (q : ℝ) ≤ (q : ℝ) ^ (10 : ℕ) := by
    calc
      (q : ℝ) = (q : ℝ) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ (q : ℝ) ^ (10 : ℕ) := pow_le_pow_right₀ hq (by norm_num)
  have hceil : 15 / estimationError ≤ (q : ℝ) := by
    have hcastCeil : ((⌈15 / estimationError⌉₊ : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.le_of_succ_le honset
    exact le_trans (Nat.le_ceil _) hcastCeil
  have hbigPow : 15 / estimationError ≤ (q : ℝ) ^ (10 : ℕ) :=
    le_trans hceil hpow
  have hpowPositive : (0 : ℝ) < (q : ℝ) ^ (10 : ℕ) := by positivity
  have hfinal : 15 * ((q : ℝ) ^ (10 : ℕ))⁻¹ ≤ estimationError := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpowPositive]
    rw [div_le_iff₀ herror] at hbigPow
    nlinarith
  have hadvantageNonneg : 0 ≤ (q : ℝ) ^ (-accuracyExponent) :=
    Real.rpow_nonneg (le_of_lt hqPositive) _
  calc
    ((2 + mass) ^ 2 + 2 * (2 + mass)) * (q : ℝ) ^ (-accuracyExponent) ≤
        (15 * (scale * scale)) * (q : ℝ) ^ (-accuracyExponent) :=
      mul_le_mul_of_nonneg_right hcap hadvantageNonneg
    _ = 15 *
          ((q : ℝ) ^ (2 * massExponent) * (q : ℝ) ^ (-accuracyExponent)) := by
      rw [hsquare]
      ring
    _ ≤ 15 * (q : ℝ) ^ (-10 : ℝ) :=
      mul_le_mul_of_nonneg_left hadvantage (by norm_num)
    _ = 15 * ((q : ℝ) ^ (10 : ℕ))⁻¹ := by rw [hten]
    _ ≤ estimationError := hfinal

/-! ## §6 Discharging the stage obligation -/

/-- **The aggregate estimator obligation, discharged.**  A supplier guarantee
at failure `failure`, an expansion coefficient mass at most `Lambda_0`, and the
numeric dial `failure * Lambda_0 <= estimationError` together fill the ledger's
`estimateClose` field. -/
theorem aggregateEstimateAccurate_of_expansion {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (estimate : List Atom → ℚ) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |(estimate circuits : ℝ) -
        conjunctionProbability evaluate circuits| ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass)
    (hbudget :
      failure * (clauseMassCap mass : ℝ) ≤
        (parameters.estimationError : ℝ)) :
    AggregateEstimateAccurate pcpp parameters
      (fun input => recoveredProofValue pcpp guess input)
      ((aggregateClausePolynomial pcpp slice).estimatedMean estimate) :=
  estimateAccurate_of_aggregateSupplierFailure pcpp parameters
    (fun input => recoveredProofValue pcpp guess input)
    ((aggregateClausePolynomial pcpp slice).estimatedMean estimate)
    (failure * (clauseMassCap mass : ℝ))
    (aggregate_estimatedMean_error_le pcpp evaluate guess slice hslice estimate
      failure hfailure hpoint mass hmassNonneg hmass)
    hbudget

/-- **The completeness comparison.**  The executed aggregation's number clears
the published threshold, with the estimator premise reduced to one supplier
failure parameter and one coefficient-mass cap. -/
theorem threshold_le_aggregateEstimate_of_l1Distance {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (delta : ℝ)
    (hnonneg : ∀ address, 0 ≤ guess address)
    (hleOne : ∀ address, guess address ≤ 1)
    (hhonest :
      ∀ input : BitInput n,
        completeness ≤
          clauseMean pcpp
            (fun j =>
              bitAsReal
                (pcpp.assignment input (pcpp.honestAuxiliary input) j)))
    (hdelta : delta ≤ 3 * (parameters.zeta : ℝ))
    (hdistance :
      l1DistanceFromBoolean (honestOccurrenceFunction pcpp) guess ≤ delta)
    (estimate : List Atom → ℚ) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |(estimate circuits : ℝ) -
        conjunctionProbability evaluate circuits| ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass)
    (hbudget :
      failure * (clauseMassCap mass : ℝ) ≤
        (parameters.estimationError : ℝ)) :
    (parameters.threshold : ℝ) ≤
      (aggregateClausePolynomial pcpp slice).estimatedMean estimate :=
  threshold_le_estimate_of_aggregateL1Distance pcpp parameters guess delta
    ((aggregateClausePolynomial pcpp slice).estimatedMean estimate) hnonneg
    hleOne hhonest hdelta hdistance
    (aggregateEstimateAccurate_of_expansion pcpp evaluate guess slice hslice
      parameters estimate failure hfailure hpoint mass hmassNonneg hmass
      hbudget)

/-- **The soundness contradiction.**  An accepting aggregate stage on a
hierarchy-NO word is impossible, with the estimator premise replaced by the
supplier failure parameter and the coefficient-mass cap. -/
theorem aggregateStage_rejects_of_expansion {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hnonneg : ∀ address, 0 ≤ guess address)
    (hleOne : ∀ address, guess address ≤ 1)
    (hvalidity :
      aggregateClausePenaltyMean pcpp
          (fun input => recoveredProofValue pcpp guess input) ≤
        6 * (parameters.zeta : ℝ))
    (hrounded :
      aggregateRoundedMean pcpp
          (fun input => recoveredProofValue pcpp guess input) ≤
        soundness + (parameters.outerError : ℝ))
    (estimate : List Atom → ℚ) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |(estimate circuits : ℝ) -
        conjunctionProbability evaluate circuits| ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass)
    (hbudget :
      failure * (clauseMassCap mass : ℝ) ≤
        (parameters.estimationError : ℝ))
    (haccepted :
      (parameters.threshold : ℝ) ≤
        (aggregateClausePolynomial pcpp slice).estimatedMean estimate) :
    False :=
  aggregateStage_rejects pcpp parameters
    (fun input => recoveredProofValue pcpp guess input)
    ((aggregateClausePolynomial pcpp slice).estimatedMean estimate)
    (fun input j =>
      (recoveredProofValue_mem_unitInterval pcpp guess input hnonneg hleOne
        j).1)
    (fun input j =>
      (recoveredProofValue_mem_unitInterval pcpp guess input hnonneg hleOne
        j).2)
    hvalidity hrounded
    (aggregateEstimateAccurate_of_expansion pcpp evaluate guess slice hslice
      parameters estimate failure hfailure hpoint mass hmassNonneg hmass
      hbudget)
    haccepted

/-- **The stage obligation against the executed symmetric aggregation.** -/
theorem aggregateEstimateAccurate_of_sharedSymmetricEstimator {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool →
      CircuitPolynomial (NormalizedSymmetricThresholdCircuit n) 1)
    (hslice :
      SliceRestricts pcpp NormalizedSymmetricThresholdCircuit.eval guess slice)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (shared : SupplierEstimator.SharedNormalizedEstimator)
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hrows : ∀ circuits : List (NormalizedSymmetricThresholdCircuit n),
      shared.symmetricRows.failure ⟨n, circuits⟩ ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass)
    (hbudget :
      failure * (clauseMassCap mass : ℝ) ≤
        (parameters.estimationError : ℝ)) :
    AggregateEstimateAccurate pcpp parameters
      (fun input => recoveredProofValue pcpp guess input)
      ((aggregateClausePolynomial pcpp slice).estimatedMean
        shared.symmetricAlgorithm.estimate) :=
  aggregateEstimateAccurate_of_expansion pcpp
    NormalizedSymmetricThresholdCircuit.eval guess slice hslice parameters
    shared.symmetricAlgorithm.estimate failure hfailure
    (fun circuits =>
      le_trans (shared.symmetric_accurate circuits) (hrows circuits))
    mass hmassNonneg hmass hbudget

/-- **The stage obligation against the executed threshold aggregation.** -/
theorem aggregateEstimateAccurate_of_sharedThresholdEstimator {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool →
      CircuitPolynomial (NormalizedThresholdThresholdCircuit n) 1)
    (hslice :
      SliceRestricts pcpp NormalizedThresholdThresholdCircuit.eval guess slice)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (shared : SupplierEstimator.SharedNormalizedEstimator)
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hrows : ∀ circuits : List (NormalizedThresholdThresholdCircuit n),
      shared.thresholdRows.failure ⟨n, circuits⟩ ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass)
    (hbudget :
      failure * (clauseMassCap mass : ℝ) ≤
        (parameters.estimationError : ℝ)) :
    AggregateEstimateAccurate pcpp parameters
      (fun input => recoveredProofValue pcpp guess input)
      ((aggregateClausePolynomial pcpp slice).estimatedMean
        shared.thresholdAlgorithm.estimate) :=
  aggregateEstimateAccurate_of_expansion pcpp
    NormalizedThresholdThresholdCircuit.eval guess slice hslice parameters
    shared.thresholdAlgorithm.estimate failure hfailure
    (fun circuits =>
      le_trans (shared.threshold_accurate circuits) (hrows circuits))
    mass hmassNonneg hmass hbudget

/-- **Completeness, against the executed symmetric aggregation.**  Every
premise is either the XOR contract's published radius or one named bound on the
executed supplier's failure parameter. -/
theorem threshold_le_sharedSymmetricEstimate_of_l1Distance {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool →
      CircuitPolynomial (NormalizedSymmetricThresholdCircuit n) 1)
    (hslice :
      SliceRestricts pcpp NormalizedSymmetricThresholdCircuit.eval guess slice)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (delta : ℝ)
    (hnonneg : ∀ address, 0 ≤ guess address)
    (hleOne : ∀ address, guess address ≤ 1)
    (hhonest :
      ∀ input : BitInput n,
        completeness ≤
          clauseMean pcpp
            (fun j =>
              bitAsReal
                (pcpp.assignment input (pcpp.honestAuxiliary input) j)))
    (hdelta : delta ≤ 3 * (parameters.zeta : ℝ))
    (hdistance :
      l1DistanceFromBoolean (honestOccurrenceFunction pcpp) guess ≤ delta)
    (shared : SupplierEstimator.SharedNormalizedEstimator)
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hrows : ∀ circuits : List (NormalizedSymmetricThresholdCircuit n),
      shared.symmetricRows.failure ⟨n, circuits⟩ ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass)
    (hbudget :
      failure * (clauseMassCap mass : ℝ) ≤
        (parameters.estimationError : ℝ)) :
    (parameters.threshold : ℝ) ≤
      (aggregateClausePolynomial pcpp slice).estimatedMean
        shared.symmetricAlgorithm.estimate :=
  threshold_le_aggregateEstimate_of_l1Distance pcpp
    NormalizedSymmetricThresholdCircuit.eval guess slice hslice parameters
    delta hnonneg hleOne hhonest hdelta hdistance
    shared.symmetricAlgorithm.estimate failure hfailure
    (fun circuits =>
      le_trans (shared.symmetric_accurate circuits) (hrows circuits))
    mass hmassNonneg hmass hbudget

/-- **Soundness, against the executed symmetric aggregation.**  An accepting
aggregate stage on a hierarchy-NO word is impossible. -/
theorem aggregateStage_rejects_of_sharedSymmetricEstimator {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool →
      CircuitPolynomial (NormalizedSymmetricThresholdCircuit n) 1)
    (hslice :
      SliceRestricts pcpp NormalizedSymmetricThresholdCircuit.eval guess slice)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hnonneg : ∀ address, 0 ≤ guess address)
    (hleOne : ∀ address, guess address ≤ 1)
    (hvalidity :
      aggregateClausePenaltyMean pcpp
          (fun input => recoveredProofValue pcpp guess input) ≤
        6 * (parameters.zeta : ℝ))
    (hrounded :
      aggregateRoundedMean pcpp
          (fun input => recoveredProofValue pcpp guess input) ≤
        soundness + (parameters.outerError : ℝ))
    (shared : SupplierEstimator.SharedNormalizedEstimator)
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hrows : ∀ circuits : List (NormalizedSymmetricThresholdCircuit n),
      shared.symmetricRows.failure ⟨n, circuits⟩ ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ slot, (slice slot).coefficientMass ≤ mass)
    (hbudget :
      failure * (clauseMassCap mass : ℝ) ≤
        (parameters.estimationError : ℝ))
    (haccepted :
      (parameters.threshold : ℝ) ≤
        (aggregateClausePolynomial pcpp slice).estimatedMean
          shared.symmetricAlgorithm.estimate) :
    False :=
  aggregateStage_rejects_of_expansion pcpp
    NormalizedSymmetricThresholdCircuit.eval guess slice hslice parameters
    hnonneg hleOne hvalidity hrounded shared.symmetricAlgorithm.estimate
    failure hfailure
    (fun circuits =>
      le_trans (shared.symmetric_accurate circuits) (hrows circuits))
    mass hmassNonneg hmass hbudget haccepted

def RestrictedLegalSum {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (mass : ℚ) : Prop :=
  ∃ slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1,
    SliceRestricts pcpp evaluate guess slice ∧
      ∀ slot, (slice slot).coefficientMass ≤ mass

theorem exists_aggregateEstimateAccurate_of_restrictedLegalSum {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (shared : SupplierEstimator.SharedNormalizedEstimator)
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hrows : ∀ circuits : List (NormalizedSymmetricThresholdCircuit n),
      shared.symmetricRows.failure ⟨n, circuits⟩ ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hsum :
      RestrictedLegalSum pcpp NormalizedSymmetricThresholdCircuit.eval guess
        mass)
    (hbudget :
      failure * (clauseMassCap mass : ℝ) ≤
        (parameters.estimationError : ℝ)) :
    ∃ estimate : ℝ,
      AggregateEstimateAccurate pcpp parameters
        (fun input => recoveredProofValue pcpp guess input) estimate := by
  obtain ⟨slice, hslice, hmass⟩ := hsum
  exact
    ⟨(aggregateClausePolynomial pcpp slice).estimatedMean
        shared.symmetricAlgorithm.estimate,
      aggregateEstimateAccurate_of_sharedSymmetricEstimator pcpp guess slice
        hslice parameters shared failure hfailure hrows mass hmassNonneg hmass
        hbudget⟩

theorem exists_threshold_le_aggregateEstimate_of_restrictedLegalSum {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (delta : ℝ)
    (hnonneg : ∀ address, 0 ≤ guess address)
    (hleOne : ∀ address, guess address ≤ 1)
    (hhonest :
      ∀ input : BitInput n,
        completeness ≤
          clauseMean pcpp
            (fun j =>
              bitAsReal
                (pcpp.assignment input (pcpp.honestAuxiliary input) j)))
    (hdelta : delta ≤ 3 * (parameters.zeta : ℝ))
    (hdistance :
      l1DistanceFromBoolean (honestOccurrenceFunction pcpp) guess ≤ delta)
    (shared : SupplierEstimator.SharedNormalizedEstimator)
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hrows : ∀ circuits : List (NormalizedSymmetricThresholdCircuit n),
      shared.symmetricRows.failure ⟨n, circuits⟩ ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hsum :
      RestrictedLegalSum pcpp NormalizedSymmetricThresholdCircuit.eval guess
        mass)
    (hbudget :
      failure * (clauseMassCap mass : ℝ) ≤
        (parameters.estimationError : ℝ)) :
    ∃ estimate : ℝ,
      (parameters.threshold : ℝ) ≤ estimate ∧
        AggregateEstimateAccurate pcpp parameters
          (fun input => recoveredProofValue pcpp guess input) estimate := by
  obtain ⟨slice, hslice, hmass⟩ := hsum
  refine
    ⟨(aggregateClausePolynomial pcpp slice).estimatedMean
        shared.symmetricAlgorithm.estimate, ?_,
      aggregateEstimateAccurate_of_sharedSymmetricEstimator pcpp guess slice
        hslice parameters shared failure hfailure hrows mass hmassNonneg hmass
        hbudget⟩
  exact
    threshold_le_sharedSymmetricEstimate_of_l1Distance pcpp guess slice hslice
      parameters delta hnonneg hleOne hhonest hdelta hdistance shared failure
      hfailure hrows mass hmassNonneg hmass hbudget

end NearCubicWires.AggregateClauseExpansion
