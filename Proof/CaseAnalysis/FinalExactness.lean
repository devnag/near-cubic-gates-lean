import Proof.CaseAnalysis.RowsOriginalScheduleMeaning
import Proof.Circuits.AggregateClauseExpansion

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.AggregateClauseExpansion
open NearCubicWires.AggregateSemanticStage
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §0 Generic polynomial arithmetic -/

theorem scale_exactMean {Atom : Type} {degree q : ℕ}
    (evaluate : Atom → BitInput q → Bool) (scalar : ℚ)
    (polynomial : CircuitPolynomial Atom degree) :
    (polynomial.scale scalar).exactMean evaluate =
      (scalar : ℝ) * polynomial.exactMean evaluate := by
  rw [CircuitPolynomial.exactMean_eq_uniformMean,
    CircuitPolynomial.exactMean_eq_uniformMean, CircuitPolynomial.uniformMean,
    CircuitPolynomial.uniformMean, Finset.mul_expect]
  exact Finset.expect_congr rfl fun input _ =>
    CircuitPolynomial.scale_value scalar evaluate polynomial input

theorem weaken_exactMean {Atom : Type} {sourceDegree targetDegree q : ℕ}
    (hdegree : sourceDegree ≤ targetDegree)
    (evaluate : Atom → BitInput q → Bool)
    (polynomial : CircuitPolynomial Atom sourceDegree) :
    (polynomial.weaken hdegree).exactMean evaluate =
      polynomial.exactMean evaluate := by
  rw [CircuitPolynomial.exactMean_eq_uniformMean,
    CircuitPolynomial.exactMean_eq_uniformMean, CircuitPolynomial.uniformMean,
    CircuitPolynomial.uniformMean]
  exact Finset.expect_congr rfl fun input _ =>
    CircuitPolynomial.weaken_value hdegree evaluate polynomial input

/-- A list sum, as a `Finset` sum over the list's own index type.  This is the
shape `Realizes.hexpansion` is stated in. -/
theorem listSum_eq_finsetSum {α β : Type} [AddCommMonoid β]
    (values : List α) (map : α → β) :
    (values.map map).sum = ∑ i : Fin values.length, map values[i] := by
  induction values with
  | nil => simp
  | cons value values inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Fin.sum_univ_succ, inductionHypothesis]
      rfl

/-! ## §1 The restriction seam, at PCPP coordinates -/

/-- **The restriction seam.**  Each recovered PCPP coordinate is one linear
polynomial in supplier circuits at arity `n`.  This is the only assumption made
about the guessed proof. -/
def CoordinateExpands {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1) : Prop :=
  ∀ (input : BitInput n)
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)),
      (coordinate j).value evaluate input = proofValue input j

theorem coordinateExpands_of_sliceRestricts {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (hslice : SliceRestricts pcpp evaluate guess slice) :
    CoordinateExpands pcpp evaluate
      (fun input => OccurrenceSliceTransport.recoveredProofValue pcpp guess input)
      (occurrenceCoordinatePolynomial pcpp slice) :=
  fun input j =>
    occurrenceCoordinatePolynomial_value pcpp evaluate guess slice hslice input j

/-- **The seam is inhabited.**  Any coordinate family is its own proof value,
so `CoordinateExpands` never blocks the soundness direction, where `Exposes`
quantifies the proof value existentially.  The content of the exactness
theorem is carried by the conclusion -- the paper's grouped phase mean AT that
value -- not by the hypothesis. -/
theorem coordinateExpands_self {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (evaluate : Atom → BitInput n → Bool)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1) :
    CoordinateExpands pcpp evaluate
      (fun input j => (coordinate j).value evaluate input) coordinate :=
  fun _ _ => rfl

/-! ## §2 The site polynomials, one per PCPP clause address -/

/-- The validity polynomial of one recovered coordinate: the paper's
`(Enc_s - T_ij)^2` on a systematic coordinate and `T_ij^2 (1-T_ij)^2` on an
auxiliary one. -/
noncomputable def coordinatePenalty {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    CircuitPolynomial Atom 4 :=
  Fin.addCases
    (fun index =>
      (systematicValidityPolynomial (systematicAtom index)
        (coordinate (Fin.castAdd pcpp.auxiliaryBits index))).weaken (by omega))
    (fun index =>
      auxiliaryValidityPolynomial
        (coordinate (Fin.natAdd pcpp.systematicBits index)))
    j

/-- The penalty site: both charged coordinates of one clause address, carrying
the schedule's own `divisor .penalty = 2`. -/
noncomputable def penaltySite {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (i : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 4 :=
  CircuitPolynomial.scale (1 / 2)
    ((coordinatePenalty pcpp coordinate systematicAtom
        (literalIndex (pcpp.clauses i).left)).add
      (coordinatePenalty pcpp coordinate systematicAtom
        (literalIndex (pcpp.clauses i).right)))

/-- The second-moment site: the paper's `Q_ij = T_ij^2` on the left occurrence
of one clause address. -/
noncomputable def momentSite {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (i : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 4 :=
  (secondMomentPolynomial
    (coordinate (literalIndex (pcpp.clauses i).left))).weaken (by omega)

/-- The clause site: the paper's `F_i = Cons_i(T_i1, T_i2)`, the degree-two
arithmetization of one indexed clause. -/
noncomputable def clauseSite {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (i : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 4 :=
  (clausePolynomial (literalNegated (pcpp.clauses i).left)
    (literalNegated (pcpp.clauses i).right)
    (coordinate (literalIndex (pcpp.clauses i).left))
    (coordinate (literalIndex (pcpp.clauses i).right))).weaken (by omega)

/-- **The site polynomial of one grouped phase at one PCPP clause address.**
The site index is `Fin (2 ^ pcpp.clauseBits)`; there is no other site index. -/
noncomputable def sitePolynomial {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (i : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 4 :=
  match ph with
  | .penalty => penaltySite pcpp coordinate systematicAtom i
  | .moment => momentSite pcpp coordinate i
  | .clause => clauseSite pcpp coordinate i

/-- **The phase polynomial.**  The uniform average of the site polynomials over
the PCPP clause addresses. -/
noncomputable def phasePolynomial {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) :
    CircuitPolynomial Atom 4 :=
  CircuitPolynomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ))
    (polynomialFinsetSum (univ : Finset (Fin (2 ^ pcpp.clauseBits)))
      (sitePolynomial ph pcpp coordinate systematicAtom))

/-- **Every supplier request stays inside the four-factor ABI.**  This is a
property of the type -- the phase polynomial has degree four, which is the
paper's "degree at most four in the guessed sums" and its "AND-four supplier
calls". -/
theorem phasePolynomial_factors_length_le_four {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (monomial : CircuitMonomial Atom 4)
    (_hmonomial : monomial ∈
      (phasePolynomial ph pcpp coordinate systematicAtom).monomials) :
    monomial.factors.length ≤ 4 :=
  monomial.degree_le

theorem clauseSite_eq_clauseIndexPolynomial {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (slice : Fin (2 ^ pcpp.clauseBits) × Bool → CircuitPolynomial Atom 1)
    (i : Fin (2 ^ pcpp.clauseBits)) :
    clauseSite pcpp (occurrenceCoordinatePolynomial pcpp slice) i =
      (clauseIndexPolynomial pcpp slice i).weaken (by omega) := rfl

/-! ## §3 The per-site quantity, and the site value theorem -/

/-- The real quantity one site contributes, in the schedule's own language and
already divided by the schedule's `divisor`. -/
noncomputable def siteQuantity {n : ℕ} {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (input : BitInput n)
    (v : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (i : Fin (2 ^ pcpp.clauseBits)) : ℝ :=
  match ph with
  | .penalty =>
      (2 : ℝ)⁻¹ *
        (validityPenalty
            (systematicConstraint pcpp input
              (literalIndex (pcpp.clauses i).left))
            (v (literalIndex (pcpp.clauses i).left)) +
          validityPenalty
            (systematicConstraint pcpp input
              (literalIndex (pcpp.clauses i).right))
            (v (literalIndex (pcpp.clauses i).right)))
  | .moment => (v (literalIndex (pcpp.clauses i).left)) ^ 2
  | .clause => clauseRealValue (pcpp.clauses i) v

theorem coordinatePenalty_value {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (input : BitInput n)
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (coordinatePenalty pcpp coordinate systematicAtom j).value evaluate input =
      validityPenalty (systematicConstraint pcpp input j)
        (proofValue input j) := by
  refine Fin.addCases ?_ ?_ j
  · intro index
    simp [coordinatePenalty, systematicConstraint, hcoordinate input,
      hsystematic, validityPenalty, systematicPenalty]
  · intro index
    simp [coordinatePenalty, systematicConstraint, hcoordinate input,
      validityPenalty, booleanityPenalty]

/-- **One site, evaluated at one PCPP input, is the schedule's own per-site
quantity.** -/
theorem sitePolynomial_value {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (input : BitInput n) (i : Fin (2 ^ pcpp.clauseBits)) :
    (sitePolynomial ph pcpp coordinate systematicAtom i).value evaluate input =
      siteQuantity ph pcpp input (proofValue input) i := by
  cases ph with
  | penalty =>
      show (penaltySite pcpp coordinate systematicAtom i).value evaluate input = _
      rw [penaltySite, CircuitPolynomial.scale_value,
        CircuitPolynomial.add_value,
        coordinatePenalty_value pcpp evaluate proofValue coordinate hcoordinate
          systematicAtom hsystematic input,
        coordinatePenalty_value pcpp evaluate proofValue coordinate hcoordinate
          systematicAtom hsystematic input]
      show ((1 / 2 : ℚ) : ℝ) * _ = (2 : ℝ)⁻¹ * _
      norm_num
  | moment =>
      show (momentSite pcpp coordinate i).value evaluate input = _
      rw [momentSite, CircuitPolynomial.weaken_value,
        secondMomentPolynomial_value, hcoordinate input]
      rfl
  | clause =>
      show (clauseSite pcpp coordinate i).value evaluate input = _
      rw [clauseSite, CircuitPolynomial.weaken_value, clausePolynomial_value,
        hcoordinate input, hcoordinate input]
      rfl

/-- The phase polynomial at one PCPP input is the uniform average of its sites'
quantities. -/
theorem phasePolynomial_value {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (input : BitInput n) :
    (phasePolynomial ph pcpp coordinate systematicAtom).value evaluate input =
      𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
        siteQuantity ph pcpp input (proofValue input) i := by
  rw [phasePolynomial, CircuitPolynomial.scale_value,
    polynomialFinsetSum_value]
  rw [Finset.sum_congr rfl fun i _ =>
    sitePolynomial_value ph pcpp evaluate proofValue coordinate hcoordinate
      systematicAtom hsystematic input i]
  rw [Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-! ## §4 The exactness theorems -/

/-- The grouped phase mean is the double average of the per-site quantities.
This is `penalty_mean` / `moment_mean` / `clause_mean` unfolded once. -/
theorem mean_eq_expect {n : ℕ} {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    CloseoutRowsOriginalSchedule.mean ph pcpp proofValue =
      𝔼 input : BitInput n,
        𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
          siteQuantity ph pcpp input (proofValue input) i := by
  cases ph with
  | penalty =>
      rw [CloseoutRowsOriginalSchedule.penalty_mean, aggregateClausePenaltyMean]
      have hinner : ∀ input : BitInput n,
          (𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
              siteQuantity .penalty pcpp input (proofValue input) i) =
            (2 : ℝ)⁻¹ *
              totalClausePenaltyMean pcpp input (proofValue input) := by
        intro input
        show (𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
            (2 : ℝ)⁻¹ * (_ + _)) = _
        rw [← Finset.mul_expect, totalClausePenaltyMean, clausePenaltyMean,
          clausePenaltyMean, ← Finset.expect_add_distrib]
      rw [Finset.expect_congr rfl fun input _ => hinner input,
        ← Finset.mul_expect]
      ring
  | moment =>
      rw [CloseoutRowsOriginalSchedule.moment_mean,
        CompetitorSourceAverage.leftSecondMoment, ← Finset.univ_product_univ,
        Finset.expect_product]
      exact Finset.expect_congr rfl fun input _ =>
        Finset.expect_congr rfl fun i _ => rfl
  | clause =>
      rw [CloseoutRowsOriginalSchedule.clause_mean, aggregateClauseMean]
      exact Finset.expect_congr rfl fun input _ => rfl

/-- **THE EXACTNESS THEOREM (paper C.10).**  The grouped phase mean of the
paper's three estimated reals IS the exact mean of a degree-four circuit
polynomial: a finite sum of `coefficient * conjunctionProbability`, one
AND-four supplier call per monomial.  A pure identity -- there is no error
term. -/
theorem mean_eq_exactMean {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input) :
    CloseoutRowsOriginalSchedule.mean ph pcpp proofValue =
      (phasePolynomial ph pcpp coordinate systematicAtom).exactMean evaluate := by
  rw [CircuitPolynomial.exactMean_eq_uniformMean, CircuitPolynomial.uniformMean,
    mean_eq_expect ph pcpp proofValue]
  exact Finset.expect_congr rfl fun input _ =>
    (phasePolynomial_value ph pcpp evaluate proofValue coordinate hcoordinate
      systematicAtom hsystematic input).symm

/-- **The expansion, fully unfolded** -- literally the `hexpansion` field of
`Realizes`: a `Finset`-indexed sum of `coefficient * conjunctionProbability`,
with `index = univ` over the monomial positions. -/
theorem mean_eq_sum_conjunctionProbability {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input) :
    CloseoutRowsOriginalSchedule.mean ph pcpp proofValue =
      ∑ i : Fin (phasePolynomial ph pcpp coordinate
            systematicAtom).monomials.length,
        (((phasePolynomial ph pcpp coordinate
            systematicAtom).monomials[i].coefficient : ℚ) : ℝ) *
          conjunctionProbability evaluate
            (phasePolynomial ph pcpp coordinate
              systematicAtom).monomials[i].factors := by
  rw [mean_eq_exactMean ph pcpp evaluate proofValue coordinate hcoordinate
      systematicAtom hsystematic, CircuitPolynomial.exactMean]
  exact listSum_eq_finsetSum _ _

/-- **The site list the physical worker must range over.**  The grouped phase
mean is the uniform average, over the PCPP clause addresses
`i : Fin (2 ^ pcpp.clauseBits)` and over NOTHING ELSE, of the site
polynomials' exact means.  `BitInput n` is never enumerated: the `u`-average
sits inside `conjunctionProbability`, which is what one supplier call returns.
This is the paper's "no parity-support enumeration occurs". -/
theorem mean_eq_site_expect {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input) :
    CloseoutRowsOriginalSchedule.mean ph pcpp proofValue =
      𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
        (sitePolynomial ph pcpp coordinate systematicAtom i).exactMean
          evaluate := by
  rw [mean_eq_expect ph pcpp proofValue, Finset.expect_comm]
  refine Finset.expect_congr rfl fun i _ => ?_
  rw [CircuitPolynomial.exactMean_eq_uniformMean, CircuitPolynomial.uniformMean]
  exact Finset.expect_congr rfl fun input _ =>
    (sitePolynomial_value ph pcpp evaluate proofValue coordinate hcoordinate
      systematicAtom hsystematic input i).symm

end NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
