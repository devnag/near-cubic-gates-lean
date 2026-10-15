import Proof.CaseAnalysis.FinalExactness

/-!
# P3b — C.10.2 stability: the propagated estimation error

Paper C.10.2 (paper.tex:4151): "Choose every propagated estimation error below
`eps_est := min{zeta, (c_p - s_p)/20}`", which is
`CompetitorRationalGap.estimationTolerance constants (zeta constants)`.

The propagation ledger is `failure * coefficientMass`: a supplier that answers
every AND-four call within `failure` moves the estimated phase mean by at most
`failure` times the expansion's coefficient mass.  `estimate_stable` below is
that bound stated against `CloseoutRowsOriginalSchedule.mean`, the paper's own
grouped quantity, so `failure * mass <= estimationTolerance` is exactly the
`hbudget` field of `Realizes`.

`phaseMassCap` is the coefficient-mass ledger of the three phases in terms of
the per-coordinate mass.  It is a DERIVED bound, not a free constant: every
term comes from a `coefficientMass` lemma of `ComponentwisePolynomial`
(`systematicValidityPolynomial`, `auxiliaryValidityPolynomial`,
`secondMomentPolynomial`, `clausePolynomial`), matching the manuscript's
`q^{rho_coef}` coefficient-mass envelope (paper.tex:1411).
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.AggregateClauseExpansion
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §0 `Finset` presentations of the two list-shaped ledgers -/

theorem ratListSum_cast (values : List ℚ) :
    ((values.sum : ℚ) : ℝ) = (values.map fun q => ((q : ℚ) : ℝ)).sum := by
  induction values with
  | nil => simp
  | cons value values inductionHypothesis => simp [inductionHypothesis]

/-- The coefficient mass, in the `Finset` shape `Realizes.hmass` is stated in. -/
theorem coefficientMass_eq_finsetSum {Atom : Type} {degree : ℕ}
    (polynomial : CircuitPolynomial Atom degree) :
    ∑ i : Fin polynomial.monomials.length,
        |((polynomial.monomials[i].coefficient : ℚ) : ℝ)| =
      ((polynomial.coefficientMass : ℚ) : ℝ) := by
  have hcast : ((polynomial.coefficientMass : ℚ) : ℝ) =
      (polynomial.monomials.map fun monomial =>
        |((monomial.coefficient : ℚ) : ℝ)|).sum := by
    rw [CircuitPolynomial.coefficientMass, ratListSum_cast, List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro monomial _
    simp
  rw [hcast, listSum_eq_finsetSum]

/-- The estimated mean, in the `Finset` shape `Realizes.hvaluesum` is stated
in. -/
theorem estimatedMean_eq_finsetSum {Atom : Type} {degree : ℕ}
    (estimate : List Atom → ℚ) (polynomial : CircuitPolynomial Atom degree) :
    polynomial.estimatedMean estimate =
      ∑ i : Fin polynomial.monomials.length,
        ((polynomial.monomials[i].coefficient : ℚ) : ℝ) *
          ((estimate polynomial.monomials[i].factors : ℚ) : ℝ) := by
  rw [CircuitPolynomial.estimatedMean]
  exact listSum_eq_finsetSum _ _

/-! ## §1 The coefficient-mass ledger of the three phases -/

/-- The per-coordinate validity mass: the systematic branch `(1+L)^2` plus the
auxiliary branch `L^2 + 2L^3 + L^4`, both at `L := mass`. -/
def coordinateMassCap (mass : ℚ) : ℚ :=
  (1 + mass) ^ 2 + (mass ^ 2 + 2 * mass ^ 3 + mass ^ 4)

/-- The coefficient mass of one grouped phase, from the per-coordinate mass. -/
def phaseMassCap (ph : CloseoutRowsOriginalSchedule.Phase) (mass : ℚ) : ℚ :=
  match ph with
  | .penalty => coordinateMassCap mass
  | .moment => mass ^ 2
  | .clause => (1 + mass) ^ 2 + 2 * (1 + mass)

theorem coordinatePenalty_coefficientMass_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (mass : ℚ)
    (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ j, (coordinate j).coefficientMass ≤ mass)
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (coordinatePenalty pcpp coordinate systematicAtom j).coefficientMass ≤
      coordinateMassCap mass := by
  refine Fin.addCases ?_ ?_ j
  · intro index
    have hnonneg :=
      coefficientMass_nonneg (coordinate (Fin.castAdd pcpp.auxiliaryBits index))
    have hle := hmass (Fin.castAdd pcpp.auxiliaryBits index)
    have hsquare : (coordinate (Fin.castAdd pcpp.auxiliaryBits index)).coefficientMass ^ 2 ≤
        mass ^ 2 := by nlinarith
    have htail : (0 : ℚ) ≤ mass ^ 2 + 2 * mass ^ 3 + mass ^ 4 := by positivity
    simp only [coordinatePenalty, Fin.addCases_left,
      CircuitPolynomial.weaken_coefficientMass,
      systematicValidityPolynomial_coefficientMass, coordinateMassCap]
    nlinarith
  · intro index
    have hnonneg :=
      coefficientMass_nonneg (coordinate (Fin.natAdd pcpp.systematicBits index))
    have hle := hmass (Fin.natAdd pcpp.systematicBits index)
    have h2 : (coordinate (Fin.natAdd pcpp.systematicBits index)).coefficientMass ^ 2 ≤
        mass ^ 2 := by nlinarith
    have h3 : (coordinate (Fin.natAdd pcpp.systematicBits index)).coefficientMass ^ 3 ≤
        mass ^ 3 := by nlinarith
    have h4 : (coordinate (Fin.natAdd pcpp.systematicBits index)).coefficientMass ^ 4 ≤
        mass ^ 4 := by nlinarith
    have hhead : (0 : ℚ) ≤ (1 + mass) ^ 2 := sq_nonneg _
    simp only [coordinatePenalty, Fin.addCases_right,
      auxiliaryValidityPolynomial_coefficientMass, coordinateMassCap]
    linarith

theorem sitePolynomial_coefficientMass_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (mass : ℚ)
    (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ j, (coordinate j).coefficientMass ≤ mass)
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (sitePolynomial ph pcpp coordinate systematicAtom i).coefficientMass ≤
      phaseMassCap ph mass := by
  cases ph with
  | penalty =>
      show (penaltySite pcpp coordinate systematicAtom i).coefficientMass ≤ _
      have hleft :=
        coordinatePenalty_coefficientMass_le pcpp coordinate systematicAtom mass
          hmassNonneg hmass (literalIndex (pcpp.clauses i).left)
      have hright :=
        coordinatePenalty_coefficientMass_le pcpp coordinate systematicAtom mass
          hmassNonneg hmass (literalIndex (pcpp.clauses i).right)
      simp only [penaltySite, CircuitPolynomial.scale_coefficientMass,
        CircuitPolynomial.add_coefficientMass, phaseMassCap]
      rw [show |(1 / 2 : ℚ)| = 1 / 2 from abs_of_nonneg (by norm_num)]
      linarith
  | moment =>
      show (momentSite pcpp coordinate i).coefficientMass ≤ _
      have hnonneg :=
        coefficientMass_nonneg (coordinate (literalIndex (pcpp.clauses i).left))
      have hle := hmass (literalIndex (pcpp.clauses i).left)
      simp only [momentSite, CircuitPolynomial.weaken_coefficientMass,
        secondMomentPolynomial_coefficientMass, phaseMassCap]
      nlinarith [hnonneg, hle, hmassNonneg]
  | clause =>
      show (clauseSite pcpp coordinate i).coefficientMass ≤ _
      have hside : ∀ (negative : Bool)
          (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)),
          (literalPolynomial negative (coordinate j)).coefficientMass ≤
            1 + mass := by
        intro negative j
        have hnonneg := coefficientMass_nonneg (coordinate j)
        have hle := hmass j
        cases negative with
        | false => simpa using by linarith
        | true => simpa using by linarith
      have hleft :=
        hside (literalNegated (pcpp.clauses i).left)
          (literalIndex (pcpp.clauses i).left)
      have hright :=
        hside (literalNegated (pcpp.clauses i).right)
          (literalIndex (pcpp.clauses i).right)
      have hleftNonneg :
          (0 : ℚ) ≤ (literalPolynomial (literalNegated (pcpp.clauses i).left)
            (coordinate (literalIndex (pcpp.clauses i).left))).coefficientMass :=
        coefficientMass_nonneg _
      have hrightNonneg :
          (0 : ℚ) ≤ (literalPolynomial (literalNegated (pcpp.clauses i).right)
            (coordinate (literalIndex (pcpp.clauses i).right))).coefficientMass :=
        coefficientMass_nonneg _
      simp only [clauseSite, CircuitPolynomial.weaken_coefficientMass,
        clausePolynomial_coefficientMass, phaseMassCap]
      nlinarith

/-- **The coefficient-mass ledger.**  The whole phase expansion has coefficient
mass at most `phaseMassCap ph mass`, from the per-coordinate mass alone. -/
theorem phasePolynomial_coefficientMass_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (mass : ℚ)
    (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ j, (coordinate j).coefficientMass ≤ mass) :
    (phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass ≤
      phaseMassCap ph mass := by
  classical
  rw [phasePolynomial, CircuitPolynomial.scale_coefficientMass,
    polynomialFinsetSum_coefficientMass]
  have hpositive : (0 : ℚ) < (2 ^ pcpp.clauseBits : ℚ) := by positivity
  have habs : |1 / (2 ^ pcpp.clauseBits : ℚ)| = 1 / (2 ^ pcpp.clauseBits : ℚ) :=
    abs_of_nonneg (by positivity)
  have hbound :
      (∑ i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
          (sitePolynomial ph pcpp coordinate systematicAtom i).coefficientMass) ≤
        (2 ^ pcpp.clauseBits : ℚ) * phaseMassCap ph mass := by
    calc
      (∑ i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
          (sitePolynomial ph pcpp coordinate systematicAtom i).coefficientMass) ≤
          ∑ _i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
            phaseMassCap ph mass :=
        Finset.sum_le_sum fun i _ =>
          sitePolynomial_coefficientMass_le ph pcpp coordinate systematicAtom
            mass hmassNonneg hmass i
      _ = (2 ^ pcpp.clauseBits : ℚ) * phaseMassCap ph mass := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        push_cast
        ring
  rw [habs, div_mul_eq_mul_div, one_mul, div_le_iff₀ hpositive]
  calc
    (∑ i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
        (sitePolynomial ph pcpp coordinate systematicAtom i).coefficientMass) ≤
        (2 ^ pcpp.clauseBits : ℚ) * phaseMassCap ph mass := hbound
    _ = phaseMassCap ph mass * (2 ^ pcpp.clauseBits : ℚ) := by ring

/-! ## §2 The propagated estimation error -/

/-- **THE STABILITY THEOREM (paper C.10.2).**  A supplier answering every
AND-four call within `failure` computes the grouped phase mean within
`failure * mass`.  With `failure * mass <= estimationTolerance constants
(zeta constants)`, this is exactly "every propagated estimation error below
`eps_est`". -/
theorem estimate_stable {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
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
    (estimate : List Atom → ℚ) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |((estimate circuits : ℚ) : ℝ) -
        conjunctionProbability evaluate circuits| ≤ failure)
    (mass : ℝ)
    (hmass :
      (((phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass :
        ℚ) : ℝ) ≤ mass) :
    |(phasePolynomial ph pcpp coordinate systematicAtom).estimatedMean estimate -
        CloseoutRowsOriginalSchedule.mean ph pcpp proofValue| ≤
      failure * mass := by
  rw [mean_eq_exactMean ph pcpp evaluate proofValue coordinate hcoordinate
    systematicAtom hsystematic]
  calc
    |(phasePolynomial ph pcpp coordinate systematicAtom).estimatedMean estimate -
        (phasePolynomial ph pcpp coordinate systematicAtom).exactMean evaluate| ≤
        failure *
          (((phasePolynomial ph pcpp coordinate
            systematicAtom).coefficientMass : ℚ) : ℝ) :=
      estimatedMean_error_le evaluate estimate
        (phasePolynomial ph pcpp coordinate systematicAtom) failure
        (fun monomial _ => hpoint monomial.factors)
    _ ≤ failure * mass := mul_le_mul_of_nonneg_left hmass hfailure

/-- The stability theorem at the derived coefficient-mass ledger: the only
inputs are the supplier's per-call accuracy and the per-coordinate mass. -/
theorem estimate_stable_of_coordinateMass {Atom : Type} {n : ℕ}
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
    (estimate : List Atom → ℚ) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |((estimate circuits : ℚ) : ℝ) -
        conjunctionProbability evaluate circuits| ≤ failure)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ j, (coordinate j).coefficientMass ≤ mass) :
    |(phasePolynomial ph pcpp coordinate systematicAtom).estimatedMean estimate -
        CloseoutRowsOriginalSchedule.mean ph pcpp proofValue| ≤
      failure * ((phaseMassCap ph mass : ℚ) : ℝ) := by
  refine estimate_stable ph pcpp evaluate proofValue coordinate hcoordinate
    systematicAtom hsystematic estimate failure hfailure hpoint _ ?_
  exact_mod_cast
    phasePolynomial_coefficientMass_le ph pcpp coordinate systematicAtom mass
      hmassNonneg hmass

end NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability
