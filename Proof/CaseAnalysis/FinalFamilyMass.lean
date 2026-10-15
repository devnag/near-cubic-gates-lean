import Proof.CaseAnalysis.FinalExactnessFamily

namespace NearCubicWires.RepairSource.CloseoutFinal.C10FamilyMass

open Finset
open NearCubicWires
open NearCubicWires.AggregateClauseExpansion
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The bound -/

/-- One site's coefficient mass, per phase, in terms of the family's mass cap. -/
def siteMassBound (M : ℚ) : CloseoutRowsOriginalSchedule.Phase → ℚ
  | .penalty => (1 + M) ^ 2 * (1 + M ^ 2)
  | .moment => M ^ 2
  | .clause => (1 + M) ^ 2 + 2 * (1 + M)

/-- **The `mass` the consumer receives**: the site bound at the family's own
`coefficientMassCap`. -/
noncomputable def massBound (limits : LegalSumLimits)
    (phase : CloseoutRowsOriginalSchedule.Phase) : ℝ :=
  ((siteMassBound limits.coefficientMassCap phase : ℚ) : ℝ)

/-! ## §2 The decoded family's coordinate mass is the checked sum's mass -/

theorem foldl_add_eq_sum {α : Type} (f : α → ℚ) (values : List α) :
    ∀ init : ℚ, values.foldl (fun total x => total + f x) init = init + (values.map f).sum := by
  induction values with
  | nil => intro init; simp
  | cons x values inductionHypothesis =>
      intro init
      rw [List.foldl_cons, inductionHypothesis, List.map_cons, List.sum_cons]
      ring

theorem description_coefficientMass_eq {Circuit : CircuitFamily}
    (description : LegalCircuitSumDescription Circuit) :
    description.coefficientMass =
      (description.terms.map fun term => |term.coefficient|).sum := by
  unfold LegalCircuitSumDescription.coefficientMass
  rw [foldl_add_eq_sum, zero_add]

theorem transportTerms_abs_sum {Circuit : CircuitFamily} {source target : ℕ}
    (harity : source = target) (terms : List (LegalCircuitTerm Circuit source)) :
    ((transportTerms harity terms).map fun term => |term.coefficient|).sum =
      (terms.map fun term => |term.coefficient|).sum := by
  subst harity
  rfl

theorem familyCoordinate_coefficientMass_eq {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits} {variableCount target : ℕ}
    (harity : limits.expectedArity = target)
    (family : SumFamily Circuit wires description limits variableCount)
    (i : Fin variableCount) :
    (familyCoordinate harity family i).coefficientMass =
      (family.getSum i).value.coefficientMass := by
  unfold familyCoordinate
  rw [linearPolynomial_coefficientMass, transportTerms_abs_sum, description_coefficientMass_eq]

/-- `CheckedLegalCircuitSum.mass_le`, at the coordinate polynomial. -/
theorem familyCoordinate_coefficientMass_le_cap {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits} {variableCount target : ℕ}
    (harity : limits.expectedArity = target)
    (family : SumFamily Circuit wires description limits variableCount)
    (i : Fin variableCount) :
    (familyCoordinate harity family i).coefficientMass ≤ limits.coefficientMassCap := by
  rw [familyCoordinate_coefficientMass_eq]
  exact (family.getSum i).mass_le

/-! ## §3 One site -/

theorem coordinatePenalty_coefficientMass_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) {M : ℚ}
    (hM : ∀ j, (coordinate j).coefficientMass ≤ M)
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (coordinatePenalty pcpp coordinate systematicAtom j).coefficientMass ≤
      (1 + M) ^ 2 * (1 + M ^ 2) := by
  refine Fin.addCases ?_ ?_ j
  · intro index
    rw [coordinatePenalty, Fin.addCases_left, CircuitPolynomial.weaken_coefficientMass,
      systematicValidityPolynomial_coefficientMass]
    have h0 := coefficientMass_nonneg (coordinate (Fin.castAdd pcpp.auxiliaryBits index))
    have h1 := hM (Fin.castAdd pcpp.auxiliaryBits index)
    have hsq : (1 + (coordinate (Fin.castAdd pcpp.auxiliaryBits index)).coefficientMass) *
        (1 + (coordinate (Fin.castAdd pcpp.auxiliaryBits index)).coefficientMass) ≤
        (1 + M) * (1 + M) :=
      mul_self_le_mul_self (by linarith) (by linarith)
    nlinarith [hsq, mul_nonneg (sq_nonneg (1 + M)) (sq_nonneg M)]
  · intro index
    rw [coordinatePenalty, Fin.addCases_right, auxiliaryValidityPolynomial_coefficientMass]
    have h0 := coefficientMass_nonneg (coordinate (Fin.natAdd pcpp.systematicBits index))
    have h1 := hM (Fin.natAdd pcpp.systematicBits index)
    have hsq : (coordinate (Fin.natAdd pcpp.systematicBits index)).coefficientMass *
        (coordinate (Fin.natAdd pcpp.systematicBits index)).coefficientMass ≤ M * M :=
      mul_self_le_mul_self h0 h1
    have hsq' : (1 + (coordinate (Fin.natAdd pcpp.systematicBits index)).coefficientMass) *
        (1 + (coordinate (Fin.natAdd pcpp.systematicBits index)).coefficientMass) ≤
        (1 + M) * (1 + M) :=
      mul_self_le_mul_self (by linarith) (by linarith)
    have hprod := mul_le_mul hsq hsq' (mul_self_nonneg _) (mul_self_nonneg _)
    nlinarith [hprod, sq_nonneg (1 + M)]

theorem literalPolynomial_coefficientMass_bounds {Atom : Type} (negative : Bool)
    (linear : CircuitPolynomial Atom 1) {M : ℚ} (h : linear.coefficientMass ≤ M) :
    0 ≤ (literalPolynomial negative linear).coefficientMass ∧
      (literalPolynomial negative linear).coefficientMass ≤ 1 + M := by
  have h0 := coefficientMass_nonneg linear
  cases negative with
  | false =>
      rw [literalPolynomial_coefficientMass, if_neg Bool.false_ne_true]
      exact ⟨h0, by linarith⟩
  | true =>
      rw [literalPolynomial_coefficientMass, if_pos rfl]
      exact ⟨by linarith, by linarith⟩

theorem sitePolynomial_coefficientMass_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) {M : ℚ}
    (hM : ∀ j, (coordinate j).coefficientMass ≤ M)
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (sitePolynomial phase pcpp coordinate systematicAtom i).coefficientMass ≤
      siteMassBound M phase := by
  cases phase with
  | penalty =>
      show (penaltySite pcpp coordinate systematicAtom i).coefficientMass ≤
        (1 + M) ^ 2 * (1 + M ^ 2)
      rw [penaltySite, CircuitPolynomial.scale_coefficientMass,
        CircuitPolynomial.add_coefficientMass, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 2)]
      have key := coordinatePenalty_coefficientMass_le pcpp coordinate systematicAtom hM
      refine (mul_le_mul_of_nonneg_left (add_le_add (key _) (key _))
        (by norm_num : (0 : ℚ) ≤ 1 / 2)).trans ?_
      linarith
  | moment =>
      show (momentSite pcpp coordinate i).coefficientMass ≤ M ^ 2
      rw [momentSite, CircuitPolynomial.weaken_coefficientMass,
        secondMomentPolynomial_coefficientMass]
      have h0 := coefficientMass_nonneg (coordinate (literalIndex (pcpp.clauses i).left))
      have h1 := hM (literalIndex (pcpp.clauses i).left)
      have := mul_self_le_mul_self h0 h1
      nlinarith [this]
  | clause =>
      show (clauseSite pcpp coordinate i).coefficientMass ≤ (1 + M) ^ 2 + 2 * (1 + M)
      rw [clauseSite, CircuitPolynomial.weaken_coefficientMass,
        clausePolynomial_coefficientMass]
      obtain ⟨hl0, hl1⟩ := literalPolynomial_coefficientMass_bounds
        (literalNegated (pcpp.clauses i).left) (coordinate (literalIndex (pcpp.clauses i).left))
        (hM _)
      obtain ⟨hr0, hr1⟩ := literalPolynomial_coefficientMass_bounds
        (literalNegated (pcpp.clauses i).right) (coordinate (literalIndex (pcpp.clauses i).right))
        (hM _)
      have hprod := mul_le_mul hl1 hr1 hr0 (by linarith)
      nlinarith [hprod]

/-! ## §4 The phase polynomial: the average of the sites -/

theorem phasePolynomial_coefficientMass_le {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) {M : ℚ}
    (hM : ∀ j, (coordinate j).coefficientMass ≤ M) :
    (phasePolynomial phase pcpp coordinate systematicAtom).coefficientMass ≤
      siteMassBound M phase := by
  unfold phasePolynomial
  rw [CircuitPolynomial.scale_coefficientMass, polynomialFinsetSum_coefficientMass]
  have hsum : ∑ i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
      (sitePolynomial phase pcpp coordinate systematicAtom i).coefficientMass ≤
      ∑ _i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))), siteMassBound M phase :=
    Finset.sum_le_sum fun i _ =>
      sitePolynomial_coefficientMass_le phase pcpp coordinate systematicAtom hM i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hpos : (0 : ℚ) < 2 ^ pcpp.clauseBits := by positivity
  rw [abs_of_pos (by positivity : (0 : ℚ) < 1 / 2 ^ pcpp.clauseBits)]
  calc 1 / (2 ^ pcpp.clauseBits : ℚ) *
        ∑ i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
          (sitePolynomial phase pcpp coordinate systematicAtom i).coefficientMass
      ≤ 1 / (2 ^ pcpp.clauseBits : ℚ) * (((2 ^ pcpp.clauseBits : ℕ) : ℚ) * siteMassBound M phase) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = siteMassBound M phase := by
        push_cast
        rw [one_div, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]

/-! ## §5 `hmass` at the decoded family -/

/-- **`hmass`.**  At the decoded family the phase polynomial's coefficient mass
is at most `massBound limits phase`. -/
theorem familyCoordinate_coefficientMass_le {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits}
    {circuit : BooleanCircuit limits.expectedArity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (family :
      SumFamily Circuit wires description limits
        (pcpp.systematicBits + pcpp.auxiliaryBits))
    (systematicAtom : Fin pcpp.systematicBits → Circuit limits.expectedArity) :
    (((phasePolynomial phase pcpp (familyCoordinate rfl family) systematicAtom).coefficientMass :
      ℚ) : ℝ) ≤ massBound limits phase := by
  unfold massBound
  exact_mod_cast phasePolynomial_coefficientMass_le phase pcpp (familyCoordinate rfl family)
    systematicAtom (fun j => familyCoordinate_coefficientMass_le_cap rfl family j)

end NearCubicWires.RepairSource.CloseoutFinal.C10FamilyMass
