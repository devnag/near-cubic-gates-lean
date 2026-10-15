import Proof.CaseAnalysis.FinalExactness
import Proof.CaseAnalysis.WitnessFamily

/-!
# Constraint 18 — `CoordinateExpands` at `CloseoutWitness.SumFamily.value`

Paper C.10 (paper.tex:4104–4105): *"All expressions have degree at most four in
the **guessed sums**."*  The guessed sums are `CloseoutWitness.SumFamily`: one
rational linear combination of supplier circuits per PCPP variable.  P3a
(`RepairCloseoutFinalC10Exactness`) states its exactness theorems over the
generalized seam `CoordinateExpands pcpp evaluate proofValue coordinate` —
each recovered PCPP coordinate is ONE linear polynomial in supplier circuits.
This module discharges that seam at the honest family presentation, so P3a
composes with E1's `SumFamily` payload and not only with the occurrence slice.

Two obstacles, both closed here:

* **the arity cast.**  `SumFamily.value` evaluates each term at
  `fun j => u (Fin.cast (family.getSum i).arity_eq j)`, because a checked legal
  sum carries its own arity `value.q` together with
  `arity_eq : value.q = limits.expectedArity`, while `CoordinateExpands` wants a
  single `evaluate : Atom → BitInput n → Bool`.  `transportTerms` moves the term
  list along that equality and `transportTerms_value` shows the move is value
  preserving (`subst`, then `rfl`).
* **`variableCount` versus `pcpp.systematicBits + pcpp.auxiliaryBits`.**  Carried
  as an explicit `hvariables` and discharged by `Fin.cast`;
  `coordinateExpands_sumFamily_matched` is the cast-free instance, which is the
  spelling E1c will use.

No new constant, atom or codec is introduced: the coordinate polynomial is
literally `linearPolynomial` of the family's own transported term list.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The arity transport of a legal term list -/

/-- Move a legal term list along an arity equality.  This is the generic form of
the transport the decoded symmetric terms already use; it is stated at FREE
arities precisely so that `subst` can fire in `transportTerms_value`. -/
def transportTerms {Circuit : CircuitFamily} {source target : ℕ}
    (harity : source = target)
    (terms : List (LegalCircuitTerm Circuit source)) :
    List (LegalCircuitTerm Circuit target) :=
  harity ▸ terms

/-- The transport preserves the real value of the term list: evaluating the
transported circuits at `input` is evaluating the original circuits at `input`
pulled back along the same equality.  This is the arity obstacle, closed. -/
theorem transportTerms_value {Circuit : CircuitFamily} {source target : ℕ}
    (eval : {q : ℕ} → Circuit q → BitInput q → Bool)
    (harity : source = target)
    (terms : List (LegalCircuitTerm Circuit source))
    (input : BitInput target) :
    ((transportTerms harity terms).map fun term =>
        (term.coefficient : ℝ) * bitAsReal (eval term.circuit input)).sum =
      (terms.map fun term =>
        (term.coefficient : ℝ) *
          bitAsReal (eval term.circuit fun index =>
            input (Fin.cast harity index))).sum := by
  subst harity
  rfl

/-! ## §2 The coordinate polynomial of the guessed sums -/

/-- **The witness of constraint 18.**  The PCPP coordinate polynomial of the
guessed sums: variable `i`'s sum, transported to the PCPP arity and presented as
a `CircuitPolynomial _ 1`.  One monomial per term, one factor per monomial —
degree one, as the seam demands. -/
noncomputable def familyCoordinate {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits} {variableCount target : ℕ}
    (harity : limits.expectedArity = target)
    (family :
      CloseoutWitness.SumFamily Circuit wires description limits variableCount)
    (i : Fin variableCount) : CircuitPolynomial (Circuit target) 1 :=
  linearPolynomial
    (transportTerms ((family.getSum i).arity_eq.trans harity)
      (family.getSum i).value.terms)

/-- The coordinate polynomial's value IS the family's per-variable sum. -/
theorem familyCoordinate_value {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits} {variableCount target : ℕ}
    (eval : {q : ℕ} → Circuit q → BitInput q → Bool)
    (harity : limits.expectedArity = target)
    (family :
      CloseoutWitness.SumFamily Circuit wires description limits variableCount)
    (i : Fin variableCount) (input : BitInput target) :
    (familyCoordinate harity family i).value
        (fun circuit : Circuit target => eval circuit) input =
      CloseoutWitness.SumFamily.value eval family
        (fun index => input (Fin.cast harity index)) i := by
  rw [familyCoordinate, linearPolynomial_value, transportTerms_value]
  rfl

/-! ## §3 The seam -/

/-- **Constraint 18.**  `CloseoutWitness.SumFamily.value` meets P3a's
`CoordinateExpands` seam, at any arity and variable count that match the PCPP. -/
theorem coordinateExpands_sumFamily {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits} {variableCount n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (eval : {q : ℕ} → Circuit q → BitInput q → Bool)
    (harity : limits.expectedArity = n)
    (hvariables : variableCount = pcpp.systematicBits + pcpp.auxiliaryBits)
    (family :
      CloseoutWitness.SumFamily Circuit wires description limits variableCount) :
    CoordinateExpands pcpp (fun c : Circuit n => eval c)
      (fun input j =>
        CloseoutWitness.SumFamily.value eval family
          (fun index => input (Fin.cast harity index))
          (Fin.cast hvariables.symm j))
      (fun j => familyCoordinate harity family (Fin.cast hvariables.symm j)) :=
  fun input j =>
    familyCoordinate_value eval harity family (Fin.cast hvariables.symm j) input

/-- **Constraint 18, cast-free.**  At the matched indices — the family's arity is
the PCPP's own arity and it carries exactly one sum per PCPP coordinate — the
seam is met by `CloseoutWitness.SumFamily.value` on the nose.  This is the
spelling E1c instantiates. -/
theorem coordinateExpands_sumFamily_matched {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits}
    {circuit : BooleanCircuit limits.expectedArity}
    (pcpp : PointwisePCPP circuit)
    (eval : {q : ℕ} → Circuit q → BitInput q → Bool)
    (family :
      CloseoutWitness.SumFamily Circuit wires description limits
        (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    CoordinateExpands pcpp (fun c : Circuit limits.expectedArity => eval c)
      (CloseoutWitness.SumFamily.value eval family)
      (familyCoordinate rfl family) :=
  coordinateExpands_sumFamily pcpp eval rfl rfl family

/-! ## §4 P3a, instantiated at the guessed sums -/

/-- **The payoff.**  P3a's expansion theorem — the grouped phase mean IS a finite
sum of `coefficient * conjunctionProbability`, one AND-four supplier call per
monomial — now holds at the honest family's proof value, with no seam left over.
This is the P3a ↔ E1 join. -/
theorem mean_eq_sum_conjunctionProbability_sumFamily {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits}
    {circuit : BooleanCircuit limits.expectedArity}
    (ph : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (eval : {q : ℕ} → Circuit q → BitInput q → Bool)
    (family :
      CloseoutWitness.SumFamily Circuit wires description limits
        (pcpp.systematicBits + pcpp.auxiliaryBits))
    (systematicAtom : Fin pcpp.systematicBits → Circuit limits.expectedArity)
    (hsystematic : ∀ index input,
      eval (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input) :
    CloseoutRowsOriginalSchedule.mean ph pcpp
        (CloseoutWitness.SumFamily.value eval family) =
      ∑ i : Fin (phasePolynomial ph pcpp (familyCoordinate rfl family)
            systematicAtom).monomials.length,
        (((phasePolynomial ph pcpp (familyCoordinate rfl family)
            systematicAtom).monomials[i].coefficient : ℚ) : ℝ) *
          SupplierPipeline.conjunctionProbability
            (fun c : Circuit limits.expectedArity => eval c)
            (phasePolynomial ph pcpp (familyCoordinate rfl family)
              systematicAtom).monomials[i].factors :=
  mean_eq_sum_conjunctionProbability ph pcpp
    (fun c : Circuit limits.expectedArity => eval c)
    (CloseoutWitness.SumFamily.value eval family)
    (familyCoordinate rfl family)
    (coordinateExpands_sumFamily_matched pcpp eval family)
    systematicAtom hsystematic

end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
