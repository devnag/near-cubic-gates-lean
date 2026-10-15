import Proof.Circuits.CanonicalWitnessCodec
import Proof.Foundations.ComponentwiseTransfer
import Proof.Foundations.ComponentwiseValidity

/-!
# Canonical degree-four verifier polynomials

The componentwise verifier reduces every validity, second-moment, and clause
test to one occurrence-sensitive list of monomials.  A monomial carries at
most four normalized atoms, so its expectation is exactly one Fourfold
supplier request.  Keeping coefficients and factor occurrences in lists
prevents an optimizer from silently merging calls or changing the error mass.
-/

open scoped BigOperators

namespace NearCubicWires.ComponentwisePolynomial

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.SupplierPipeline

structure CircuitMonomial (Circuit : Type) (degree : ℕ) where
  coefficient : ℚ
  factors : List Circuit
  degree_le : factors.length ≤ degree

structure CircuitPolynomial (Circuit : Type) (degree : ℕ) where
  monomials : List (CircuitMonomial Circuit degree)

def CircuitMonomial.value
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (monomial : CircuitMonomial Circuit degree)
    (input : BitInput q) : ℝ :=
  (monomial.coefficient : ℝ) *
    bitAsReal (conjunctionBit evaluate monomial.factors input)

def CircuitPolynomial.value
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (polynomial : CircuitPolynomial Circuit degree)
    (input : BitInput q) : ℝ :=
  (polynomial.monomials.map fun monomial =>
    monomial.value evaluate input).sum

def CircuitPolynomial.coefficientMass
    {Circuit : Type} {degree : ℕ}
    (polynomial : CircuitPolynomial Circuit degree) : ℚ :=
  (polynomial.monomials.map fun monomial => |monomial.coefficient|).sum

def CircuitMonomial.weaken
    {Circuit : Type} {sourceDegree targetDegree : ℕ}
    (hdegree : sourceDegree ≤ targetDegree)
    (monomial : CircuitMonomial Circuit sourceDegree) :
    CircuitMonomial Circuit targetDegree where
  coefficient := monomial.coefficient
  factors := monomial.factors
  degree_le := monomial.degree_le.trans hdegree

def CircuitPolynomial.weaken
    {Circuit : Type} {sourceDegree targetDegree : ℕ}
    (hdegree : sourceDegree ≤ targetDegree)
    (polynomial : CircuitPolynomial Circuit sourceDegree) :
    CircuitPolynomial Circuit targetDegree where
  monomials := polynomial.monomials.map (CircuitMonomial.weaken hdegree)

@[simp] theorem CircuitMonomial.weaken_value
    {Circuit : Type} {sourceDegree targetDegree q : ℕ}
    (hdegree : sourceDegree ≤ targetDegree)
    (evaluate : Circuit → BitInput q → Bool)
    (monomial : CircuitMonomial Circuit sourceDegree)
    (input : BitInput q) :
    (monomial.weaken hdegree).value evaluate input =
      monomial.value evaluate input := rfl

@[simp] theorem CircuitPolynomial.weaken_value
    {Circuit : Type} {sourceDegree targetDegree q : ℕ}
    (hdegree : sourceDegree ≤ targetDegree)
    (evaluate : Circuit → BitInput q → Bool)
    (polynomial : CircuitPolynomial Circuit sourceDegree)
    (input : BitInput q) :
    (polynomial.weaken hdegree).value evaluate input =
      polynomial.value evaluate input := by
  unfold CircuitPolynomial.weaken CircuitPolynomial.value
  rw [List.map_map]
  change
    (polynomial.monomials.map fun monomial =>
      (monomial.weaken hdegree).value evaluate input).sum =
      (polynomial.monomials.map fun monomial =>
        monomial.value evaluate input).sum
  induction polynomial.monomials with
  | nil => rfl
  | cons monomial monomials inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [CircuitMonomial.weaken_value, inductionHypothesis]

@[simp] theorem CircuitPolynomial.weaken_coefficientMass
    {Circuit : Type} {sourceDegree targetDegree : ℕ}
    (hdegree : sourceDegree ≤ targetDegree)
    (polynomial : CircuitPolynomial Circuit sourceDegree) :
    (polynomial.weaken hdegree).coefficientMass =
      polynomial.coefficientMass := by
  unfold CircuitPolynomial.weaken CircuitPolynomial.coefficientMass
  rw [List.map_map]
  change
    (polynomial.monomials.map fun monomial =>
      |(monomial.weaken hdegree).coefficient|).sum =
      (polynomial.monomials.map fun monomial =>
        |monomial.coefficient|).sum
  induction polynomial.monomials with
  | nil => rfl
  | cons monomial monomials inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [show (monomial.weaken hdegree).coefficient =
          monomial.coefficient by rfl, inductionHypothesis]

def CircuitPolynomial.constant
    {Circuit : Type} (degree : ℕ) (coefficient : ℚ) :
    CircuitPolynomial Circuit degree where
  monomials :=
    [{ coefficient := coefficient
       factors := []
       degree_le := by simp }]

@[simp] theorem CircuitPolynomial.constant_value
    {Circuit : Type} {q : ℕ}
    (degree : ℕ) (coefficient : ℚ)
    (evaluate : Circuit → BitInput q → Bool) (input : BitInput q) :
    (CircuitPolynomial.constant (Circuit := Circuit) degree coefficient).value
        evaluate input =
      (coefficient : ℝ) := by
  simp [CircuitPolynomial.constant, CircuitPolynomial.value,
    CircuitMonomial.value, conjunctionBit, bitAsReal]

@[simp] theorem CircuitPolynomial.constant_coefficientMass
    {Circuit : Type} (degree : ℕ) (coefficient : ℚ) :
    CircuitPolynomial.coefficientMass
        (CircuitPolynomial.constant (Circuit := Circuit) degree coefficient) =
      |coefficient| := by
  simp [CircuitPolynomial.constant, CircuitPolynomial.coefficientMass]

def CircuitPolynomial.add
    {Circuit : Type} {degree : ℕ}
    (left right : CircuitPolynomial Circuit degree) :
    CircuitPolynomial Circuit degree where
  monomials := left.monomials ++ right.monomials

@[simp] theorem CircuitPolynomial.add_value
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (left right : CircuitPolynomial Circuit degree)
    (input : BitInput q) :
    (left.add right).value evaluate input =
      left.value evaluate input + right.value evaluate input := by
  simp [CircuitPolynomial.add, CircuitPolynomial.value]

@[simp] theorem CircuitPolynomial.add_coefficientMass
    {Circuit : Type} {degree : ℕ}
    (left right : CircuitPolynomial Circuit degree) :
    (left.add right).coefficientMass =
      left.coefficientMass + right.coefficientMass := by
  simp [CircuitPolynomial.add, CircuitPolynomial.coefficientMass]

def CircuitMonomial.scale
    {Circuit : Type} {degree : ℕ} (scalar : ℚ)
    (monomial : CircuitMonomial Circuit degree) :
    CircuitMonomial Circuit degree where
  coefficient := scalar * monomial.coefficient
  factors := monomial.factors
  degree_le := monomial.degree_le

def CircuitPolynomial.scale
    {Circuit : Type} {degree : ℕ} (scalar : ℚ)
    (polynomial : CircuitPolynomial Circuit degree) :
    CircuitPolynomial Circuit degree where
  monomials := polynomial.monomials.map (CircuitMonomial.scale scalar)

@[simp] theorem CircuitMonomial.scale_value
    {Circuit : Type} {degree q : ℕ}
    (scalar : ℚ) (evaluate : Circuit → BitInput q → Bool)
    (monomial : CircuitMonomial Circuit degree)
    (input : BitInput q) :
    (monomial.scale scalar).value evaluate input =
      (scalar : ℝ) * monomial.value evaluate input := by
  simp [CircuitMonomial.scale, CircuitMonomial.value]
  ring

@[simp] theorem CircuitPolynomial.scale_value
    {Circuit : Type} {degree q : ℕ}
    (scalar : ℚ) (evaluate : Circuit → BitInput q → Bool)
    (polynomial : CircuitPolynomial Circuit degree)
    (input : BitInput q) :
    (polynomial.scale scalar).value evaluate input =
      (scalar : ℝ) * polynomial.value evaluate input := by
  unfold CircuitPolynomial.scale CircuitPolynomial.value
  rw [List.map_map]
  change
    (polynomial.monomials.map fun monomial =>
      (monomial.scale scalar).value evaluate input).sum =
      (scalar : ℝ) *
        (polynomial.monomials.map fun monomial =>
          monomial.value evaluate input).sum
  induction polynomial.monomials with
  | nil => simp
  | cons monomial monomials inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [CircuitMonomial.scale_value, inductionHypothesis, mul_add]

@[simp] theorem CircuitMonomial.scale_coefficient_abs
    {Circuit : Type} {degree : ℕ}
    (scalar : ℚ) (monomial : CircuitMonomial Circuit degree) :
    |(monomial.scale scalar).coefficient| =
      |scalar| * |monomial.coefficient| := by
  simp [CircuitMonomial.scale, abs_mul]

@[simp] theorem CircuitPolynomial.scale_coefficientMass
    {Circuit : Type} {degree : ℕ}
    (scalar : ℚ) (polynomial : CircuitPolynomial Circuit degree) :
    (polynomial.scale scalar).coefficientMass =
      |scalar| * polynomial.coefficientMass := by
  unfold CircuitPolynomial.scale CircuitPolynomial.coefficientMass
  rw [List.map_map]
  change
    (polynomial.monomials.map fun monomial =>
      |(monomial.scale scalar).coefficient|).sum =
      |scalar| *
        (polynomial.monomials.map fun monomial =>
          |monomial.coefficient|).sum
  induction polynomial.monomials with
  | nil => simp
  | cons monomial monomials inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [CircuitMonomial.scale_coefficient_abs,
        inductionHypothesis, mul_add]

def CircuitMonomial.mul
    {Circuit : Type} {leftDegree rightDegree : ℕ}
    (left : CircuitMonomial Circuit leftDegree)
    (right : CircuitMonomial Circuit rightDegree) :
    CircuitMonomial Circuit (leftDegree + rightDegree) where
  coefficient := left.coefficient * right.coefficient
  factors := left.factors ++ right.factors
  degree_le := by
    simp only [List.length_append]
    exact Nat.add_le_add left.degree_le right.degree_le

theorem CircuitMonomial.mul_value
    {Circuit : Type} {leftDegree rightDegree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (left : CircuitMonomial Circuit leftDegree)
    (right : CircuitMonomial Circuit rightDegree)
    (input : BitInput q) :
    (left.mul right).value evaluate input =
      left.value evaluate input * right.value evaluate input := by
  unfold CircuitMonomial.mul CircuitMonomial.value conjunctionBit
  simp only [List.all_append]
  cases left.factors.all fun circuit => evaluate circuit input <;>
    cases right.factors.all fun circuit => evaluate circuit input <;>
      simp [bitAsReal]

def CircuitPolynomial.mul
    {Circuit : Type} {leftDegree rightDegree : ℕ}
    (left : CircuitPolynomial Circuit leftDegree)
    (right : CircuitPolynomial Circuit rightDegree) :
    CircuitPolynomial Circuit (leftDegree + rightDegree) where
  monomials :=
    left.monomials.flatMap fun leftMonomial =>
      right.monomials.map leftMonomial.mul

private theorem sum_mul_monomial_values
    {Circuit : Type} {leftDegree rightDegree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (left : CircuitMonomial Circuit leftDegree)
    (right : List (CircuitMonomial Circuit rightDegree))
    (input : BitInput q) :
    (right.map fun candidate =>
        (left.mul candidate).value evaluate input).sum =
      left.value evaluate input *
        (right.map fun candidate => candidate.value evaluate input).sum := by
  induction right with
  | nil => simp
  | cons monomial monomials inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [CircuitMonomial.mul_value, inductionHypothesis, mul_add]

@[simp] theorem CircuitPolynomial.mul_value
    {Circuit : Type} {leftDegree rightDegree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (left : CircuitPolynomial Circuit leftDegree)
    (right : CircuitPolynomial Circuit rightDegree)
    (input : BitInput q) :
    (left.mul right).value evaluate input =
      left.value evaluate input * right.value evaluate input := by
  unfold CircuitPolynomial.mul CircuitPolynomial.value
  induction left.monomials with
  | nil => simp
  | cons monomial monomials inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
      have hhead :
          (right.monomials.map
            ((fun candidate => candidate.value evaluate input) ∘
              monomial.mul)).sum =
            monomial.value evaluate input *
              (right.monomials.map fun candidate =>
                candidate.value evaluate input).sum := by
        rw [show
          ((fun candidate => candidate.value evaluate input) ∘
              monomial.mul) =
            (fun candidate =>
              (monomial.mul candidate).value evaluate input) by
          funext candidate
          rfl]
        exact sum_mul_monomial_values evaluate monomial
          right.monomials input
      have htail :
          ((monomials.flatMap fun leftMonomial =>
              right.monomials.map leftMonomial.mul).map fun candidate =>
                candidate.value evaluate input).sum =
            (monomials.map fun candidate =>
              candidate.value evaluate input).sum *
              (right.monomials.map fun candidate =>
                candidate.value evaluate input).sum := by
        simpa using inductionHypothesis
      simp only [List.map_map, List.map_cons,
        List.sum_cons, hhead, htail, add_mul]

private theorem sum_abs_mul_coefficients
    {Circuit : Type} {leftDegree rightDegree : ℕ}
    (left : CircuitMonomial Circuit leftDegree)
    (right : List (CircuitMonomial Circuit rightDegree)) :
    (right.map fun candidate =>
        |(left.mul candidate).coefficient|).sum =
      |left.coefficient| *
        (right.map fun candidate => |candidate.coefficient|).sum := by
  induction right with
  | nil => simp
  | cons monomial monomials inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [show |(left.mul monomial).coefficient| =
          |left.coefficient| * |monomial.coefficient| by
        simp [CircuitMonomial.mul, abs_mul]]
      rw [inductionHypothesis, mul_add]

@[simp] theorem CircuitPolynomial.mul_coefficientMass
    {Circuit : Type} {leftDegree rightDegree : ℕ}
    (left : CircuitPolynomial Circuit leftDegree)
    (right : CircuitPolynomial Circuit rightDegree) :
    (left.mul right).coefficientMass =
      left.coefficientMass * right.coefficientMass := by
  unfold CircuitPolynomial.mul CircuitPolynomial.coefficientMass
  induction left.monomials with
  | nil => simp
  | cons monomial monomials inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
      have hhead :
          (right.monomials.map
            ((fun candidate => |candidate.coefficient|) ∘
              monomial.mul)).sum =
            |monomial.coefficient| *
              (right.monomials.map fun candidate =>
                |candidate.coefficient|).sum := by
        rw [show
          ((fun candidate => |candidate.coefficient|) ∘
              monomial.mul) =
            (fun candidate => |(monomial.mul candidate).coefficient|) by
          funext candidate
          rfl]
        exact sum_abs_mul_coefficients monomial right.monomials
      have htail :
          ((monomials.flatMap fun leftMonomial =>
              right.monomials.map leftMonomial.mul).map fun candidate =>
                |candidate.coefficient|).sum =
            (monomials.map fun candidate => |candidate.coefficient|).sum *
              (right.monomials.map fun candidate =>
                |candidate.coefficient|).sum := by
        simpa using inductionHypothesis
      simp only [List.map_map, List.map_cons,
        List.sum_cons, hhead, htail, add_mul]

def linearPolynomial
    {Circuit : CanonicalWitnessCodec.CircuitFamily} {q : ℕ}
    (terms : List (LegalCircuitTerm Circuit q)) :
    CircuitPolynomial (Circuit q) 1 where
  monomials := terms.map fun term =>
    { coefficient := term.coefficient
      factors := [term.circuit]
      degree_le := by simp }

@[simp] theorem linearPolynomial_value
    {Circuit : CanonicalWitnessCodec.CircuitFamily} {q : ℕ}
    (evaluate : Circuit q → BitInput q → Bool)
    (terms : List (LegalCircuitTerm Circuit q))
    (input : BitInput q) :
    (linearPolynomial terms).value evaluate input =
      (terms.map fun term =>
        (term.coefficient : ℝ) * bitAsReal (evaluate term.circuit input)).sum := by
  unfold linearPolynomial CircuitPolynomial.value
  rw [List.map_map]
  change
    (terms.map fun term =>
      (term.coefficient : ℝ) *
        bitAsReal ([term.circuit].all fun circuit =>
          evaluate circuit input)).sum =
      (terms.map fun term =>
        (term.coefficient : ℝ) *
          bitAsReal (evaluate term.circuit input)).sum
  induction terms with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.all_cons,
        List.all_nil, Bool.and_true]

@[simp] theorem linearPolynomial_coefficientMass
    {Circuit : CanonicalWitnessCodec.CircuitFamily} {q : ℕ}
    (terms : List (LegalCircuitTerm Circuit q)) :
    (linearPolynomial terms).coefficientMass =
      (terms.map fun term => |term.coefficient|).sum := by
  unfold linearPolynomial CircuitPolynomial.coefficientMass
  rw [List.map_map]
  change
    (terms.map fun term => |term.coefficient|).sum =
      (terms.map fun term => |term.coefficient|).sum
  rfl

def auxiliaryValidityPolynomial
    {Circuit : Type} (linear : CircuitPolynomial Circuit 1) :
    CircuitPolynomial Circuit 4 :=
  let square := linear.mul linear
  let cube := square.mul linear
  let fourth := square.mul square
  (square.weaken (by omega)).add <|
    (cube.weaken (by omega)).scale (-2) |>.add fourth

@[simp] theorem auxiliaryValidityPolynomial_value
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (linear : CircuitPolynomial Circuit 1) (input : BitInput q) :
    (auxiliaryValidityPolynomial linear).value evaluate input =
      (linear.value evaluate input) ^ 2 *
        (1 - linear.value evaluate input) ^ 2 := by
  simp [auxiliaryValidityPolynomial]
  ring

@[simp] theorem auxiliaryValidityPolynomial_coefficientMass
    {Circuit : Type} (linear : CircuitPolynomial Circuit 1) :
    (auxiliaryValidityPolynomial linear).coefficientMass =
      linear.coefficientMass ^ 2 +
        2 * linear.coefficientMass ^ 3 +
        linear.coefficientMass ^ 4 := by
  simp [auxiliaryValidityPolynomial]
  ring

def atomPolynomial {Circuit : Type} (circuit : Circuit) :
    CircuitPolynomial Circuit 1 where
  monomials :=
    [{ coefficient := 1
       factors := [circuit]
       degree_le := by simp }]

@[simp] theorem atomPolynomial_value
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (circuit : Circuit) (input : BitInput q) :
    (atomPolynomial circuit).value evaluate input =
      bitAsReal (evaluate circuit input) := by
  simp [atomPolynomial, CircuitPolynomial.value, CircuitMonomial.value,
    conjunctionBit]

@[simp] theorem atomPolynomial_coefficientMass
    {Circuit : Type} (circuit : Circuit) :
    (atomPolynomial circuit).coefficientMass = 1 := by
  simp [atomPolynomial, CircuitPolynomial.coefficientMass]

def CircuitPolynomial.FactorsSatisfy
    {Circuit : Type} {degree : ℕ}
    (polynomial : CircuitPolynomial Circuit degree)
    (predicate : Circuit → Prop) : Prop :=
  ∀ monomial ∈ polynomial.monomials,
    ∀ circuit ∈ monomial.factors, predicate circuit

theorem CircuitPolynomial.constant_factorsSatisfy
    {Circuit : Type} (degree : ℕ) (coefficient : ℚ)
    (predicate : Circuit → Prop) :
    (CircuitPolynomial.constant degree coefficient).FactorsSatisfy predicate := by
  simp [CircuitPolynomial.FactorsSatisfy, CircuitPolynomial.constant]

theorem CircuitPolynomial.weaken_factorsSatisfy
    {Circuit : Type} {sourceDegree targetDegree : ℕ}
    (hdegree : sourceDegree ≤ targetDegree)
    (polynomial : CircuitPolynomial Circuit sourceDegree)
    (predicate : Circuit → Prop)
    (hsatisfies : polynomial.FactorsSatisfy predicate) :
    (polynomial.weaken hdegree).FactorsSatisfy predicate := by
  intro monomial hmonomial circuit hcircuit
  rcases List.mem_map.mp hmonomial with
    ⟨source, hsource, rfl⟩
  exact hsatisfies source hsource circuit hcircuit

theorem CircuitPolynomial.add_factorsSatisfy
    {Circuit : Type} {degree : ℕ}
    (left right : CircuitPolynomial Circuit degree)
    (predicate : Circuit → Prop)
    (hleft : left.FactorsSatisfy predicate)
    (hright : right.FactorsSatisfy predicate) :
    (left.add right).FactorsSatisfy predicate := by
  intro monomial hmonomial circuit hcircuit
  rcases List.mem_append.mp hmonomial with hmonomial | hmonomial
  · exact hleft monomial hmonomial circuit hcircuit
  · exact hright monomial hmonomial circuit hcircuit

theorem CircuitPolynomial.scale_factorsSatisfy
    {Circuit : Type} {degree : ℕ}
    (scalar : ℚ) (polynomial : CircuitPolynomial Circuit degree)
    (predicate : Circuit → Prop)
    (hsatisfies : polynomial.FactorsSatisfy predicate) :
    (polynomial.scale scalar).FactorsSatisfy predicate := by
  intro monomial hmonomial circuit hcircuit
  rcases List.mem_map.mp hmonomial with
    ⟨source, hsource, rfl⟩
  exact hsatisfies source hsource circuit hcircuit

theorem CircuitPolynomial.mul_factorsSatisfy
    {Circuit : Type} {leftDegree rightDegree : ℕ}
    (left : CircuitPolynomial Circuit leftDegree)
    (right : CircuitPolynomial Circuit rightDegree)
    (predicate : Circuit → Prop)
    (hleft : left.FactorsSatisfy predicate)
    (hright : right.FactorsSatisfy predicate) :
    (left.mul right).FactorsSatisfy predicate := by
  intro monomial hmonomial circuit hcircuit
  rcases List.mem_flatMap.mp hmonomial with
    ⟨leftMonomial, hleftMonomial, hmonomial⟩
  rcases List.mem_map.mp hmonomial with
    ⟨rightMonomial, hrightMonomial, rfl⟩
  rcases List.mem_append.mp hcircuit with hcircuit | hcircuit
  · exact hleft leftMonomial hleftMonomial circuit hcircuit
  · exact hright rightMonomial hrightMonomial circuit hcircuit

theorem linearPolynomial_factorsSatisfy
    {Circuit : CanonicalWitnessCodec.CircuitFamily} {q : ℕ}
    (terms : List (LegalCircuitTerm Circuit q))
    (predicate : Circuit q → Prop)
    (hterms : ∀ term ∈ terms, predicate term.circuit) :
    (linearPolynomial terms).FactorsSatisfy predicate := by
  intro monomial hmonomial circuit hcircuit
  rcases List.mem_map.mp hmonomial with ⟨term, hterm, rfl⟩
  simp only [List.mem_singleton] at hcircuit
  simpa [hcircuit] using hterms term hterm

theorem atomPolynomial_factorsSatisfy
    {Circuit : Type} (circuit : Circuit) (predicate : Circuit → Prop)
    (hcircuit : predicate circuit) :
    (atomPolynomial circuit).FactorsSatisfy predicate := by
  simpa [CircuitPolynomial.FactorsSatisfy, atomPolynomial] using hcircuit

theorem auxiliaryValidityPolynomial_factorsSatisfy
    {Circuit : Type} (linear : CircuitPolynomial Circuit 1)
    (predicate : Circuit → Prop)
    (hlinear : linear.FactorsSatisfy predicate) :
    (auxiliaryValidityPolynomial linear).FactorsSatisfy predicate := by
  unfold auxiliaryValidityPolynomial
  apply CircuitPolynomial.add_factorsSatisfy
  · exact CircuitPolynomial.weaken_factorsSatisfy _ _ _ <|
      CircuitPolynomial.mul_factorsSatisfy linear linear predicate
        hlinear hlinear
  · apply CircuitPolynomial.add_factorsSatisfy
    · apply CircuitPolynomial.scale_factorsSatisfy
      exact CircuitPolynomial.weaken_factorsSatisfy _ _ _ <|
        CircuitPolynomial.mul_factorsSatisfy (linear.mul linear) linear
          predicate
          (CircuitPolynomial.mul_factorsSatisfy linear linear predicate
            hlinear hlinear)
          hlinear
    · exact CircuitPolynomial.mul_factorsSatisfy
        (linear.mul linear) (linear.mul linear) predicate
        (CircuitPolynomial.mul_factorsSatisfy linear linear predicate
          hlinear hlinear)
        (CircuitPolynomial.mul_factorsSatisfy linear linear predicate
          hlinear hlinear)

def systematicValidityPolynomial
    {Circuit : Type} (systematic : Circuit)
    (linear : CircuitPolynomial Circuit 1) :
    CircuitPolynomial Circuit 2 :=
  let encoded := atomPolynomial systematic
  encoded.weaken (by omega) |>.add <|
    (encoded.mul linear).scale (-2) |>.add (linear.mul linear)

@[simp] theorem systematicValidityPolynomial_value
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (systematic : Circuit) (linear : CircuitPolynomial Circuit 1)
    (input : BitInput q) :
    (systematicValidityPolynomial systematic linear).value evaluate input =
      (bitAsReal (evaluate systematic input) -
        linear.value evaluate input) ^ 2 := by
  simp [systematicValidityPolynomial]
  cases evaluate systematic input <;> simp [bitAsReal] <;> ring

@[simp] theorem systematicValidityPolynomial_coefficientMass
    {Circuit : Type} (systematic : Circuit)
    (linear : CircuitPolynomial Circuit 1) :
  (systematicValidityPolynomial systematic linear).coefficientMass =
      1 + 2 * linear.coefficientMass + linear.coefficientMass ^ 2 := by
  simp [systematicValidityPolynomial]
  ring

theorem systematicValidityPolynomial_factorsSatisfy
    {Circuit : Type} (systematic : Circuit)
    (linear : CircuitPolynomial Circuit 1)
    (predicate : Circuit → Prop)
    (hsystematic : predicate systematic)
    (hlinear : linear.FactorsSatisfy predicate) :
    (systematicValidityPolynomial systematic linear).FactorsSatisfy
      predicate := by
  let encoded := atomPolynomial systematic
  have hencoded : encoded.FactorsSatisfy predicate :=
    atomPolynomial_factorsSatisfy systematic predicate hsystematic
  unfold systematicValidityPolynomial
  apply CircuitPolynomial.add_factorsSatisfy
  · exact CircuitPolynomial.weaken_factorsSatisfy _ encoded predicate
      hencoded
  · apply CircuitPolynomial.add_factorsSatisfy
    · exact CircuitPolynomial.scale_factorsSatisfy _
        (encoded.mul linear) predicate <|
          CircuitPolynomial.mul_factorsSatisfy encoded linear predicate
            hencoded hlinear
    · exact CircuitPolynomial.mul_factorsSatisfy linear linear predicate
        hlinear hlinear

def secondMomentPolynomial
    {Circuit : Type} (linear : CircuitPolynomial Circuit 1) :
    CircuitPolynomial Circuit 2 :=
  linear.mul linear

@[simp] theorem secondMomentPolynomial_value
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (linear : CircuitPolynomial Circuit 1) (input : BitInput q) :
    (secondMomentPolynomial linear).value evaluate input =
      (linear.value evaluate input) ^ 2 := by
  simp [secondMomentPolynomial, pow_two]

@[simp] theorem secondMomentPolynomial_coefficientMass
    {Circuit : Type} (linear : CircuitPolynomial Circuit 1) :
    (secondMomentPolynomial linear).coefficientMass =
      linear.coefficientMass ^ 2 := by
  simp [secondMomentPolynomial, pow_two]

theorem secondMomentPolynomial_factorsSatisfy
    {Circuit : Type} (linear : CircuitPolynomial Circuit 1)
    (predicate : Circuit → Prop)
    (hlinear : linear.FactorsSatisfy predicate) :
    (secondMomentPolynomial linear).FactorsSatisfy predicate :=
  CircuitPolynomial.mul_factorsSatisfy linear linear predicate
    hlinear hlinear

def literalPolynomial
    {Circuit : Type} (negative : Bool)
    (linear : CircuitPolynomial Circuit 1) :
    CircuitPolynomial Circuit 1 :=
  if negative then
    (CircuitPolynomial.constant 1 1).add (linear.scale (-1))
  else
    linear

@[simp] theorem literalPolynomial_value
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (negative : Bool) (linear : CircuitPolynomial Circuit 1)
    (input : BitInput q) :
    (literalPolynomial negative linear).value evaluate input =
      ComponentwiseValidity.literalValue negative
        (linear.value evaluate input) := by
  cases negative <;>
    simp [literalPolynomial, ComponentwiseValidity.literalValue]
  ring

@[simp] theorem literalPolynomial_coefficientMass
    {Circuit : Type} (negative : Bool)
    (linear : CircuitPolynomial Circuit 1) :
    (literalPolynomial negative linear).coefficientMass =
      if negative then 1 + linear.coefficientMass
      else linear.coefficientMass := by
  cases negative <;> simp [literalPolynomial]

theorem literalPolynomial_factorsSatisfy
    {Circuit : Type} (negative : Bool)
    (linear : CircuitPolynomial Circuit 1)
    (predicate : Circuit → Prop)
    (hlinear : linear.FactorsSatisfy predicate) :
    (literalPolynomial negative linear).FactorsSatisfy predicate := by
  cases negative with
  | false => simpa [literalPolynomial] using hlinear
  | true =>
      exact CircuitPolynomial.add_factorsSatisfy
        (CircuitPolynomial.constant 1 1) (linear.scale (-1)) predicate
        (CircuitPolynomial.constant_factorsSatisfy 1 1 predicate)
        (CircuitPolynomial.scale_factorsSatisfy (-1) linear predicate
          hlinear)

def clausePolynomial
    {Circuit : Type} (leftNegative rightNegative : Bool)
    (left right : CircuitPolynomial Circuit 1) :
    CircuitPolynomial Circuit 2 :=
  let leftLiteral := literalPolynomial leftNegative left
  let rightLiteral := literalPolynomial rightNegative right
  (leftLiteral.weaken (by omega)).add <|
    (rightLiteral.weaken (by omega)).add <|
      (leftLiteral.mul rightLiteral).scale (-1)

@[simp] theorem clausePolynomial_value
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (leftNegative rightNegative : Bool)
    (left right : CircuitPolynomial Circuit 1)
    (input : BitInput q) :
    (clausePolynomial leftNegative rightNegative left right).value
        evaluate input =
      ComponentwiseValidity.clauseValue leftNegative rightNegative
        (left.value evaluate input) (right.value evaluate input) := by
  simp [clausePolynomial, ComponentwiseValidity.clauseValue]
  ring

@[simp] theorem clausePolynomial_coefficientMass
    {Circuit : Type} (leftNegative rightNegative : Bool)
    (left right : CircuitPolynomial Circuit 1) :
    (clausePolynomial leftNegative rightNegative left right).coefficientMass =
      (literalPolynomial leftNegative left).coefficientMass +
        (literalPolynomial rightNegative right).coefficientMass +
      (literalPolynomial leftNegative left).coefficientMass *
          (literalPolynomial rightNegative right).coefficientMass := by
  simp [clausePolynomial]
  ring

theorem clausePolynomial_factorsSatisfy
    {Circuit : Type} (leftNegative rightNegative : Bool)
    (left right : CircuitPolynomial Circuit 1)
    (predicate : Circuit → Prop)
    (hleft : left.FactorsSatisfy predicate)
    (hright : right.FactorsSatisfy predicate) :
    (clausePolynomial leftNegative rightNegative left right).FactorsSatisfy
      predicate := by
  let leftLiteral := literalPolynomial leftNegative left
  let rightLiteral := literalPolynomial rightNegative right
  have hleftLiteral : leftLiteral.FactorsSatisfy predicate :=
    literalPolynomial_factorsSatisfy leftNegative left predicate hleft
  have hrightLiteral : rightLiteral.FactorsSatisfy predicate :=
    literalPolynomial_factorsSatisfy rightNegative right predicate hright
  unfold clausePolynomial
  apply CircuitPolynomial.add_factorsSatisfy
  · exact CircuitPolynomial.weaken_factorsSatisfy _ leftLiteral predicate
      hleftLiteral
  · apply CircuitPolynomial.add_factorsSatisfy
    · exact CircuitPolynomial.weaken_factorsSatisfy _ rightLiteral predicate
        hrightLiteral
    · exact CircuitPolynomial.scale_factorsSatisfy _
        (leftLiteral.mul rightLiteral) predicate <|
          CircuitPolynomial.mul_factorsSatisfy leftLiteral rightLiteral
            predicate hleftLiteral hrightLiteral

noncomputable def CircuitPolynomial.exactMean
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (polynomial : CircuitPolynomial Circuit degree) : ℝ :=
  (polynomial.monomials.map fun monomial =>
    (monomial.coefficient : ℝ) *
      conjunctionProbability evaluate monomial.factors).sum

noncomputable def CircuitPolynomial.uniformMean
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (polynomial : CircuitPolynomial Circuit degree) : ℝ :=
  𝔼 input, polynomial.value evaluate input

theorem conjunctionProbability_eq_expect
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (circuits : List Circuit) :
    conjunctionProbability evaluate circuits =
      𝔼 input, bitAsReal (conjunctionBit evaluate circuits input) := by
  simp [conjunctionProbability, booleanMean, Finset.expect,
    NNRat.smul_def, NNRat.cast_inv,
    div_eq_mul_inv, mul_comm]

private theorem exactMeanList_eq_expect
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (monomials : List (CircuitMonomial Circuit degree)) :
    (monomials.map fun monomial =>
      (monomial.coefficient : ℝ) *
        conjunctionProbability evaluate monomial.factors).sum =
      𝔼 input, (monomials.map fun monomial =>
        monomial.value evaluate input).sum := by
  induction monomials with
  | nil => simp
  | cons monomial monomials inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.expect_add_distrib]
      rw [conjunctionProbability_eq_expect, Finset.mul_expect]
      exact congrArg₂ (· + ·) rfl inductionHypothesis

theorem CircuitPolynomial.exactMean_eq_uniformMean
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (polynomial : CircuitPolynomial Circuit degree) :
    polynomial.exactMean evaluate = polynomial.uniformMean evaluate := by
  exact exactMeanList_eq_expect evaluate polynomial.monomials

theorem auxiliaryValidityPolynomial_exactMean
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (linear : CircuitPolynomial Circuit 1) :
    (auxiliaryValidityPolynomial linear).exactMean evaluate =
      𝔼 input,
        ComponentwiseValidity.booleanityPenalty
          (linear.value evaluate input) := by
  rw [CircuitPolynomial.exactMean_eq_uniformMean]
  simp [CircuitPolynomial.uniformMean,
    ComponentwiseValidity.booleanityPenalty]

theorem systematicValidityPolynomial_exactMean
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (systematic : Circuit) (linear : CircuitPolynomial Circuit 1) :
    (systematicValidityPolynomial systematic linear).exactMean evaluate =
      𝔼 input,
        ComponentwiseValidity.systematicPenalty
          (evaluate systematic input) (linear.value evaluate input) := by
  rw [CircuitPolynomial.exactMean_eq_uniformMean]
  simp [CircuitPolynomial.uniformMean,
    ComponentwiseValidity.systematicPenalty]

theorem secondMomentPolynomial_exactMean
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (linear : CircuitPolynomial Circuit 1) :
    (secondMomentPolynomial linear).exactMean evaluate =
      𝔼 input, (linear.value evaluate input) ^ 2 := by
  rw [CircuitPolynomial.exactMean_eq_uniformMean]
  simp [CircuitPolynomial.uniformMean]

theorem clausePolynomial_exactMean
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (leftNegative rightNegative : Bool)
    (left right : CircuitPolynomial Circuit 1) :
    (clausePolynomial leftNegative rightNegative left right).exactMean
        evaluate =
      𝔼 input,
        ComponentwiseValidity.clauseValue leftNegative rightNegative
          (left.value evaluate input) (right.value evaluate input) := by
  rw [CircuitPolynomial.exactMean_eq_uniformMean]
  simp [CircuitPolynomial.uniformMean]

def CircuitPolynomial.estimatedMean
    {Circuit : Type} {degree : ℕ}
    (estimate : List Circuit → ℚ)
    (polynomial : CircuitPolynomial Circuit degree) : ℝ :=
  (polynomial.monomials.map fun monomial =>
    (monomial.coefficient : ℝ) * (estimate monomial.factors : ℝ)).sum

private theorem estimatedMeanList_error_le
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (estimate : List Circuit → ℚ)
    (monomials : List (CircuitMonomial Circuit degree))
    (error : ℝ)
    (hpoint : ∀ monomial ∈ monomials,
      |(estimate monomial.factors : ℝ) -
        conjunctionProbability evaluate monomial.factors| ≤ error) :
    |(monomials.map fun monomial =>
        (monomial.coefficient : ℝ) *
          (estimate monomial.factors : ℝ)).sum -
      (monomials.map fun monomial =>
        (monomial.coefficient : ℝ) *
          conjunctionProbability evaluate monomial.factors).sum| ≤
      error *
        ((monomials.map fun monomial => |monomial.coefficient|).sum :
          ℚ) := by
  revert hpoint
  induction monomials with
  | nil =>
      intro _
      simp
  | cons monomial monomials inductionHypothesis =>
      intro hpoint
      have hhead :
          |(estimate monomial.factors : ℝ) -
            conjunctionProbability evaluate monomial.factors| ≤ error :=
        hpoint monomial List.mem_cons_self
      have htail :
          ∀ candidate ∈ monomials,
            |(estimate candidate.factors : ℝ) -
              conjunctionProbability evaluate candidate.factors| ≤ error := by
        intro candidate hcandidate
        exact hpoint candidate
          (List.mem_cons_of_mem monomial hcandidate)
      have hinduction := inductionHypothesis htail
      simp only [List.map_cons, List.sum_cons]
      rw [show
        (monomial.coefficient : ℝ) *
              (estimate monomial.factors : ℝ) +
            (monomials.map fun candidate =>
              (candidate.coefficient : ℝ) *
                (estimate candidate.factors : ℝ)).sum -
          ((monomial.coefficient : ℝ) *
              conjunctionProbability evaluate monomial.factors +
            (monomials.map fun candidate =>
              (candidate.coefficient : ℝ) *
                conjunctionProbability evaluate candidate.factors).sum) =
          (monomial.coefficient : ℝ) *
              ((estimate monomial.factors : ℝ) -
                conjunctionProbability evaluate monomial.factors) +
            ((monomials.map fun candidate =>
              (candidate.coefficient : ℝ) *
                (estimate candidate.factors : ℝ)).sum -
              (monomials.map fun candidate =>
                (candidate.coefficient : ℝ) *
                  conjunctionProbability evaluate candidate.factors).sum) by
        ring]
      calc
        _ ≤
            |(monomial.coefficient : ℝ) *
              ((estimate monomial.factors : ℝ) -
                conjunctionProbability evaluate monomial.factors)| +
            |(monomials.map fun candidate =>
                (candidate.coefficient : ℝ) *
                  (estimate candidate.factors : ℝ)).sum -
              (monomials.map fun candidate =>
                (candidate.coefficient : ℝ) *
                  conjunctionProbability evaluate candidate.factors).sum| :=
          abs_add_le _ _
        _ ≤ |(monomial.coefficient : ℝ)| * error +
            error *
              ((monomials.map fun candidate =>
                |candidate.coefficient|).sum : ℚ) := by
          rw [abs_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_left hhead (abs_nonneg _))
            hinduction
        _ = error *
            ((|monomial.coefficient| ::
              monomials.map fun candidate => |candidate.coefficient|).sum :
                ℚ) := by
          push_cast
          simp only [List.map_cons, List.sum_cons, List.map_map,
            Rat.cast_abs]
          ring

theorem estimatedMean_error_le
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (estimate : List Circuit → ℚ)
    (polynomial : CircuitPolynomial Circuit degree)
    (error : ℝ)
    (hpoint : ∀ monomial ∈ polynomial.monomials,
      |(estimate monomial.factors : ℝ) -
        conjunctionProbability evaluate monomial.factors| ≤ error) :
    |polynomial.estimatedMean estimate -
        polynomial.exactMean evaluate| ≤
      error * (polynomial.coefficientMass : ℝ) := by
  exact estimatedMeanList_error_le evaluate estimate polynomial.monomials
    error hpoint

end NearCubicWires.ComponentwisePolynomial
