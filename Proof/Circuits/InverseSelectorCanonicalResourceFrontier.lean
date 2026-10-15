import Proof.Circuits.InverseSelectorHexecutes
import Proof.Circuits.ValidatorCompositeLeafBounds
import Proof.Circuits.ValidatorPolynomialDomination

/-! # Exact polynomial resource splice for the inverse selector terminal -/

namespace NearCubicWires.InverseSelectorCanonicalResourceFrontier

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseLengthStage
open NearCubicWires.InverseSelectorHexecutes
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

/-! ## 1. Exact selector resource census -/

/-- The actual bank-width term occurring inside `selectorUniformBits`. -/
noncomputable def inverseSelectorCanonicalBankBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (request : LanguageEvaluationRequest) : ℕ :=
  publishedSourceDrivenBankBits
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    request.length
    (inverseLengthBits contracts clockDepth advantageExponent request)
    (inverseScheduleLength contracts clockDepth advantageExponent request.length)
    request.code

/-- The actual bank-fuel term occurring inside `selectorUniformFuel`. -/
noncomputable def inverseSelectorCanonicalBankFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (request : LanguageEvaluationRequest) : ℕ :=
  publishedSourceDrivenBankFuel
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (inverseLengthFuel contracts clockDepth advantageExponent request)
    (inverseScheduleLength contracts clockDepth advantageExponent request.length)

set_option maxRecDepth 2000 in
/-- Exact width census: public length, the actual source-driven bank, and the
actual body width are the three heads of the outer maximum. -/
theorem selectorUniformBits_eq_canonicalFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (bodyBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) :
    selectorUniformBits contracts clockDepth advantageExponent bodyBits
        request =
      occurrenceStageBits request.length
        (inverseSelectorCanonicalBankBits contracts clockDepth
          advantageExponent request)
        (bodyBits request) := by
  rfl

set_option maxRecDepth 2000 in
/-- Exact fuel census: one link from the actual bank fuel into the body fuel. -/
theorem selectorUniformFuel_eq_canonicalFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (body : NPOracleProgram)
    (bodyFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) :
    selectorUniformFuel contracts clockDepth advantageExponent body bodyFuel
        request =
      linkFuel body
        (inverseSelectorCanonicalBankFuel contracts clockDepth
          advantageExponent request)
        (bodyFuel request) := by
  rfl

/-! ## 2. Polynomial closure of the exact outer splice -/

/-- The public input-length width is degree-one in the terminal request
measure. -/
theorem requestLengthBits_polyBounded
    (request : LanguageEvaluationRequest) :
    PolyBounded (natBitLength request.length) request.measure 1 1 := by
  unfold PolyBounded
  rw [pow_one, Nat.one_mul]
  exact (ValidatorCompositeLeafBounds.natBitLength_le_succ request.length).trans
    (Nat.add_le_add_right (Nat.le_max_right 1 request.length) 1)

/-- The exact selector width is polynomial from polynomial bounds for its
actual source-driven bank and actual body width. -/
theorem selectorUniformBits_polyBounded_of_canonicalFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (bodyBits : LanguageEvaluationRequest → ℕ)
    (bankCoefficient bodyCoefficient degree : ℕ)
    (hdegree : 1 ≤ degree)
    (hbank : ∀ request,
      PolyBounded
        (inverseSelectorCanonicalBankBits contracts clockDepth
          advantageExponent request)
        request.measure bankCoefficient degree)
    (hbody : ∀ request,
      PolyBounded (bodyBits request) request.measure bodyCoefficient degree) :
    ∀ request,
      PolyBounded
        (selectorUniformBits contracts clockDepth advantageExponent bodyBits
          request)
        request.measure (max 1 (max bankCoefficient bodyCoefficient)) degree := by
  intro request
  rw [selectorUniformBits_eq_canonicalFrontier]
  exact (requestLengthBits_polyBounded request).degree_mono hdegree |>.max
    ((hbank request).max (hbody request))

/-- The exact selector fuel is polynomial from polynomial bounds for its
actual source-driven bank and actual body fuel. -/
theorem selectorUniformFuel_polyBounded_of_canonicalFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (body : NPOracleProgram)
    (bodyFuel : LanguageEvaluationRequest → ℕ)
    (bankCoefficient bodyCoefficient degree : ℕ)
    (hbank : ∀ request,
      PolyBounded
        (inverseSelectorCanonicalBankFuel contracts clockDepth
          advantageExponent request)
        request.measure bankCoefficient degree)
    (hbody : ∀ request,
      PolyBounded (bodyFuel request) request.measure bodyCoefficient degree) :
    ∀ request,
      PolyBounded
        (selectorUniformFuel contracts clockDepth advantageExponent body
          bodyFuel request)
        request.measure
        (programRegisterSpan body + 5 + bankCoefficient + bodyCoefficient)
        degree := by
  intro request
  rw [selectorUniformFuel_eq_canonicalFrontier]
  exact linkFuel_polyBounded (hbank request) (hbody request)

end NearCubicWires.InverseSelectorCanonicalResourceFrontier
