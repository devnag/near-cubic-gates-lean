import Proof.Foundations.Semantics
import Proof.Foundations.ThresholdCompiler

/-!
# Semantic adapter for the executable threshold compiler

`ThresholdCompiler` proves the corrected crossing algorithm over integer
equations.  This module is the only adapter from that executable representation
to the exact-gate representation used by the source interfaces and headlines.
-/

namespace NearCubicWires.CompilerSemantics

open NearCubicWires.ThresholdCompiler

/-- Integer non-strict syntax `[score ≥ θ]` is the strict gate
`[score > θ - 1]`; no coefficient or support changes. -/
def nonStrictAsStrict {n : ℕ} (gate : NormalizedThresholdGate n) :
    NormalizedThresholdGate n where
  weight := gate.weight
  threshold := gate.threshold - 1

theorem nonStrictAsStrict_eval {n : ℕ} (gate : NormalizedThresholdGate n)
    (input : BitInput n) :
    (nonStrictAsStrict gate).strictEval input = gate.eval input := by
  simp only [NormalizedThresholdGate.strictEval, NormalizedThresholdGate.eval,
    nonStrictAsStrict]
  apply decide_eq_decide.mpr
  omega

theorem normalizedScore_eq_bitInt {n : ℕ} (gate : NormalizedThresholdGate n)
    (input : BitInput n) :
    (∑ i, gate.weight i * if input i then 1 else 0) =
      ∑ i, gate.weight i * bitInt (input i) := by
  apply Finset.sum_congr rfl
  intro index _
  cases input index <;> rfl

def toExactThresholdGate {n : ℕ} (equation : ExactEquation n) :
    ExactThresholdGate n where
  weight := equation.weights
  target := equation.target

@[simp] theorem toExactThresholdGate_eval {n : ℕ}
    (equation : ExactEquation n) (input : BitInput n) :
    (toExactThresholdGate equation).eval input =
      decide (equation.Holds input) := by
  rfl

def compiledExactGates {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) : List (ExactThresholdGate n) :=
  (erratumSafeDisjointChildren weights target).map toExactThresholdGate

/-- The executable acceptance count is exactly the number of accepting
children.  This prevents the semantic adapter from weakening “disjoint OR” to
an unconstrained existential OR. -/
theorem acceptanceCount_eq_filterLength {n : ℕ}
    (children : List (ExactEquation n)) (input : BitInput n) :
    acceptanceCount children input =
      (children.filter fun child => decide (child.Holds input)).length := by
  induction children with
  | nil =>
      rfl
  | cons child children inductionHypothesis =>
      by_cases hchild : child.Holds input
      · simp [hchild, inductionHypothesis, add_comm]
      · simp [hchild, inductionHypothesis]

theorem compiledFilterLength {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (input : BitInput n) :
    ((compiledExactGates weights target).filter fun child => child.eval input).length =
      ((erratumSafeDisjointChildren weights target).filter fun child =>
        decide (child.Holds input)).length := by
  unfold compiledExactGates
  generalize erratumSafeDisjointChildren weights target = children
  induction children with
  | nil =>
      rfl
  | cons child children inductionHypothesis =>
      by_cases hchild : child.Holds input
      · simp [hchild, inductionHypothesis]
      · simp [hchild, inductionHypothesis]

theorem compiledAny {n : ℕ}
    (weights : Fin n → ℤ) (target : ℤ) (input : BitInput n) :
    (compiledExactGates weights target).any (fun child => child.eval input) =
      acceptsAny (erratumSafeDisjointChildren weights target) input := by
  unfold compiledExactGates acceptsAny
  generalize erratumSafeDisjointChildren weights target = children
  induction children with
  | nil =>
      rfl
  | cons child children inductionHypothesis =>
      simp [inductionHypothesis]

/-- The corrected executable construction inhabits the semantic disjoint-OR
record used by the typed source boundary.  No second oracle implementation is
introduced at this seam. -/
def compiledExactDecomposition {n : ℕ}
    (gate : NormalizedThresholdGate n) : ExactDecomposition gate where
  children := compiledExactGates gate.weight gate.threshold
  equivalent := by
    intro input
    rw [compiledAny]
    apply Bool.eq_iff_iff.mpr
    simp only [NormalizedThresholdGate.strictEval, decide_eq_true_eq]
    rw [normalizedScore_eq_bitInt]
    exact (erratumSafeDisjointChildren_any_iff
      gate.weight gate.threshold input).symm
  disjoint := by
    intro input
    rw [compiledFilterLength, ← acceptanceCount_eq_filterLength,
      erratumSafeDisjointChildren_count]
    split <;> omega

def compiledNormalizedDecomposition {n : ℕ}
    (gate : NormalizedThresholdGate n) :
    ExactDecomposition (nonStrictAsStrict gate) :=
  compiledExactDecomposition (nonStrictAsStrict gate)

end NearCubicWires.CompilerSemantics
