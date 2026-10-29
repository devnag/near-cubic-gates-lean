import Proof.Gates.Target
import Mathlib.Tactic.Linarith

/-!
# Semantic checks on the paper's target (`thm:main`)

These checks validate basic properties of the statement definitions. They do
not prove any of the hardness target propositions in `Target.lean`.
-/

set_option autoImplicit false

namespace NearCubicGates.Target

open scoped BigOperators
open NearCubicWires

/-- One positive unit top connection per bottom gate gives exactly the
bottom-gate count, without charging the bottom support. -/
theorem topWeight_eq_bottomCount_of_unit {n : ℕ}
    (C : WeightedSymmetricCircuit n)
    (h : ∀ i, C.coefficient i = 1) : C.topWeight = C.bottomCount := by
  simp [WeightedSymmetricCircuit.topWeight, h]

/-- Complementing the lookup preserves the underlying representation. -/
def WeightedSymmetricCircuit.outputComplement {n : ℕ}
    (C : WeightedSymmetricCircuit n) : WeightedSymmetricCircuit n :=
  { C with lookup := fun z => !(C.lookup z) }

@[simp] theorem outputComplement_topWeight {n : ℕ}
    (C : WeightedSymmetricCircuit n) :
    C.outputComplement.topWeight = C.topWeight := rfl

@[simp] theorem outputComplement_score {n : ℕ}
    (C : WeightedSymmetricCircuit n) (x : BitInput n) :
    C.outputComplement.score x = C.score x := rfl

@[simp] theorem outputComplement_eval {n : ℕ}
    (C : WeightedSymmetricCircuit n) (x : BitInput n) :
    C.outputComplement.eval x = !(C.eval x) := rfl

/-- Periodicity on the full frame is preserved in both directions. -/
theorem outputComplement_hasPeriod_iff {n : ℕ}
    (C : WeightedSymmetricCircuit n) (m : ℕ) :
    C.outputComplement.HasPeriod m ↔ C.HasPeriod m := by
  constructor
  · rintro ⟨hm, f, hf⟩
    refine ⟨hm, (fun r => !(f r)), ?_⟩
    intro z hz
    have h := congrArg Bool.not (hf z hz)
    simpa [WeightedSymmetricCircuit.outputComplement] using h
  · rintro ⟨hm, f, hf⟩
    refine ⟨hm, (fun r => !(f r)), ?_⟩
    intro z hz
    exact congrArg Bool.not (hf z hz)

theorem outputComplement_eligiblePeriod_iff {n : ℕ}
    (C : WeightedSymmetricCircuit n) :
    EligiblePeriod C.outputComplement ↔ EligiblePeriod C := by
  simp only [EligiblePeriod, outputComplement_hasPeriod_iff]

/-- The zero-bottom-gate constant circuit is included in the quantified
class and consumes zero top weight. -/
def constantCircuit (n : ℕ) (b : Bool) : WeightedSymmetricCircuit n where
  bottomCount := 0
  bottom := Fin.elim0
  coefficient := Fin.elim0
  coefficient_ne_zero := fun i => Fin.elim0 i
  lookup := fun _ => b

def constantLanguage (b : Bool) : Language := fun _ _ => b

@[simp] theorem constantCircuit_eval (n : ℕ) (b : Bool) (x : BitInput n) :
    (constantCircuit n b).eval x = b := rfl

@[simp] theorem constantCircuit_topWeight (n : ℕ) (b : Bool) :
    (constantCircuit n b).topWeight = 0 := by
  simp [WeightedSymmetricCircuit.topWeight, constantCircuit]

theorem constantCircuit_agreement (n : ℕ) (b : Bool) :
    agreement (constantCircuit n b) (constantLanguage b) = 1 := by
  simp [agreement, constantLanguage]

theorem constantCircuit_mainBudget (K n : ℕ) (b : Bool) :
    MainBudget K n (constantCircuit n b).topWeight := by
  simp [MainBudget]

/-- A constant language cannot meet the paper's eventual positive-error
hardness condition (`thm:main`), even for an arbitrary proposed constant multiplier. -/
theorem constantLanguage_not_eventually_hard (K : ℕ) (b : Bool)
    (d : ℝ) (hd : 0 < d) :
    ¬ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ C : WeightedSymmetricCircuit n,
        MainBudget K n C.topWeight →
          agreement C (constantLanguage b) < 1 - d := by
  rintro ⟨n₀, h⟩
  have hc := h n₀ (Nat.le_refl n₀) (constantCircuit n₀ b)
    (constantCircuit_mainBudget K n₀ b)
  rw [constantCircuit_agreement] at hc
  linarith

end NearCubicGates.Target
