import Proof.Gates.CircuitRestriction
import Proof.Gates.FiniteAverages

/-! Averaging over the actual ignored suffix yields a literal restriction
    of the weighted circuit with at least the padded agreement. -/

set_option autoImplicit false

namespace NearCubicGates.Target

open scoped BigOperators
open NearCubicWires

def splitInputEquiv (n k : ℕ) : BitInput (n + k) ≃ BitInput n × BitInput k where
  toFun x := (fun i => x (Fin.castAdd k i), fun j => x (Fin.natAdd n j))
  invFun x := Fin.append x.1 x.2
  left_inv x := by
    funext i
    exact Fin.addCases (fun i => by simp) (fun j => by simp) i
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp

theorem agreement_eq_mean {n : ℕ} (C : WeightedSymmetricCircuit n) (F : Language) :
    agreement C F = FiniteAverages.agreement C.eval (F n) := by
  classical
  simp [agreement, FiniteAverages.agreement, FiniteAverages.mean]

theorem padding_agreement_average {n k : ℕ} (C : WeightedSymmetricCircuit (n + k))
    (f : BoolFunction n) :
    FiniteAverages.agreement C.eval (fun x => f (fun i => x (Fin.castAdd k i))) =
      FiniteAverages.mean (fun suffix : BitInput k =>
        FiniteAverages.agreement (C.restrictSuffix suffix).eval f) := by
  unfold FiniteAverages.agreement
  have hm := FiniteAverages.mean_equiv (splitInputEquiv n k).symm
    (fun x => if C.eval x = f (fun i => x (Fin.castAdd k i)) then (1 : ℝ) else 0)
  rw [← hm, FiniteAverages.mean_prod]
  congr 1
  funext suffix
  simp [splitInputEquiv, restrictSuffix_eval]

/-- A cofactor with at least the full padded agreement, and identical weight. -/
theorem exists_padding_restriction {n k : ℕ} (C : WeightedSymmetricCircuit (n + k))
    (f : BoolFunction n) :
    ∃ suffix : BitInput k,
      (C.restrictSuffix suffix).topWeight = C.topWeight ∧
      FiniteAverages.agreement C.eval (fun x => f (fun i => x (Fin.castAdd k i))) ≤
        FiniteAverages.agreement (C.restrictSuffix suffix).eval f := by
  rw [padding_agreement_average]
  obtain ⟨suffix, h⟩ := FiniteAverages.exists_mean_le
    (fun suffix : BitInput k => FiniteAverages.agreement (C.restrictSuffix suffix).eval f)
  exact ⟨suffix, rfl, h⟩

end NearCubicGates.Target
