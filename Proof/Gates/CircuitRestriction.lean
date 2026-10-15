import Proof.Gates.TargetChecks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

/-! Literal suffix restrictions of the actual weighted threshold representation.
    No normalization or closure hypothesis is used. -/

set_option autoImplicit false

namespace NearCubicGates.Target

open scoped BigOperators
open NearCubicWires

noncomputable def restrictGate {n k : ℕ} (g : RealThresholdGate (n + k))
    (suffix : BitInput k) : RealThresholdGate n where
  weight i := g.weight (Fin.castAdd k i)
  threshold := g.threshold - ∑ j, g.weight (Fin.natAdd n j) * bitAsReal (suffix j)
  support := Finset.univ.filter fun i => g.weight (Fin.castAdd k i) ≠ 0
  mem_support_iff := by intro i; simp

@[simp] theorem restrictGate_eval {n k : ℕ} (g : RealThresholdGate (n + k))
    (suffix : BitInput k) (x : BitInput n) :
    (restrictGate g suffix).eval x = g.eval (Fin.append x suffix) := by
  unfold RealThresholdGate.eval restrictGate
  congr 1
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  exact propext (sub_le_iff_le_add)

noncomputable def WeightedSymmetricCircuit.restrictSuffix {n k : ℕ}
    (C : WeightedSymmetricCircuit (n + k)) (suffix : BitInput k) :
    WeightedSymmetricCircuit n where
  bottomCount := C.bottomCount
  bottom i := restrictGate (C.bottom i) suffix
  coefficient := C.coefficient
  coefficient_ne_zero := C.coefficient_ne_zero
  lookup := C.lookup

@[simp] theorem restrictSuffix_topWeight {n k : ℕ}
    (C : WeightedSymmetricCircuit (n + k)) (suffix : BitInput k) :
    (C.restrictSuffix suffix).topWeight = C.topWeight := rfl

@[simp] theorem restrictSuffix_score {n k : ℕ}
    (C : WeightedSymmetricCircuit (n + k)) (suffix : BitInput k) (x : BitInput n) :
    (C.restrictSuffix suffix).score x = C.score (Fin.append x suffix) := by
  unfold WeightedSymmetricCircuit.score WeightedSymmetricCircuit.restrictSuffix
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [restrictGate_eval]

@[simp] theorem restrictSuffix_eval {n k : ℕ}
    (C : WeightedSymmetricCircuit (n + k)) (suffix : BitInput k) (x : BitInput n) :
    (C.restrictSuffix suffix).eval x = C.eval (Fin.append x suffix) := by
  change C.lookup ((C.restrictSuffix suffix).score x) = _
  rw [restrictSuffix_score]
  rfl

theorem restrictSuffix_hasPeriod {n k : ℕ}
    (C : WeightedSymmetricCircuit (n + k)) (suffix : BitInput k) (m : ℕ) :
    (C.restrictSuffix suffix).HasPeriod m ↔ C.HasPeriod m := Iff.rfl

end NearCubicGates.Target
