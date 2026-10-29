import Proof.Gates.CircuitRestriction
import Proof.Gates.MainBudgetDilation
import Proof.Foundations.SourceInterfaces

/-! Actual integer descriptions of the real-bottom target circuits, from the
    threshold-normalization fact `ThresholdNormalizationContract` alone (input 1,
    `lem:integer` in `paper/paper.tex`: "Only existence of normalized integer
    descriptions is required; an efficient normalization algorithm is not
    assumed"). -/

set_option autoImplicit false

namespace NearCubicGates.CircuitNormalization

open scoped BigOperators
open NearCubicWires Target
open NearCubicWires.SourceInterfaces

structure IntegerGate (n : ℕ) where
  weight : Fin n → ℤ
  threshold : ℤ

def IntegerGate.eval {n : ℕ} (g : IntegerGate n) (x : BitInput n) : Bool :=
  decide (g.threshold ≤ ∑ i, g.weight i * (if x i then 1 else 0))

def parameterBits (n : ℕ) : ℕ := 4 * n * Nat.clog 2 (n + 1)

theorem magnitude_fits_parameters {n : ℕ} (hn : 1 ≤ n) :
    n ^ n < 2 ^ parameterBits n := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (n + 1)
  have hp : n ^ n ≤ 2 ^ (Nat.clog 2 (n + 1) * n) := by
    calc
      _ ≤ (2 ^ Nat.clog 2 (n + 1)) ^ n := Nat.pow_le_pow_left (by omega) n
      _ = _ := (pow_mul 2 _ _).symm
  have hc : 1 ≤ Nat.clog 2 (n + 1) := by
    have hmono := Nat.clog_mono_right 2 (show 2 ≤ n + 1 by omega)
    simpa only [show Nat.clog 2 2 = 1 from by decide] using hmono
  have he : Nat.clog 2 (n + 1) * n < parameterBits n := by
    unfold parameterBits
    nlinarith
  exact hp.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) he)

theorem normalize_gate (normalized : ThresholdNormalizationContract) {n : ℕ} (hn : 1 ≤ n)
    (g : RealThresholdGate n) :
    ∃ h : IntegerGate n,
      (∀ x, h.eval x = g.eval x) ∧
      h.threshold.natAbs < 2 ^ parameterBits n ∧
      ∀ i, (h.weight i).natAbs < 2 ^ parameterBits n := by
  obtain ⟨gate, heval, hw, ht⟩ := normalized n hn g
  have hb := magnitude_fits_parameters hn
  exact ⟨⟨gate.weight, gate.threshold⟩, heval, ht.trans_lt hb, fun i => (hw i).trans_lt hb⟩

theorem bottomCount_le_topWeight {n : ℕ} (C : WeightedSymmetricCircuit n) :
    C.bottomCount ≤ C.topWeight := by
  have h : (∑ _ : Fin C.bottomCount, 1) ≤ ∑ i, (C.coefficient i).natAbs := by
    apply Finset.sum_le_sum
    intro i _
    have hi := Int.natAbs_pos.mpr (C.coefficient_ne_zero i)
    omega
  simpa [WeightedSymmetricCircuit.topWeight] using h

theorem score_magnitude_le_topWeight {n : ℕ} (C : WeightedSymmetricCircuit n) (x : BitInput n) :
    (C.score x).natAbs ≤ C.topWeight := by
  unfold WeightedSymmetricCircuit.score WeightedSymmetricCircuit.topWeight
  apply (Int.natAbs_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp

structure IntegerDescription {n : ℕ} (C : WeightedSymmetricCircuit n) where
  bottom : Fin C.bottomCount → IntegerGate n
  correct : ∀ i x, (bottom i).eval x = (C.bottom i).eval x
  thresholdBound : ∀ i, (bottom i).threshold.natAbs < 2 ^ parameterBits n
  weightBound : ∀ i j, ((bottom i).weight j).natAbs < 2 ^ parameterBits n

theorem integer_description_exists (normalized : ThresholdNormalizationContract) {n : ℕ}
    (hn : 1 ≤ n) (C : WeightedSymmetricCircuit n) : Nonempty (IntegerDescription C) := by
  classical
  choose bottom hc ht hw using fun i => normalize_gate normalized hn (C.bottom i)
  exact ⟨⟨bottom, hc, ht, hw⟩⟩

end NearCubicGates.CircuitNormalization
