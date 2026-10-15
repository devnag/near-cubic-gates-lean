import Proof.Gates.CircuitRestriction
import Proof.Gates.MainBudgetDilation

/-! Actual integer descriptions of the real-bottom target circuits, using
    only the literal published threshold-normalization input already present
    in the author's statement layer. No normalization algorithm is assumed. -/

set_option autoImplicit false

namespace NearCubicGates.CircuitNormalization

open scoped BigOperators
open NearCubicWires Target
open NearCubicWires.Bindings.CTW26

structure IntegerGate (n : ℕ) where
  weight : Fin n → ℤ
  threshold : ℤ

def IntegerGate.eval {n : ℕ} (g : IntegerGate n) (x : BitInput n) : Bool :=
  decide (g.threshold ≤ ∑ i, g.weight i * (if x i then 1 else 0))

def parameterBits (n : ℕ) : ℕ := 4 * n * Nat.clog 2 (n + 1)

theorem nat_indicator_eq_iff (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1 : ℕ) else 0) = (if Q then (1 : ℕ) else 0) ↔ (P ↔ Q) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

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

theorem normalize_gate (published : CTW26_Lemma3_2) {n : ℕ} (hn : 1 ≤ n)
    (g : RealThresholdGate n) :
    ∃ h : IntegerGate n,
      (∀ x, h.eval x = g.eval x) ∧
      h.threshold.natAbs < 2 ^ parameterBits n ∧
      ∀ i, (h.weight i).natAbs < 2 ^ parameterBits n := by
  classical
  let original : THRGate n := ⟨g.weight, g.threshold⟩
  obtain ⟨normalized, hequiv, hw, ht⟩ := published n original
  choose wi hwi hwi0 hwi1 using hw
  obtain ⟨t, ht, ht0, ht1⟩ := ht
  let h : IntegerGate n := ⟨wi, t⟩
  have hb := magnitude_fits_parameters hn
  refine ⟨h, ?_, ?_, ?_⟩
  · intro x
    have hex := hequiv (fun i => bitAsReal (x i)) (fun i => by
      cases x i <;> simp [bitAsReal])
    have hwreal : (∑ i, normalized.w i * bitAsReal (x i)) =
        ((∑ i, wi i * (if x i then (1 : ℤ) else 0) : ℤ) : ℝ) := by
      simp only [Int.cast_sum, Int.cast_mul, hwi]
      congr 1
      funext i
      cases x i <;> simp [bitAsReal]
    have hiff : normalized.t ≤ ∑ i, normalized.w i * bitAsReal (x i) ↔
        t ≤ ∑ i, wi i * (if x i then 1 else 0) := by
      rw [ht, hwreal]
      exact Int.cast_le
    apply Bool.eq_iff_iff.mpr
    simp only [IntegerGate.eval, RealThresholdGate.eval, Bool.decide_iff, h]
    have ho : g.threshold ≤ ∑ i, g.weight i * bitAsReal (x i) ↔
        normalized.t ≤ ∑ i, normalized.w i * bitAsReal (x i) := by
      exact (nat_indicator_eq_iff _ _).mp hex
    exact hiff.symm.trans ho.symm
  · dsimp [h]
    have habs : t.natAbs ≤ n ^ n := by omega
    exact habs.trans_lt hb
  · intro i
    dsimp [h]
    have habs : (wi i).natAbs ≤ n ^ n := by
      have h0 := hwi0 i
      have h1 := hwi1 i
      omega
    exact habs.trans_lt hb

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

theorem integer_description_exists (published : CTW26_Lemma3_2) {n : ℕ}
    (hn : 1 ≤ n) (C : WeightedSymmetricCircuit n) : Nonempty (IntegerDescription C) := by
  classical
  choose bottom hc ht hw using fun i => normalize_gate published hn (C.bottom i)
  exact ⟨⟨bottom, hc, ht, hw⟩⟩

end NearCubicGates.CircuitNormalization
