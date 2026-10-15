import Proof.Gates.Interfaces.Counter
import Proof.Gates.CircuitNormalization

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicGates NearCubicGates.Close.Interfaces NearCubicGates.CircuitNormalization

theorem zip_ofFn {α β : Type*} {m : ℕ} (f : Fin m → α) (g : Fin m → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn fun i => (f i, g i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_zip]

noncomputable def toNCircuit {n : ℕ} (C : Target.WeightedSymmetricCircuit n) (D : IntegerDescription C) : NCircuit n where
  gates := List.ofFn fun i => (⟨(D.bottom i).weight, (D.bottom i).threshold⟩ : NormalizedThresholdGate n)
  coeffs := List.ofFn C.coefficient
  table := List.ofFn fun k : Fin (2 * C.topWeight + 1) => C.lookup ((k.val : ℤ) - C.topWeight)

theorem toNCircuit_topWeight {n : ℕ} (C : Target.WeightedSymmetricCircuit n) (D : IntegerDescription C) :
    (toNCircuit C D).topWeight = C.topWeight := by
  unfold NCircuit.topWeight toNCircuit Target.WeightedSymmetricCircuit.topWeight
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

theorem toNCircuit_score {n : ℕ} (C : Target.WeightedSymmetricCircuit n) (D : IntegerDescription C) (z : BitInput n) :
    (toNCircuit C D).score z = C.score z := by
  unfold NCircuit.score toNCircuit Target.WeightedSymmetricCircuit.score
  rw [zip_ofFn, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp]
  have h := D.correct i z
  unfold IntegerGate.eval at h
  rw [show NormalizedThresholdGate.eval (⟨(D.bottom i).weight, (D.bottom i).threshold⟩ : NormalizedThresholdGate n) z =
    (C.bottom i).eval z from h]

theorem toNCircuit_eval {n : ℕ} (C : Target.WeightedSymmetricCircuit n) (D : IntegerDescription C) (z : BitInput n) :
    (toNCircuit C D).eval z = C.eval z := by
  unfold NCircuit.eval
  rw [toNCircuit_score, toNCircuit_topWeight]
  have hb := score_magnitude_le_topWeight C z
  have hlt : (C.score z + C.topWeight).toNat < 2 * C.topWeight + 1 := by omega
  have hidx : (((C.score z + C.topWeight).toNat : ℤ)) - C.topWeight = C.score z := by omega
  unfold toNCircuit
  simp only
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn]
  simp only [hidx]
  rfl

theorem toNCircuit_wellFormed {n : ℕ} (C : Target.WeightedSymmetricCircuit n) (D : IntegerDescription C) :
    (toNCircuit C D).WellFormed (Call.B0 n) := by
  refine ⟨by simp [toNCircuit], ?_, ?_, ?_⟩
  · intro a ha
    simp only [toNCircuit, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact C.coefficient_ne_zero i
  · rw [toNCircuit_topWeight]
    simp [toNCircuit]
  · intro g hg
    simp only [toNCircuit, List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    exact ⟨fun j => D.weightBound i j, D.thresholdBound i⟩

end NearCubicGates.Close.Worker
