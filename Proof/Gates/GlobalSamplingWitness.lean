import Proof.Gates.FiniteAverages
import Proof.Gates.CircuitNormalization

set_option autoImplicit false

namespace NearCubicGates.GlobalSamplingWitness

open scoped BigOperators
open FiniteAverages NearCubicWires Target

def failure (b : Bool) : ℝ := if b then 0 else 1

theorem global_useful_witness {Cells Samples : Type*}
    [Fintype Cells] [Nonempty Cells] [Fintype Samples] [Nonempty Samples]
    (live : Cells → Bool) (good : Samples → Cells → Bool) (β : ℝ) (hβ : 0 ≤ β)
    (hlive : mean (fun c => failure (live c)) ≤ β)
    (hlocal : ∀ c, live c = true → mean (fun s => failure (good s c)) ≤ β) :
    ∃ sample : Samples, mean (fun c => failure (live c && good sample c)) / 2 ≤ β := by
  let badOnLive (s : Samples) (c : Cells) : ℝ := if live c then failure (good s c) else 0
  have hmean : mean (fun s => mean (badOnLive s)) ≤ β := by
    rw [mean_mean_comm]
    apply (mean_le_mean _ (fun _ : Cells => β) ?_).trans_eq (mean_const β)
    intro c
    cases hc : live c with
    | false => simpa only [badOnLive, hc, Bool.false_eq_true, if_false, mean_const] using hβ
    | true => simpa only [badOnLive, hc, if_true] using hlocal c hc
  obtain ⟨sample, hs⟩ := exists_le_mean (fun s => mean (badOnLive s))
  have hpoint (c : Cells) : failure (live c && good sample c) ≤
      failure (live c) + badOnLive sample c := by
    cases hc : live c <;> cases hg : good sample c <;>
      simp [failure, badOnLive, hc, hg]
  have hb := (mean_le_mean _ _ hpoint)
  rw [mean_add] at hb
  refine ⟨sample, ?_⟩
  linarith

abbrev UnitCopy {n : ℕ} (C : WeightedSymmetricCircuit n) :=
  Σ i : Fin C.bottomCount, Fin (C.coefficient i).natAbs

def sampledCount {n : ℕ} (C : WeightedSymmetricCircuit n)
    (keep : UnitCopy C → Bool) (i : Fin C.bottomCount) : ℕ :=
  ∑ j : Fin (C.coefficient i).natAbs, if keep ⟨i, j⟩ then 1 else 0

def sampledCoefficient {n : ℕ} (C : WeightedSymmetricCircuit n)
    (keep : UnitCopy C → Bool) (i : Fin C.bottomCount) : ℤ :=
  if C.coefficient i < 0 then -(sampledCount C keep i : ℤ) else sampledCount C keep i

theorem sampledCount_le {n : ℕ} (C : WeightedSymmetricCircuit n)
    (keep : UnitCopy C → Bool) (i : Fin C.bottomCount) :
    sampledCount C keep i ≤ (C.coefficient i).natAbs := by
  unfold sampledCount
  calc
    _ ≤ ∑ _ : Fin (C.coefficient i).natAbs, 1 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> omega
    _ = _ := by simp

theorem sampledCoefficient_magnitude {n : ℕ} (C : WeightedSymmetricCircuit n)
    (keep : UnitCopy C → Bool) (i : Fin C.bottomCount) :
    (sampledCoefficient C keep i).natAbs ≤ (C.coefficient i).natAbs := by
  unfold sampledCoefficient
  split_ifs <;> simpa using sampledCount_le C keep i

theorem sampledCoefficient_witness_range {n : ℕ} (C : WeightedSymmetricCircuit n)
    (keep : UnitCopy C → Bool) (i : Fin C.bottomCount) :
    -((C.coefficient i).natAbs : ℤ) ≤ sampledCoefficient C keep i ∧
      sampledCoefficient C keep i ≤ (C.coefficient i).natAbs := by
  have h := sampledCoefficient_magnitude C keep i
  omega

def nestedKeep {n M : ℕ} (C : WeightedSymmetricCircuit n)
    (draw : UnitCopy C → Fin M) (cutoff : ℕ) : UnitCopy C → Bool :=
  fun u => decide ((draw u).val < cutoff)

theorem nestedKeep_mono {n M : ℕ} (C : WeightedSymmetricCircuit n)
    (draw : UnitCopy C → Fin M) {a b : ℕ} (hab : a ≤ b)
    (u : UnitCopy C) : nestedKeep C draw a u = true → nestedKeep C draw b u = true := by
  simp only [nestedKeep, decide_eq_true_eq]
  omega

theorem unitCopy_card {n : ℕ} (C : WeightedSymmetricCircuit n) :
    Fintype.card (UnitCopy C) = C.topWeight := by
  simp [WeightedSymmetricCircuit.topWeight, Fintype.card_sigma]

end NearCubicGates.GlobalSamplingWitness
