import Proof.Gates.Counter.SamplingLive

set_option autoImplicit false

namespace NearCubicGates.Close.Counter.Sampling.WitnessFailure

open scoped BigOperators

def ActualDataSupply : Prop :=
  ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → ∀ I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k, NearCubicGates.Close.Counter.Sampling.WitnessContract.ActualBernsteinData p C I

def ScalarTailSupply : Prop :=
  ∀ (T h ell pi V : ℝ), 0 < T → 0 ≤ pi * NearCubicGates.PublicSamplingRates.liveCap T h ell → 0 ≤ V → V ≤ pi * NearCubicGates.PublicSamplingRates.liveCap T h ell → 0 < NearCubicGates.PublicSamplingRates.fluctuation T h ell pi ∧ 2 * Real.exp (-(NearCubicGates.PublicSamplingRates.fluctuation T h ell pi) ^ 2 / (2 * (V + (NearCubicGates.PublicSamplingRates.fluctuation T h ell pi) / 3))) ≤ 2 * Real.exp (-T)

def UnionSupply : Prop :=
  ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → ∀ (I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k) (y : NearCubicGates.Close.Counter.Sampling.WitnessContract.Cells I), (∀ (r : Fin 2) (x : NearCubicGates.Close.Counter.Sampling.WitnessContract.Points I) (j : Fin p.s), NearCubicGates.FiniteAverages.mean (fun draw : NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C) => NearCubicGates.PublishedSources.Witness.indicator (p.fluctuation C j.val ≤ |NearCubicGates.Close.Counter.Sampling.WitnessContract.error p C I r y x j.val draw|)) ≤ 2 * Real.exp (-(p.T : ℝ))) → NearCubicGates.FiniteAverages.mean (fun draw : NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C) => NearCubicGates.GlobalSamplingWitness.failure (NearCubicGates.Close.Counter.Sampling.WitnessContract.good p C I draw y)) ≤ (p.beta : ℝ)

theorem enclose
  (hBernstein : NearCubicGates.PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
  (actualData : ActualDataSupply)
  (scalarBounds : ScalarTailSupply)
  (unionBound : UnionSupply)
  : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n)
      (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n),
      NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C →
      ∀ I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k,
      NearCubicGates.Close.Counter.Sampling.WitnessContract.LocalFailureBound p C I := by
  classical
  intro n p C hG I y hlive
  have hT : (0 : ℝ) < p.T := by exact_mod_cast hG.TPositive
  have hh : (64 : ℝ) * p.T ≤ p.h := by exact_mod_cast hG.height
  have hc := NearCubicGates.PublicSamplingRates.cap_bounds p.T p.h (p.ell0 C) hT hh
  have hcap : 0 < p.cap C := by
    change 0 < NearCubicGates.PublicSamplingRates.liveCap p.T p.h (p.ell0 C)
    linarith [hc.2.2.1]
  have hM : 0 < p.M C :=
    (NearCubicGates.PublicSamplingRates.denominator_bounds p.T p.h (p.ell0 C) hT hh).1
  letI : Nonempty (NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C)) :=
    ⟨fun _ => ⟨0, hM⟩⟩
  have hcard : Fintype.card (NearCubicGates.Close.Counter.Sampling.WitnessContract.Terms C) =
      NearCubicGates.Close.Counter.Sampling.WitnessContract.totalWeight C := by
    simp only [NearCubicGates.Close.Counter.Sampling.WitnessContract.Terms, Fintype.card_sigma,
      Fintype.card_fin, NearCubicGates.Close.Counter.Sampling.WitnessContract.totalWeight, NearCubicGates.Target.WeightedSymmetricCircuit.topWeight]
  letI : Nonempty (NearCubicGates.Close.Counter.Sampling.WitnessContract.Terms C) := by
    apply Fintype.card_pos_iff.mp
    rw [hcard]
    exact hG.weightPositive
  apply unionBound n p C hG I y
  intro r x j
  obtain ⟨hind, hzero, hmag, hvar, hsum⟩ := actualData n p C hG I y hlive r x j
  have hpi : 0 < p.pi C j.val :=
    (NearCubicGates.PublicSamplingRates.all_rates_bounded p.T p.h (p.ell0 C) hT hh j.val).1
  have hV : 0 ≤ ∑ u : NearCubicGates.Close.Counter.Sampling.WitnessContract.Terms C,
      NearCubicGates.FiniteAverages.mean
        (fun draw : NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C) =>
          (NearCubicGates.Close.Counter.Sampling.WitnessContract.Y p C I r y x j.val u draw) ^ 2) := by
    apply Finset.sum_nonneg
    intro u _
    unfold NearCubicGates.FiniteAverages.mean
    positivity
  obtain ⟨hspos, hsbound⟩ := scalarBounds p.T p.h (p.ell0 C) (p.pi C j.val)
    (∑ u : NearCubicGates.Close.Counter.Sampling.WitnessContract.Terms C,
      NearCubicGates.FiniteAverages.mean
        (fun draw : NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C) =>
          (NearCubicGates.Close.Counter.Sampling.WitnessContract.Y p C I r y x j.val u draw) ^ 2))
    hT (mul_nonneg hpi.le hcap.le) hV hvar
  have htail := hBernstein
    (NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C))
    (NearCubicGates.Close.Counter.Sampling.WitnessContract.Terms C)
    (NearCubicGates.Close.Counter.Sampling.WitnessContract.Y p C I r y x j.val)
    hind hzero hmag (p.fluctuation C j.val) hspos
  calc
    _ = NearCubicGates.FiniteAverages.mean
        (fun draw : NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C) =>
          NearCubicGates.PublishedSources.Witness.indicator
            (p.fluctuation C j.val ≤
              |∑ u : NearCubicGates.Close.Counter.Sampling.WitnessContract.Terms C,
                NearCubicGates.Close.Counter.Sampling.WitnessContract.Y p C I r y x j.val u draw|)) := by
      congr 1
      funext draw
      rw [hsum draw]
    _ ≤ _ := htail
    _ ≤ _ := hsbound

end NearCubicGates.Close.Counter.Sampling.WitnessFailure

namespace NearCubicGates.Close.Counter.Sampling.WitnessFailure

open scoped BigOperators
open FiniteAverages PublishedSources.Witness

theorem mean_sub {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a - g a) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

theorem mean_sum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] (f : A → B → ℝ) :
    mean (fun b => ∑ a, f a b) = ∑ a, mean (f a) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

/-- The literal uniform mean on the complete function type is a product mean. -/
theorem mean_product {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] (f : A → B → ℝ) :
    mean (fun draw : A → B => ∏ a, f a (draw a)) = ∏ a, mean (f a) := by
  classical
  unfold mean
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

theorem mean_coordinate {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [Nonempty B]
    (a : A) (f : B → ℝ) : mean (fun draw : A → B => f (draw a)) = mean f := by
  classical
  have h := mean_product (fun i b => if i = a then f b else 1)
  have hi (i : A) : mean (fun b : B => if i = a then f b else 1) =
      if i = a then mean f else 1 := by
    by_cases he : i = a <;> simp [he]
  simp_rw [hi] at h
  simpa using h

/-- Arbitrary real events factor because every variable uses only its own
coordinate of the same complete function-valued draw. -/
theorem independent_coordinates {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [Nonempty B]
    (F : A → B → ℝ) : finiteIndependent (fun a (draw : A → B) => F a (draw a)) := by
  classical
  intro S events
  let f (a : A) (b : B) : ℝ := if a ∈ S then indicator (F a b ∈ events a) else 1
  have hjoint (draw : A → B) :
      indicator (∀ a ∈ S, F a (draw a) ∈ events a) = ∏ a, f a (draw a) := by
    by_cases hall : ∀ a ∈ S, F a (draw a) ∈ events a
    · rw [indicator, if_pos hall]
      symm
      apply Finset.prod_eq_one
      intro a _
      by_cases ha : a ∈ S
      · simp [f, ha, indicator, hall a ha]
      · simp [f, ha]
    · rw [indicator, if_neg hall]
      push Not at hall
      obtain ⟨a, ha, hbad⟩ := hall
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      simp [f, ha, indicator, hbad]
  calc
    _ = mean (fun draw : A → B => ∏ a, f a (draw a)) := by
      congr 1
      funext draw
      exact hjoint draw
    _ = ∏ a, mean (f a) := mean_product f
    _ = ∏ a ∈ S, mean (fun draw : A → B => indicator (F a (draw a) ∈ events a)) := by
      have hi (a : A) : mean (f a) =
          if a ∈ S then mean (fun draw : A → B => indicator (F a (draw a) ∈ events a)) else 1 := by
        by_cases ha : a ∈ S
        · simp only [f, ha, if_true]
          exact (mean_coordinate a (fun b => indicator (F a b ∈ events a))).symm
        · simp [f, ha]
      simp_rw [hi]
      simp

/-- Counting the actual rational cutoff, including both endpoints a=0 and a=M. -/
theorem mean_cutoff (M a : ℕ) (ha : a ≤ M) :
    mean (fun b : Fin M => if b.val < a then (1 : ℝ) else 0) = (a : ℝ) / M := by
  classical
  let E : {b : Fin M // b.val < a} ≃ Fin a :=
    { toFun := fun b => ⟨b.val.val, b.property⟩
      invFun := fun b => ⟨⟨b.val, lt_of_lt_of_le b.isLt ha⟩, b.isLt⟩
      left_inv := by intro b; rfl
      right_inv := by intro b; rfl }
  have hc : Fintype.card {b : Fin M // b.val < a} = a := by
    simpa using Fintype.card_congr E
  have hs : (∑ b : Fin M, if b.val < a then (1 : ℝ) else 0) = a := by
    have hn : (∑ b : Fin M, if b.val < a then (1 : ℕ) else 0) = a := by
      simpa only [Fintype.card_subtype, Finset.card_filter] using hc
    exact_mod_cast hn
  unfold mean
  rw [hs, Fintype.card_fin]

theorem mean_centered_cutoff {A : Type*} [Fintype A] [DecidableEq A] (M a : ℕ) (hM : 0 < M)
    (ha : a ≤ M) (u : A) :
    mean (fun draw : A → Fin M =>
      (if (draw u).val < a then (1 : ℝ) else 0) - (a : ℝ) / M) = 0 := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  rw [mean_coordinate u (fun b : Fin M => (if b.val < a then (1 : ℝ) else 0) - (a : ℝ) / M),
    mean_sub, mean_cutoff M a ha, mean_const, sub_self]

theorem variance_centered_cutoff {A : Type*} [Fintype A] [DecidableEq A] (M a : ℕ) (hM : 0 < M)
    (ha : a ≤ M) (u : A) :
    mean (fun draw : A → Fin M =>
      ((if (draw u).val < a then (1 : ℝ) else 0) - (a : ℝ) / M) ^ 2) =
      (a : ℝ) / M * (1 - (a : ℝ) / M) := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  rw [mean_coordinate u (fun b : Fin M =>
    ((if b.val < a then (1 : ℝ) else 0) - (a : ℝ) / M) ^ 2)]
  have heq (b : Fin M) :
      ((if b.val < a then (1 : ℝ) else 0) - (a : ℝ) / M) ^ 2 =
      (1 - 2 * ((a : ℝ) / M)) * (if b.val < a then 1 else 0) + ((a : ℝ) / M) ^ 2 := by
    split_ifs <;> ring
  simp_rw [heq]
  rw [mean_add, mean_smul, mean_cutoff M a ha, mean_const]
  ring

end NearCubicGates.Close.Counter.Sampling.WitnessFailure

namespace NearCubicGates.Close.Counter.Sampling.WitnessFailure

open scoped BigOperators
open Target WitnessContract

/-- The compressed signed coefficient evaluates as the sum of its actual
absolute unit copies, using the same global draw in every role and stage. -/
theorem compressed_identity (n : ℕ) (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (draw : Samples C (p.M C)) :
    CompressedScoreIdentity p C draw := by
  classical
  intro r j z
  unfold sampledScore
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hneg : (C r).coefficient i < 0
  · simp [coefficient, GlobalSamplingWitness.sampledCoefficient,
      GlobalSamplingWitness.sampledCount, GlobalSamplingWitness.nestedKeep,
      sign, hneg]
  · simp [coefficient, GlobalSamplingWitness.sampledCoefficient,
      GlobalSamplingWitness.sampledCount, GlobalSamplingWitness.nestedKeep,
      sign, hneg]

end NearCubicGates.Close.Counter.Sampling.WitnessFailure

namespace NearCubicGates.Close.Counter.Sampling.WitnessFailure

open scoped BigOperators
open NearCubicWires Target WitnessContract FiniteAverages PublishedSources.Witness

noncomputable def amplitude {n k : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n)
    (I : Coordinates n k) (r : Fin 2) (y : Cells I) (x : Points I) (u : Terms C) : ℝ :=
  if u.1 = r then (sign C u : ℝ) *
    ((if ((C u.1).bottom u.2.1).eval (extend I y x) then (1 : ℝ) else 0) -
      (if ((C u.1).bottom u.2.1).eval (extend I y (reference I)) then (1 : ℝ) else 0))
  else 0

theorem Y_amplitude {n : ℕ} (p : PublicData n) (C : Fin 2 → WeightedSymmetricCircuit n)
    (I : Coordinates n p.k) (r : Fin 2) (y : Cells I) (x : Points I) (j : ℕ)
    (u : Terms C) (draw : Samples C (p.M C)) :
    Y p C I r y x j u draw = amplitude C I r y x u *
      ((if (draw u).val < p.cutoff C j then (1 : ℝ) else 0) - p.pi C j) := by
  unfold Y amplitude
  split_ifs <;> ring

theorem amplitude_abs {n k : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n)
    (I : Coordinates n k) (r : Fin 2) (y : Cells I) (x : Points I) (u : Terms C) :
    |amplitude C I r y x u| ≤ 1 := by
  unfold amplitude sign
  split_ifs <;>
    cases ((C u.1).bottom u.2.1).eval (extend I y x) <;>
    cases ((C u.1).bottom u.2.1).eval (extend I y (reference I)) <;> norm_num

private theorem extension_agrees {n k : ℕ} (I : Coordinates n k)
    (y : Cells I) (x : Points I) : cellAgrees ⟨I, y⟩ (extend I y x) := by
  intro i hi
  simp only [extend, dif_neg hi]

theorem amplitude_nonlive {n k : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n)
    (I : Coordinates n k) (r : Fin 2) (y : Cells I) (x : Points I) (u : Terms C)
    (hg : ¬ gateLive ((C u.1).bottom u.2.1) ⟨I, y⟩) :
    amplitude C I r y x u = 0 := by
  have heq : ((C u.1).bottom u.2.1).eval (extend I y x) =
      ((C u.1).bottom u.2.1).eval (extend I y (reference I)) := by
    by_contra hne
    exact hg ⟨extend I y x, extend I y (reference I),
      extension_agrees I y x, extension_agrees I y (reference I), hne⟩
  simp only [amplitude, heq, sub_self, mul_zero, ite_self]

theorem actual_independent {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (r : Fin 2) (y : Cells I) (x : Points I) (j : ℕ) (hM : 0 < p.M C) :
    finiteIndependent (Y p C I r y x j) := by
  classical
  letI : Nonempty (Fin (p.M C)) := ⟨⟨0, hM⟩⟩
  have heq : Y p C I r y x j = fun u draw => amplitude C I r y x u *
      ((if (draw u).val < p.cutoff C j then (1 : ℝ) else 0) - p.pi C j) := by
    funext u draw
    exact Y_amplitude p C I r y x j u draw
  rw [heq]
  exact independent_coordinates (A := Terms C) (B := Fin (p.M C))
    (fun (u : Terms C) (b : Fin (p.M C)) => amplitude C I r y x u *
    ((if b.val < p.cutoff C j then (1 : ℝ) else 0) - p.pi C j))

theorem actual_mean_zero {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (r : Fin 2) (y : Cells I) (x : Points I) (j : ℕ)
    (hM : 0 < p.M C) (ha : p.cutoff C j ≤ p.M C)
    (hpi : p.pi C j = (p.cutoff C j : ℝ) / p.M C) (u : Terms C) :
    mean (Y p C I r y x j u) = 0 := by
  classical
  have heq : Y p C I r y x j u = fun draw => amplitude C I r y x u *
      ((if (draw u).val < p.cutoff C j then (1 : ℝ) else 0) - p.pi C j) := by
    funext draw
    exact Y_amplitude p C I r y x j u draw
  rw [heq, mean_smul, hpi, mean_centered_cutoff (p.M C) (p.cutoff C j) hM ha u, mul_zero]

theorem actual_magnitude {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (r : Fin 2) (y : Cells I) (x : Points I) (j : ℕ)
    (hpi0 : 0 ≤ p.pi C j) (hpi1 : p.pi C j ≤ 1)
    (u : Terms C) (draw : Samples C (p.M C)) : |Y p C I r y x j u draw| ≤ 1 := by
  have hb : |(if (draw u).val < p.cutoff C j then (1 : ℝ) else 0) - p.pi C j| ≤ 1 := by
    apply abs_le.mpr
    split_ifs <;> constructor <;> linarith
  rw [Y_amplitude, abs_mul]
  simpa only [one_mul] using
    mul_le_mul (amplitude_abs C I r y x u) hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem actual_variance_copy {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (r : Fin 2) (y : Cells I) (x : Points I) (j : ℕ)
    (hM : 0 < p.M C) (ha : p.cutoff C j ≤ p.M C)
    (hpi : p.pi C j = (p.cutoff C j : ℝ) / p.M C)
    (hpi0 : 0 ≤ p.pi C j) (hpi1 : p.pi C j ≤ 1) (u : Terms C) :
    mean (fun draw : Samples C (p.M C) => (Y p C I r y x j u draw) ^ 2) ≤
      p.pi C j * indicator (gateLive ((C u.1).bottom u.2.1) ⟨I, y⟩) := by
  classical
  by_cases hg : gateLive ((C u.1).bottom u.2.1) ⟨I, y⟩
  · simp only [indicator, if_pos hg, mul_one]
    have hsq : amplitude C I r y x u ^ 2 ≤ 1 := by
      have hab := abs_le.mp (amplitude_abs C I r y x u)
      nlinarith [sq_nonneg (amplitude C I r y x u)]
    have heq : (fun draw : Samples C (p.M C) => (Y p C I r y x j u draw) ^ 2) =
        fun draw => amplitude C I r y x u ^ 2 *
          ((if (draw u).val < p.cutoff C j then (1 : ℝ) else 0) - p.pi C j) ^ 2 := by
      funext draw
      rw [Y_amplitude, mul_pow]
    rw [heq, mean_smul, hpi, variance_centered_cutoff (p.M C) (p.cutoff C j) hM ha u,
      ← hpi]
    calc
      _ ≤ 1 * (p.pi C j * (1 - p.pi C j)) :=
        mul_le_mul_of_nonneg_right hsq (mul_nonneg hpi0 (sub_nonneg.mpr hpi1))
      _ ≤ _ := by nlinarith [sq_nonneg (p.pi C j)]
  · simp only [indicator, if_neg hg, mul_zero]
    have heq : (fun draw : Samples C (p.M C) => (Y p C I r y x j u draw) ^ 2) =
        fun _ => (0 : ℝ) := by
      funext draw
      rw [Y_amplitude, amplitude_nonlive C I r y x u hg]
      simp
    simp [heq, mean]

theorem live_copy_census {n k : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n)
    (I : Coordinates n k) (y : Cells I) (pi : ℝ) :
    (∑ u : Terms C, pi * indicator (gateLive ((C u.1).bottom u.2.1) ⟨I, y⟩)) =
      pi * (liveWeight C I y : ℝ) := by
  classical
  have hweight : (liveWeight C I y : ℝ) = ∑ r, ∑ i : Fin (C r).bottomCount,
      if gateLive ((C r).bottom i) ⟨I, y⟩ then (((C r).coefficient i).natAbs : ℝ) else 0 := by
    simp [liveWeight]
  rw [hweight]
  simp_rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hg : gateLive ((C r).bottom i) ⟨I, y⟩ <;>
    simp [indicator, hg, mul_comm]

/-- The original integer score is the signed sum of its actual absolute copies. -/
theorem score_unitcopies {n : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n)
    (r : Fin 2) (z : BitInput n) :
    (C r).score z = ∑ u : GlobalSamplingWitness.UnitCopy (C r),
      sign C ⟨r, u⟩ * (if ((C r).bottom u.1).eval z then (1 : ℤ) else 0) := by
  classical
  unfold WeightedSymmetricCircuit.score
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hn : (C r).coefficient i < 0
  · simp [sign, hn, abs_of_neg hn]
  · simp [sign, hn, abs_of_nonneg (le_of_not_gt hn)]

theorem sum_Y_role {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (r : Fin 2) (y : Cells I) (x : Points I) (j : ℕ) (draw : Samples C (p.M C)) :
    (∑ u : Terms C, Y p C I r y x j u draw) =
      ∑ u : GlobalSamplingWitness.UnitCopy (C r),
        ((if (draw ⟨r, u⟩).val < p.cutoff C j then (1 : ℝ) else 0) - p.pi C j) *
          (sign C ⟨r, u⟩ : ℝ) *
          ((if ((C r).bottom u.1).eval (extend I y x) then (1 : ℝ) else 0) -
            (if ((C r).bottom u.1).eval (extend I y (reference I)) then (1 : ℝ) else 0)) := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single r]
  · simp [Y]
  · intro a _ har
    simp [Y, har]
  · simp

/-- Compression and centering give the actual error, with the same draw
appearing in both scores and all stages. -/
theorem actual_error_identity {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (r : Fin 2) (y : Cells I) (x : Points I) (j : Fin p.s) (draw : Samples C (p.M C)) :
    error p C I r y x j.val draw = ∑ u : Terms C, Y p C I r y x j.val u draw := by
  classical
  have hsample (z : BitInput n) : (sampledScore p C draw r j.val z : ℝ) =
      ∑ u : GlobalSamplingWitness.UnitCopy (C r),
        (if (draw ⟨r, u⟩).val < p.cutoff C j.val then (1 : ℝ) else 0) *
          (sign C ⟨r, u⟩ : ℝ) * (if ((C r).bottom u.1).eval z then 1 else 0) := by
    exact_mod_cast compressed_identity n p C draw r j z
  have hscore (z : BitInput n) : ((C r).score z : ℝ) =
      ∑ u : GlobalSamplingWitness.UnitCopy (C r),
        (sign C ⟨r, u⟩ : ℝ) * (if ((C r).bottom u.1).eval z then 1 else 0) := by
    exact_mod_cast score_unitcopies C r z
  change (((sampledScore p C draw r j.val (extend I y x) -
      sampledScore p C draw r j.val (extend I y (reference I))) : ℤ) : ℝ) -
      p.pi C j.val * ((((C r).score (extend I y x) -
        (C r).score (extend I y (reference I))) : ℤ) : ℝ) = _
  simp only [Int.cast_sub]
  rw [hsample, hsample, hscore, hscore, sum_Y_role]
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- All literal reviewed-Bernstein inputs for the actual finite common draw. -/
theorem actual_data : ActualDataSupply := by
  classical
  intro n p C hG I y hlive r x j
  have hT : (0 : ℝ) < p.T := by exact_mod_cast hG.TPositive
  have hh : (64 : ℝ) * p.T ≤ p.h := by exact_mod_cast hG.height
  have hM : 0 < p.M C :=
    (PublicSamplingRates.denominator_bounds p.T p.h (p.ell0 C) hT hh).1
  have ha : p.cutoff C j.val ≤ p.M C :=
    PublicSamplingRates.product_fits_denominator p.T p.h (p.ell0 C) hT hh j.val
  have hpi : p.pi C j.val = (p.cutoff C j.val : ℝ) / p.M C :=
    PublicSamplingRates.rate_is_rational_product p.T p.h (p.ell0 C) hT hh j.val
  have hb : 0 < p.pi C j.val ∧ p.pi C j.val ≤ 1 :=
    PublicSamplingRates.all_rates_bounded p.T p.h (p.ell0 C) hT hh j.val
  have hweight : (liveWeight C I y : ℝ) ≤ p.ell0 C := by
    simpa only [live, decide_eq_true_eq] using hlive
  have hcap : (p.ell0 C : ℝ) ≤ p.cap C :=
    (PublicSamplingRates.cap_bounds p.T p.h (p.ell0 C) hT hh).2.1
  refine ⟨actual_independent p C I r y x j.val hM,
    actual_mean_zero p C I r y x j.val hM ha hpi,
    actual_magnitude p C I r y x j.val hb.1.le hb.2, ?_,
    actual_error_identity p C I r y x j⟩
  calc
    _ ≤ ∑ u : Terms C, p.pi C j.val * indicator (gateLive ((C u.1).bottom u.2.1) ⟨I, y⟩) := by
      exact Finset.sum_le_sum (fun u _ => actual_variance_copy p C I r y x j.val
        hM ha hpi hb.1.le hb.2 u)
    _ = p.pi C j.val * (liveWeight C I y : ℝ) := live_copy_census C I y _
    _ ≤ p.pi C j.val * (p.ell0 C : ℝ) := mul_le_mul_of_nonneg_left hweight hb.1.le
    _ ≤ p.pi C j.val * p.cap C := mul_le_mul_of_nonneg_left hcap hb.1.le

end NearCubicGates.Close.Counter.Sampling.WitnessFailure

namespace NearCubicGates.Close.Counter.Sampling.WitnessFailure

/-- The exact public fluctuation implies the literal reviewed Bernstein tail. -/
theorem scalar_tail : ScalarTailSupply := by
  intro T h ell pi V hT hU hV hVU
  let a := Real.sqrt (2 * T * pi * PublicSamplingRates.liveCap T h ell)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * T * (pi * PublicSamplingRates.liveCap T h ell) := by
    dsimp [a]
    rw [Real.sq_sqrt (by nlinarith [mul_nonneg hT.le hU])]
    ring
  have hs : 0 < PublicSamplingRates.fluctuation T h ell pi := by
    change 0 < a + 2 * T / 3
    linarith
  refine ⟨hs, ?_⟩
  have hsq : 2 * T * (V + PublicSamplingRates.fluctuation T h ell pi / 3) ≤
      PublicSamplingRates.fluctuation T h ell pi ^ 2 := by
    change 2 * T * (V + (a + 2 * T / 3) / 3) ≤ (a + 2 * T / 3) ^ 2
    nlinarith [mul_nonneg hT.le ha, mul_le_mul_of_nonneg_left hVU hT.le]
  have hd : 0 < 2 * (V + PublicSamplingRates.fluctuation T h ell pi / 3) := by
    positivity
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hd).mpr
  nlinarith

end NearCubicGates.Close.Counter.Sampling.WitnessFailure

namespace NearCubicGates.Close.Counter.Sampling.WitnessFailure

open scoped BigOperators
open Target WitnessContract FiniteAverages PublishedSources.Witness

private theorem indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  classical
  unfold indicator
  split_ifs <;> norm_num

theorem exponential_decay (T : ℕ) : Real.exp (-(T : ℝ)) ≤ 1 / (2 : ℝ) ^ T := by
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  have hp : (2 : ℝ) ^ T ≤ Real.exp (T : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ T := pow_le_pow_left₀ (by norm_num) hbase T
      _ = Real.exp (T : ℝ) := by rw [← Real.exp_nat_mul]; simp
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) hp

/-- The test census is exactly two roles, 2^k points and s=Jlean+1 stages.
No union over independent stage draws is used. -/
theorem union_bound : UnionSupply := by
  classical
  intro n p C hG I y htail
  let Tests := Fin 2 × Points I × Fin p.s
  let event (t : Tests) (draw : Samples C (p.M C)) : ℝ :=
    indicator (p.fluctuation C t.2.2.val ≤ |error p C I t.1 y t.2.1 t.2.2.val draw|)
  have hpoint (draw : Samples C (p.M C)) :
      GlobalSamplingWitness.failure (good p C I draw y) ≤ ∑ t : Tests, event t draw := by
    by_cases hg : good p C I draw y = true
    · rw [hg]
      change 0 ≤ ∑ t : Tests, event t draw
      exact Finset.sum_nonneg (fun t _ => indicator_nonneg _)
    · have hbad : ¬ ∀ (r : Fin 2) (x : Points I) (j : Fin p.s),
          |error p C I r y x j.val draw| ≤ p.fluctuation C j.val := by
        intro hh
        exact hg (by simpa only [good, decide_eq_true_eq] using hh)
      push Not at hbad
      obtain ⟨r, x, j, hj⟩ := hbad
      have he : event (r, x, j) draw = 1 := by
        simp only [event, indicator, if_pos hj.le]
      have hf : GlobalSamplingWitness.failure (good p C I draw y) = 1 := by
        cases heq : good p C I draw y <;> simp_all [GlobalSamplingWitness.failure]
      rw [hf, ← he]
      have hn (t : Tests) : 0 ≤ event t draw := indicator_nonneg _
      exact Finset.single_le_sum (fun t _ => hn t) (Finset.mem_univ (r, x, j))
  have hpoints : Fintype.card (Points I) = 2 ^ p.k := by
    simp [Points, Fintype.card_pi, I.property]
  have hcard : Fintype.card Tests = 2 * 2 ^ p.k * p.s := by
    simp [Tests, Fintype.card_prod, hpoints, Nat.mul_assoc]
  have hsum : mean (fun draw : Samples C (p.M C) =>
      GlobalSamplingWitness.failure (good p C I draw y)) ≤
      (4 * (p.s : ℝ) * 2 ^ p.k) * Real.exp (-(p.T : ℝ)) := by
    calc
      _ ≤ mean (fun draw : Samples C (p.M C) => ∑ t : Tests, event t draw) :=
        mean_le_mean _ _ hpoint
      _ = ∑ t : Tests, mean (event t) := mean_sum event
      _ ≤ ∑ _t : Tests, 2 * Real.exp (-(p.T : ℝ)) := by
        exact Finset.sum_le_sum (fun t _ => htail t.1 t.2.1 t.2.2)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
          Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]; ring
  have hstage : (p.s : ℝ) ≤ p.Jmax := by exact_mod_cast hG.stageCap
  have hweight : (4 * (p.s : ℝ) * 2 ^ p.k) ≤
      ((4 * p.Jmax * 2 ^ p.k : ℕ) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstage (by norm_num))
      (by positivity)
  have hguard : ((4 * p.Jmax * 2 ^ p.k : ℕ) : ℝ) / (2 : ℝ) ^ p.T ≤ p.beta := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ p.T)).mpr
    simpa only [mul_comm] using hG.TGuard
  calc
    _ ≤ _ := hsum
    _ ≤ (4 * (p.s : ℝ) * 2 ^ p.k) * (1 / (2 : ℝ) ^ p.T) :=
      mul_le_mul_of_nonneg_left (exponential_decay p.T) (by positivity)
    _ = (4 * (p.s : ℝ) * 2 ^ p.k) / (2 : ℝ) ^ p.T := by ring
    _ ≤ ((4 * p.Jmax * 2 ^ p.k : ℕ) : ℝ) / (2 : ℝ) ^ p.T :=
      div_le_div_of_nonneg_right hweight (by positivity)
    _ ≤ _ := hguard

end NearCubicGates.Close.Counter.Sampling.WitnessFailure

namespace NearCubicGates.Close.Counter.Sampling.StandaloneSupply

def SamplingSupply : Prop :=
  ∀ n : ℕ, ∀ p : WitnessContract.PublicData n,
    ∀ C : Fin 2 → Target.WeightedSymmetricCircuit n,
      WitnessContract.PublicGuards p C → WitnessContract.SamplingParent p C

theorem fixedIAdapters
  (centralBound : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → (((p.k * Nat.choose (n - p.k) ((n - p.k) / 2) : ℕ) : ℝ) / (2 : ℝ) ^ (n - p.k)) ≤ (p.k : ℝ) / (p.R0 : ℝ))
  (weightedExpectation : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → NearCubicGates.FiniteAverages.mean (fun I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k => NearCubicGates.FiniteAverages.mean (fun y : NearCubicGates.Close.Counter.Sampling.WitnessContract.Cells I => (NearCubicGates.Close.Counter.Sampling.WitnessContract.liveWeight C I y : ℝ))) ≤ (NearCubicGates.Close.Counter.Sampling.WitnessContract.totalWeight C : ℝ) * (((p.k * Nat.choose (n - p.k) ((n - p.k) / 2) : ℕ) : ℝ) / (2 : ℝ) ^ (n - p.k)))
  (cellMarkov : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → ∀ I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k, NearCubicGates.FiniteAverages.mean (fun y : NearCubicGates.Close.Counter.Sampling.WitnessContract.Cells I => (NearCubicGates.Close.Counter.Sampling.WitnessContract.liveWeight C I y : ℝ)) ≤ (p.beta : ℝ) * (p.ell0 C : ℝ) → NearCubicGates.Close.Counter.Sampling.WitnessContract.LiveBound p C I)
  : (∀ (n : Nat) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n)
  (C :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      NearCubicGates.Target.WeightedSymmetricCircuit n),
  @NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards n p C → ∃ I, @NearCubicGates.Close.Counter.Sampling.WitnessContract.LiveBound n p C I) :=
  by
    classical
    intro n p C hG
    obtain ⟨I0, _hsubset, hcard⟩ := Finset.exists_subset_card_eq
      (show p.k ≤ (Finset.univ : Finset (Fin n)).card by simpa using hG.kBelowN.le)
    letI : Nonempty (NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k) := ⟨⟨I0, hcard⟩⟩
    obtain ⟨I, hI⟩ := NearCubicGates.FiniteAverages.exists_le_mean
      (fun I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k =>
        NearCubicGates.FiniteAverages.mean
          (fun y : NearCubicGates.Close.Counter.Sampling.WitnessContract.Cells I =>
            (NearCubicGates.Close.Counter.Sampling.WitnessContract.liveWeight C I y : ℝ)))
    have hbeta : (0 : ℝ) < p.beta := by exact_mod_cast hG.betaPositive
    have hRnat : p.R0 ≠ 0 := by
      intro hz
      have hn : n - p.k + 1 = 0 := Nat.sqrt_eq_zero.mp hz
      omega
    have hR : (p.R0 : ℝ) ≠ 0 := by exact_mod_cast hRnat
    have hell : (p.beta : ℝ) * (p.ell0 C : ℝ) =
        (NearCubicGates.Close.Counter.Sampling.WitnessContract.totalWeight C : ℝ) * (p.k : ℝ) / (p.R0 : ℝ) := by
      unfold NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData.ell0
      push_cast
      field_simp
    refine ⟨I, cellMarkov n p C hG I ?_⟩
    rw [hell]
    calc
      _ ≤ _ := hI
      _ ≤ _ := weightedExpectation n p C hG
      _ ≤ (NearCubicGates.Close.Counter.Sampling.WitnessContract.totalWeight C : ℝ) *
          ((p.k : ℝ) / (p.R0 : ℝ)) :=
        mul_le_mul_of_nonneg_left (centralBound n p C hG) (Nat.cast_nonneg _)
      _ = _ := by ring

theorem momentAdapters
  (liveScore : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → ∀ (I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k) (y : NearCubicGates.Close.Counter.Sampling.WitnessContract.Cells I), NearCubicGates.Close.Counter.Sampling.WitnessContract.live p C I y = true → ∀ (r : Fin 2) (x : NearCubicGates.Close.Counter.Sampling.WitnessContract.Points I), |NearCubicGates.SampledChainMoments.scoreDelta (NearCubicGates.Close.Counter.Sampling.WitnessContract.score C I r y) (NearCubicGates.Close.Counter.Sampling.WitnessContract.reference I) x| ≤ p.cap C)
  (digitMargin : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → Real.sqrt 2 * ((p.h : ℝ) / 2) < (p.hE : ℝ))
  (terminalBound : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → ∀ (I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k) (draw : NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C)) (y : NearCubicGates.Close.Counter.Sampling.WitnessContract.Cells I), NearCubicGates.Close.Counter.Sampling.WitnessContract.good p C I draw y = true → ∀ (r : Fin 2) (x : NearCubicGates.Close.Counter.Sampling.WitnessContract.Points I), (((NearCubicGates.CertifiedScoreSupport.phi (p.M C) (p.A C) (NearCubicGates.Close.Counter.Sampling.WitnessContract.values p C I draw r y) (NearCubicGates.Close.Counter.Sampling.WitnessContract.score C I r y) p.Jlean x - NearCubicGates.CertifiedScoreSupport.phi (p.M C) (p.A C) (NearCubicGates.Close.Counter.Sampling.WitnessContract.values p C I draw r y) (NearCubicGates.Close.Counter.Sampling.WitnessContract.score C I r y) p.Jlean (NearCubicGates.Close.Counter.Sampling.WitnessContract.reference I)).natAbs : ℕ) : ℝ) ≤ (p.A C : ℝ) * (86 * (p.T : ℝ) * p.cap C / (p.h : ℝ)))
  (terminalMargin : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → Real.sqrt 2 * ((p.A C : ℝ) * (86 * (p.T : ℝ) * p.cap C / (p.h : ℝ))) < (p.Lambda C : ℝ))
  : (∀ (n : Nat) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n)
  (C :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      NearCubicGates.Target.WeightedSymmetricCircuit n),
  @NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards n p C →
    ∀ (I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n (@NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData.k n p)),
      @NearCubicGates.Close.Counter.Sampling.WitnessContract.GoodImpliesPass n p C I) :=
  by
    classical
    intro n p C hG I draw y hlive hgood
    have hT : (0 : ℝ) < p.T := by exact_mod_cast hG.TPositive
    have hheight : (64 : ℝ) * p.T ≤ p.h := by exact_mod_cast hG.height
    have hg : ∀ (r : Fin 2) (x : NearCubicGates.Close.Counter.Sampling.WitnessContract.Points I)
        (j : Fin p.s), |NearCubicGates.Close.Counter.Sampling.WitnessContract.error p C I r y x j.val draw| ≤
          p.fluctuation C j.val := by
      simpa only [NearCubicGates.Close.Counter.Sampling.WitnessContract.good, decide_eq_true_eq] using hgood
    have hcard : Fintype.card (NearCubicGates.Close.Counter.Sampling.WitnessContract.Points I) ≤ 2 ^ p.k := by
      simp only [NearCubicGates.Close.Counter.Sampling.WitnessContract.Points, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_coe]
      rw [I.property]
    simp only [NearCubicGates.Close.Counter.Sampling.WitnessContract.passesLiteralMoments, decide_eq_true_eq]
    constructor
    · intro r j
      apply NearCubicGates.CountingCore.finite_integer_moment_complete
        p.k hG.kPositive _ p.hE ((p.h : ℝ) / 2) hcard (by positivity) _
        (digitMargin n p C hG)
      intro x
      have hd := NearCubicGates.SampledChainMoments.good_chain_digits_small
        p.T p.h (p.ell0 C) hT hheight
        (NearCubicGates.Close.Counter.Sampling.WitnessContract.values p C I draw r y)
        (NearCubicGates.Close.Counter.Sampling.WitnessContract.score C I r y)
        (NearCubicGates.Close.Counter.Sampling.WitnessContract.reference I) x p.Jlean
        hG.active (liveScore n p C hG I y hlive r x)
        (fun a ha => hg r x ⟨a, by change a < p.Jlean + 1; omega⟩)
        j.val (by have hj := j.isLt; change j.val < p.Jlean + 1 at hj; omega)
      have hf : p.factor C = fun i =>
          (NearCubicGates.NestedRateChain.factor
            (NearCubicGates.NestedRateChain.rateRatio
              (NearCubicGates.PublicSamplingRates.initialRatio p.T p.h (p.ell0 C)) i) : ℤ) := rfl
      rw [hf]
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hd
    · intro r
      have hb := terminalBound n p C hG I draw y hgood r
      have hR : 0 ≤ (p.A C : ℝ) * (86 * (p.T : ℝ) * p.cap C / (p.h : ℝ)) := by
        have href := hb (NearCubicGates.Close.Counter.Sampling.WitnessContract.reference I)
        simpa only [sub_self, Int.natAbs_zero, Nat.cast_zero] using href
      exact NearCubicGates.CountingCore.finite_integer_moment_complete
        p.k hG.kPositive _ (p.Lambda C)
        ((p.A C : ℝ) * (86 * (p.T : ℝ) * p.cap C / (p.h : ℝ)))
        hcard hR hb (terminalMargin n p C hG)

theorem compressionAdapters
  (compressed : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), ∀ draw : NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C), NearCubicGates.Close.Counter.Sampling.WitnessContract.CompressedScoreIdentity p C draw)
  (prefixBound : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PrefixBound p C)
  : (∀ (n : Nat) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n)
  (C :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      NearCubicGates.Target.WeightedSymmetricCircuit n),
  @NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards n p C →
    ∀ (draw : @NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples n C (@NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData.M n p C)),
      And (@NearCubicGates.Close.Counter.Sampling.WitnessContract.BoundedCoefficients n p C draw)
        (And (@NearCubicGates.Close.Counter.Sampling.WitnessContract.CompressedScoreIdentity n p C draw)
          (@NearCubicGates.Close.Counter.Sampling.WitnessContract.PrefixBound n p C))) :=
  by
    intro n p C _hG draw
    refine ⟨?_, compressed n p C draw, prefixBound n p C⟩
    intro r j i
    exact NearCubicGates.GlobalSamplingWitness.sampledCoefficient_witness_range (C r)
      (NearCubicGates.GlobalSamplingWitness.nestedKeep (C r)
        (fun u => draw ⟨r, u⟩) (p.cutoff C j.val)) i

theorem samplingAdapters
    (fixed_I : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → ∃ I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k, NearCubicGates.Close.Counter.Sampling.WitnessContract.LiveBound p C I)
    (local_failure : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → ∀ I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k, NearCubicGates.Close.Counter.Sampling.WitnessContract.LocalFailureBound p C I)
    (moments : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → ∀ I : NearCubicGates.Close.Counter.Sampling.WitnessContract.Coordinates n p.k, NearCubicGates.Close.Counter.Sampling.WitnessContract.GoodImpliesPass p C I)
    (compression : ∀ (n : ℕ) (p : NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicData n) (C : Fin 2 → NearCubicGates.Target.WeightedSymmetricCircuit n), NearCubicGates.Close.Counter.Sampling.WitnessContract.PublicGuards p C → ∀ draw : NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C), NearCubicGates.Close.Counter.Sampling.WitnessContract.BoundedCoefficients p C draw ∧ NearCubicGates.Close.Counter.Sampling.WitnessContract.CompressedScoreIdentity p C draw ∧ NearCubicGates.Close.Counter.Sampling.WitnessContract.PrefixBound p C)
    : SamplingSupply :=
  by
    classical
    intro n p C hG
    have hT : (0 : ℝ) < p.T := by exact_mod_cast hG.TPositive
    have hheight : (64 : ℝ) * p.T ≤ p.h := by exact_mod_cast hG.height
    have hM : 0 < p.M C :=
      (NearCubicGates.PublicSamplingRates.denominator_bounds
        p.T p.h (p.ell0 C) hT hheight).1
    letI : Nonempty (NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C)) :=
      ⟨fun _ => ⟨0, hM⟩⟩
    obtain ⟨I, hlive⟩ := fixed_I n p C hG
    have hlocal := local_failure n p C hG I
    have hbeta : (0 : ℝ) ≤ p.beta := by exact_mod_cast hG.betaPositive.le
    obtain ⟨draw, hdraw⟩ :=
      NearCubicGates.GlobalSamplingWitness.global_useful_witness
        (Cells := NearCubicGates.Close.Counter.Sampling.WitnessContract.Cells I)
        (Samples := NearCubicGates.Close.Counter.Sampling.WitnessContract.Samples C (p.M C))
        (NearCubicGates.Close.Counter.Sampling.WitnessContract.live p C I)
        (NearCubicGates.Close.Counter.Sampling.WitnessContract.good p C I)
        (p.beta : ℝ) hbeta hlive hlocal
    obtain ⟨hcoef, hid, hprefix⟩ := compression n p C hG draw
    refine ⟨I, draw, hcoef, hid, hprefix, ?_⟩
    have hpoint : ∀ y : NearCubicGates.Close.Counter.Sampling.WitnessContract.Cells I,
        NearCubicGates.GlobalSamplingWitness.failure
          (NearCubicGates.Close.Counter.Sampling.WitnessContract.passesLiteralMoments p C I draw y) ≤
        NearCubicGates.GlobalSamplingWitness.failure
          (NearCubicGates.Close.Counter.Sampling.WitnessContract.live p C I y &&
            NearCubicGates.Close.Counter.Sampling.WitnessContract.good p C I draw y) := by
      intro y
      cases hl : NearCubicGates.Close.Counter.Sampling.WitnessContract.live p C I y <;>
        cases hg : NearCubicGates.Close.Counter.Sampling.WitnessContract.good p C I draw y
      · cases hp : NearCubicGates.Close.Counter.Sampling.WitnessContract.passesLiteralMoments p C I draw y <;>
          norm_num [NearCubicGates.GlobalSamplingWitness.failure]
      · cases hp : NearCubicGates.Close.Counter.Sampling.WitnessContract.passesLiteralMoments p C I draw y <;>
          norm_num [NearCubicGates.GlobalSamplingWitness.failure]
      · cases hp : NearCubicGates.Close.Counter.Sampling.WitnessContract.passesLiteralMoments p C I draw y <;>
          norm_num [NearCubicGates.GlobalSamplingWitness.failure]
      · have hp := moments n p C hG I draw y hl hg
        rw [hp]
        norm_num [NearCubicGates.GlobalSamplingWitness.failure]
    apply le_trans ?_ hdraw
    exact div_le_div_of_nonneg_right
      (NearCubicGates.FiniteAverages.mean_le_mean _ _ hpoint) (by norm_num)

theorem samplingSupply
    (hRestriction : PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction)
    (hBernstein : PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0}) :
    SamplingSupply := by
  exact samplingAdapters
    (fixedIAdapters WitnessFixedI.central_bound
      (WitnessFixedI.weighted_expectation hRestriction) WitnessFixedI.cell_markov)
    (WitnessFailure.enclose hBernstein WitnessFailure.actual_data
      WitnessFailure.scalar_tail WitnessFailure.union_bound)
    (momentAdapters WitnessMoments.live_score WitnessMoments.digit_margin
      WitnessMoments.terminal_bound WitnessMoments.terminal_margin)
    (compressionAdapters WitnessCompression.compressed_identity WitnessCompression.prefix_bound)

end NearCubicGates.Close.Counter.Sampling.StandaloneSupply
