import Proof.Gates.PublishedSources.Witness
import Proof.Gates.GlobalSamplingWitness
import Proof.Gates.SampledChainMoments
import Proof.Gates.MomentCompleteness
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Choose.Central
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Nat.Log

/-!
# Counter module 4/9 — Sampling port, parts 1–2: the sampling contract, lem:live, the moment adapters, compression
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter.Sampling.WitnessContract

open scoped BigOperators
open NearCubicWires Target FiniteAverages

structure PublicData (n : ℕ) where
  beta : ℚ
  precisionExponent : ℕ
  cT : ℕ
  T : ℕ
  P : ℕ
  Lw : ℕ
  Jlean : ℕ

def PublicData.Jmax {n : ℕ} (_p : PublicData n) : ℕ := mu n + 1
def PublicData.k {n : ℕ} (p : PublicData n) : ℕ :=
  (2 * p.Jmax + p.cT + mu n) * lambda n
def PublicData.s {n : ℕ} (p : PublicData n) : ℕ := p.Jlean + 1
def PublicData.hE {n : ℕ} (p : PublicData n) : ℕ := p.P / 4
def PublicData.h {n : ℕ} (p : PublicData n) : ℕ := Nat.sqrt (2 * p.hE ^ 2)
def PublicData.R0 {n : ℕ} (p : PublicData n) : ℕ := Nat.sqrt (n - p.k + 1)

def totalWeight {n : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n) : ℕ :=
  ∑ r, (C r).topWeight

def PublicData.ell0 {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) : ℚ :=
  ((totalWeight C * p.k : ℕ) : ℚ) / (p.beta * p.R0)

noncomputable def PublicData.cap {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) : ℝ :=
  PublicSamplingRates.liveCap p.T p.h (p.ell0 C)
noncomputable def PublicData.M {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) : ℕ :=
  PublicSamplingRates.denominator p.T p.h (p.ell0 C)
noncomputable def PublicData.x0 {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) : ℝ :=
  PublicSamplingRates.initialRatio p.T p.h (p.ell0 C)
noncomputable def PublicData.cutoff {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (j : ℕ) : ℕ :=
  NestedRateChain.product (p.x0 C) j
noncomputable def PublicData.pi {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (j : ℕ) : ℝ :=
  PublicSamplingRates.rate p.T p.h (p.ell0 C) j
noncomputable def PublicData.factor {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (j : ℕ) : ℤ :=
  (NestedRateChain.factor (NestedRateChain.rateRatio (p.x0 C) j) : ℤ)
noncomputable def PublicData.A {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) : ℕ := p.cutoff C p.Jlean
noncomputable def PublicData.Lambda {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) : ℕ :=
  (p.Lw - 1) * p.A C / 2 + 1
noncomputable def PublicData.fluctuation {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (j : ℕ) : ℝ :=
  PublicSamplingRates.fluctuation p.T p.h (p.ell0 C) (p.pi C j)

/-- Only numerical/public chain guards. No hlive, local concentration,
sampling independence, moment passing or implementation premise is a field. -/
structure PublicGuards {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) : Prop where
  nLarge : 4 ≤ n
  weightPositive : 0 < totalWeight C
  normalizedWeight : totalWeight C ≤ 2 * n ^ 4
  precisionPositive : 0 < p.precisionExponent
  betaPositive : 0 < p.beta
  betaLower : (1 : ℚ) / (n : ℚ) ^ p.precisionExponent ≤ p.beta
  betaUpper : p.beta ≤ 1 / 16
  cTPositive : 0 < p.cT
  kPositive : 1 ≤ p.k
  kBelowN : p.k < n
  TPositive : 0 < p.T
  TGuard : ((4 * p.Jmax * 2 ^ p.k : ℕ) : ℝ) ≤ (2 : ℝ) ^ p.T * (p.beta : ℝ)
  TMinimal : ∀ t : ℕ, t < p.T →
    (2 : ℝ) ^ t * (p.beta : ℝ) < ((4 * p.Jmax * 2 ^ p.k : ℕ) : ℝ)
  PMinimum : 100 ≤ p.P
  PBelowN : p.P ≤ n
  height : 64 * p.T ≤ p.h
  stageCap : p.s ≤ p.Jmax
  stopped : (1 : ℝ) / 256 ≤ NestedRateChain.rateRatio (p.x0 C) p.Jlean
  active : ∀ j : ℕ, j < p.Jlean →
    NestedRateChain.rateRatio (p.x0 C) j < (1 : ℝ) / 256
  windowSize : 2 ≤ p.Lw
  usefulWindow : 244 * (p.T : ℝ) * p.cap C / (p.h : ℝ) < (p.Lw : ℝ) - 1

abbrev Coordinates (n k : ℕ) := {I : Finset (Fin n) // I.card = k}
abbrev Cells {n k : ℕ} (I : Coordinates n k) := {i : Fin n // i ∉ I.val} → Bool
abbrev Points {n k : ℕ} (I : Coordinates n k) := {i : Fin n // i ∈ I.val} → Bool
abbrev Terms {n : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n) :=
  Σ r : Fin 2, GlobalSamplingWitness.UnitCopy (C r)
abbrev Samples {n : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n) (M : ℕ) :=
  Terms C → Fin M

def extend {n k : ℕ} (I : Coordinates n k) (y : Cells I) (x : Points I) : BitInput n :=
  fun i => if hi : i ∈ I.val then x ⟨i, hi⟩ else y ⟨i, hi⟩
def reference {n k : ℕ} (I : Coordinates n k) : Points I := fun _ => false

noncomputable def liveWeight {n k : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n)
    (I : Coordinates n k) (y : Cells I) : ℕ := by
  classical
  exact ∑ r, ∑ i : Fin (C r).bottomCount,
    if PublishedSources.Witness.gateLive ((C r).bottom i) ⟨I, y⟩
    then ((C r).coefficient i).natAbs else 0

noncomputable def live {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k) (y : Cells I) : Bool :=
  decide ((liveWeight C I y : ℝ) ≤ (p.ell0 C : ℝ))

def sign {n : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n) (u : Terms C) : ℤ :=
  if (C u.1).coefficient u.2.1 < 0 then -1 else 1

noncomputable def coefficient {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (draw : Samples C (p.M C))
    (r : Fin 2) (j : ℕ) (i : Fin (C r).bottomCount) : ℤ :=
  GlobalSamplingWitness.sampledCoefficient (C r)
    (GlobalSamplingWitness.nestedKeep (C r) (fun u => draw ⟨r, u⟩) (p.cutoff C j)) i

noncomputable def sampledScore {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (draw : Samples C (p.M C))
    (r : Fin 2) (j : ℕ) (z : BitInput n) : ℤ :=
  ∑ i, coefficient p C draw r j i * (if ((C r).bottom i).eval z then 1 else 0)

noncomputable def values {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (draw : Samples C (p.M C)) (r : Fin 2) (y : Cells I) : Points I → ℕ → ℤ :=
  fun x j => sampledScore p C draw r j (extend I y x)

noncomputable def score {n : ℕ} (C : Fin 2 → WeightedSymmetricCircuit n)
    {k : ℕ} (I : Coordinates n k) (r : Fin 2) (y : Cells I) : Points I → ℤ :=
  fun x => (C r).score (extend I y x)

noncomputable def error {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (r : Fin 2) (y : Cells I) (x : Points I) (j : ℕ)
    (draw : Samples C (p.M C)) : ℝ :=
  SampledChainMoments.delta (values p C I draw r y) (reference I) x j -
    p.pi C j * SampledChainMoments.scoreDelta (score C I r y) (reference I) x

/-- Actual centered summands, including zero summands outside the selected
role. Every term depends only on its own coordinate in the ONE common draw. -/
noncomputable def Y {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (r : Fin 2) (y : Cells I) (x : Points I) (j : ℕ)
    (u : Terms C) (draw : Samples C (p.M C)) : ℝ :=
  if u.1 = r then
    ((if (draw u).val < p.cutoff C j then (1 : ℝ) else 0) - p.pi C j) *
      (sign C u : ℝ) *
      ((if ((C u.1).bottom u.2.1).eval (extend I y x) then (1 : ℝ) else 0) -
        (if ((C u.1).bottom u.2.1).eval (extend I y (reference I)) then (1 : ℝ) else 0))
  else 0

noncomputable def good {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (draw : Samples C (p.M C)) (y : Cells I) : Bool := by
  classical
  exact decide (∀ (r : Fin 2) (x : Points I) (j : Fin p.s),
    |error p C I r y x j.val draw| ≤ p.fluctuation C j.val)

noncomputable def digitMoment {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (draw : Samples C (p.M C)) (r : Fin 2) (y : Cells I) (j : Fin p.s) : ℤ :=
  ∑ x : Points I,
    (CountingCore.proposedDigit (p.factor C) (values p C I draw r y x) j.val -
      CountingCore.proposedDigit (p.factor C) (values p C I draw r y (reference I)) j.val) ^
        (2 * p.k)

noncomputable def phiMoment {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (draw : Samples C (p.M C)) (r : Fin 2) (y : Cells I) : ℤ :=
  ∑ x : Points I,
    (CertifiedScoreSupport.phi (p.M C) (p.A C)
        (values p C I draw r y) (score C I r y) p.Jlean x -
      CertifiedScoreSupport.phi (p.M C) (p.A C)
        (values p C I draw r y) (score C I r y) p.Jlean (reference I)) ^ (2 * p.k)

noncomputable def passesLiteralMoments {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k)
    (draw : Samples C (p.M C)) (y : Cells I) : Bool := by
  classical
  exact decide ((∀ (r : Fin 2) (j : Fin p.s),
    digitMoment p C I draw r y j < (p.hE : ℤ) ^ (2 * p.k)) ∧
    (∀ r : Fin 2, phiMoment p C I draw r y < (p.Lambda C : ℤ) ^ (2 * p.k)))

noncomputable def LiveBound {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k) : Prop :=
  mean (fun y : Cells I => GlobalSamplingWitness.failure (live p C I y)) ≤ p.beta

/-- Local construction obligation, not a literature field. -/
noncomputable def ActualBernsteinData {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k) : Prop :=
  ∀ y : Cells I, live p C I y = true →
    ∀ (r : Fin 2) (x : Points I) (j : Fin p.s),
      PublishedSources.Witness.finiteIndependent (Y p C I r y x j.val) ∧
      (∀ u : Terms C, mean (Y p C I r y x j.val u) = 0) ∧
      (∀ (u : Terms C) (draw : Samples C (p.M C)), |Y p C I r y x j.val u draw| ≤ 1) ∧
      (∑ u : Terms C, mean (fun draw : Samples C (p.M C) =>
        (Y p C I r y x j.val u draw) ^ 2)) ≤ p.pi C j.val * p.cap C ∧
      (∀ draw : Samples C (p.M C),
        error p C I r y x j.val draw = ∑ u : Terms C, Y p C I r y x j.val u draw)

noncomputable def LocalFailureBound {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k) : Prop :=
  ∀ y : Cells I, live p C I y = true →
    mean (fun draw : Samples C (p.M C) => GlobalSamplingWitness.failure (good p C I draw y)) ≤
      p.beta

noncomputable def GoodImpliesPass {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n p.k) : Prop :=
  ∀ (draw : Samples C (p.M C)) (y : Cells I),
    live p C I y = true → good p C I draw y = true → passesLiteralMoments p C I draw y = true

noncomputable def BoundedCoefficients {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (draw : Samples C (p.M C)) : Prop :=
  ∀ (r : Fin 2) (j : Fin p.s) (i : Fin (C r).bottomCount),
    -(((C r).coefficient i).natAbs : ℤ) ≤ coefficient p C draw r j.val i ∧
      coefficient p C draw r j.val i ≤ (((C r).coefficient i).natAbs : ℤ)

noncomputable def CompressedScoreIdentity {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (draw : Samples C (p.M C)) : Prop :=
  ∀ (r : Fin 2) (j : Fin p.s) (z : BitInput n),
    sampledScore p C draw r j.val z =
      ∑ u : GlobalSamplingWitness.UnitCopy (C r),
        (if (draw ⟨r, u⟩).val < p.cutoff C j.val then (1 : ℤ) else 0) *
          sign C ⟨r, u⟩ * (if ((C r).bottom u.1).eval z then 1 else 0)

def prefixBits {n : ℕ} (p : PublicData n) (C : Fin 2 → WeightedSymmetricCircuit n) : ℕ :=
  p.k * lambda n + p.s * ∑ r, ∑ i : Fin (C r).bottomCount,
    Nat.clog 2 (2 * ((C r).coefficient i).natAbs + 1)

def PrefixBound {n : ℕ} (p : PublicData n) (C : Fin 2 → WeightedSymmetricCircuit n) : Prop :=
  prefixBits p C ≤ p.k * lambda n + p.s * totalWeight C * Nat.clog 2 (2 * totalWeight C + 1)

/-- Proposed enclosing result. It contains one I and one draw, and does not
take hlive/hlocal or sampled honesty as extra published hypotheses. -/
noncomputable def SamplingParent {n : ℕ} (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) : Prop :=
  ∃ I : Coordinates n p.k, ∃ draw : Samples C (p.M C),
    BoundedCoefficients p C draw ∧ CompressedScoreIdentity p C draw ∧ PrefixBound p C ∧
      mean (fun y : Cells I =>
        GlobalSamplingWitness.failure (passesLiteralMoments p C I draw y)) / 2 ≤ p.beta

end NearCubicGates.Close.Counter.Sampling.WitnessContract

set_option autoImplicit false

namespace NearCubicGates.Close.Counter.Sampling.WitnessFixedI

open scoped BigOperators
open Target WitnessContract FiniteAverages PublishedSources.Witness

private theorem mean_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (f : ι → α → ℝ) : mean (fun x => ∑ i, f i x) = ∑ i, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

/-- Every coordinate set has the same number of complement assignments,
so the literal uniform sigma restriction law is the iterated uniform law. -/
private theorem mean_sigma_uniform (n k : ℕ) (f : ∀ I : Coordinates n k, Cells I → ℝ) :
    mean (fun ρ : FiniteRestriction n k => f ρ.1 ρ.2) =
      mean (fun I : Coordinates n k => mean (f I)) := by
  classical
  have hcard (I : Coordinates n k) : Fintype.card (Cells I) = 2 ^ (n - k) := by
    simp only [Cells, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
      Fintype.card_fin, Fintype.card_coe]
    rw [I.property]
  simp only [mean, Fintype.sum_sigma, Fintype.card_sigma]
  simp_rw [hcard]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
  rw [← Finset.sum_div, div_div, mul_comm]
  norm_cast

private theorem liveWeight_cast {n k : ℕ}
    (C : Fin 2 → WeightedSymmetricCircuit n) (I : Coordinates n k) (y : Cells I) :
    (liveWeight C I y : ℝ) = ∑ r, ∑ i : Fin (C r).bottomCount,
      (((C r).coefficient i).natAbs : ℝ) * indicator (gateLive ((C r).bottom i) ⟨I, y⟩) := by
  classical
  simp only [liveWeight, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hg : gateLive ((C r).bottom i) ⟨I, y⟩ <;> simp [indicator, hg]

/-- The source is applied to each actual gate; its absolute coefficient
counts its actual signed unit copies. Both circuit roles are summed first. -/
theorem weighted_expectation (hRestriction : CTW26_AppendixA3_CentralBinomialRestriction)
    (n : ℕ) (p : PublicData n) (C : Fin 2 → WeightedSymmetricCircuit n)
    (hG : PublicGuards p C) :
    mean (fun I : Coordinates n p.k => mean (fun y : Cells I => (liveWeight C I y : ℝ))) ≤
      (totalWeight C : ℝ) *
        (((p.k * Nat.choose (n - p.k) ((n - p.k) / 2) : ℕ) : ℝ) /
          (2 : ℝ) ^ (n - p.k)) := by
  classical
  rw [← mean_sigma_uniform n p.k (fun I y => (liveWeight C I y : ℝ))]
  simp_rw [liveWeight_cast]
  rw [mean_sum]
  simp_rw [mean_sum, mean_smul]
  calc
    _ ≤ ∑ r, ∑ i : Fin (C r).bottomCount, (((C r).coefficient i).natAbs : ℝ) *
        (((p.k * Nat.choose (n - p.k) ((n - p.k) / 2) : ℕ) : ℝ) /
          (2 : ℝ) ^ (n - p.k)) := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (hRestriction n p.k (by have hk := hG.kPositive; omega) hG.kBelowN ((C r).bottom i))
        (Nat.cast_nonneg _)
    _ = _ := by
      simp only [totalWeight, WeightedSymmetricCircuit.topWeight, Nat.cast_sum, Finset.sum_mul]

/-- Finite Markov with the literal live threshold; ties count as live. -/
theorem cell_markov (n : ℕ) (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (hG : PublicGuards p C)
    (I : Coordinates n p.k)
    (hexpect : mean (fun y : Cells I => (liveWeight C I y : ℝ)) ≤
      (p.beta : ℝ) * (p.ell0 C : ℝ)) : LiveBound p C I := by
  classical
  have hw := hG.weightPositive
  have hk : 0 < p.k := by have hp := hG.kPositive; omega
  have hb := hG.betaPositive
  have hR : 0 < p.R0 := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hn : n - p.k + 1 = 0 := Nat.sqrt_eq_zero.mp hz
    omega
  have hellQ : 0 < p.ell0 C := by unfold PublicData.ell0; positivity
  have hell : (0 : ℝ) < p.ell0 C := by exact_mod_cast hellQ
  have hpoint (y : Cells I) : (p.ell0 C : ℝ) *
      GlobalSamplingWitness.failure (live p C I y) ≤ (liveWeight C I y : ℝ) := by
    cases hl : live p C I y with
    | false =>
      have hn : ¬ (liveWeight C I y : ℝ) ≤ (p.ell0 C : ℝ) := by
        intro he
        have ht : live p C I y = true := by
          simpa only [live, decide_eq_true_eq] using he
        simp only [hl, Bool.false_eq_true] at ht
      simpa only [GlobalSamplingWitness.failure, Bool.false_eq_true, if_false, mul_one] using
        (not_le.mp hn).le
    | true =>
      simp only [GlobalSamplingWitness.failure, if_true, mul_zero]
      positivity
  unfold LiveBound
  apply le_of_mul_le_mul_left _ hell
  calc
    _ = mean (fun y : Cells I => (p.ell0 C : ℝ) *
        GlobalSamplingWitness.failure (live p C I y)) := (mean_smul _ _).symm
    _ ≤ _ := mean_le_mean _ _ hpoint
    _ ≤ _ := hexpect
    _ = _ := by ring

end NearCubicGates.Close.Counter.Sampling.WitnessFixedI

namespace NearCubicGates.Close.Counter.Sampling.WitnessFixedI

open Target WitnessContract

private noncomputable def centralRatio (a : ℕ) : ℝ := (Nat.centralBinom a : ℝ) / (4 : ℝ) ^ a

private theorem centralRatio_succ (a : ℕ) :
    centralRatio (a + 1) = ((2 * (a : ℝ) + 1) / (2 * ((a : ℝ) + 1))) * centralRatio a := by
  have hc : ((a : ℝ) + 1) * (Nat.centralBinom (a + 1) : ℝ) =
      2 * (2 * (a : ℝ) + 1) * (Nat.centralBinom a : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ a
  have hd : (a : ℝ) + 1 ≠ 0 := by positivity
  have he : (Nat.centralBinom (a + 1) : ℝ) =
      (2 * (2 * (a : ℝ) + 1) * (Nat.centralBinom a : ℝ)) / ((a : ℝ) + 1) := by
    apply (eq_div_iff hd).mpr
    nlinarith
  unfold centralRatio
  rw [he, pow_succ]
  field_simp
  ring

/-- Elementary central-binomial square bound, proved from its recurrence. -/
private theorem centralRatio_square (a : ℕ) :
    centralRatio a ^ 2 * (2 * (a : ℝ) + 1) ≤ 1 := by
  induction a with
  | zero => norm_num [centralRatio]
  | succ a ih =>
    have hd : (a : ℝ) + 1 ≠ 0 := by positivity
    let alpha : ℝ := ((2 * (a : ℝ) + 1) * (2 * (a : ℝ) + 3)) /
      (4 * ((a : ℝ) + 1) ^ 2)
    have ha0 : 0 ≤ alpha := by dsimp [alpha]; positivity
    have ha1 : alpha ≤ 1 := by
      dsimp [alpha]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((a : ℝ) + 1) ^ 2)).mpr
      nlinarith
    rw [centralRatio_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      _ = (centralRatio a ^ 2 * (2 * (a : ℝ) + 1)) * alpha := by
        dsimp [alpha]
        field_simp
        ring
      _ ≤ 1 * alpha := mul_le_mul_of_nonneg_right ih ha0
      _ ≤ 1 := by simpa only [one_mul] using ha1

private theorem odd_ratio (a : ℕ) :
    (Nat.choose (2 * a + 1) a : ℝ) / (2 : ℝ) ^ (2 * a + 1) = centralRatio (a + 1) := by
  have hb : Nat.centralBinom (a + 1) = 2 * Nat.choose (2 * a + 1) a := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have he : 2 * (a + 1) = (2 * a + 1) + 1 := by omega
    rw [he, Nat.choose_succ_succ', Nat.choose_symm_half]
    omega
  have hp : (2 : ℝ) ^ (2 * a + 1) = (4 : ℝ) ^ a * 2 := by
    norm_num [pow_add, pow_mul]
  unfold centralRatio
  rw [hb, hp, pow_succ]
  push_cast
  field_simp
  ring

private theorem central_binomial_square (m : ℕ) :
    ((Nat.choose m (m / 2) : ℝ) / (2 : ℝ) ^ m) ^ 2 * ((m : ℝ) + 1) ≤ 1 := by
  let a := m / 2
  have hrem : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hrem with heven | hodd
  · have hm : m = 2 * a := by dsimp [a]; omega
    have hh : (2 * a) / 2 = a := by omega
    have hr : (Nat.choose m (m / 2) : ℝ) / (2 : ℝ) ^ m = centralRatio a := by
      rw [hm, hh]
      simp only [centralRatio, Nat.centralBinom_eq_two_mul_choose, pow_mul]
      norm_num
    rw [hr, hm]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using centralRatio_square a
  · have hm : m = 2 * a + 1 := by dsimp [a]; omega
    have hh : (2 * a + 1) / 2 = a := by omega
    have hr : (Nat.choose m (m / 2) : ℝ) / (2 : ℝ) ^ m = centralRatio (a + 1) := by
      rw [hm, hh]
      exact odd_ratio a
    rw [hr]
    calc
      _ ≤ centralRatio (a + 1) ^ 2 * (2 * ((a + 1 : ℕ) : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [hm]
        push_cast
        linarith
      _ ≤ 1 := centralRatio_square (a + 1)

theorem central_bound (n : ℕ) (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (_hG : PublicGuards p C) :
    (((p.k * Nat.choose (n - p.k) ((n - p.k) / 2) : ℕ) : ℝ) /
      (2 : ℝ) ^ (n - p.k)) ≤ (p.k : ℝ) / (p.R0 : ℝ) := by
  let ratio : ℝ := (Nat.choose (n - p.k) ((n - p.k) / 2) : ℝ) / (2 : ℝ) ^ (n - p.k)
  have hr0 : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hRnat : 0 < p.R0 := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hn : n - p.k + 1 = 0 := Nat.sqrt_eq_zero.mp hz
    omega
  have hR : (0 : ℝ) < p.R0 := by exact_mod_cast hRnat
  have hs : (p.R0 : ℝ) ^ 2 ≤ ((n - p.k : ℕ) : ℝ) + 1 := by
    exact_mod_cast Nat.sqrt_le' (n - p.k + 1)
  have hbin : ratio ^ 2 * (((n - p.k : ℕ) : ℝ) + 1) ≤ 1 :=
    central_binomial_square (n - p.k)
  have hprod : (ratio * (p.R0 : ℝ)) ^ 2 ≤ 1 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hs (sq_nonneg ratio)).trans hbin
  have hsmall : ratio * (p.R0 : ℝ) ≤ 1 := by nlinarith [mul_nonneg hr0 hR.le]
  have hratio : ratio ≤ 1 / (p.R0 : ℝ) := (le_div_iff₀ hR).mpr hsmall
  calc
    _ = (p.k : ℝ) * ratio := by dsimp [ratio]; push_cast; ring
    _ ≤ (p.k : ℝ) * (1 / (p.R0 : ℝ)) := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
    _ = _ := by ring

end NearCubicGates.Close.Counter.Sampling.WitnessFixedI

namespace NearCubicGates.Close.Counter.Sampling.WitnessMoments

open scoped BigOperators
open Target WitnessContract

private theorem extension_agrees {n k : ℕ} (I : Coordinates n k)
    (y : Cells I) (x : Points I) :
    PublishedSources.Witness.cellAgrees ⟨I, y⟩ (extend I y x) := by
  intro i hi
  simp only [extend, dif_neg hi]

/-- A gate that changes between two points of the actual cell is live.
Thus absolute top multiplicity bounds each role's score difference. -/
theorem live_score (n : ℕ) (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (hG : PublicGuards p C)
    (I : Coordinates n p.k) (y : Cells I) (hlive : live p C I y = true)
    (r : Fin 2) (x : Points I) :
    |SampledChainMoments.scoreDelta (score C I r y) (reference I) x| ≤ p.cap C := by
  classical
  have hsingle (i : Fin (C r).bottomCount) :
      ((C r).coefficient i * (if ((C r).bottom i).eval (extend I y x) then 1 else 0) -
        (C r).coefficient i *
          (if ((C r).bottom i).eval (extend I y (reference I)) then 1 else 0)).natAbs ≤
      if PublishedSources.Witness.gateLive ((C r).bottom i) ⟨I, y⟩
      then ((C r).coefficient i).natAbs else 0 := by
    by_cases hg : PublishedSources.Witness.gateLive ((C r).bottom i) ⟨I, y⟩
    · rw [if_pos hg]
      cases ((C r).bottom i).eval (extend I y x) <;>
        cases ((C r).bottom i).eval (extend I y (reference I)) <;> simp
    · have heq : ((C r).bottom i).eval (extend I y x) =
          ((C r).bottom i).eval (extend I y (reference I)) := by
        by_contra hne
        exact hg ⟨extend I y x, extend I y (reference I),
          extension_agrees I y x, extension_agrees I y (reference I), hne⟩
      rw [if_neg hg, heq, sub_self]
      simp
  have hdelta : (score C I r y x - score C I r y (reference I)).natAbs ≤
      liveWeight C I y := by
    unfold score WeightedSymmetricCircuit.score
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ((C r).coefficient i *
          (if ((C r).bottom i).eval (extend I y x) then 1 else 0) -
          (C r).coefficient i *
          (if ((C r).bottom i).eval (extend I y (reference I)) then 1 else 0)).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ i : Fin (C r).bottomCount,
          if PublishedSources.Witness.gateLive ((C r).bottom i) ⟨I, y⟩
          then ((C r).coefficient i).natAbs else 0 :=
        Finset.sum_le_sum (fun i _ => hsingle i)
      _ ≤ liveWeight C I y := by
        exact Finset.single_le_sum (fun a _ => Nat.zero_le
          (∑ i : Fin (C a).bottomCount,
            if PublishedSources.Witness.gateLive ((C a).bottom i) ⟨I, y⟩
            then ((C a).coefficient i).natAbs else 0)) (Finset.mem_univ r)
  have hreal : |SampledChainMoments.scoreDelta (score C I r y) (reference I) x| ≤
      (liveWeight C I y : ℝ) := by
    simpa only [SampledChainMoments.scoreDelta, Nat.cast_natAbs, Int.cast_abs] using
      (Nat.cast_le.mpr hdelta :
        ((score C I r y x - score C I r y (reference I)).natAbs : ℝ) ≤ liveWeight C I y)
  have hell : (liveWeight C I y : ℝ) ≤ (p.ell0 C : ℝ) := by
    simpa only [live, decide_eq_true_eq] using hlive
  have hT : (0 : ℝ) < p.T := by exact_mod_cast hG.TPositive
  have hh : (64 : ℝ) * p.T ≤ p.h := by exact_mod_cast hG.height
  exact hreal.trans (hell.trans (PublicSamplingRates.cap_bounds p.T p.h (p.ell0 C) hT hh).2.1)

/-- The positive integer cutoff cannot attain the irrational sqrt(2) boundary. -/
theorem digit_margin (n : ℕ) (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (hG : PublicGuards p C) :
    Real.sqrt 2 * ((p.h : ℝ) / 2) < (p.hE : ℝ) := by
  have hEnat : 0 < p.hE := by
    have hP := hG.PMinimum
    change 0 < p.P / 4
    omega
  have hE : (0 : ℝ) < p.hE := by exact_mod_cast hEnat
  have hsquare : (p.h : ℝ) ^ 2 ≤ 2 * (p.hE : ℝ) ^ 2 := by
    exact_mod_cast Nat.sqrt_le' (2 * p.hE ^ 2)
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hupper : (p.h : ℝ) ≤ Real.sqrt 2 * (p.hE : ℝ) := by
    have hsq : (Real.sqrt 2 * (p.hE : ℝ)) ^ 2 = 2 * (p.hE : ℝ) ^ 2 := by
      rw [mul_pow, hs]
    have hp := mul_nonneg hs0 hE.le
    nlinarith
  have hne : (p.h : ℝ) ≠ Real.sqrt 2 * (p.hE : ℝ) := by
    intro heq
    have hrat : Real.sqrt 2 = (p.h : ℝ) / (p.hE : ℝ) :=
      (eq_div_iff hE.ne').mpr heq.symm
    apply irrational_sqrt_two.ne_rational (p.h : ℤ) (p.hE : ℤ)
    simpa only [Int.cast_natCast] using hrat
  have hstrict := lt_of_le_of_ne hupper hne
  have hm := mul_lt_mul_of_pos_left hstrict (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  rw [← mul_assoc, ← pow_two, hs] at hm
  nlinarith

/-- The literal phi difference is M times the centered terminal score error. -/
theorem terminal_bound (n : ℕ) (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (hG : PublicGuards p C)
    (I : Coordinates n p.k) (draw : Samples C (p.M C)) (y : Cells I)
    (hgood : good p C I draw y = true) (r : Fin 2) (x : Points I) :
    ((CertifiedScoreSupport.phi (p.M C) (p.A C) (values p C I draw r y)
          (score C I r y) p.Jlean x -
        CertifiedScoreSupport.phi (p.M C) (p.A C) (values p C I draw r y)
          (score C I r y) p.Jlean (reference I)).natAbs : ℝ) ≤
      (p.A C : ℝ) * (86 * (p.T : ℝ) * p.cap C / (p.h : ℝ)) := by
  classical
  have hT : (0 : ℝ) < p.T := by exact_mod_cast hG.TPositive
  have hh : (64 : ℝ) * p.T ≤ p.h := by exact_mod_cast hG.height
  have hM : (0 : ℝ) < p.M C := by
    exact_mod_cast (PublicSamplingRates.denominator_bounds p.T p.h (p.ell0 C) hT hh).1
  have hpi : 0 < p.pi C p.Jlean :=
    (PublicSamplingRates.all_rates_bounded p.T p.h (p.ell0 C) hT hh p.Jlean).1
  have hrate : p.pi C p.Jlean = (p.A C : ℝ) / (p.M C : ℝ) :=
    PublicSamplingRates.rate_is_rational_product p.T p.h (p.ell0 C) hT hh p.Jlean
  have hAeq : (p.M C : ℝ) * p.pi C p.Jlean = (p.A C : ℝ) := by
    rw [hrate]
    field_simp
  have hg : ∀ (r : Fin 2) (x : Points I) (j : Fin p.s),
      |error p C I r y x j.val draw| ≤ p.fluctuation C j.val := by
    simpa only [good, decide_eq_true_eq] using hgood
  have hb := hg r x ⟨p.Jlean, by change p.Jlean < p.Jlean + 1; omega⟩
  have hphi :
      ((CertifiedScoreSupport.phi (p.M C) (p.A C) (values p C I draw r y)
          (score C I r y) p.Jlean x -
        CertifiedScoreSupport.phi (p.M C) (p.A C) (values p C I draw r y)
          (score C I r y) p.Jlean (reference I) : ℤ) : ℝ) =
      (p.M C : ℝ) * error p C I r y x p.Jlean draw := by
    simp only [CertifiedScoreSupport.phi, error, SampledChainMoments.delta,
      SampledChainMoments.scoreDelta, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [hrate]
    field_simp
    ring
  rw [Nat.cast_natAbs, Int.cast_abs, hphi, abs_mul, abs_of_pos hM]
  calc
    _ ≤ (p.M C : ℝ) * p.fluctuation C p.Jlean := mul_le_mul_of_nonneg_left hb hM.le
    _ = ((p.M C : ℝ) * p.pi C p.Jlean) *
          (p.fluctuation C p.Jlean / p.pi C p.Jlean) := by
      field_simp
    _ = (p.A C : ℝ) * (p.fluctuation C p.Jlean / p.pi C p.Jlean) := by rw [hAeq]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (PublicSamplingRates.terminal_error_bound p.T p.h (p.ell0 C) hT hh
        p.Jlean hG.stopped) (Nat.cast_nonneg _)

/-- The public 244 constant supplies strict sqrt(2) slack even after the
integer window cutoff is rounded down and then increased by one. -/
theorem terminal_margin (n : ℕ) (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) (hG : PublicGuards p C) :
    Real.sqrt 2 * ((p.A C : ℝ) * (86 * (p.T : ℝ) * p.cap C / (p.h : ℝ))) <
      (p.Lambda C : ℝ) := by
  have hT : (0 : ℝ) < p.T := by exact_mod_cast hG.TPositive
  have hh : (64 : ℝ) * p.T ≤ p.h := by exact_mod_cast hG.height
  have hc := PublicSamplingRates.cap_bounds p.T p.h (p.ell0 C) hT hh
  have hcap : 0 < p.cap C := by change 0 < PublicSamplingRates.liveCap p.T p.h (p.ell0 C); linarith [hc.2.2.1]
  have hx := (PublicSamplingRates.initial_bounds p.T p.h (p.ell0 C) hT hh).2.2.1
  have hA : (0 : ℝ) < p.A C := by
    exact_mod_cast NestedRateChain.product_positive (p.x0 C) hx p.Jlean
  let ratio : ℝ := (p.T : ℝ) * p.cap C / (p.h : ℝ)
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hs : Real.sqrt 2 * 86 < (122 : ℝ) := by
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hbound : Real.sqrt 2 * (86 * ratio) ≤ 122 * ratio := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.le) hratio]
  have hwindow : 122 * ratio < ((p.Lw : ℝ) - 1) / 2 := by
    have hw := hG.usefulWindow
    change 244 * (p.T : ℝ) * p.cap C / (p.h : ℝ) < (p.Lw : ℝ) - 1 at hw
    have heq : 244 * (p.T : ℝ) * p.cap C / (p.h : ℝ) = 244 * ratio := by
      dsimp [ratio]
      ring
    rw [heq] at hw
    linarith
  have hm := mul_lt_mul_of_pos_left (hbound.trans_lt hwindow) hA
  have hL : 1 ≤ p.Lw := by have hw := hG.windowSize; omega
  have hn : (p.Lw - 1) * p.A C < 2 * ((p.Lw - 1) * p.A C / 2 + 1) := by omega
  have hround : (p.A C : ℝ) * ((p.Lw : ℝ) - 1) / 2 < (p.Lambda C : ℝ) := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hn' : (((p.Lw - 1) * p.A C : ℕ) : ℝ) <
        2 * (p.Lambda C : ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_mul, Nat.cast_sub hL, Nat.cast_one, mul_comm] using hn'
  calc
    _ = (p.A C : ℝ) * (Real.sqrt 2 * (86 * ratio)) := by dsimp [ratio]; ring
    _ < (p.A C : ℝ) * ((p.Lw : ℝ) - 1) / 2 := by simpa only [mul_div_assoc] using hm
    _ < _ := hround

end NearCubicGates.Close.Counter.Sampling.WitnessMoments

namespace NearCubicGates.Close.Counter.Sampling.WitnessCompression

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

/-- Prefix widths are charged to absolute top multiplicity. -/
theorem prefix_bound (n : ℕ) (p : PublicData n)
    (C : Fin 2 → WeightedSymmetricCircuit n) : PrefixBound p C := by
  classical
  have hweight (r : Fin 2) (i : Fin (C r).bottomCount) :
      ((C r).coefficient i).natAbs ≤ totalWeight C := by
    have hi : ((C r).coefficient i).natAbs ≤ (C r).topWeight := by
      exact Finset.single_le_sum
        (fun a _ => Nat.zero_le ((C r).coefficient a).natAbs) (Finset.mem_univ i)
    have hr : (C r).topWeight ≤ totalWeight C := by
      exact Finset.single_le_sum
        (fun a _ => Nat.zero_le (C a).topWeight) (Finset.mem_univ r)
    exact hi.trans hr
  have hwidth (r : Fin 2) (i : Fin (C r).bottomCount) :
      Nat.clog 2 (2 * ((C r).coefficient i).natAbs + 1) ≤
        ((C r).coefficient i).natAbs * Nat.clog 2 (2 * totalWeight C + 1) := by
    have hpos := Int.natAbs_pos.mpr ((C r).coefficient_ne_zero i)
    calc
      _ ≤ Nat.clog 2 (2 * totalWeight C + 1) :=
        Nat.clog_mono_right 2 (by have hi := hweight r i; omega)
      _ ≤ ((C r).coefficient i).natAbs * Nat.clog 2 (2 * totalWeight C + 1) := by
        nlinarith
  have hsum : (∑ r, ∑ i : Fin (C r).bottomCount,
      Nat.clog 2 (2 * ((C r).coefficient i).natAbs + 1)) ≤
      totalWeight C * Nat.clog 2 (2 * totalWeight C + 1) := by
    calc
      _ ≤ ∑ r, ∑ i : Fin (C r).bottomCount,
          ((C r).coefficient i).natAbs * Nat.clog 2 (2 * totalWeight C + 1) := by
        apply Finset.sum_le_sum
        intro r _
        exact Finset.sum_le_sum (fun i _ => hwidth r i)
      _ = _ := by simp only [totalWeight, WeightedSymmetricCircuit.topWeight, Finset.sum_mul]
  unfold PrefixBound prefixBits
  simpa only [Nat.mul_assoc] using
    Nat.add_le_add_left (Nat.mul_le_mul_left p.s hsum) (p.k * lambda n)

end NearCubicGates.Close.Counter.Sampling.WitnessCompression
