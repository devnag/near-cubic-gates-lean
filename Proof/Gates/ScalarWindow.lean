import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.NormNum
import Mathlib.Data.Int.ModEq

/-!
# Scalar distribution uniqueness from prime residue histograms

This is the roots-of-unity proof of manuscript `lem:one-window`, not an
assumption of injectivity or of the existence of a reconstruction certificate.
Masses may be signed rationals. The first theorem uses a finite consecutive
frame; the integer-frame adapter below permits negative endpoints.
-/

namespace NearCubicGates.ScalarWindow

open scoped BigOperators Polynomial
open Polynomial

/-- The exact scalar distributional window in the manuscript. -/
def window (primes : Finset ℕ) : ℕ := 1 + ∑ p ∈ primes, (p - 1)

/-- Residue histogram of a rational-valued distribution on `0,...,L-1`. -/
def residueData {L : ℕ} (mass : Fin L → ℚ) (p r : ℕ) : ℚ :=
  ∑ i : Fin L, if i.val % p = r then mass i else 0

noncomputable def generating {L : ℕ} (mass : Fin L → ℚ) : ℂ[X] :=
  ∑ i : Fin L, C (mass i : ℂ) * X ^ i.val

noncomputable def frequencyRoots (primes : Finset ℕ) : Finset ℂ :=
  insert 1 (primes.biUnion fun p => primitiveRoots p ℂ)

theorem generating_degree_lt {L : ℕ} (mass : Fin L → ℚ) :
    (generating mass).degree < L :=
  Polynomial.degree_sum_fin_lt (fun i => (mass i : ℂ))

theorem generating_coeff {L : ℕ} (mass : Fin L → ℚ) (i : Fin L) :
    (generating mass).coeff i.val = (mass i : ℂ) := by
  classical
  simp only [generating, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hval : i.val ≠ j.val := by
      intro h
      exact hji (Fin.ext h.symm)
    simp [hval]
  · simp

theorem generating_eval_zero {L p : ℕ} (mass : Fin L → ℚ) (hp : 0 < p)
    (hdata : ∀ r < p, residueData mass p r = 0)
    (z : ℂ) (hz : z ^ p = 1) : (generating mass).eval z = 0 := by
  classical
  simp only [generating, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  let g : Fin L → ℕ := fun i => i.val % p
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin L)), g i ∈ Finset.range p := by
    intro i _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  rw [← Finset.sum_fiberwise_of_maps_to hg]
  apply Finset.sum_eq_zero
  intro r hr
  have hrp : r < p := Finset.mem_range.mp hr
  calc
    (∑ i ∈ Finset.univ.filter (fun i => g i = r), (mass i : ℂ) * z ^ i.val)
      = (∑ i ∈ Finset.univ.filter (fun i => g i = r), (mass i : ℂ)) * z ^ r := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          have hmod : i.val % p = r := (Finset.mem_filter.mp hi).2
          rw [pow_eq_pow_mod i.val hz, hmod]
    _ = 0 := by
      have hsum : (∑ i ∈ Finset.univ.filter (fun i => g i = r), mass i) = 0 := by
        simpa [residueData, Finset.sum_filter, g] using hdata r hrp
      have hcast : (∑ i ∈ Finset.univ.filter (fun i => g i = r), (mass i : ℂ)) = 0 := by
        exact_mod_cast hsum
      rw [hcast, zero_mul]

theorem frequencyRoots_card (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p) :
    (frequencyRoots primes).card = window primes := by
  classical
  have hdisjoint : (primes : Set ℕ).PairwiseDisjoint (fun p => primitiveRoots p ℂ) := by
    intro p _ q _ hpq
    exact IsPrimitiveRoot.disjoint hpq
  have hone : (1 : ℂ) ∉ primes.biUnion (fun p => primitiveRoots p ℂ) := by
    intro h
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp h
    have hprim := isPrimitiveRoot_of_mem_primitiveRoots hz
    have hp1 : p = 1 := IsPrimitiveRoot.one_left_iff.mp hprim
    have hge := (hprime p hp).two_le
    omega
  rw [frequencyRoots, Finset.card_insert_of_notMem hone, Finset.card_biUnion hdisjoint]
  unfold window
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Complex.isPrimitiveRoot_exp p (hprime p hp).ne_zero).card_primitiveRoots,
    Nat.totient_prime (hprime p hp)]

/-- The manuscript's scalar uniqueness statement on a zero-based frame. -/
theorem zero_of_residueData_zero {L : ℕ} (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (mass : Fin L → ℚ) (hL : L ≤ window primes)
    (hdata : ∀ p ∈ primes, ∀ r < p, residueData mass p r = 0) :
    ∀ i, mass i = 0 := by
  classical
  have hroots : ∀ z ∈ frequencyRoots primes, (generating mass).eval z = 0 := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      obtain ⟨p, hp⟩ := hne
      exact generating_eval_zero mass (hprime p hp).pos (hdata p hp) 1 (one_pow p)
    · obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      exact generating_eval_zero mass (hprime p hp).pos (hdata p hp) z
        (isPrimitiveRoot_of_mem_primitiveRoots hz).pow_eq_one
  have hzpoly : generating mass = 0 := by
    by_contra hnepoly
    have hd := (Polynomial.natDegree_lt_iff_degree_lt hnepoly).mpr
      (generating_degree_lt mass)
    have hcard : (generating mass).natDegree < (frequencyRoots primes).card := by
      rw [frequencyRoots_card primes hprime]
      exact hd.trans_le hL
    exact hnepoly (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (generating mass) (frequencyRoots primes) hroots hcard)
  intro i
  have hcoef := generating_coeff mass i
  rw [hzpoly, coeff_zero] at hcoef
  exact_mod_cast hcoef.symm

/-- Histograms uniquely determine the signed rational distribution. -/
theorem residueData_injective {L : ℕ} (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (hL : L ≤ window primes) (a b : Fin L → ℚ)
    (hdata : ∀ p ∈ primes, ∀ r < p, residueData a p r = residueData b p r) :
    a = b := by
  have hz := zero_of_residueData_zero primes hne hprime (fun i => a i - b i) hL
    (by
      intro p hp r hr
      have hzero := sub_eq_zero.mpr (hdata p hp r hr)
      simp only [residueData] at hzero ⊢
      rw [← Finset.sum_sub_distrib] at hzero
      convert hzero using 1
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp)
  funext i
  exact sub_eq_zero.mp (hz i)

/-- The same data on an arbitrary integer frame, including negative scores. -/
def frameResidueData {L : ℕ} (mass : Fin L → ℚ) (lo : ℤ) (p : ℕ) (r : ℤ) : ℚ :=
  ∑ i : Fin L, if (lo + (i.val : ℤ)) % (p : ℤ) = r then mass i else 0

theorem shifted_residue_iff (lo : ℤ) (i p r : ℕ) (hr : r < p) :
    (lo + (i : ℤ)) % (p : ℤ) = (lo + (r : ℤ)) % (p : ℤ) ↔ i % p = r := by
  constructor
  · intro h
    have hc : (i : ℤ) ≡ (r : ℤ) [ZMOD (p : ℤ)] :=
      Int.ModEq.add_left_cancel' lo h
    have hn := Int.natCast_modEq_iff.mp hc
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hr] using hn
  · intro h
    have hn : i ≡ r [MOD p] := by simpa [Nat.ModEq, Nat.mod_eq_of_lt hr] using h
    exact (Int.natCast_modEq_iff.mpr hn).add_left lo

theorem frameResidueData_eq {L : ℕ} (mass : Fin L → ℚ)
    (lo : ℤ) (p r : ℕ) (hr : r < p) :
    frameResidueData mass lo p ((lo + (r : ℤ)) % (p : ℤ)) = residueData mass p r := by
  simp only [frameResidueData, residueData]
  apply Finset.sum_congr rfl
  intro i _
  simp only [shifted_residue_iff lo i.val p r hr]

/-- Full scalar-window uniqueness on an arbitrary translated integer frame. -/
theorem zero_of_frameResidueData_zero {L : ℕ} (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (mass : Fin L → ℚ) (lo : ℤ) (hL : L ≤ window primes)
    (hdata : ∀ p ∈ primes, ∀ r : ℤ, frameResidueData mass lo p r = 0) :
    ∀ i, mass i = 0 := by
  apply zero_of_residueData_zero primes hne hprime mass hL
  intro p hp r hr
  rw [← frameResidueData_eq mass lo p r hr]
  exact hdata p hp _

theorem frameResidueData_injective {L : ℕ} (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo : ℤ) (hL : L ≤ window primes) (a b : Fin L → ℚ)
    (hdata : ∀ p ∈ primes, ∀ r : ℤ,
      frameResidueData a lo p r = frameResidueData b lo p r) : a = b := by
  apply residueData_injective primes hne hprime hL
  intro p hp r hr
  rw [← frameResidueData_eq a lo p r hr, ← frameResidueData_eq b lo p r hr]
  exact hdata p hp _

section Histograms

variable {Points : Type*} [Fintype Points] {L : ℕ}

/-- Collect signed masses of finitely many points at each score in the frame. -/
def histogram (index : Points → Fin L) (mass : Points → ℚ) : Fin L → ℚ :=
  fun j => ∑ i : Points, if index i = j then mass i else 0

/-- Taking a score histogram and taking residues commute exactly. -/
theorem histogram_residueData (index : Points → Fin L) (mass : Points → ℚ)
    (lo : ℤ) (p : ℕ) (r : ℤ) :
    frameResidueData (histogram index mass) lo p r =
      ∑ i : Points, if (lo + ((index i).val : ℤ)) % (p : ℤ) = r then mass i else 0 := by
  classical
  simp only [frameResidueData, histogram]
  have hsplit (j : Fin L) :
      (if (lo + (j.val : ℤ)) % (p : ℤ) = r then
        ∑ i : Points, if index i = j then mass i else 0
       else 0) =
      ∑ i : Points, if (lo + (j.val : ℤ)) % (p : ℤ) = r then
        (if index i = j then mass i else 0) else 0 := by
    by_cases h : (lo + (j.val : ℤ)) % (p : ℤ) = r <;> simp [h]
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (index i)]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

/-- Zero modular data for a short score imply that every exact line sum is zero. -/
theorem histogram_zero_of_residues_zero (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (index : Points → Fin L) (mass : Points → ℚ) (lo : ℤ)
    (hL : L ≤ window primes)
    (hdata : ∀ p ∈ primes, ∀ r : ℤ,
      (∑ i : Points,
        if (lo + ((index i).val : ℤ)) % (p : ℤ) = r then mass i else 0) = 0) :
    ∀ j, histogram index mass j = 0 := by
  apply zero_of_frameResidueData_zero primes hne hprime (histogram index mass) lo hL
  intro p hp r
  rw [histogram_residueData]
  exact hdata p hp r

end Histograms

end NearCubicGates.ScalarWindow
