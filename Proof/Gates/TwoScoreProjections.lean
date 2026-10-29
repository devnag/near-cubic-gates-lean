import Proof.Gates.ScalarWindow
import Proof.Gates.FiniteDistributions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Short projections of actual joint residue data

This proves the first step of `lem:two-window`: modular reduction commutes
with an integer linear projection, and the proved scalar window makes every
short exact line sum vanish. Neither tomography nor a matrix rank hypothesis
is assumed. The subsequent binomial-product argument is a separate obligation.
-/

namespace NearCubicGates.TwoScoreProjections

open scoped BigOperators
open NearCubicGates.FiniteDistributions NearCubicGates.ScalarWindow

/-- Canonical Euclidean residue, valid even for negative integer scores. -/
def residueIndex (p : ℕ) (hp : 0 < p) (s : ℤ) : Fin p :=
  ⟨(s % (p : ℤ)).toNat, by
    have h0 := Int.emod_nonneg s (show (p : ℤ) ≠ 0 by omega)
    have hlt := Int.emod_lt_of_pos s (show (0 : ℤ) < p by omega)
    omega⟩

theorem residueIndex_cast (p : ℕ) (hp : 0 < p) (s : ℤ) :
    ((residueIndex p hp s).val : ℤ) = s % (p : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg s (by omega))

theorem residueIndex_congr (p : ℕ) (hp : 0 < p) {a b : ℤ}
    (h : a ≡ b [ZMOD (p : ℤ)]) : residueIndex p hp a = residueIndex p hp b := by
  apply Fin.ext
  exact congrArg Int.toNat h

/-- Residue projection on the actual finite pair of residue coordinates. -/
def residueProjection (p : ℕ) (hp : 0 < p) (α β : ℤ)
    (r : Fin p × Fin p) : Fin p :=
  residueIndex p hp (α * (r.1.val : ℤ) + β * (r.2.val : ℤ))

theorem residue_projection_commutes (p : ℕ) (hp : 0 < p) (α β a b : ℤ) :
    residueIndex p hp (α * a + β * b) =
      residueProjection p hp α β (residueIndex p hp a, residueIndex p hp b) := by
  apply residueIndex_congr
  simp only [residueIndex_cast]
  exact ((Int.mod_modEq a (p : ℤ)).symm.mul_left α).add
    ((Int.mod_modEq b (p : ℤ)).symm.mul_left β)

section Distributions

variable {Points : Type*} [Fintype Points]

/-- Full joint residue distribution, with both coordinates using the same modulus. -/
def jointData (score₁ score₂ : Points → ℤ) (mass : Points → ℚ)
    (p : ℕ) (hp : 0 < p) : Fin p × Fin p → ℚ :=
  pushforward (fun i => (residueIndex p hp (score₁ i), residueIndex p hp (score₂ i))) mass

theorem jointData_eq (score₁ score₂ : Points → ℤ) (mass : Points → ℚ)
    (p : ℕ) (hp : 0 < p) (r s : Fin p) :
    jointData score₁ score₂ mass p hp (r, s) =
      ∑ i : Points, if score₁ i % (p : ℤ) = (r.val : ℤ) ∧
        score₂ i % (p : ℤ) = (s.val : ℤ) then mass i else 0 := by
  simp only [jointData, pushforward]
  apply Finset.sum_congr rfl
  intro i _
  have h₁ : residueIndex p hp (score₁ i) = r ↔
      score₁ i % (p : ℤ) = (r.val : ℤ) := by
    constructor
    · intro h
      rw [← residueIndex_cast p hp (score₁ i), h]
    · intro h
      apply Fin.ext
      have hc := congrArg Int.toNat h
      simpa only [residueIndex, Int.toNat_natCast] using hc
  have h₂ : residueIndex p hp (score₂ i) = s ↔
      score₂ i % (p : ℤ) = (s.val : ℤ) := by
    constructor
    · intro h
      rw [← residueIndex_cast p hp (score₂ i), h]
    · intro h
      apply Fin.ext
      have hc := congrArg Int.toNat h
      simpa only [residueIndex, Int.toNat_natCast] using hc
  simp only [Prod.mk.injEq, h₁, h₂]

/-- Projection of full joint modular histograms equals the scalar modular histogram. -/
theorem projected_modular_data (score₁ score₂ : Points → ℤ) (mass : Points → ℚ)
    (p : ℕ) (hp : 0 < p) (α β : ℤ) :
    pushforward (residueProjection p hp α β) (jointData score₁ score₂ mass p hp) =
      pushforward (fun i => residueIndex p hp (α * score₁ i + β * score₂ i)) mass := by
  rw [jointData, pushforward_comp]
  apply pushforward_congr
  intro i
  exact (residue_projection_commutes p hp α β (score₁ i) (score₂ i)).symm

/-- A finite score confined to an integer frame has a canonical frame index. -/
def scoreIndex (W : ℕ) (lo : ℤ) (score : Points → ℤ)
    (hscore : ∀ i, lo ≤ score i ∧ score i < lo + (W : ℤ)) (i : Points) : Fin W :=
  ⟨(score i - lo).toNat, by have hi := hscore i; omega⟩

omit [Fintype Points] in
theorem scoreIndex_eq (W : ℕ) (lo : ℤ) (score : Points → ℤ)
    (hscore : ∀ i, lo ≤ score i ∧ score i < lo + (W : ℤ)) (i : Points) :
    lo + ((scoreIndex W lo score hscore i).val : ℤ) = score i := by
  change lo + ((score i - lo).toNat : ℤ) = score i
  rw [Int.toNat_of_nonneg (by have hi := hscore i; omega)]
  omega

/-- Every line sum of a projection in a sufficiently short frame is zero.
The only measurement premise is zero actual joint residue data. -/
theorem short_projection_zero (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (score₁ score₂ : Points → ℤ) (mass : Points → ℚ) (α β : ℤ)
    (W : ℕ) (lo : ℤ) (hW : W ≤ window primes)
    (hscore : ∀ i, lo ≤ α * score₁ i + β * score₂ i ∧
      α * score₁ i + β * score₂ i < lo + (W : ℤ))
    (hdata : ∀ p, ∀ hp : p ∈ primes, ∀ r : Fin p × Fin p,
      jointData score₁ score₂ mass p (hprime p hp).pos r = 0) :
    ∀ j : Fin W, (∑ i : Points,
      if α * score₁ i + β * score₂ i = lo + (j.val : ℤ) then mass i else 0) = 0 := by
  let score : Points → ℤ := fun i => α * score₁ i + β * score₂ i
  let idx := scoreIndex W lo score hscore
  have hzero : ∀ j, histogram idx mass j = 0 := by
    apply histogram_zero_of_residues_zero primes hne hprime idx mass lo hW
    intro p hp r
    have hD : jointData score₁ score₂ mass p (hprime p hp).pos = fun _ => 0 :=
      funext (hdata p hp)
    have hz := projected_modular_data score₁ score₂ mass p (hprime p hp).pos α β
    rw [hD, pushforward_zero] at hz
    have hscalar : ∀ t, pushforward
        (fun i => residueIndex p (hprime p hp).pos (score i)) mass t = 0 := by
      intro t
      exact (congrFun hz t).symm
    simp_rw [idx, scoreIndex_eq]
    by_cases hr : ∃ t : Fin p, (t.val : ℤ) = r
    · obtain ⟨t, ht⟩ := hr
      have hscalar' := hscalar t
      simp only [pushforward] at hscalar'
      convert hscalar' using 1
      apply Finset.sum_congr rfl
      intro i _
      have heq : residueIndex p (hprime p hp).pos (score i) = t ↔
          score i % (p : ℤ) = r := by
        rw [← ht, ← residueIndex_cast p (hprime p hp).pos (score i)]
        constructor
        · intro h
          exact congrArg (fun k : Fin p => (k.val : ℤ)) h
        · intro h
          apply Fin.ext
          exact_mod_cast h
      simp only [heq]
    · apply Finset.sum_eq_zero
      intro i _
      have hnot : score i % (p : ℤ) ≠ r := by
        intro h
        exact hr ⟨residueIndex p (hprime p hp).pos (score i),
          (residueIndex_cast p (hprime p hp).pos (score i)).trans h⟩
      simp [hnot]
  intro j
  have hz := hzero j
  simp only [histogram] at hz
  convert hz using 1
  apply Finset.sum_congr rfl
  intro i _
  have heq : idx i = j ↔ score i = lo + (j.val : ℤ) := by
    constructor
    · intro h
      rw [← scoreIndex_eq W lo score hscore i]
      exact congrArg (fun k : Fin W => lo + (k.val : ℤ)) h
    · intro h
      apply Fin.ext
      have hi := scoreIndex_eq W lo score hscore i
      change lo + ((idx i).val : ℤ) = score i at hi
      rw [h] at hi
      omega
  simp only [heq, score]

end Distributions

/-- The left endpoint of the smallest rectangular projection frame. -/
def boxProjectionLo (L : ℕ) (α β : ℤ) : ℤ :=
  (min 0 α + min 0 β) * ((L - 1 : ℕ) : ℤ)

/-- The number of possible integer positions, not the number of occupied lines. -/
def boxProjectionWidth (L : ℕ) (α β : ℤ) : ℕ :=
  (L - 1) * (α.natAbs + β.natAbs) + 1

theorem scaled_coordinate_bounds (c x B : ℤ) (hx0 : 0 ≤ x) (hxB : x ≤ B) :
    min 0 c * B ≤ c * x ∧ c * x ≤ max 0 c * B := by
  by_cases hc : 0 ≤ c
  · simp only [min_eq_left hc, max_eq_right hc, zero_mul]
    constructor <;> nlinarith
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    simp only [min_eq_right hc', max_eq_left hc', zero_mul]
    constructor <;> nlinarith

theorem box_projection_bounds (L : ℕ) (hL : 1 ≤ L) (α β : ℤ)
    (a b : Fin L) :
    boxProjectionLo L α β ≤ α * (a.val : ℤ) + β * (b.val : ℤ) ∧
      α * (a.val : ℤ) + β * (b.val : ℤ) <
        boxProjectionLo L α β + (boxProjectionWidth L α β : ℤ) := by
  have ha0 : (0 : ℤ) ≤ a.val := by omega
  have hb0 : (0 : ℤ) ≤ b.val := by omega
  have haB : (a.val : ℤ) ≤ ((L - 1 : ℕ) : ℤ) := by have ha := a.isLt; omega
  have hbB : (b.val : ℤ) ≤ ((L - 1 : ℕ) : ℤ) := by have hb := b.isLt; omega
  have ha := scaled_coordinate_bounds α a.val ((L - 1 : ℕ) : ℤ) ha0 haB
  have hb := scaled_coordinate_bounds β b.val ((L - 1 : ℕ) : ℤ) hb0 hbB
  have hα : min 0 α + |α| = max 0 α := by
    by_cases h : 0 ≤ α
    · simp [min_eq_left h, max_eq_right h, abs_of_nonneg h]
    · have h' : α ≤ 0 := le_of_lt (lt_of_not_ge h)
      simp [min_eq_right h', max_eq_left h', abs_of_nonpos h']
  have hβ : min 0 β + |β| = max 0 β := by
    by_cases h : 0 ≤ β
    · simp [min_eq_left h, max_eq_right h, abs_of_nonneg h]
    · have h' : β ≤ 0 := le_of_lt (lt_of_not_ge h)
      simp [min_eq_right h', max_eq_left h', abs_of_nonpos h']
  have hwidth : boxProjectionLo L α β + (boxProjectionWidth L α β : ℤ) =
      (max 0 α + max 0 β) * ((L - 1 : ℕ) : ℤ) + 1 := by
    simp only [boxProjectionLo, boxProjectionWidth, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Int.natCast_natAbs]
    calc
      (min 0 α + min 0 β) * ((L - 1 : ℕ) : ℤ) +
          (((L - 1 : ℕ) : ℤ) * (|α| + |β|) + 1) =
        ((min 0 α + |α|) + (min 0 β + |β|)) * ((L - 1 : ℕ) : ℤ) + 1 := by ring
      _ = _ := by rw [hα, hβ]
  constructor
  · unfold boxProjectionLo
    nlinarith [ha.1, hb.1]
  · rw [hwidth]
    nlinarith [ha.2, hb.2]

/-- The floor `q = ⌊(D'−1)/(L−1)⌋` of `lem:two-window` makes every norm-at-most-`q`
projection fit the proved scalar distribution window. -/
theorem box_projection_window (primes : Finset ℕ) (L : ℕ) (α β : ℤ)
    (hnorm : α.natAbs + β.natAbs ≤ (window primes - 1) / (L - 1)) :
    boxProjectionWidth L α β ≤ window primes := by
  have hmul := Nat.mul_le_mul_left (L - 1) hnorm
  have hdiv := Nat.mul_div_le (window primes - 1) (L - 1)
  have hwindow : 1 ≤ window primes := by unfold window; omega
  unfold boxProjectionWidth
  omega

/-- First step of quantitative two-score tomography on the full square box,
including positive, negative, and coordinate projections. -/
theorem box_short_projection_zero (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (L : ℕ) (hL : 1 ≤ L) (mass : Fin L × Fin L → ℚ) (α β : ℤ)
    (hnorm : α.natAbs + β.natAbs ≤ (window primes - 1) / (L - 1))
    (hdata : ∀ p, ∀ hp : p ∈ primes, ∀ r : Fin p × Fin p,
      jointData (fun i : Fin L × Fin L => (i.1.val : ℤ))
        (fun i => (i.2.val : ℤ)) mass p (hprime p hp).pos r = 0) :
    ∀ j : Fin (boxProjectionWidth L α β),
      (∑ i : Fin L × Fin L,
        if α * (i.1.val : ℤ) + β * (i.2.val : ℤ) =
          boxProjectionLo L α β + (j.val : ℤ) then mass i else 0) = 0 := by
  exact short_projection_zero primes hne hprime _ _ mass α β
    (boxProjectionWidth L α β) (boxProjectionLo L α β)
    (box_projection_window primes L α β hnorm)
    (fun i => box_projection_bounds L hL α β i.1 i.2) hdata

end NearCubicGates.TwoScoreProjections
