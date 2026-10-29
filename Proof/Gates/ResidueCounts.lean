import Proof.Gates.PrimePowerLifting
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Exact joint residue counts from the literal lifting polynomial

Pointwise Fermat tests and the amplifier of `lem:amp` give a value congruent
to the actual indicator modulo `p^e`. Summing and using the cardinality guard
gives the unique exact count, not just a residue or an approximate count.
Polynomial multilinearization and the batch evaluator are separate modules.
-/

namespace NearCubicGates.ResidueCounts

open scoped BigOperators
open NearCubicGates.PrimePowerLifting

/-- Computable evaluation of the literal amplifier (no polynomial representation needed). -/
def amplifierValue (e : ℕ) (t : ℤ) : ℤ :=
  1 - (1 - t) ^ e * ∑ j ∈ Finset.range e, ((e - 1 + j).choose j : ℤ) * t ^ j

theorem amplifierValue_eq (e : ℕ) (t : ℤ) :
    amplifierValue e t = (amplifier e).eval t := by
  simp only [amplifierValue, amplifier, binomialTrunc, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_C]

/-- The product of all Fermat tests, before prime-power lifting. -/
def fermatProduct {Forms : Type*} [Fintype Forms]
    (p : ℕ) (scores residues : Forms → ℤ) : ℤ :=
  ∏ i : Forms, (1 - (scores i - residues i) ^ (p - 1))

theorem fermat_test (p : ℕ) (hp : Nat.Prime p) (a b : ℤ) :
    ((1 - (a - b) ^ (p - 1) : ℤ) : ZMod p) =
      if a ≡ b [ZMOD (p : ℤ)] then 1 else 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have heq : ((a - b : ℤ) : ZMod p) = 0 ↔ a ≡ b [ZMOD (p : ℤ)] := by
    rw [Int.cast_sub, sub_eq_zero, ZMod.intCast_eq_intCast_iff]
  by_cases h : a ≡ b [ZMOD (p : ℤ)]
  · have hz := heq.mpr h
    simp only [Int.cast_sub, Int.cast_one, Int.cast_pow, if_pos h]
    rw [show (a : ZMod p) - (b : ZMod p) = 0 from by simpa using hz]
    simp [show p - 1 ≠ 0 by have hh := hp.two_le; omega]
  · have hn : ((a - b : ℤ) : ZMod p) ≠ 0 := fun hz => h (heq.mp hz)
    have hpow := ZMod.pow_card_sub_one_eq_one hn
    simp only [Int.cast_sub] at hpow
    simp only [Int.cast_sub, Int.cast_one, Int.cast_pow, if_neg h]
    rw [hpow, sub_self]

theorem fermat_product_modEq {Forms : Type*} [Fintype Forms]
    (p : ℕ) (hp : Nat.Prime p) (scores residues : Forms → ℤ) :
    fermatProduct p scores residues ≡
      (if ∀ i, scores i ≡ residues i [ZMOD (p : ℤ)] then 1 else 0) [ZMOD (p : ℤ)] := by
  classical
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  simp only [fermatProduct, Int.cast_prod]
  simp_rw [fermat_test p hp]
  by_cases h : ∀ i, scores i ≡ residues i [ZMOD (p : ℤ)]
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [h]

/-- Literal prime-power lifted joint residue indicator, as integer code. -/
def liftedIndicator {Forms : Type*} [Fintype Forms]
    (p e : ℕ) (scores residues : Forms → ℤ) : ℤ :=
  amplifierValue e (fermatProduct p scores residues)

theorem liftedIndicator_modEq {Forms : Type*} [Fintype Forms]
    (p : ℕ) (hp : Nat.Prime p) (e : ℕ) (he : 1 ≤ e)
    (scores residues : Forms → ℤ) :
    liftedIndicator p e scores residues ≡
      (if ∀ i, scores i ≡ residues i [ZMOD (p : ℤ)] then 1 else 0)
        [ZMOD (p : ℤ) ^ e] := by
  classical
  rw [liftedIndicator, amplifierValue_eq]
  have hf := fermat_product_modEq p hp scores residues
  by_cases h : ∀ i, scores i ≡ residues i [ZMOD (p : ℤ)]
  · simp only [if_pos h] at hf ⊢
    exact amplifier_modEq_one e p _ hf
  · simp only [if_neg h] at hf ⊢
    exact amplifier_modEq_zero e he p _ hf

theorem sum_modEq {Points : Type*} [Fintype Points] (f g : Points → ℤ)
    (m : ℤ) (h : ∀ i, f i ≡ g i [ZMOD m]) :
    (∑ i, f i) ≡ (∑ i, g i) [ZMOD m] := by
  classical
  have hfin : ∀ s : Finset Points, (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [ZMOD m] := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact Int.ModEq.rfl
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i).add ih
  exact hfin Finset.univ

/-- The exact count over any finite cell, with the public prime-power guard.
The input scores may be arbitrary signed integers and need not be honest
sampled forms. -/
theorem exact_joint_residue_count {Points Forms : Type*}
    [Fintype Points] [Fintype Forms]
    (p : ℕ) (hp : Nat.Prime p) (e : ℕ) (he : 1 ≤ e)
    (scores : Points → Forms → ℤ) (residues : Forms → ℤ)
    (hsize : Fintype.card Points < p ^ e) :
    (∑ x : Points, liftedIndicator p e (scores x) residues) % ((p : ℤ) ^ e) =
      ((Finset.univ.filter
        (fun x : Points => ∀ i, scores x i ≡ residues i [ZMOD (p : ℤ)])).card : ℤ) := by
  classical
  let good : Finset Points := Finset.univ.filter
    (fun x => ∀ i, scores x i ≡ residues i [ZMOD (p : ℤ)])
  have hsum : (∑ x : Points,
      if ∀ i, scores x i ≡ residues i [ZMOD (p : ℤ)] then (1 : ℤ) else 0) =
        (good.card : ℤ) := by
    simp [good]
  have hmod := sum_modEq
    (fun x => liftedIndicator p e (scores x) residues)
    (fun x => if ∀ i, scores x i ≡ residues i [ZMOD (p : ℤ)] then 1 else 0)
    ((p : ℤ) ^ e) (fun x => liftedIndicator_modEq p hp e he (scores x) residues)
  rw [hsum] at hmod
  have hcount : good.card < p ^ e :=
    (Finset.card_filter_le _ _).trans_lt (by simpa using hsize)
  have hnonneg : (0 : ℤ) ≤ good.card := by omega
  have hlt : (good.card : ℤ) < (p : ℤ) ^ e := by exact_mod_cast hcount
  exact hmod.eq.trans (Int.emod_eq_of_lt hnonneg hlt)

end NearCubicGates.ResidueCounts
