import Proof.Gates.PairCellCounter
import Proof.Gates.CountingCore
import Mathlib.Data.Fintype.Sum

/-! A modular digit vector isolates the exact digit class for arbitrary
    proposals passing the strict windows. The counter's lifted joint tables
    consequently reconstruct the literal score distribution on that class.
    Nothing here assumes that the proposed digits came from sampling. -/

set_option autoImplicit false

namespace NearCubicGates.DigitClassReconstruction

open scoped BigOperators Matrix
open Reconstruction PairCellCounter ResidueCounts CountingCore

variable {Points Digits : Type*} [Fintype Points] [Fintype Digits] {L : ℕ}

abbrev ExactClass (digits : Points → Digits → ℤ) (κ : Digits → ℤ) :=
  {x : Points // ∀ i, digits x i = κ i}

instance exactClassFintype (digits : Points → Digits → ℤ) (κ : Digits → ℤ) :
    Fintype (ExactClass digits κ) := inferInstanceAs (Fintype {x // ∀ i, digits x i = κ i})

omit [Fintype Points] [Fintype Digits] in
theorem digit_class_iff (digits : Points → Digits → ℤ) (κ center : Digits → ℤ)
    (h p : ℤ)
    (hd : ∀ x i, center i - h < digits x i ∧ digits x i < center i + h)
    (hκ : ∀ i, center i - h < κ i ∧ κ i < center i + h)
    (hwidth : 2 * h - 1 ≤ p) (x : Points) :
    (∀ i, digits x i ≡ κ i [ZMOD p]) ↔ ∀ i, digits x i = κ i := by
  constructor
  · intro hm i
    exact centered_digit_residue_unique _ _ _ _ _ (hd x i).1 (hd x i).2
      (hκ i).1 (hκ i).2 hwidth (hm i)
  · intro he i
    rw [he i]

def jointForms (digits : Points → Digits → ℤ) (scores : Points → Fin 2 → ℤ)
    (x : Points) : Digits ⊕ Fin 2 → ℤ := Sum.elim (digits x) (scores x)

def jointResidues (κ : Digits → ℤ) (r : Fin 2 → ℤ) : Digits ⊕ Fin 2 → ℤ :=
  Sum.elim κ r

def jointRaw (digits : Points → Digits → ℤ) (scores : Points → Fin 2 → ℤ)
    (κ : Digits → ℤ) (p e : ℕ) (r : Fin 2 → ℤ) : ℤ :=
  ∑ x : Points, liftedIndicator p e (jointForms digits scores x) (jointResidues κ r)

theorem joint_class_count (digits : Points → Digits → ℤ) (scores : Points → Fin 2 → ℤ)
    (κ center : Digits → ℤ) (h : ℤ) (p e : ℕ) (hp : Nat.Prime p) (he : 1 ≤ e)
    (hsize : Fintype.card Points < p ^ e)
    (hd : ∀ x i, center i - h < digits x i ∧ digits x i < center i + h)
    (hκ : ∀ i, center i - h < κ i ∧ κ i < center i + h)
    (hwidth : 2 * h - 1 ≤ p) (r : Fin 2 → ℤ) :
    jointRaw digits scores κ p e r % (p : ℤ) ^ e =
      ((Finset.univ.filter (fun x : Points =>
        (∀ i, digits x i = κ i) ∧ (∀ i, scores x i ≡ r i [ZMOD (p : ℤ)]))).card : ℤ) := by
  classical
  have hcount := exact_joint_residue_count p hp e he
    (jointForms digits scores) (jointResidues κ r) hsize
  change jointRaw digits scores κ p e r % (p : ℤ) ^ e = _ at hcount
  rw [hcount]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sum.forall,
    jointForms, jointResidues, Sum.elim_inl, Sum.elim_inr]
  rw [digit_class_iff digits κ center h p hd hκ hwidth x]

noncomputable def classData (digits : Points → Digits → ℤ) (scores : Points → Fin 2 → ℤ)
    (κ : Digits → ℤ) (primes : Finset ℕ) (exponent : primes → ℕ) :
    PairResidueRow (fun p : primes => p.val) → ℚ :=
  fun row => ((jointRaw digits scores κ row.1.val (exponent row.1)
    ![(row.2.1.val : ℤ), (row.2.2.val : ℤ)] %
      (row.1.val : ℤ) ^ exponent row.1 : ℤ) : ℚ)

theorem classData_correct
    (digits : Points → Digits → ℤ) (scores : Points → Fin 2 → ℤ)
    (κ center : Digits → ℤ) (h : ℤ)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (exponent : primes → ℕ) (he : ∀ p, 1 ≤ exponent p)
    (hsize : ∀ p, Fintype.card Points < p.val ^ exponent p)
    (hd : ∀ x i, center i - h < digits x i ∧ digits x i < center i + h)
    (hκ : ∀ i, center i - h < κ i ∧ κ i < center i + h)
    (hwidth : ∀ p ∈ primes, 2 * h - 1 ≤ p)
    (lo₁ lo₂ : ℤ) (index : ExactClass digits κ → Fin L × Fin L)
    (hscore : ∀ x : ExactClass digits κ, scores x.val =
      ![lo₁ + ((index x).1.val : ℤ), lo₂ + ((index x).2.val : ℤ)]) :
    classData digits scores κ primes exponent =
      pairMatrix primes lo₁ lo₂ L *ᵥ multiplicities index := by
  classical
  funext row
  rw [classData, joint_class_count digits scores κ center h row.1.val (exponent row.1)
    (hprime _ row.1.property) (he row.1) (hsize row.1) hd hκ
      (hwidth _ row.1.property), matrix_measurements_exact]
  push_cast
  congr 1
  apply Finset.card_bij (fun x hx =>
    (⟨x, (Finset.mem_filter.mp hx).2.1⟩ : ExactClass digits κ))
  · intro x hx
    have hs := (Finset.mem_filter.mp hx).2.2
    have hs' := hscore ⟨x, (Finset.mem_filter.mp hx).2.1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := hs 0
    have h2 := hs 1
    rw [hs'] at h1 h2
    simpa only [Int.ModEq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ row.2.1.val)
        (by exact_mod_cast row.2.1.isLt : (row.2.1.val : ℤ) < (row.1.val : ℤ)),
      Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ row.2.2.val)
        (by exact_mod_cast row.2.2.isLt : (row.2.2.val : ℤ) < (row.1.val : ℤ))]
      using And.intro h1 h2
  · intro x hx y hy hxy
    exact congrArg Subtype.val hxy
  · intro x hx
    refine ⟨x.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨x.property, ?_⟩
      rw [hscore x]
      have hs := (Finset.mem_filter.mp hx).2
      simpa only [Fin.forall_fin_two, Int.ModEq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons,
        Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ row.2.1.val)
          (by exact_mod_cast row.2.1.isLt : (row.2.1.val : ℤ) < (row.1.val : ℤ)),
        Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ row.2.2.val)
          (by exact_mod_cast row.2.2.isLt : (row.2.2.val : ℤ) < (row.1.val : ℤ))] using hs
    · rfl

theorem every_accepted_inverse_recovers_class
    (digits : Points → Digits → ℤ) (scores : Points → Fin 2 → ℤ)
    (κ center : Digits → ℤ) (h : ℤ)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (exponent : primes → ℕ) (he : ∀ p, 1 ≤ exponent p)
    (hsize : ∀ p, Fintype.card Points < p.val ^ exponent p)
    (hd : ∀ x i, center i - h < digits x i ∧ digits x i < center i + h)
    (hκ : ∀ i, center i - h < κ i ∧ κ i < center i + h)
    (hwidth : ∀ p ∈ primes, 2 * h - 1 ≤ p)
    (lo₁ lo₂ : ℤ) (index : ExactClass digits κ → Fin L × Fin L)
    (hscore : ∀ x : ExactClass digits κ, scores x.val =
      ![lo₁ + ((index x).1.val : ℤ), lo₂ + ((index x).2.val : ℤ)])
    (B : Matrix (Fin L × Fin L) (PairResidueRow (fun p : primes => p.val)) ℚ)
    (hB : leftInverseCheck (pairMatrix primes lo₁ lo₂ L) B = true)
    (lookup : Fin L × Fin L → ℚ) :
    (∑ j, lookup j * (B *ᵥ classData digits scores κ primes exponent) j) =
      ∑ x : ExactClass digits κ, lookup (index x) := by
  rw [classData_correct digits scores κ center h primes hprime exponent he hsize
    hd hκ hwidth lo₁ lo₂ index hscore, reconstruct_exact _ B hB]
  exact multiplicity_statistic index lookup

end NearCubicGates.DigitClassReconstruction
