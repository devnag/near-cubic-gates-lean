import Proof.Wire_3_5.Skeleton
import Proof.Wire_3_5.RowsSymState

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Rows

instance instNonemptyMargulisWalkSample (m t : ℕ) [NeZero m] : Nonempty (SupplierWalk.MargulisWalkSample m t) :=
  ⟨⟨(0, 0), fun _ _ => 0⟩⟩

theorem uMean_prod_eq {A C : Type} [Fintype A] [Fintype C] (f : A × C → ℝ) :
    uMean f = uMean (fun a => uMean (fun c => f (a, c))) := by
  unfold uMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div, div_div, mul_comm]

theorem uMean_equiv {A C : Type} [Fintype A] [Fintype C] (e : A ≃ C) (f : C → ℝ) :
    uMean (fun a => f (e a)) = uMean f := by
  unfold uMean
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e f

theorem uMean_const {A : Type} [Fintype A] [Nonempty A] (r : ℝ) : uMean (fun _ : A => r) = r := by
  unfold uMean
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem uMean_prod_swap {A C : Type} [Fintype A] [Fintype C] (f : A → C → ℝ) :
    uMean (fun a => uMean (fun c => f a c)) = uMean (fun c => uMean (fun a => f a c)) := by
  rw [← uMean_prod_eq (fun p : A × C => f p.1 p.2), ← uMean_prod_eq (fun p : C × A => f p.2 p.1)]
  exact (uMean_equiv (Equiv.prodComm C A) (fun p : A × C => f p.1 p.2)).symm

/-- The live-pair average over `Fin N` is the iterated average. -/
theorem liveMean_eq_uMean {N : ℕ} (f : Fin N → Fin N → ℝ) :
    liveMean f = uMean (fun i => uMean (fun j => f i j)) := by
  unfold liveMean uMean
  simp only [Fintype.card_fin]
  rw [← Finset.sum_div, div_div, sq]

theorem seedMaskedMean_eq {Seed : Type} [Fintype Seed] {n a : ℕ} (M : Seed → BitInput n → Bool)
    (C : Fin a → BitInput n → Bool) :
    WireExponent3_5.maskedMean M C =
      uMean (fun e => uMean (fun x => bitR (M e x) * bitR (decide (∀ i, C i x = true)))) := by
  unfold WireExponent3_5.maskedMean
  have hcard : (Fintype.card (BitInput n) : ℝ) = 2 ^ n := by simp [BitInput]
  have h1 : ∀ e x, ((if M e x then (1 : ℝ) else 0) * ∏ i, (if C i x then (1 : ℝ) else 0)) =
      bitR (M e x) * bitR (decide (∀ i, C i x = true)) := by
    intro e x
    rw [← bitR_prod_eq]
    rfl
  simp only [h1]
  unfold uMean
  rw [hcard, ← Finset.sum_div, div_div, mul_comm (2 ^ n : ℝ)]

end NearCubicWires.WireExponent3_5.Primitive
