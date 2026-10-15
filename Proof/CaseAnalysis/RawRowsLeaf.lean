import Proof.CaseAnalysis.RowsRawOccurrenceBound
import Proof.Circuits.ValidatorPolynomialDomination

namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem sum_length (ps : List StructuralGF2Polynomial) :
    (structuralGF2Sum ps).length = (ps.map List.length).sum := List.length_flatten

theorem mul_length (p q : StructuralGF2Polynomial) :
    (structuralGF2Mul p q).length = p.length*q.length :=
  RepairOrdinary.CloseoutRowsRawOccurrenceBound.mul_length p q

theorem scale_length (c : ZMod 2) (p : StructuralGF2Polynomial) :
    (structuralGF2Scale c p).length ≤ p.length := by
  unfold structuralGF2Scale
  split_ifs <;> simp

theorem sum_map_bound {α : Type} (xs : List α) (f : α → StructuralGF2Polynomial)
    (B : Nat) (hf : ∀ x ∈ xs, (f x).length ≤ B) :
    (structuralGF2Sum (xs.map f)).length ≤ xs.length*B := by
  induction xs with
  | nil => simp [structuralGF2Sum]
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [structuralGF2Sum,List.map_cons,List.flatten_cons,List.length_append,List.length_cons] at ht ⊢
    nlinarith

theorem elementary_bound (codes : List Nat) (d W : Nat) (hd : d ≤ W) :
    (structuralGF2ElementarySymmetric codes d).length ≤ (codes.length+1)^W := by
  change (codes.sublistsLen d).length ≤ _
  rw [List.length_sublistsLen]
  exact (Nat.choose_le_pow codes.length d).trans
    ((Nat.pow_le_pow_left (Nat.le_succ _) d).trans (Nat.pow_le_pow_right (by omega) hd))

theorem shifted_bound (codes : List Nat) (offset d W : Nat) (hd : d ≤ W) :
    (structuralGF2ShiftedElementarySymmetric codes offset d).length ≤
      (d+1)*(codes.length+1)^W := by
  unfold structuralGF2ShiftedElementarySymmetric
  calc
    _ ≤ (List.Nat.antidiagonal d).length*(codes.length+1)^W := by
      apply sum_map_bound
      intro pair hp
      have hs := List.Nat.mem_antidiagonal.mp hp
      exact (scale_length _ _).trans (elementary_bound codes pair.1 W (by omega))
    _ = _ := by rw [List.Nat.length_antidiagonal]

theorem window_bound (codes : List Nat) (offset W target : Nat) :
    (structuralGF2ConsecutiveWindowIndicator codes offset W target).length ≤
      (W+1)^2*(codes.length+1)^W := by
  unfold structuralGF2ConsecutiveWindowIndicator
  calc
    _ ≤ (List.range (W+1)).length*((W+1)*(codes.length+1)^W) := by
      apply sum_map_bound
      intro d hd
      have hW : d ≤ W := by have := List.mem_range.mp hd; omega
      exact (scale_length _ _).trans ((shifted_bound codes offset d W hW).trans
        (Nat.mul_le_mul_right _ (by omega)))
    _ = _ := by rw [List.length_range]; ring

theorem parity_length : ∀ {n : Nat} (ps : Fin n → StructuralGF2Polynomial),
    (structuralGF2FinParity ps).length = ∑ i, (ps i).length
  | 0, _ => by simp [structuralGF2FinParity,structuralGF2Zero]
  | n+1, ps => by
    rw [structuralGF2FinParity]
    simp only [structuralGF2Add,List.length_append]
    change (ps 0).length+(structuralGF2FinParity (fun i : Fin n => ps i.succ)).length = _
    rw [parity_length,Fin.sum_univ_succ]

theorem conjunction_bound {n B : Nat} (ps : Fin n → StructuralGF2Polynomial)
    (h : ∀ i, (ps i).length ≤ B) : (structuralGF2FiniteConjunction ps).length ≤ B^n := by
  have hp := RepairOrdinary.CloseoutRowsRawOccurrenceBound.product_bound B (List.ofFn ps) (by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact h i)
  simpa only [structuralGF2FiniteConjunction,List.length_ofFn] using hp

end NearCubicWires.RepairSource.CloseoutRawRows
