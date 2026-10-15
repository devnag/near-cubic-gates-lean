import Proof.Gates.Gadget
import Proof.Gates.FiveCycle
import Proof.Gates.NameCofactors
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

/-! The actual cycling table, unsigned names, literal signs, one shared
    cofactor per name, and its aggregate gadget penalty. This proves the
    finite combinatorial transfer without an incidence hypothesis. -/

set_option autoImplicit false

namespace NearCubicGates.GadgetTableTransfer

open scoped BigOperators
open FiniteAverages FiveCycle

variable {G Name Input : Type*} [Fintype G] [Nonempty G]
  [Fintype Input] [Nonempty Input]

def literal (negative value : Bool) : Bool := if negative then !value else value

theorem literal_mismatch (negative a b : Bool) :
    mismatch (literal negative a) (literal negative b) = mismatch a b := by
  cases negative <;> simp [literal, mismatch_not]

omit [Nonempty Input] in
theorem literal_error (negative : Bool) (a b : Input → Bool) :
    error (fun x => literal negative (a x)) (fun x => literal negative (b x)) =
      error a b := by simp [error, literal_mismatch]

noncomputable def table {P : ℕ} (name : G → Fin 5 → Name)
    (honest : Name → Input → Bool) (a : G × Fin P) (x : Input) : Bool :=
  honest (name a.1 (slot a.2)) x

noncomputable def cofactors {P : ℕ} (hP : 0 < P) (name : G → Fin 5 → Name)
    (honest : Name → Input → Bool) (candidate : G × Fin P → Input → Bool) :
    Name → Input → Bool := by
  letI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  exact NameCofactors.selected (fun a => name a.1 (slot a.2)) honest candidate

omit [Nonempty Input] in
theorem cofactor_error_le {P : ℕ} (hP : 0 < P) (name : G → Fin 5 → Name)
    (honest : Name → Input → Bool) (candidate : G × Fin P → Input → Bool)
    (a : G) (j : Fin P) :
    error (honest (name a (slot j))) (cofactors hP name honest candidate (name a (slot j))) ≤
      error (table name honest (a, j)) (candidate (a, j)) := by
  letI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  exact NameCofactors.selected_error_le (fun a => name a.1 (slot a.2))
    honest candidate (a, j)

noncomputable def penalty (name : G → Fin 5 → Name) (negative : G → Fin 3 → Bool)
    (assignment : Name → Input → Bool) (a : G) (x : Input) : ℝ :=
  (Gadget.penalty
    (literal (negative a 0) (assignment (name a 0) x))
    (literal (negative a 1) (assignment (name a 1) x))
    (literal (negative a 2) (assignment (name a 2) x))
    (assignment (name a 3) x) : ℤ)

theorem distance_cast (a b : Bool) : (Gadget.distance a b : ℝ) = mismatch a b := by
  cases a <;> cases b <;> norm_num [Gadget.distance, mismatch]

omit [Fintype G] [Nonempty G] [Fintype Input] [Nonempty Input] in
/-- Literal signs stay in the verifier; the two helper entries share a name. -/
theorem pointwise_stability (name : G → Fin 5 → Name) (negative : G → Fin 3 → Bool)
    (honest chosen : Name → Input → Bool)
    (htrue : ∀ a x, Gadget.originalClause
      (literal (negative a 0) (honest (name a 0) x))
      (literal (negative a 1) (honest (name a 1) x))
      (literal (negative a 2) (honest (name a 2) x)) = true)
    (hhelper : ∀ a x, honest (name a 3) x = Gadget.honestHelper
      (literal (negative a 0) (honest (name a 0) x))
      (literal (negative a 1) (honest (name a 1) x))
      (literal (negative a 2) (honest (name a 2) x)))
    (hduplicate : ∀ a, name a 4 = name a 3) (a : G) (x : Input) :
    penalty name negative chosen a x ≤
      ∑ s : Fin 5, mismatch (honest (name a s) x) (chosen (name a s) x) := by
  have h := Gadget.weighted_stability
    (literal (negative a 0) (honest (name a 0) x))
    (literal (negative a 1) (honest (name a 1) x))
    (literal (negative a 2) (honest (name a 2) x))
    (literal (negative a 0) (chosen (name a 0) x))
    (literal (negative a 1) (chosen (name a 1) x))
    (literal (negative a 2) (chosen (name a 2) x))
    (chosen (name a 3) x) (htrue a x)
  have hc : (Gadget.penalty
    (literal (negative a 0) (chosen (name a 0) x))
    (literal (negative a 1) (chosen (name a 1) x))
    (literal (negative a 2) (chosen (name a 2) x))
    (chosen (name a 3) x) : ℝ) ≤
      (Gadget.weightedError
        (literal (negative a 0) (honest (name a 0) x))
        (literal (negative a 1) (honest (name a 1) x))
        (literal (negative a 2) (honest (name a 2) x))
        (literal (negative a 0) (chosen (name a 0) x))
        (literal (negative a 1) (chosen (name a 1) x))
        (literal (negative a 2) (chosen (name a 2) x))
        (chosen (name a 3) x) : ℝ) := by exact_mod_cast h
  simpa [penalty, Gadget.weightedError, ← hhelper a x, Int.cast_add, Int.cast_mul,
    distance_cast, literal_mismatch, Fin.sum_univ_succ, hduplicate, two_mul,
    add_assoc] using hc

/-- Complete averaged stability for the concrete cycling table. -/
theorem chosen_table_penalty_bound {P : ℕ} (hP : 5 ≤ P)
    (name : G → Fin 5 → Name) (negative : G → Fin 3 → Bool)
    (honest chosen : Name → Input → Bool) (candidate : G × Fin P → Input → Bool)
    (htrue : ∀ a x, Gadget.originalClause
      (literal (negative a 0) (honest (name a 0) x))
      (literal (negative a 1) (honest (name a 1) x))
      (literal (negative a 2) (honest (name a 2) x)) = true)
    (hhelper : ∀ a x, honest (name a 3) x = Gadget.honestHelper
      (literal (negative a 0) (honest (name a 0) x))
      (literal (negative a 1) (honest (name a 1) x))
      (literal (negative a 2) (honest (name a 2) x)))
    (hduplicate : ∀ a, name a 4 = name a 3)
    (hchoice : ∀ a j, error (honest (name a (slot j))) (chosen (name a (slot j))) ≤
      error (table name honest (a, j)) (candidate (a, j))) :
    mean (fun a => mean (penalty name negative chosen a)) ≤
      ((P : ℝ) / (P / 5 : ℕ)) *
        mean (fun a : G × Fin P => error (table name honest a) (candidate a)) := by
  let hp : 0 < P := by omega
  let e := fun n => error (honest n) (chosen n)
  let err := fun a j => error (table name honest (a, j)) (candidate (a, j))
  have hs : ∀ a, mean (penalty name negative chosen a) ≤ ∑ s : Fin 5, e (name a s) := by
    intro a
    have hm := mean_le_mean _ _ (pointwise_stability name negative honest chosen
      htrue hhelper hduplicate a)
    simpa [mean_finset_sum, e, error] using hm
  have ht : 0 < P / 5 := Nat.div_pos hP (by decide)
  have htR : (0 : ℝ) < (P / 5 : ℕ) := by exact_mod_cast ht
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hPR : (0 : ℝ) < P := by exact_mod_cast hp
  have hmin := table_minimum_bound P name e err
    (fun n => error_nonneg _ _) (fun a j => error_nonneg _ _)
    hchoice
  have hpen : (P / 5 : ℕ) * (∑ a, mean (penalty name negative chosen a)) ≤
      ∑ a, ∑ j, err a j := by
    exact (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hs a)
      htR.le).trans hmin
  have hδ : (∑ a, ∑ j, err a j) = (Fintype.card G : ℝ) * P *
      mean (fun a : G × Fin P => error (table name honest a) (candidate a)) := by
    simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin,
      Nat.cast_mul, err]
    field_simp
  apply WeightedTable.normalized_table_bound
    (mean (fun a => mean (penalty name negative chosen a)))
    (∑ a, ∑ j, err a j) (Fintype.card G) P (P / 5 : ℕ)
    (mean (fun a : G × Fin P => error (table name honest a) (candidate a))) hG htR
  · calc
      _ = (P / 5 : ℕ) * (∑ a, mean (penalty name negative chosen a)) := by
        rw [mul_assoc, mul_left_comm, card_mul_mean]
      _ ≤ _ := hpen
  · exact hδ

theorem table_penalty_bound {P : ℕ} (hP : 5 ≤ P)
    (name : G → Fin 5 → Name) (negative : G → Fin 3 → Bool)
    (honest : Name → Input → Bool) (candidate : G × Fin P → Input → Bool)
    (htrue : ∀ a x, Gadget.originalClause
      (literal (negative a 0) (honest (name a 0) x))
      (literal (negative a 1) (honest (name a 1) x))
      (literal (negative a 2) (honest (name a 2) x)) = true)
    (hhelper : ∀ a x, honest (name a 3) x = Gadget.honestHelper
      (literal (negative a 0) (honest (name a 0) x))
      (literal (negative a 1) (honest (name a 1) x))
      (literal (negative a 2) (honest (name a 2) x)))
    (hduplicate : ∀ a, name a 4 = name a 3) :
    let chosen := cofactors (by omega : 0 < P) name honest candidate
    mean (fun a => mean (penalty name negative chosen a)) ≤
      ((P : ℝ) / (P / 5 : ℕ)) *
        mean (fun a : G × Fin P => error (table name honest a) (candidate a)) := by
  exact chosen_table_penalty_bound hP name negative honest _ candidate htrue hhelper hduplicate
    (cofactor_error_le (by omega) name honest candidate)

end NearCubicGates.GadgetTableTransfer
