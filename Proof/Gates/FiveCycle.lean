import Proof.Gates.FiniteAverages
import Proof.Gates.WeightedTable
import Mathlib.Data.Finset.Image
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases

/-! The actual P-position cycle of a five-entry list. Its incidence bound is
    proved by an injection of the complete blocks, not postulated. -/

set_option autoImplicit false

namespace NearCubicGates.FiveCycle

open scoped BigOperators

def slot {P : ℕ} (j : Fin P) : Fin 5 := ⟨j.val % 5, Nat.mod_lt _ (by decide)⟩

def blockAddress (P : ℕ) (i : Fin (P / 5)) (s : Fin 5) : Fin P :=
  ⟨5 * i.val + s.val, by
    have h := Nat.div_mul_le_self P 5
    have hi := i.isLt
    have hs := s.isLt
    omega⟩

@[simp] theorem blockAddress_slot (P : ℕ) (i : Fin (P / 5)) (s : Fin 5) :
    slot (blockAddress P i s) = s := by
  apply Fin.ext
  simp [slot, blockAddress, Nat.add_mod]

theorem blockAddress_injective (P : ℕ) :
    Function.Injective (fun is : Fin (P / 5) × Fin 5 => blockAddress P is.1 is.2) := by
  intro a b hab
  have h := congrArg Fin.val hab
  have ha := a.2.isLt
  have hb := b.2.isLt
  have hi : a.1 = b.1 := by apply Fin.ext; dsimp [blockAddress] at h; omega
  have hs : a.2 = b.2 := by apply Fin.ext; dsimp [blockAddress] at h; omega
  exact Prod.ext hi hs

theorem complete_blocks_sum_le (P : ℕ) (f : Fin P → ℝ)
    (hf : ∀ j, 0 ≤ f j) :
    (∑ i : Fin (P / 5), ∑ s : Fin 5, f (blockAddress P i s)) ≤ ∑ j, f j := by
  classical
  let E : Fin (P / 5) × Fin 5 ↪ Fin P :=
    ⟨fun is => blockAddress P is.1 is.2, blockAddress_injective P⟩
  have h := Finset.sum_le_univ_sum_of_nonneg (s := Finset.univ.map E) hf
  simpa [Finset.sum_map, E, Fintype.sum_prod_type] using h

/-- Every one of the five positions is charged once in each complete block.
    The function `name` can repeat arbitrarily, including twice for a helper. -/
theorem cycle_minimum_bound {Name : Type*} (P : ℕ) (name : Fin 5 → Name)
    (e : Name → ℝ) (err : Fin P → ℝ)
    (_he : ∀ x, 0 ≤ e x) (herr : ∀ j, 0 ≤ err j)
    (hmin : ∀ j, e (name (slot j)) ≤ err j) :
    (P / 5 : ℕ) * (∑ s : Fin 5, e (name s)) ≤ ∑ j, err j := by
  calc
    _ = ∑ i : Fin (P / 5), ∑ s : Fin 5, e (name s) := by simp
    _ ≤ ∑ i : Fin (P / 5), ∑ s : Fin 5, err (blockAddress P i s) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro s _
      simpa using hmin (blockAddress P i s)
    _ ≤ _ := complete_blocks_sum_le P err herr

theorem table_minimum_bound {G Name : Type*} [Fintype G]
    (P : ℕ) (name : G → Fin 5 → Name) (e : Name → ℝ) (err : G → Fin P → ℝ)
    (he : ∀ x, 0 ≤ e x) (herr : ∀ a j, 0 ≤ err a j)
    (hmin : ∀ a j, e (name a (slot j)) ≤ err a j) :
    (P / 5 : ℕ) * (∑ a, ∑ s : Fin 5, e (name a s)) ≤ ∑ a, ∑ j, err a j := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ =>
    cycle_minimum_bound P (name a) e (err a) he (herr a) (hmin a)

/-- The floor hypotheses in the earlier arithmetic lemma now follow from
    the actual integer `P / 5`. -/
theorem cycle_factor (P : ℕ) (ε : ℝ) (hP : 5 ≤ P)
    (hε : 0 < ε) (hε₁ : ε < 1) (hlarge : 128 ≤ ε * P) :
    (P : ℝ) / (P / 5 : ℕ) ≤ 5 + ε := by
  have ht : 0 < P / 5 := Nat.div_pos hP (by decide)
  have hf : P < 5 * (P / 5) + 5 := by omega
  apply WeightedTable.five_position_factor (P : ℝ) (P / 5 : ℕ) ε
    (by exact_mod_cast ht) hε hε₁
  · exact_mod_cast (show (P : ℤ) - 5 < 5 * (P / 5 : ℕ) by omega)
  · exact hlarge

end NearCubicGates.FiveCycle
