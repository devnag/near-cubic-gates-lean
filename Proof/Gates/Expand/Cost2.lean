import Proof.Gates.Expand.Cost1

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

theorem degree_le_weight {V : ℕ} (F : Formula V) : F.degree ≤ F.weight := by
  induction F with
  | const a => simp [Formula.degree]
  | var v => simp [Formula.degree, Formula.weight]
  | add f g hf hg => simp only [Formula.degree, Formula.weight]; omega
  | neg f hf => simpa [Formula.degree, Formula.weight] using hf
  | sub f g hf hg => simp only [Formula.degree, Formula.weight]; omega
  | mul f g hf hg => simp only [Formula.degree, Formula.weight]; omega
  | pow f e hf => simp only [Formula.degree, Formula.weight]; exact Nat.mul_le_mul_left _ hf

theorem nbl_le_of_lt (n k : ℕ) (h : n < 2 ^ k) : natBitLength n ≤ k + 1 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  · have := Nat.log_lt_of_lt_pow (by omega) h; omega

theorem natWord_len_le (n k : ℕ) (h : n < 2 ^ k) : (natWord n).length ≤ 2 * k + 3 := by
  rw [natWord_len]; have := nbl_le_of_lt n k h; omega

theorem nbl_V_le (r : FormulaReq) : natBitLength r.1 ≤ Lw r := by
  have : (natWord r.1).length ≤ Lw r := by unfold Lw formulaWord; simp
  rw [natWord_len] at this; omega

theorem monoWord_le {V : ℕ} (F : Formula V) (t : Finset (Fin V) × ℤ) (ht : t ∈ expandM F) :
    (monoWord t).length ≤ 2 * F.degree + 3 + F.degree * (2 * V + 3) + 5 + (2 * (F.weight + 1) + 3) := by
  simp only [expandM, List.mem_map, List.mem_filter] at ht
  obtain ⟨S, ⟨hS, _⟩, rfl⟩ := ht
  have hc : S.card ≤ F.degree := famS_card V F.degree S hS
  have hco : (coeff F.expand S).natAbs < 2 ^ (F.weight + 1) := by
    have h1 := expandM_coeff_le F S
    have h2 := Formula.mass_le_two_pow_weight F
    have h3 : 2 ^ F.weight < 2 ^ (F.weight + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  simp only [monoWord, Interfaces.listWord, Interfaces.intWord, List.length_append, List.length_map, Finset.length_sort,
    List.length_flatMap]
  have a1 := natWord_len_le S.card F.degree (lt_of_le_of_lt hc Nat.lt_two_pow_self)
  have a2 : ((S.sort (· ≤ ·)).map fun v : Fin V => (natWord v.val).length).sum ≤ S.card * (2 * V + 3) := by
    have : ∀ x ∈ (S.sort (· ≤ ·)).map fun v : Fin V => (natWord v.val).length, x ≤ 2 * V + 3 := by
      intro x hx; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact natWord_len_le _ _ (lt_trans v.isLt Nat.lt_two_pow_self)
    have := List.sum_le_card_nsmul _ _ this
    simpa [Finset.length_sort] using this
  have a3 := natWord_len_le (if coeff F.expand S < 0 then 1 else 0) 1 (by split_ifs <;> norm_num)
  have a4 := natWord_len_le _ _ hco
  have a5 : S.card * (2 * V + 3) ≤ F.degree * (2 * V + 3) := Nat.mul_le_mul_right _ hc
  simp only [List.map_map, Function.comp_def]
  omega

theorem expandM_length_le {V : ℕ} (F : Formula V) : (expandM F).length ≤ (fam V F.degree).length := by
  unfold expandM famS; simp only [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem termsWord_le {V : ℕ} (F : Formula V) : (termsWord (expandM F)).length ≤
    2 * (fam V F.degree).length + 3 + (fam V F.degree).length *
      (2 * F.degree + 3 + F.degree * (2 * V + 3) + 5 + (2 * (F.weight + 1) + 3)) := by
  unfold termsWord Interfaces.listWord
  rw [List.length_append, List.length_flatMap]
  have h1 := expandM_length_le F
  have a1 := natWord_len_le (expandM F).length (fam V F.degree).length
    (lt_of_le_of_lt h1 Nat.lt_two_pow_self)
  have a2 := List.sum_le_card_nsmul ((expandM F).map fun t => (monoWord t).length)
    (2 * F.degree + 3 + F.degree * (2 * V + 3) + 5 + (2 * (F.weight + 1) + 3)) (by
      intro x hx; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact monoWord_le F t ht)
  simp only [List.length_map, smul_eq_mul] at a2
  have a3 := Nat.mul_le_mul_right (2 * F.degree + 3 + F.degree * (2 * V + 3) + 5 + (2 * (F.weight + 1) + 3)) h1
  omega

end NearCubicGates.Close.Expand.Layout
