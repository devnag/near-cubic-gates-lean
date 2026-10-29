import SourceAdapters.Proximity.ClauseBlocks
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Q02, `app:sources`, "Uniform three-query PCPP and code interfaces" and CW19 Appendix A, p. 19:39: a rejected old coin
string forces at least one rejection in its padded clause block. Counting
these witnesses proves a rejection gap of at least the old gap divided by B.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": `r + k` binary coins are exactly an independent old coin and block index. -/
def splitBinaryCoins (r k : ℕ) : Fin (2 ^ (r + k)) ≃ Fin (2 ^ r) × Fin (2 ^ k) :=
  (finCongr (pow_add 2 r k)).trans finProdFinEquiv.symm

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": choose one false clause in each rejected old row. -/
theorem block_reject_count {R B : ℕ} (hB : 0 < B)
    (old : Fin R → Bool) (fresh : Fin R × Fin B → Bool)
    (hrow : ∀ i, old i = false → ∃ j, fresh (i, j) = false) :
    (Finset.univ.filter fun i => old i = false).card ≤
      (Finset.univ.filter fun p => fresh p = false).card := by
  classical
  let pick (i : Fin R) : Fin B :=
    if h : old i = false then Classical.choose (hrow i h) else ⟨0, hB⟩
  apply Finset.card_le_card_of_injOn (fun i => (i, pick i))
  · intro i hi
    have hold : old i = false := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [pick]
    rw [dif_pos hold]
    exact Classical.choose_spec (hrow i hold)
  · intro i _ j _ h
    exact congrArg Prod.fst h

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the exact rejection loss for a uniform padded block. -/
theorem block_soundness {R B : ℕ} (hR : 0 < R) (hB : 0 < B)
    (old : Fin R → Bool) (fresh : Fin R × Fin B → Bool)
    (hrow : ∀ i, old i = false → ∃ j, fresh (i, j) = false)
    (s : ℝ)
    (hs : ((Finset.univ.filter fun i => old i = true).card : ℝ) / R ≤ s) :
    ((Finset.univ.filter fun p => fresh p = true).card : ℝ) / (R * B) ≤
      1 - (1 - s) / B := by
  classical
  have hcount := block_reject_count hB old fresh hrow
  have hold := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin R))) (fun i => old i = true)
  have hfresh := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin R × Fin B))) (fun p => fresh p = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin,
    Fintype.card_prod] at hold hfresh
  have hcountR : ((Finset.univ.filter fun i => old i = false).card : ℝ) ≤
      ((Finset.univ.filter fun p => fresh p = false).card : ℝ) := by exact_mod_cast hcount
  have holdR : ((Finset.univ.filter fun i => old i = true).card : ℝ) +
      ((Finset.univ.filter fun i => old i = false).card : ℝ) = R := by exact_mod_cast hold
  have hfreshR : ((Finset.univ.filter fun p => fresh p = true).card : ℝ) +
      ((Finset.univ.filter fun p => fresh p = false).card : ℝ) = (R : ℝ) * B := by
    exact_mod_cast hfresh
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hsa := (div_le_iff₀ hRp).mp hs
  apply (div_le_iff₀ (mul_pos hRp hBp)).mpr
  calc
    ((Finset.univ.filter fun p => fresh p = true).card : ℝ) ≤
        (R : ℝ) * B - (1 - s) * R := by nlinarith
    _ = (1 - (1 - s) / B) * ((R : ℝ) * B) := by
      field_simp

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the new soundness constant stays strictly between zero and one. -/
theorem block_soundness_range {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {B : ℕ} (hB : 0 < B) :
    0 < 1 - (1 - s) / B ∧ 1 - (1 - s) / B < 1 := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hBone : (1 : ℝ) ≤ B := by exact_mod_cast hB
  constructor
  · have hlt : (1 - s) / B < 1 := by
      apply (div_lt_iff₀ hBpos).mpr
      linarith
    linarith
  · have : 0 < (1 - s) / B := div_pos (by linarith) hBpos
    linarith

end NearCubicGates.Adapters.Proximity
