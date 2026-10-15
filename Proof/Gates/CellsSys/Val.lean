import Proof.Gates.CellsSys.Role4

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

section V
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

/-- The number of digit vectors. -/
abbrev BN : ℕ := wWin p ^ nDig c p

/-- The joint counts of the system of part `part`, counter value `t` (row order). -/
noncomputable def Rw (part : Option Bool) (t : ℕ) : List ℕ :=
  (rowsOf c p wt y (kap c p wt y t) part).map (fun row => row.2.2)

/-- The term of the system of part `part`, counter value `t`. -/
noncomputable def Tm (part : Option Bool) (t : ℕ) : ℚ :=
  ((ptsOf c p wt y (kap c p wt y t)).map fun u =>
    trueDist c p wt y part (kap c p wt y t) u * predW c wt y part u).sum

theorem vecs_rep : vecsM (List.replicate (nDig c p) (wWin p)) =
    (List.range (BN c p)).map (digitsM (List.replicate (nDig c p) (wWin p))) := by
  rw [vecsM_eq, prod_replicate]

theorem rowVals_eq : rowVals c p wt y =
    (parts c).flatMap fun part => (List.range (BN c p)).flatMap fun t => Rw c p wt y part t := by
  unfold rowVals
  apply List.flatMap_congr
  intro part _
  rw [vecs_rep, List.flatMap_map]
  apply List.flatMap_congr
  intro t _
  simp [Rw, rowsOf, kap, List.map_flatMap, Function.comp_def]

theorem cellCount_eq {cT : ℕ} (hs : Spec cT (header c) p) (ht : CellTests c p wt y) :
    cellCount c p wt y = ((parts c).map fun part => ((List.range (BN c p)).map fun t => Tm c p wt y part t).sum).sum := by
  rw [cellCount_eq_sum c p wt y hs ht]
  congr 1
  apply List.map_congr_left
  intro part _
  rw [vecs_rep, List.map_map]
  rfl

theorem kap_mem {cT : ℕ} (hs : Spec cT (header c) p) (t : ℕ) (ht : t < BN c p) :
    kap c p wt y t ∈ digitVectors c p wt y := by
  apply kappaOf_mem c p wt y _ _ (hE_pos c p hs)
  rw [vecs_rep]
  exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩

theorem boxLo_ge (κ : Role c × Fin p.J → ℤ) (r : Role c) :
    -((circ c r.val).topWeight : ℤ) ≤ boxLo c p wt y κ r := by
  unfold boxLo; simp only; split_ifs with h <;> omega

theorem boxHi_le (κ : Role c × Fin p.J → ℤ) (r : Role c) :
    boxHi c p wt y κ r ≤ ((circ c r.val).topWeight : ℤ) := by
  unfold boxHi; simp only; split_ifs with h <;> omega

theorem pts_le (κ : Role c × Fin p.J → ℤ) : (ptsOf c p wt y κ).length ≤ (2 * c.W + 1) ^ 2 := by
  unfold ptsOf
  rw [List.length_map, vecsM_length]
  have hle : ∀ x ∈ boxLens c p wt y κ, x ≤ 2 * c.W + 1 := by
    intro x hx
    simp only [boxLens, List.mem_map, List.mem_finRange, true_and] at hx
    obtain ⟨r, rfl⟩ := hx
    have h1 := boxLo_ge c p wt y κ r
    have h2 := boxHi_le c p wt y κ r
    have h3 : ((circ c r.val).topWeight : ℤ) ≤ c.W := by exact_mod_cast topWeight_le_W c r.val
    omega
  calc (boxLens c p wt y κ).prod ≤ (2 * c.W + 1) ^ (boxLens c p wt y κ).length := List.prod_le_pow_card _ _ hle
    _ ≤ (2 * c.W + 1) ^ 2 := by
        apply Nat.pow_le_pow_right (by omega)
        rw [boxLens_length]; exact roleCount_le_two c

theorem trueDist_le (part : Option Bool) (κ : Role c × Fin p.J → ℤ) (u : Role c → ℤ) :
    trueDist c p wt y part κ u ≤ 2 ^ c.n := by
  unfold trueDist
  have h1 := Finset.card_filter_le (Finset.univ : Finset (Points wt.I)) (fun x =>
    inPart c wt part x = true ∧ digitVec c p wt y x = κ ∧ scoreVec c wt y x = u)
  have h2 : (Finset.univ : Finset (Points wt.I)).card = 2 ^ wt.I.card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have h3 : wt.I.card ≤ c.n := (Finset.card_le_univ _).trans (by simp)
  have h4 : 2 ^ wt.I.card ≤ 2 ^ c.n := Nat.pow_le_pow_right (by norm_num) h3
  have : ((Finset.univ.filter fun x : Points wt.I =>
      inPart c wt part x = true ∧ digitVec c p wt y x = κ ∧ scoreVec c wt y x = u).card : ℚ) ≤ ((2 ^ c.n : ℕ) : ℚ) := by
    exact_mod_cast (h1.trans (h2 ▸ h4))
  simpa using this

theorem trueDist_nonneg (part : Option Bool) (κ : Role c × Fin p.J → ℤ) (u : Role c → ℤ) :
    0 ≤ trueDist c p wt y part κ u := by unfold trueDist; positivity

theorem predW_le (part : Option Bool) (u : Role c → ℤ) : 0 ≤ predW c wt y part u ∧ predW c wt y part u ≤ 1 := by
  unfold predW; split_ifs <;> norm_num

theorem Tm_bounds (part : Option Bool) (t : ℕ) :
    0 ≤ Tm c p wt y part t ∧ Tm c p wt y part t ≤ ((ptsOf c p wt y (kap c p wt y t)).length * 2 ^ c.n : ℕ) := by
  unfold Tm
  set L := ptsOf c p wt y (kap c p wt y t)
  have hterm : ∀ u, 0 ≤ trueDist c p wt y part (kap c p wt y t) u * predW c wt y part u ∧
      trueDist c p wt y part (kap c p wt y t) u * predW c wt y part u ≤ 2 ^ c.n := fun u => by
    have h1 := trueDist_le c p wt y part (kap c p wt y t) u
    have h0 := trueDist_nonneg c p wt y part (kap c p wt y t) u
    have h2 := predW_le c wt y part u
    constructor
    · exact mul_nonneg h0 h2.1
    · calc _ ≤ trueDist c p wt y part (kap c p wt y t) u * 1 := mul_le_mul_of_nonneg_left h2.2 h0
        _ ≤ 2 ^ c.n := by rw [mul_one]; exact h1
  constructor
  · exact List.sum_nonneg (fun x hx => by
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx; exact (hterm u).1)
  · have := List.sum_le_card_nsmul (L.map fun u => trueDist c p wt y part (kap c p wt y t) u * predW c wt y part u)
      (2 ^ c.n) (fun x hx => by obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx; exact (hterm u).2)
    rw [List.length_map, nsmul_eq_mul] at this
    push_cast; linarith

end V

end NearCubicGates.Close.Cells.SystemsPhase
