import Proof.Gates.Cells.Sys

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

section Digits
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

/-- The digit `E_j^r(z_y)` (the centre of the digit window). -/
def ctr (rj : Role c × Fin p.J) : ℤ := digit c p wt rj.1.val rj.2.val (extend wt.I y (zeroPoint wt.I))

/-- The number of digit coordinates and the window width. -/
abbrev nDig : ℕ := roleCount c.kind * p.J
abbrev wWin : ℕ := 2 * p.hE - 1

theorem idx_lt (rj : Role c × Fin p.J) : rj.1.val * p.J + rj.2.val < nDig c p := by
  have h1 := rj.1.isLt
  have h2 := rj.2.isLt
  unfold nDig
  calc rj.1.val * p.J + rj.2.val < rj.1.val * p.J + p.J := by omega
    _ = (rj.1.val + 1) * p.J := by ring
    _ ≤ roleCount c.kind * p.J := Nat.mul_le_mul_right _ h1

/-- The digit vector of offsets `v` (entry `r·J + j`). -/
def kappaOf (v : List ℕ) : Role c × Fin p.J → ℤ :=
  fun rj => ctr c p wt y rj - p.hE + 1 + (v.getD (rj.1.val * p.J + rj.2.val) 0 : ℤ)

theorem mem_digitVectors_iff (κ : Role c × Fin p.J → ℤ) :
    κ ∈ digitVectors c p wt y ↔ ∀ rj, ctr c p wt y rj - p.hE < κ rj ∧ κ rj < ctr c p wt y rj + p.hE := by
  simp [digitVectors, Fintype.mem_piFinset, Finset.mem_Ioo, ctr]

theorem kappaOf_mem (v : List ℕ) (hv : v ∈ vecsM (List.replicate (nDig c p) (wWin p))) (hE : 1 ≤ p.hE) :
    kappaOf c p wt y v ∈ digitVectors c p wt y := by
  rw [mem_digitVectors_iff]
  intro rj
  obtain ⟨h1, h2⟩ := (mem_vecsM' _ v).1 hv
  have hi := idx_lt c p rj
  have := h2 _ (by rw [h1, List.length_replicate]; exact hi)
  have e : (List.replicate (nDig c p) (wWin p)).getD (rj.1.val * p.J + rj.2.val) 0 = wWin p := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hi), List.getElem_replicate]
  rw [e] at this
  unfold wWin at this
  simp only [kappaOf]
  omega

/-- The digit coordinate of index `i` (role `i / J`, digit `i % J`). -/
def rjOf (i : ℕ) (h : i < nDig c p) : Role c × Fin p.J :=
  (⟨i / p.J, by
      have hJ : 0 < p.J := by unfold nDig at h; rcases Nat.eq_zero_or_pos p.J with h0 | h0 <;> simp_all
      rw [Nat.div_lt_iff_lt_mul hJ]; exact h⟩,
   ⟨i % p.J, Nat.mod_lt _ (by unfold nDig at h; rcases Nat.eq_zero_or_pos p.J with h0 | h0 <;> simp_all)⟩)

theorem rjOf_idx (rj : Role c × Fin p.J) : rjOf c p (rj.1.val * p.J + rj.2.val) (idx_lt c p rj) = rj := by
  have hJ : 0 < p.J := by have := rj.2.isLt; omega
  unfold rjOf
  ext
  · simp only; rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt rj.2.isLt, zero_add]
  · simp only; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt rj.2.isLt]

theorem idx_rjOf (i : ℕ) (h : i < nDig c p) : (rjOf c p i h).1.val * p.J + (rjOf c p i h).2.val = i := by
  unfold rjOf; simp only; exact Nat.div_add_mod' i p.J

/-- The offsets of a digit vector. -/
def offsOf (κ : Role c × Fin p.J → ℤ) : List ℕ :=
  List.ofFn fun i : Fin (nDig c p) =>
    (κ (rjOf c p i.val i.isLt) - (ctr c p wt y (rjOf c p i.val i.isLt) - p.hE + 1)).toNat

theorem offsOf_getD (κ : Role c × Fin p.J → ℤ) (rj : Role c × Fin p.J) :
    (offsOf c p wt y κ).getD (rj.1.val * p.J + rj.2.val) 0 = (κ rj - (ctr c p wt y rj - p.hE + 1)).toNat := by
  unfold offsOf
  rw [List.getD_eq_getElem _ _ (by simp [idx_lt c p rj]), List.getElem_ofFn]
  simp only [rjOf_idx]

theorem kappaOf_offsOf (κ : Role c × Fin p.J → ℤ) (hκ : κ ∈ digitVectors c p wt y) :
    kappaOf c p wt y (offsOf c p wt y κ) = κ := by
  funext rj
  have := (mem_digitVectors_iff c p wt y κ).1 hκ rj
  simp only [kappaOf, offsOf_getD]
  omega

theorem offsOf_mem (κ : Role c × Fin p.J → ℤ) (hκ : κ ∈ digitVectors c p wt y) :
    offsOf c p wt y κ ∈ vecsM (List.replicate (nDig c p) (wWin p)) := by
  refine (mem_vecsM' _ _).2 ⟨by simp [offsOf], fun i hi => ?_⟩
  have hi' : i < nDig c p := by simpa [offsOf] using hi
  have e : (List.replicate (nDig c p) (wWin p)).getD i 0 = wWin p := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hi'), List.getElem_replicate]
  rw [e, ← idx_rjOf c p i hi', offsOf_getD]
  have := (mem_digitVectors_iff c p wt y κ).1 hκ (rjOf c p i hi')
  unfold wWin
  omega

theorem kappaOf_inj (v w : List ℕ) (hv : v ∈ vecsM (List.replicate (nDig c p) (wWin p)))
    (hw : w ∈ vecsM (List.replicate (nDig c p) (wWin p))) (h : kappaOf c p wt y v = kappaOf c p wt y w) : v = w := by
  obtain ⟨hv1, -⟩ := (mem_vecsM' _ v).1 hv
  obtain ⟨hw1, -⟩ := (mem_vecsM' _ w).1 hw
  rw [List.length_replicate] at hv1 hw1
  apply List.ext_getElem (by rw [hv1, hw1])
  intro i h1 h2
  have hi : i < nDig c p := by omega
  have := congrFun h (rjOf c p i hi)
  simp only [kappaOf, add_right_inj, Nat.cast_inj, idx_rjOf] at this
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- **Sums over the digit vectors are sums over the counter's enumeration.** -/
theorem sum_digitVectors_eq (hE : 1 ≤ p.hE) (g : (Role c × Fin p.J → ℤ) → ℚ) :
    ∑ κ ∈ digitVectors c p wt y, g κ =
      ((vecsM (List.replicate (nDig c p) (wWin p))).map fun v => g (kappaOf c p wt y v)).sum := by
  have hnd : ((vecsM (List.replicate (nDig c p) (wWin p))).map (kappaOf c p wt y)).Nodup :=
    (vecsM_nodup _).map_on (fun v hv w hw h => kappaOf_inj c p wt y v w hv hw h)
  have hfs : ((vecsM (List.replicate (nDig c p) (wWin p))).map (kappaOf c p wt y)).toFinset =
      digitVectors c p wt y := by
    ext κ
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact kappaOf_mem c p wt y v hv hE
    · intro hκ; exact ⟨_, offsOf_mem c p wt y κ hκ, kappaOf_offsOf c p wt y κ hκ⟩
  rw [← hfs, List.sum_toFinset _ hnd, List.map_map]
  rfl

/-- The predicate weight of a score vector on a part (`sec:algorithm`, "Reconstruction inside a certified cell"). -/
def predW (part : Option Bool) (u : Role c → ℤ) : ℚ :=
  if scorePredicate c (xor (outerParity c wt y) (part.getD false)) u then 1 else 0

theorem partAnswer_list {cT : ℕ} (hs : Spec cT (header c) p) (ht : CellTests c p wt y) (part : Option Bool)
    (κ : Role c × Fin p.J → ℤ) (hκ : κ ∈ digitVectors c p wt y) :
    partAnswer c p wt part y κ =
      ((ptsOf c p wt y κ).map fun u => trueDist c p wt y part κ u * predW c wt y part u).sum := by
  classical
  have hex : ∃ F, Solves c p wt part y κ F := ⟨_, trueDist_solves c p wt y hs ht part κ hκ⟩
  have hsol : solveSystem c p wt part y κ = some (Classical.choose hex) := by
    simp only [solveSystem, dif_pos hex]
  have hF := solution_eq_trueDist c p wt y hs ht part κ hκ _ (Classical.choose_spec hex)
  simp only [partAnswer, hsol]
  rw [← ptsOf_toFinset c p wt y κ, List.sum_toFinset _ (ptsOf_nodup c p wt y κ)]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [hF u ((mem_ptsOf c p wt y κ u).1 hu)]
  rfl

theorem hE_pos {cT : ℕ} (hs : Spec cT (header c) p) : 1 ≤ p.hE := by
  rw [hs.hE_eq]; have := hs.P_large; omega

theorem cellCount_eq_sum {cT : ℕ} (hs : Spec cT (header c) p) (ht : CellTests c p wt y) :
    cellCount c p wt y = ((parts c).map fun part =>
      ((vecsM (List.replicate (nDig c p) (wWin p))).map fun v =>
        ((ptsOf c p wt y (kappaOf c p wt y v)).map fun u =>
          trueDist c p wt y part (kappaOf c p wt y v) u * predW c wt y part u).sum).sum).sum := by
  unfold cellCount
  congr 1
  apply List.map_congr_left
  intro part _
  rw [sum_digitVectors_eq c p wt y (hE_pos c p hs)]
  congr 1
  apply List.map_congr_left
  intro v hv
  exact partAnswer_list c p wt y hs ht part _ (kappaOf_mem c p wt y v hv (hE_pos c p hs))

end Digits

end NearCubicGates.Close.Cells
