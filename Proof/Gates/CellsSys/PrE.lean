import Proof.Gates.CellsSys.PrD

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

theorem fms (l : List ℕ) : l.flatMap (fun a => [[a]]) = l.map (fun a => [a]) := by
  induction l <;> simp_all

theorem vecsM_two (bs : List ℕ) (h : bs.length = 1 ∨ bs.length = 2) :
    vecsM bs = (List.range (bs.getD 0 1)).flatMap
      (fun a => (List.range (bs.getD 1 1)).map (fun b => [a, b].take bs.length)) := by
  rcases bs with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at h
  · simp [vecsM]
  · simp [vecsM, fms, Function.comp_def]
  · simp at h

section W
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ)

theorem rc12 : roleCount c.kind = 1 ∨ roleCount c.kind = 2 := by
  have := roleCount_pos c.kind; have := roleCount_le_two c; omega

theorem ofFn_ptOf (a b : ℕ) : List.ofFn (ptOf c p wt y κ ([a, b].take (roleCount c.kind))) =
    [loR c p wt y κ 0 + a] ++ (if 1 < roleCount c.kind then [loR c p wt y κ 1 + b] else []) := by
  have hrc := roleCount_pos c.kind
  have hrc2 := roleCount_le_two c
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_singleton]; split_ifs <;> simp <;> omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    rw [List.getElem_ofFn]
    unfold ptOf loR
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [dif_pos hrc]
      have : ([a, b].take (roleCount c.kind)).getD 0 0 = a := by
        rcases (show roleCount c.kind = 1 ∨ roleCount c.kind = 2 by omega) with h | h <;> rw [h] <;> rfl
      simp only [List.getD_eq_getElem?_getD] at this
      simp [this]
    · have h2' : 1 < roleCount c.kind := by omega
      simp [h2']

theorem boxLens_get0 : (boxLens c p wt y κ).getD 0 1 = lenR c p wt y κ 0 := by
  have hrc := roleCount_pos c.kind
  rw [List.getD_eq_getElem _ _ (by rw [boxLens_length]; exact hrc)]
  unfold lenR; rw [dif_pos hrc]; simp [boxLens]

theorem boxLens_get1 : (boxLens c p wt y κ).getD 1 1 = lenR c p wt y κ 1 := by
  unfold lenR
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by rw [boxLens_length]; exact h)]; simp [boxLens]
  · rw [List.getD_eq_default _ _ (by rw [boxLens_length]; omega)]

theorem intWord_lo (r a : ℕ) : Interfaces.intWord (zOf ((loR c p wt y κ r).toNat + a) (-loR c p wt y κ r).toNat) =
    Interfaces.intWord (loR c p wt y κ r + a) := by
  congr 1; unfold zOf; omega

/-- **The points, in the order `ptsP` prints them.** -/
theorem pts_word : ((ptsOf c p wt y κ).map fun u => List.ofFn u).flatMap (listWord Interfaces.intWord) =
    (List.range (lenR c p wt y κ 0)).flatMap (rowPts (roleCount c.kind) (loR c p wt y κ 0).toNat
      (-loR c p wt y κ 0).toNat (loR c p wt y κ 1).toNat (-loR c p wt y κ 1).toNat (lenR c p wt y κ 1)) := by
  unfold ptsOf
  rw [vecsM_two _ (by rw [boxLens_length]; exact rc12 c), boxLens_get0, boxLens_get1, boxLens_length]
  simp only [List.map_map, List.map_flatMap, List.flatMap_assoc]
  unfold rowPts
  apply List.flatMap_congr
  intro a _
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro b _
  simp only [Function.comp, ofFn_ptOf, ptWn, listWord, intWord_lo]
  have hl : ([loR c p wt y κ 0 + a] ++ (if 1 < roleCount c.kind then [loR c p wt y κ 1 + b] else [])).length =
      roleCount c.kind := by
    have := rc12 c; split_ifs <;> simp <;> omega
  rw [hl]
  split_ifs <;> simp

theorem pts_len : ((ptsOf c p wt y κ).map fun u => List.ofFn u).length = lenR c p wt y κ 0 * lenR c p wt y κ 1 := by
  rw [List.length_map]
  unfold ptsOf
  rw [List.length_map, vecsM_two _ (by rw [boxLens_length]; exact rc12 c), boxLens_get0, boxLens_get1]
  simp [List.length_flatMap]

/-- The joint count of the row `(q, s0, s1)`. -/
noncomputable def Jf (part : Option Bool) (q s0 s1 : ℕ) : ℕ :=
  jointCount c p wt q part y κ (fun r => ((([s0, s1].take (roleCount c.kind)).getD r.val 0 : ℕ) : ℤ))

theorem vecs_two (q : ℕ) : vecs q (roleCount c.kind) = (List.range q).flatMap
    (fun s0 => (List.range (qBn q (roleCount c.kind))).map (fun s1 => [s0, s1].take (roleCount c.kind))) := by
  have h12 := rc12 c
  rw [vecs_eq_vecsM, vecsM_two _ (by simpa using h12)]
  simp only [List.length_replicate]
  have e0 : (List.replicate (roleCount c.kind) q).getD 0 1 = q := by
    rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
  have e1 : (List.replicate (roleCount c.kind) q).getD 1 1 = qBn q (roleCount c.kind) := by
    unfold qBn; split_ifs with h
    · rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]
  rw [e0, e1]

theorem row_word (d q s0 s1 v : ℕ) (hd : d = 1 ∨ d = 2) :
    natWord q ++ listWord natWord ([s0, s1].take d) ++ natWord v = rowWn d q s0 s1 v := by
  rcases hd with rfl | rfl <;> simp [rowWn, listWord]

theorem rowsOf_eq (part : Option Bool) : rowsOf c p wt y κ part = (p.primes.sort (· ≤ ·)).flatMap fun q =>
    (List.range q).flatMap fun s0 => (List.range (qBn q (roleCount c.kind))).map fun s1 =>
      (q, [s0, s1].take (roleCount c.kind), Jf c p wt y κ part q s0 s1) := by
  unfold rowsOf
  apply List.flatMap_congr
  intro q _
  rw [vecs_two, List.map_flatMap]
  apply List.flatMap_congr
  intro s0 _
  rw [List.map_map]
  rfl

/-- **The rows, in the order `rowsQ` prints them.** -/
theorem rows_word (part : Option Bool) :
    (rowsOf c p wt y κ part).flatMap (fun row : ℕ × List ℕ × ℕ => natWord row.1 ++ listWord natWord row.2.1 ++
      natWord row.2.2) = (p.primes.sort (· ≤ ·)).flatMap (rowsS0W (roleCount c.kind) (Jf c p wt y κ part)) := by
  rw [rowsOf_eq, List.flatMap_assoc]
  apply List.flatMap_congr
  intro q _
  unfold rowsS0W
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro s0 _
  unfold rowsS1W
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro s1 _
  exact row_word _ _ _ _ _ (rc12 c)

theorem rows_vals (part : Option Bool) : (rowsOf c p wt y κ part).map (fun row => row.2.2) =
    (p.primes.sort (· ≤ ·)).flatMap (rowsS0A (roleCount c.kind) (Jf c p wt y κ part)) := by
  rw [rowsOf_eq, List.map_flatMap]
  apply List.flatMap_congr
  intro q _
  unfold rowsS0A
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro s0 _
  unfold rowsS1A
  rw [List.map_map]
  rfl

theorem rows_len (part : Option Bool) : (rowsOf c p wt y κ part).length =
    ((p.primes.sort (· ≤ ·)).map fun q => q * qBn q (roleCount c.kind)).sum := by
  rw [rowsOf_eq]
  simp [List.length_flatMap]

end W

end NearCubicGates.Close.Cells.SystemsPhase
