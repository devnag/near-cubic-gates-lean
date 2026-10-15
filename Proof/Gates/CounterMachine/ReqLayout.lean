import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

variable {n : ℕ}

theorem compl_eq_filter (I : Finset (Fin n)) : Iᶜ = Finset.univ.filter (· ∉ I) := by
  ext i; simp

theorem card_compl_eq (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) : Iᶜ.card = n - k := by
  rw [Finset.card_compl, Fintype.card_fin, hk]

/-- `{i // i ∉ I}` as the subtype of the complement. -/
def notMemEquiv (I : Finset (Fin n)) : {i // i ∉ I} ≃ {i // i ∈ Iᶜ} :=
  Equiv.subtypeEquivRight fun i => by simp

/-- The layout of a tabulation from the inner set. -/
noncomputable def layoutOf (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) : Fin n ≃ Fin k ⊕ Fin (n - k) :=
  (Equiv.sumCompl (· ∈ I)).symm.trans
    (Equiv.sumCongr (I.orderIsoOfFin hk).symm.toEquiv
      ((notMemEquiv I).trans (Iᶜ.orderIsoOfFin (card_compl_eq I hk)).symm.toEquiv))

/-- The inner assignment as a point of the counter (`Points I`). -/
noncomputable def pointsOf (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) (x : Fin k → Bool) : Points I :=
  fun i => x ((I.orderIsoOfFin hk).symm i)

noncomputable def pointsEquiv (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) : (Fin k → Bool) ≃ Points I :=
  (Equiv.arrowCongr (I.orderIsoOfFin hk).toEquiv (Equiv.refl Bool))

theorem pointsEquiv_apply (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) (x : Fin k → Bool) :
    pointsEquiv I hk x = pointsOf I hk x := by
  funext i; simp [pointsEquiv, pointsOf, Equiv.arrowCongr_apply]

theorem layoutOf_mem (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) (i : Fin n) (hi : i ∈ I) :
    layoutOf I hk i = .inl ((I.orderIsoOfFin hk).symm ⟨i, hi⟩) := by
  simp [layoutOf, Equiv.sumCompl, hi]

theorem layoutOf_not_mem (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) (i : Fin n) (hi : i ∉ I) :
    layoutOf I hk i = .inr ((Iᶜ.orderIsoOfFin (card_compl_eq I hk)).symm ⟨i, by simpa using hi⟩) := by
  simp [layoutOf, Equiv.sumCompl, hi, notMemEquiv]
  rfl

theorem idx_compl (I : Finset (Fin n)) (i : Fin n) :
    (Iᶜ.sort (· ≤ ·)).idxOf i = (outerCoords I).idxOf i := by
  unfold outerCoords; rw [compl_eq_filter]

/-- **The joined point is the counter's point**: at the outer index `i` and the inner assignment `x`, lem:print's
`joinPoint` is `extend I (cellOf I i) (pointsOf I hk x)`. -/
theorem joinPoint_layoutOf (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) (i : ℕ) (x : Fin k → Bool) :
    joinPoint (layoutOf I hk) (outerOf (n - k) i) x = extend I (cellOf I i) (pointsOf I hk x) := by
  funext j
  unfold joinPoint extend
  by_cases hj : j ∈ I
  · rw [layoutOf_mem I hk j hj, dif_pos hj]; rfl
  · rw [layoutOf_not_mem I hk j hj, dif_neg hj]
    simp only [Sum.elim_inr, outerOf, cellOf]
    congr 1
    rw [Finset.orderIsoOfFin_symm_apply, idx_compl]

theorem layoutOf_symm_inl (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) (j : Fin k) :
    ((layoutOf I hk).symm (.inl j)).val = (coordsOf I).getD j.val 0 := by
  have h : layoutOf I hk (I.orderEmbOfFin hk j) = .inl j := by
    rw [layoutOf_mem I hk _ (I.orderEmbOfFin_mem hk j)]
    congr 1
    apply (I.orderIsoOfFin hk).injective
    simp only [OrderIso.apply_symm_apply]
    exact Subtype.ext rfl
  rw [(Equiv.symm_apply_eq _).mpr h.symm, Finset.orderEmbOfFin_apply]
  unfold coordsOf
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_map]
  rfl

theorem layoutOf_symm_inr (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) (t : Fin (n - k)) :
    ((layoutOf I hk).symm (.inr t)).val = ((outerCoords I).map Fin.val).getD t.val 0 := by
  have hc := card_compl_eq I hk
  have hm := Iᶜ.orderEmbOfFin_mem hc t
  have hn : Iᶜ.orderEmbOfFin hc t ∉ I := Finset.mem_compl.mp hm
  have h : layoutOf I hk (Iᶜ.orderEmbOfFin hc t) = .inr t := by
    rw [layoutOf_not_mem I hk _ hn]
    congr 1
    apply (Iᶜ.orderIsoOfFin hc).injective
    simp only [OrderIso.apply_symm_apply]
    exact Subtype.ext rfl
  rw [(Equiv.symm_apply_eq _).mpr h.symm, Finset.orderEmbOfFin_apply]
  unfold outerCoords
  have hl : t.val < (Iᶜ.sort (· ≤ ·)).length := by simp [hc]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, ← compl_eq_filter]; exact hl), List.getElem_map]
  congr 2
  rw [compl_eq_filter]

end NearCubicGates.Close.CounterMachine
