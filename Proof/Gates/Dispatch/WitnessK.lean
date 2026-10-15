import Proof.Gates.Dispatch.WitnessJ

/-!
# Fragment (W), part K: `witWord` is what `print` writes

`witWord c p wt = natWord k ++ (the set bits of the coordinate mask, as words) ++ ⋃_g segOut g`, for the decoded
witness `wt`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- The coordinate decoder's map. -/
def finOf (n : ℕ) (i : ℕ) : Option (Fin n) := if h : i < n then some ⟨i, h⟩ else none

theorem decode_some (c : Call) (p : Params) (w : List Bool) (wt : Wit c.n) (h : decodeWitness c p w = some wt) :
    wt.I = ((cl w (Target.lambda c.n) p.k).filterMap (finOf c.n)).toFinset ∧
      ∀ s r, wt.coef s r = ((circ c r).coeffs.zip ((segsOf c p w).getD (segmentIndex c s r) [])).map
        fun av => coefOf av.1 av.2 := by
  have hsegs : (readSegments (readBlock w (List.replicate p.k (Target.lambda c.n))).2 (segmentWidths c p)).1 =
      segsOf c p w := by rw [readBlock_snd]; simp [segsOf, List.sum_replicate]
  unfold decodeWitness at h
  rw [hsegs] at h
  dsimp only at h
  split_ifs at h with hok
  · cases h; exact ⟨rfl, fun _ _ => rfl⟩

theorem cl_length (w : List Bool) (lam k : ℕ) : (cl w lam k).length = k := by
  unfold cl; rw [readBlock_fst_length]; simp

theorem filterMap_finOf_length (n : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x < n) : (xs.filterMap (finOf n)).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x < n := h x (by simp)
    rw [List.filterMap_cons, show finOf n x = some ⟨x, hx⟩ by simp [finOf, hx]]
    simp [ih (fun y hy => h y (by simp [hy]))]

theorem mem_filterMap_finOf (n : ℕ) (xs : List ℕ) (y : ℕ) (hy : y < n) :
    (⟨y, hy⟩ : Fin n) ∈ xs.filterMap (finOf n) ↔ y ∈ xs := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hf⟩
    unfold finOf at hf; split_ifs at hf with h
    · cases hf; exact hx
  · intro hm; exact ⟨y, hm, by simp [finOf, hy]⟩

/-- The coordinate words. -/
theorem coords_words (n : ℕ) (xs : List ℕ) (hg : goodC n xs) :
    listWord natWord (coordsOf (xs.filterMap (finOf n)).toFinset) = natWord xs.length ++ maskWords (maskOf n xs) n := by
  have hfilter : coordsOf (xs.filterMap (finOf n)).toFinset = (List.range n).filter fun y => (maskOf n xs).getD y false := by
    rw [coordsOf_eq_filter]
    apply List.filter_congr
    intro y hy
    rw [List.mem_range] at hy
    rw [maskOf_getD]
    simp only [List.mem_toFinset]
    by_cases hm : y ∈ xs
    · simp [hy, hm, (mem_filterMap_finOf n xs y hy).mpr hm]
    · have : (⟨y, hy⟩ : Fin n) ∉ xs.filterMap (finOf n) := fun h => hm ((mem_filterMap_finOf n xs y hy).mp h)
      simp only [hm, and_false, decide_false]
      simp only [decide_eq_false_iff_not, not_exists]
      intro h; exact this
  have hlen : (coordsOf (xs.filterMap (finOf n)).toFinset).length = xs.length := by
    unfold coordsOf
    rw [List.length_map, Finset.length_sort, List.toFinset_card_of_nodup]
    · exact filterMap_finOf_length n xs hg.1
    · refine List.Nodup.filterMap ?_ hg.2
      intro a a' b ha ha'
      unfold finOf at ha ha'
      by_cases h1 : a < n
      · by_cases h2 : a' < n
        · rw [dif_pos h1] at ha; rw [dif_pos h2] at ha'
          simp only [Option.mem_def, Option.some.injEq] at ha ha'
          have := ha.trans ha'.symm; exact congrArg Fin.val this
        · rw [dif_neg h2] at ha'; simp at ha'
      · rw [dif_neg h1] at ha; simp at ha
  unfold listWord
  rw [hlen]
  congr 1
  unfold maskWords; rw [hfilter]

theorem flatMap_range_mul {α : Type} (J R : ℕ) (F : ℕ → List α) :
    (List.range (J * R)).flatMap F = (List.range J).flatMap fun s => (List.range R).flatMap fun r => F (s * R + r) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [show (J + 1) * R = J * R + R by ring, List.range_add, List.flatMap_append, ih, List.range_succ,
      List.flatMap_append, List.flatMap_map]
    simp [Nat.add_comm]

/-- The coefficient words. -/
theorem coefs_words (c : Call) (p : Params) (w : List Bool) (wt : Wit c.n)
    (hcoef : ∀ s r, wt.coef s r = ((circ c r).coeffs.zip ((segsOf c p w).getD (segmentIndex c s r) [])).map
        fun av => coefOf av.1 av.2) :
    (((List.range p.J).flatMap fun s => (List.range (roleCount c.kind)).map fun r => (s, r)).flatMap
      fun sr => listWord Interfaces.intWord (wt.coef sr.1 sr.2)) =
    (List.range (p.J * roleCount c.kind)).flatMap (segOut c p w) := by
  rw [flatMap_range_mul, List.flatMap_assoc]
  apply List.flatMap_congr
  intro s hs
  rw [List.mem_range] at hs
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro r hr
  rw [List.mem_range] at hr
  have hg : s * roleCount c.kind + r < p.J * roleCount c.kind := by nlinarith
  have hm := mod_role c s r hr
  unfold segOut
  rw [hm, hcoef]
  congr 1
  have hlen := segsOf_get_length c p w _ hg
  rw [hm, List.getD_eq_getElem?_getD] at hlen
  apply List.ext_getElem
  · simp [segmentIndex, hlen]
  · intro i h1 h2
    simp only [List.length_map, List.length_zip, segmentIndex] at h1
    simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
    unfold segCoef coefOf
    rw [hm, fieldV_eq c p w _ i hg (by rw [hm]; omega)]
    simp only [segmentIndex, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (show i < ((segsOf c p w)[s * roleCount c.kind + r]?.getD []).length by
      rw [hlen]; simp [List.length_map] at h1 h2; omega)]
    simp [List.getElem?_eq_getElem (show i < (circ c r).coeffs.length by simp at h1 h2; omega)]

/-- **`witWord` in the printer's form.** -/
theorem witWord_eq (c : Call) (p : Params) (w : List Bool) (wt : Wit c.n) (h : decodeWitness c p w = some wt) :
    witWord c p wt = natWord p.k ++ maskWords (maskOf c.n (cl w (Target.lambda c.n) p.k)) c.n ++
      (List.range (p.J * roleCount c.kind)).flatMap (segOut c p w) := by
  obtain ⟨hI, hcoef⟩ := decode_some c p w wt h
  have hok := (decode_isSome_iff c p w).mp (by rw [h]; rfl)
  unfold witWord
  rw [hI, coords_words c.n _ hok.1, cl_length, coefs_words c p w wt hcoef]

end NearCubicGates.Close.Dispatch
