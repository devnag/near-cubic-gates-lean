import Proof.Gates.WorkerArith.VerdictVal

/-!
# `upperL` on the gadget-major list is `upperQ` (`eq:gadget-upper`)

For `J : Fin M → Fin 10 → Bool × (ℚ × ℚ)` (flip bit and raw interval of term `t` of gadget `a`), the gadget-major
list `gmList J = (List.finRange M).flatMap (fun a => (List.finRange 10).map (J a))` holds term `(a, t)` at index
`10a + t`, and **`upperL_eq`**: `upperL M (gmList J) = upperQ (fun a t => flipI (J a t))`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicGates.Close.Worker

/-- The gadget-major list. -/
def gmList {M : ℕ} (J : Fin M → Fin 10 → Bool × (ℚ × ℚ)) : List (Bool × (ℚ × ℚ)) :=
  (List.finRange M).flatMap (fun a => (List.finRange 10).map (J a))

theorem gmList_length {M : ℕ} (J : Fin M → Fin 10 → Bool × (ℚ × ℚ)) : (gmList J).length = 10 * M := by
  unfold gmList
  rw [List.length_flatMap]
  simp [List.sum_replicate, List.map_const']
  ring

theorem flatMap_getD_len {α β : Type} (k : ℕ) (f : α → List β) (hf : ∀ x, (f x).length = k) (d : β) :
    ∀ (l : List α) (i j : ℕ) (hi : i < l.length), j < k → (l.flatMap f).getD (k * i + j) d = (f l[i]).getD j d
  | [], i, _, hi, _ => by simp at hi
  | x :: l, 0, j, _, hj => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
    rw [List.getD_append _ _ _ _ (by rw [hf]; exact hj)]
  | x :: l, i + 1, j, hi, hj => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [List.getD_append_right _ _ _ _ (by rw [hf]; nlinarith), hf]
    rw [show k * (i + 1) + j - k = k * i + j by rw [Nat.mul_succ]; omega]
    exact flatMap_getD_len k f hf d l i j (by simpa using hi) hj

theorem gmList_getD {M : ℕ} (J : Fin M → Fin 10 → Bool × (ℚ × ℚ)) (a : Fin M) (t : Fin 10) (d : Bool × (ℚ × ℚ)) :
    (gmList J).getD (10 * a.val + t.val) d = J a t := by
  unfold gmList
  rw [flatMap_getD_len 10 _ (fun x => by simp) d (List.finRange M) a.val t.val (by simp) t.isLt]
  simp [List.getD_eq_getElem?_getD]
  rfl

theorem sum_range_mul10 (f : ℕ → ℚ) (M : ℕ) :
    ∑ i ∈ Finset.range (10 * M), f i = ∑ a ∈ Finset.range M, ∑ t ∈ Finset.range 10, f (10 * a + t) := by
  induction M with
  | zero => simp
  | succ M ih => rw [show 10 * (M + 1) = 10 * M + 10 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ (fun a => ∑ t ∈ Finset.range 10, f (10 * a + t)) M]

/-- **`upperL` on the gadget-major list is `upperQ` of the flipped intervals.** -/
theorem upperL_eq {M : ℕ} (J : Fin M → Fin 10 → Bool × (ℚ × ℚ)) :
    upperL M (gmList J) = upperQ (fun a t => flipI (J a t)) := by
  unfold upperL upperQ
  congr 2
  rw [list_sum_range, gmList_length, sum_range_mul10, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  have h1 : (10 * a.val + t.val) % 10 = t.val := by omega
  have ht : (⟨(10 * a.val + t.val) % 10, Nat.mod_lt _ (by norm_num)⟩ : Fin 10) = t := Fin.ext h1
  rw [ht, gmList_getD]

end NearCubicGates.Close.WorkerArith
