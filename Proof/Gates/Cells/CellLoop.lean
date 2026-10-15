import Proof.Gates.Cells.CellSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable {C : Ctx}

theorem drop_flatMap_range' {α : Type} (f : ℕ → List α) (k J : ℕ) (hk : k < J) (R : List α) :
    ((List.range J).flatMap f ++ R).drop ((List.range k).flatMap f).length =
      f k ++ ((List.range J).flatMap f ++ R).drop ((List.range (k + 1)).flatMap f).length := by
  obtain ⟨d, rfl⟩ : ∃ d, J = k + 1 + d := ⟨J - (k + 1), by omega⟩
  have hs : (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
    rw [List.range_succ, List.flatMap_append]; simp
  rw [List.range_add, List.flatMap_append, hs]
  set A := (List.range k).flatMap f
  set B := (List.map (fun x => k + 1 + x) (List.range d)).flatMap f
  rw [show A ++ f k ++ B ++ R = A ++ (f k ++ (B ++ R)) by simp [List.append_assoc], List.drop_left,
    show A ++ (f k ++ (B ++ R)) = (A ++ f k) ++ (B ++ R) by simp [List.append_assoc], List.drop_left]

theorem flatMap_range_len {α : Type} (f : ℕ → List α) (L : ℕ) (h : ∀ i, (f i).length = L) :
    ∀ k, ((List.range k).flatMap f).length = k * L
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_range_len f L h k]
    simp [h]; ring

theorem vecs_len (q : ℕ) : ∀ d, (vecs q d).length = q ^ d
  | 0 => by simp [vecs]
  | d + 1 => by
    simp only [vecs, List.length_flatMap, List.length_map, vecs_len q d]
    simp [pow_succ, mul_comm]

theorem sum_sort_eq' (s : Finset ℕ) (f : ℕ → ℕ) : ((s.sort (· ≤ ·)).map f).sum = ∑ q ∈ s, f q := by
  rw [((Finset.sort_perm_toList s (· ≤ ·)).map f).sum_eq, Finset.sum_map_toList]

/-- The number of requests (copied from the counter's `requestCount`). -/
theorem reqIds_len (c : Call) (p : Params) : (reqIds c p).length = requestCount c p := by
  unfold reqIds requestCount formCount
  simp only [List.length_append, List.length_flatMap, List.length_map, List.length_range,
    List.length_cons, List.length_nil]
  simp only [sum_sort_eq', List.map_const', List.sum_replicate, smul_eq_mul, vecs_len, List.length_range]
  have : ∀ x : ℕ, x ^ (roleCount c.kind * p.J) * x ^ roleCount c.kind = x ^ (roleCount c.kind * (p.J + 1)) := by
    intro x; rw [← pow_add, show roleCount c.kind * p.J + roleCount c.kind = roleCount c.kind * (p.J + 1) by ring]
  simp only [this]

section L
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

/-- The frames of one cell block. -/
def blkWord (i : ℕ) : List Bool :=
  (blk c p wt i).flatMap fun x => RepairOrdinary.frame (binary (recWidth c p wt) x)

theorem blkWord_length (i : ℕ) :
    (blkWord c p wt i).length = (reqIds c p).length * (2 * recWidth c p wt + 1) := by
  unfold blkWord
  rw [← blk_length c p wt i]
  have h1 : ∀ x, (RepairOrdinary.frame (binary (recWidth c p wt) x)).length = 2 * recWidth c p wt + 1 := by
    intro x
    have := WordPrograms.flatMap_frame_length (recWidth c p wt) [binary (recWidth c p wt) x]
      (fun v hv => by simp at hv; rw [hv]; exact binary_length _ _)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_singleton, one_mul] at this
    exact this
  rw [List.length_flatMap]
  simp only [h1, List.map_const', List.sum_replicate, smul_eq_mul]

include hs hw in
theorem cellWord_eq : cellWord c p wt =
    (List.range (2 ^ cellBits wt.I)).flatMap (blkWord c p wt) ++ [false] := by
  unfold cellWord
  rw [sorted_blocks c p wt hs w hw]
  unfold WordPrograms.recStream blkWord
  simp [List.flatMap_map, List.flatMap_assoc]

include hs hw in
theorem cellWord_drop (i : ℕ) (hi : i < 2 ^ cellBits wt.I) :
    (cellWord c p wt).drop (i * ((reqIds c p).length * (2 * recWidth c p wt + 1))) =
      blkWord c p wt i ++ (cellWord c p wt).drop ((i + 1) * ((reqIds c p).length * (2 * recWidth c p wt + 1))) := by
  have hl := flatMap_range_len (blkWord c p wt) _ (blkWord_length c p wt)
  rw [cellWord_eq c p wt hs w hw, ← hl i, ← hl (i + 1)]
  exact drop_flatMap_range' (blkWord c p wt) i _ hi [false]

end L

end NearCubicGates.Close.Cells
