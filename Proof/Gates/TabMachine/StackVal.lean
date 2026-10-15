import Proof.Gates.TabMachine.Tuple
import Proof.Gates.TabMachine.CutsVal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Tabulator

/-- The stacked field `j`: `Σ_{c < k} b^c · ls[c][j]` (first `k` children). -/
def fsum (b : ℤ) (ls : List (List ℤ)) (j k : ℕ) : ℤ :=
  ((List.range k).map fun c => b ^ c * (ls.getD c []).getD j 0).sum

theorem fsum_succ (b : ℤ) (ls : List (List ℤ)) (j k : ℕ) :
    fsum b ls j (k + 1) = fsum b ls j k + b ^ k * (ls.getD k []).getD j 0 := by
  unfold fsum; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem fsum_cons (b : ℤ) (l : List ℤ) (ls : List (List ℤ)) (j : ℕ) :
    fsum b (l :: ls) j (ls.length + 1) = l.getD j 0 + b * fsum b ls j ls.length := by
  unfold fsum
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, ← List.sum_map_mul_left]
  simp only [pow_zero, one_mul, List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  rw [Nat.succ_eq_add_one, pow_succ]; ring

theorem stackL_eq (s : ℕ) (b : ℤ) (ls : List (List ℤ)) (h : ∀ l ∈ ls, l.length = s + 1) :
    stackL s b ls = (List.range (s + 1)).map fun j => fsum b ls j ls.length := by
  induction ls with
  | nil => simp [stackL, fsum, List.map_const']
  | cons l ls ih =>
    rw [stackL, ih (fun l' hl' => h l' (by simp [hl']))]
    apply List.ext_getElem
    · simp [h l (by simp)]
    · intro j h1 h2
      have hj : j < s + 1 := by simpa using h2
      have hl : l.length = s + 1 := h l (by simp)
      rw [List.getElem_zipWith, List.getElem_map, List.getElem_map, List.getElem_range,
        List.length_cons, fsum_cons, List.getD_eq_getElem _ _ (by omega)]

/-- The flat tuple's entry `c·N + j` is field `j` of child `c`. -/
theorem flat_get (N : ℕ) (ls : List (List ℤ)) (h : ∀ l ∈ ls, l.length = N) (c j : ℕ) (hc : c < ls.length)
    (hj : j < N) : ls.flatten.getD (c * N + j) 0 = (ls.getD c []).getD j 0 := by
  have hct := chunk_drop_take N ls c h hc
  have hl : (ls.flatten.drop (c * N)).take N = ls[c] := hct
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hc]
  simp only [Option.getD_some]
  rw [← hl, List.getElem?_take, if_pos hj, List.getElem?_drop]

theorem fsum_bound (b : ℕ) (hb : 1 ≤ b) (ls : List (List ℤ)) (j : ℕ) :
    ∀ k, (∀ c < k, ((ls.getD c []).getD j 0).natAbs ≤ b - 1) → (fsum (b : ℤ) ls j k).natAbs < b ^ k
  | 0, _ => by simp [fsum]
  | k + 1, h => by
    rw [fsum_succ]
    have ih := fsum_bound b hb ls j k (fun c hc => h c (by omega))
    have hf := h k (by omega)
    have h1 := Int.natAbs_add_le (fsum (b : ℤ) ls j k) ((b : ℤ) ^ k * (ls.getD k []).getD j 0)
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h1
    have h2 : b ^ k * ((ls.getD k []).getD j 0).natAbs ≤ b ^ k * (b - 1) := Nat.mul_le_mul_left _ hf
    have h3 : b ^ (k + 1) = b ^ k * (b - 1) + b ^ k := by
      rw [pow_succ, ← Nat.mul_succ]; congr 1; omega
    omega

theorem magL_flatten (ls : List (List ℤ)) : magL ls = (ls.flatten.map Int.natAbs).sum := by
  unfold magL
  induction ls with
  | nil => simp
  | cons l ls ih => simp [ih]

end NearCubicGates.Close.TabMachine
