import SourceAdapters.Amplification.NetAlgebra

/-!
# A02 infrastructure: counting, thresholds and rank selection as nets

Used by the slot oracle (STV text l.890–897: "find a list of all elements z such that Had(z) has agreement at
least 1/2 + ε/2 with r|_i … The oracle r'_m, on query i, outputs the m'th element of this list (after sorting them
using some canonical order)") and by the majority vote that fixes the coins (STV Remark 21, text l.776–781;
`app:sources`, "Full-range amplification interface" "fixing the decoder's randomness").

* `cntState θ c`: the vector `i ↦ [i ≤ c]`, `i ≤ θ` (a capped unary counter); `foldl_cntStep`: counting a list.
* `Real.count`: `[θ ≤ #{i ∈ l | f_i(x_{src i})}]` and the whole capped counter, with `O(θ·|l|)` nodes.
* `Real.select`: the bits of the `j`-th element (default `0`) of the sublist of `l` selected by input bits.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Finset

/-- The capped unary counter holding `c`. -/
def cntState (θ c : ℕ) : Fin (θ + 1) → Bool := fun i => decide (i.val ≤ c)

/-- One counting step: add the bit `b`. -/
def cntStep {θ : ℕ} (b : Bool) (ge : Fin (θ + 1) → Bool) : Fin (θ + 1) → Bool :=
  fun i => if i.val = 0 then true else ge i || (b && ge ⟨i.val - 1, by omega⟩)

theorem cntStep_state (θ c : ℕ) (b : Bool) : cntStep b (cntState θ c) = cntState θ (c + b.toNat) := by
  funext i
  simp only [cntStep, cntState]
  by_cases h0 : i.val = 0
  · rw [if_pos h0, h0]; simp
  · rw [if_neg h0, Bool.eq_iff_iff]
    cases b
    · simp
    · simp; omega
theorem foldl_cntStep {ι : Type} (θ : ℕ) (y : ι → Bool) :
    ∀ (l : List ι) (c : ℕ), l.foldl (fun ge i => cntStep (y i) ge) (cntState θ c) =
      cntState θ (c + (l.filter y).length)
  | [], c => by simp
  | i :: l, c => by
      rw [List.foldl_cons, cntStep_state, foldl_cntStep θ y l, List.filter_cons]
      congr 1
      cases y i
      · simp
      · simp; ring
/-- A list with every element of a finite type, once: filtered length = filtered cardinality. -/
theorem length_filter_eq_card {ι : Type} [Fintype ι] [DecidableEq ι] (l : List ι) (hl : l.Nodup)
    (hall : ∀ i, i ∈ l) (p : ι → Bool) : (l.filter p).length = (univ.filter fun i => p i = true).card := by
  rw [← List.toFinset_card_of_nodup (hl.filter p)]
  congr 1
  ext i
  simp [hall i]

namespace Real

variable {α : Type}

/-- **Counting** the selected bits of a list, as the capped counter. -/
theorem count {ι : Type} (θ : ℕ) (l : List ι) (src : ι → α) (f : ι → Bool → Bool) :
    Real ((θ + 1) + l.length * ((θ + 1) * (3 + 8 * 2 ^ 3)))
      (fun x => cntState θ ((l.filter fun i => f i (x (src i))).length)) := by
  have h0 : Real (θ + 1) (fun (_ : α → Bool) => cntState θ 0) := by
    refine ((leaves (fun i : Fin (θ + 1) => (Sum.inl (cntState θ 0 i) : Bool ⊕ α))).mono le_rfl).congr ?_
    intro x i; rfl
  have h := foldList (σ := Fin (θ + 1)) (c := (θ + 1) * (3 + 8 * 2 ^ 3))
    (fun i ge x => cntStep (f i (x (src i))) ge) l (fun _ => cntState θ 0) h0 (fun i _ => by
      have hl := «local» (α := α ⊕ Fin (θ + 1)) (β := Fin (θ + 1)) 3
        (fun j => ![Sum.inr j, Sum.inr ⟨j.val - 1, by omega⟩, Sum.inl (src i)])
        (fun j v => if j.val = 0 then true else v 0 || (f i (v 2) && v 1))
      rw [Fintype.card_fin] at hl
      refine hl.congr fun z j => ?_
      simp [cntStep])
  refine h.congr fun x j => ?_
  rw [foldl_cntStep θ (fun i => f i (x (src i))) l 0, zero_add]

/-- The state of the selection fold after the prefix `l`: the counter of selected codes and the bits of the
`j`-th selected code (`0` if there is none yet). -/
def selState (j t : ℕ) (L : ℕ → Bool) (l : List ℕ) : Fin (j + 1 + 1) ⊕ Fin t → Bool :=
  Sum.elim (cntState (j + 1) (l.filter L).length) (fun s => ((l.filter L).getD j 0).testBit s.val)

/-- One selection step with code `c`. -/
def selStep (j t : ℕ) (c : ℕ) (b : Bool) (st : Fin (j + 1 + 1) ⊕ Fin t → Bool) : Fin (j + 1 + 1) ⊕ Fin t → Bool :=
  Sum.elim (cntStep b (st ∘ Sum.inl))
    (fun s => st (Sum.inr s) ||
      (b && st (Sum.inl ⟨j, by omega⟩) && !st (Sum.inl ⟨j + 1, by omega⟩) && c.testBit s.val))

theorem selStep_state (j t : ℕ) (L : ℕ → Bool) (l : List ℕ) (c : ℕ) :
    selStep j t c (L c) (selState j t L l) = selState j t L (l ++ [c]) := by
  funext z
  cases z with
  | inl i =>
      simp only [selStep, selState, Sum.elim_inl]
      rw [show (Sum.elim (cntState (j + 1) (l.filter L).length)
          (fun s : Fin t => ((l.filter L).getD j 0).testBit s.val) ∘ Sum.inl) =
          cntState (j + 1) (l.filter L).length from rfl, cntStep_state, List.filter_append,
        List.length_append, List.filter_singleton]
      cases L c <;> rfl
  | inr s =>
      simp only [selStep, selState, Sum.elim_inl, Sum.elim_inr, cntState, List.filter_append,
        List.filter_singleton]
      set F := l.filter L with hF
      by_cases hj : j < F.length
      · rw [List.getD_append _ _ _ _ hj]
        cases hc : L c
        · simp
        · simp; omega
      · have hnone : F[j]? = none := List.getElem?_eq_none (by omega)
        rw [List.getD_eq_getElem?_getD, hnone]
        cases hc : L c
        · simp only [cond_false, List.append_nil, List.getD_eq_getElem?_getD, hnone]
          simp
        · simp only [cond_true]
          by_cases hje : j = F.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hje]
            simp
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
            simp; omega

theorem foldl_selStep (j t : ℕ) (L : ℕ → Bool) :
    ∀ (l pre : List ℕ), l.foldl (fun st c => selStep j t c (L c) st) (selState j t L pre) =
      selState j t L (pre ++ l)
  | [], pre => by simp
  | c :: l, pre => by
      rw [List.foldl_cons, selStep_state, foldl_selStep j t L l (pre ++ [c])]
      simp

/-- **Rank selection**: the bits of the `j`-th element (default `0`) of the sublist of `l` selected by the input
bits `x (src c)`. -/
theorem select (j t : ℕ) (l : List ℕ) (src : ℕ → α) :
    Real ((j + 2 + t) + l.length * ((j + 2 + t) * (4 + 8 * 2 ^ 4)))
      (fun x (s : Fin t) => ((l.filter fun c => x (src c)).getD j 0).testBit s.val) := by
  have h0 : Real (j + 2 + t) (fun (x : α → Bool) => selState j t (fun c => x (src c)) []) := by
    have hl := leaves (α := α) (fun i : Fin (j + 1 + 1 + t) =>
      (Sum.inl (selState j t (fun _ => false) [] (finSumFinEquiv.symm i)) : Bool ⊕ α))
    refine ((hl.reindex (fun z => finSumFinEquiv z)).mono (by omega)).congr fun x z => ?_
    simp only [Function.comp_apply, leafEval, Sum.elim_inl, id, Equiv.symm_apply_apply]
    cases z <;> simp [selState, cntState]
  have h := foldList (σ := Fin (j + 1 + 1) ⊕ Fin t) (c := (j + 2 + t) * (4 + 8 * 2 ^ 4))
    (fun c st x => selStep j t c (x (src c)) st) l (fun x => selState j t (fun c => x (src c)) []) h0
    (fun c _ => by
      have hl := «local» (α := α ⊕ (Fin (j + 1 + 1) ⊕ Fin t)) (β := Fin (j + 1 + 1) ⊕ Fin t) 4
        (fun z => Sum.elim
          (fun i => ![Sum.inr (Sum.inl i), Sum.inr (Sum.inl ⟨i.val - 1, by omega⟩), Sum.inl (src c),
            Sum.inl (src c)])
          (fun s => ![Sum.inr (Sum.inr s), Sum.inl (src c), Sum.inr (Sum.inl ⟨j, by omega⟩),
            Sum.inr (Sum.inl ⟨j + 1, by omega⟩)]) z)
        (fun z v => Sum.elim (fun i => if i.val = 0 then true else v 0 || (v 2 && v 1))
          (fun s => v 0 || (v 1 && v 2 && !v 3 && c.testBit s.val)) z)
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hl
      refine (hl.mono (by omega)).congr fun z w => ?_
      cases w <;> simp [selStep, cntStep])
  refine (h.reindex Sum.inr).congr fun x s => ?_
  simp only [Function.comp_apply]
  rw [foldl_selStep j t (fun c => x (src c)) l []]
  rfl

end Real

end NearCubicGates.Adapters.Amplification
