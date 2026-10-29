import SourceAdapters.Amplification.NetCount
import SourceAdapters.Amplification.Layout

/-!
# A02 step (b): the slot oracle as a net built from `2^t` copies of the adversary circuit

STV text l.890–897 (proof of Lemma 28): "we consider the oracle r|_i : [2^t] → {0,1} given by r|_i(j) = r(i,j).
We find a list of all elements z ∈ [q] such that Had(z) has agreement at least 1/2 + ε/2 with r|_i. … The oracle
r'_m, on query i, outputs the m'th element of this list (after sorting them using some canonical order)."
`app:sources`, "Full-range amplification interface": the circuit for the decoded function is built from the `s'`-node circuit for the code.

`real_slot`: for a circuit `B` on `ℓ = (m+1)·t` bits, a threshold `θ = (1/2 + η)·2^t` (an integer) and a slot
`j0`, the slot oracle `z ↦ slot η j0 (u ↦ B(layout(z, u)))` (`ListDecode.slot`) is computed by a net with at most
`2^t·(ℓ + |B|) + 2^t·((θ+1) + 2^t·67(θ+1)) + (j0+2+t)(1 + 2^t·132)` nodes:
(a) `2^t` copies of `B`, one per Hadamard position `u` (the block `z` as inputs, `u` as constants);
(b) for every candidate word `a`, the threshold `θ ≤ #{u : B(z,u) = Had(a,u)}` (`Real.count`);
(c) the `j0`-th listed code in increasing order (`Real.select`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Finset NearCubicWires

/-- The leaf of the laid-out word at position `w`: a bit of the block `z` (an input) or of `u` (a constant). -/
def layoutLeaf (m t : ℕ) (u : Fin t → Bool) (w : Fin ((m + 1) * t)) : Bool ⊕ (Fin m × Fin t) :=
  if _h : w.divNat.val = 0 then Sum.inl (u w.modNat)
  else Sum.inr (⟨w.divNat.val - 1, by have := w.divNat.isLt; omega⟩, w.modNat)

theorem layoutEquiv_leaf (m t : ℕ) (z : Fin m × Fin t → Bool) (u : Fin t → Bool) (w : Fin ((m + 1) * t)) :
    layoutEquiv m t (fun i j => z (i, j), u) w = Real.leafEval z (layoutLeaf m t u w) := by
  simp only [layoutEquiv, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
    Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, Equiv.curry_symm_apply]
  simp only [finProdFinEquiv_symm_apply, Function.uncurry_apply_pair, Fin.consEquiv_apply]
  unfold layoutLeaf
  rcases Fin.eq_zero_or_eq_succ w.divNat with h | ⟨i, hi⟩
  · rw [dif_pos (by rw [h]; rfl), h, Fin.cons_zero]; rfl
  · have hv : w.divNat.val = i.val + 1 := by rw [hi]; rfl
    rw [dif_neg (by omega)]
    have hj : (⟨w.divNat.val - 1, by have := w.divNat.isLt; omega⟩ : Fin m) = i := Fin.ext (by simp only; omega)
    rw [hj, hi, Fin.cons_succ]
    rfl

theorem card_words (t : ℕ) : Fintype.card (Fin t → Bool) = 2 ^ t := by simp

/-- (a) The `2^t` evaluations of `B` on the block `z`. -/
theorem real_blockEvals (m t : ℕ) (B : BooleanCircuit ((m + 1) * t)) :
    Real (2 ^ t * ((m + 1) * t + B.size))
      (fun (z : Fin m × Fin t → Bool) (u : Fin t → Bool) => B.eval (layoutEquiv m t (fun i j => z (i, j), u))) := by
  have h := Real.pi (β := Fin t → Bool) (s := (m + 1) * t + B.size)
    (fun (z : Fin m × Fin t → Bool) (u : Fin t → Bool) => B.eval (layoutEquiv m t (fun i j => z (i, j), u)))
    (fun u => by
      have h1 := Real.leaves (fun w : Fin ((m + 1) * t) => layoutLeaf m t u w)
      refine (Real.comp h1 (Real.ofCircuit B)).congr fun z _ => ?_
      congr 1
      funext w
      rw [layoutEquiv_leaf])
  rwa [card_words] at h

/-- (b) For every candidate word `a`, whether its Hadamard codeword agrees with the evaluations on at least `θ`
positions. -/
theorem real_listBits {Z : Type} (t θ : ℕ) :
    Real (2 ^ t * ((θ + 1) + 2 ^ t * ((θ + 1) * (3 + 8 * 2 ^ 3))))
      (fun (y : Z ⊕ (Fin t → Bool) → Bool) (a : Fin t → Bool) =>
        decide (θ ≤ agreeCount (fun u => y (Sum.inr u)) a)) := by
  classical
  have h := Real.pi (β := Fin t → Bool) (s := (θ + 1) + 2 ^ t * ((θ + 1) * (3 + 8 * 2 ^ 3)))
    (fun (y : Z ⊕ (Fin t → Bool) → Bool) (a : Fin t → Bool) =>
        decide (θ ≤ agreeCount (fun u => y (Sum.inr u)) a))
    (fun a => by
      have hc := Real.count (α := Z ⊕ (Fin t → Bool)) θ (univ : Finset (Fin t → Bool)).toList Sum.inr
        (fun u b => b == had a u)
      rw [length_toList, card_univ, card_words] at hc
      refine (hc.reindex (fun _ : Unit => Fin.last θ)).congr fun y _ => ?_
      simp only [Function.comp_apply, cntState, Fin.val_last]
      rw [length_filter_eq_card _ (nodup_toList _) (fun u => mem_toList.mpr (mem_univ u))]
      simp [agreeCount])
  rwa [card_words] at h

/-- The threshold of `hadList η` as an integer. -/
theorem mem_hadList_iff {t θ : ℕ} (η : ℝ) (hθ : (1 / 2 + η) * 2 ^ t = (θ : ℝ)) (r : (Fin t → Bool) → Bool)
    (a : Fin t → Bool) : a ∈ hadList η r ↔ θ ≤ agreeCount r a := by
  simp only [hadList, mem_filter, mem_univ, true_and, hθ, Nat.cast_le]

/-- **The slot oracle as a net.** -/
theorem real_slot (m t θ j0 : ℕ) (η : ℝ) (hθ : (1 / 2 + η) * 2 ^ t = (θ : ℝ)) (B : BooleanCircuit ((m + 1) * t)) :
    Real (2 ^ t * ((m + 1) * t + B.size) + 2 ^ t * ((θ + 1) + 2 ^ t * ((θ + 1) * (3 + 8 * 2 ^ 3))) +
        ((j0 + 2 + t) + 2 ^ t * ((j0 + 2 + t) * (4 + 8 * 2 ^ 4))))
      (fun (z : Fin m × Fin t → Bool) =>
        slot η j0 (fun u => B.eval (layoutEquiv m t (fun i j => z (i, j), u)))) := by
  have ha := real_blockEvals m t B
  have hb := real_listBits (Z := Fin m × Fin t) t θ
  have hc := Real.select (α := (Fin m × Fin t) ⊕ (Fin t → Bool)) j0 t (List.range (2 ^ t))
    (fun c => Sum.inr (wordOfCode c))
  rw [List.length_range] at hc
  refine (Real.bind (Real.bind ha hb) hc).congr fun z s => ?_
  simp only [Sum.elim_inr, slot, hadCodes, wordOfCode]
  congr 3
  funext c
  exact decide_eq_decide.mpr (mem_hadList_iff η hθ _ _).symm

end NearCubicGates.Adapters.Amplification
