import SourceAdapters.Routing.InputEmbeddingBits

/-!
The construction in `app:affine-embedding`: the exact LSB input basis embeds in the reserved lane half.
The input points have the specified cell addresses, the affine cube map
is injective, and every point belongs to H. This includes m = omega = 0.
-/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.LayoutFacts

variable {F : Type} [Field F]

theorem inputPoint_eq_mask [CharP F 2] (l : Layout) (e : Fin l.m → F) (omega m i : ℕ) (ho : omega≤m) :
    inputPoint l e omega m i = maskEval l.m e (inputMask l omega m i) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le ho
  unfold inputPoint inputMask
  rw [Nat.add_sub_cancel_left]
  rw [maskEval_xor,maskEval_xor,maskEval_scatter,maskEval_scatter,Fin.sum_univ_add]
  simp only [Fin.val_castAdd,Fin.val_natAdd]
  rw [add_assoc]
  congr 1
  apply congrArg₂ (fun a b : F => a+b)
  · apply Finset.sum_congr rfl
    intro j _
    simp only [inputBasis,j.isLt,if_true]
  · apply Finset.sum_congr rfl
    intro j _
    have hj : ¬omega+j.val<omega := by omega
    simp only [inputBasis,hj,if_false,Nat.add_sub_cancel_left,Nat.add_zero,
      Nat.testBit_div_two_pow,Nat.add_comm]

theorem inputPoint_eq_label [CharP F 2] (l : Layout) (e : Fin l.m → F) (omega m i : ℕ)
    (ho : omega≤m) (hm : m-omega≤l.k-1) (hi : i<2^m) :
    inputPoint l e omega m i = label l e (2^(l.k-1)+i/2^omega) 0 (i%2^omega) 0 0 := by
  rw [inputPoint_eq_mask l e omega m i ho,inputMask_eq l omega m i ho hm hi]
  rfl

theorem inputCube_eq_point (l : Layout) (e : Fin l.m → F) (omega m : ℕ) (v : Fin m → Bool) :
    maskEval l.m e (2^(l.k-1)) +
      (∑ j : Fin m, if v j then inputBasis l e omega j.val else 0) =
        inputPoint l e omega m (cubeMask v) := by
  simp only [inputPoint,cubeMask_testBit]

theorem inputCube_injective [CharP F 2] (l : Layout) (e : Fin l.m → F) (he : Independent l.m e)
    (omega m : ℕ) (hq : omega≤l.q) (ho : omega≤m) (hm : m-omega≤l.k-1) :
    Function.Injective (fun v : Fin m → Bool => maskEval l.m e (2^(l.k-1)) +
      ∑ j : Fin m, if v j then inputBasis l e omega j.val else 0) := by
  intro u v huv
  dsimp only at huv
  rw [inputCube_eq_point,inputCube_eq_point,
    inputPoint_eq_label l e omega m _ ho hm (cubeMask_lt u),
    inputPoint_eq_label l e omega m _ ho hm (cubeMask_lt v)] at huv
  obtain ⟨hx,_,hc,_,_⟩ := (label_eq_iff l e he _ _ _ _ _ _ _ _ _ _
    (input_range l omega m _ hq ho hm (cubeMask_lt u))
    (input_range l omega m _ hq ho hm (cubeMask_lt v))).mp huv
  have hquot : cubeMask u/2^omega=cubeMask v/2^omega := Nat.add_left_cancel hx
  have hu := Nat.mod_add_div (cubeMask u) (2^omega)
  have hv := Nat.mod_add_div (cubeMask v) (2^omega)
  have hmask : cubeMask u=cubeMask v := by rw [hc,hquot] at hu;omega
  funext j
  have hb := congrArg (fun a : ℕ => a.testBit j.val) hmask
  simpa only [cubeMask_testBit] using hb

theorem inputEmbedding [CharP F 2] (l : Layout) (e : Fin l.m → F) (he : Independent l.m e) :
    InputEmbedding l e := by
  intro omega m hq ho hm
  refine ⟨fun i hi => inputPoint_eq_label l e omega m i ho hm hi,
    inputCube_injective l e he omega m hq ho hm,?_⟩
  intro i hi
  rw [inputPoint_eq_label l e omega m i ho hm hi]
  exact label_mem l e _ _ _ _ _

end NearCubicGates.Adapters.Routing.LayoutFacts
