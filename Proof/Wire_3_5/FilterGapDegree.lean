import Proof.Wire_3_5.FilterGap

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.SupplierWalk MvPolynomial Finset

/-- A bit as an element of `𝔽₂`. -/
def bitF2 (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bitF2_one_add (y b : Bool) : 1 + bitF2 y + bitF2 b = if y = b then 1 else 0 := by
  cases y <;> cases b <;> decide

/-- `Φ(ℓ)`: the polynomial of a Boolean function `Φ` of the forms `ℓ_j` (indicator expansion). -/
noncomputable def polyOfForms {ι σ : Type} [Fintype ι] [DecidableEq ι] (Φ : (ι → Bool) → Bool)
    (ℓ : ι → MvPolynomial σ (ZMod 2)) : MvPolynomial σ (ZMod 2) :=
  ∑ b : ι → Bool, C (bitF2 (Φ b)) * ∏ j, (1 + ℓ j + C (bitF2 (b j)))

theorem totalDegree_polyOfForms {ι σ : Type} [Fintype ι] [DecidableEq ι] (Φ : (ι → Bool) → Bool)
    (ℓ : ι → MvPolynomial σ (ZMod 2)) (hℓ : ∀ j, (ℓ j).totalDegree ≤ 1) :
    (polyOfForms Φ ℓ).totalDegree ≤ Fintype.card ι := by
  unfold polyOfForms
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun b _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j, (1 + ℓ j + C (bitF2 (b j))).totalDegree ≤ ∑ _j : ι, 1 := by
        apply Finset.sum_le_sum; intro j _
        refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ (hℓ j))) ?_)
        · rw [totalDegree_one]; exact Nat.zero_le _
        · rw [totalDegree_C]; exact Nat.zero_le _
    _ = Fintype.card ι := by simp

theorem eval_polyOfForms {ι σ : Type} [Fintype ι] [DecidableEq ι] (Φ : (ι → Bool) → Bool)
    (ℓ : ι → MvPolynomial σ (ZMod 2)) (x : σ → ZMod 2) (y : ι → Bool) (hy : ∀ j, eval x (ℓ j) = bitF2 (y j)) :
    eval x (polyOfForms Φ ℓ) = bitF2 (Φ y) := by
  unfold polyOfForms
  simp only [map_sum, map_mul, map_prod, map_add, map_one, eval_C, hy, bitF2_one_add]
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    rw [Finset.prod_eq_zero (i := Classical.choose (Function.ne_iff.mp (Ne.symm hb))) (Finset.mem_univ _)]
    · simp
    · rw [if_neg (Classical.choose_spec (Function.ne_iff.mp (Ne.symm hb)))]
  · intro h; exact absurd (Finset.mem_univ y) h

/-! ## The selected parity is a linear form in `Z` -/

/-- The coefficient `κ_i = H_i a_i` of coordinate `i` in the parity `P = Σ_i H_i a_i Z_i` of one copy. -/
def parityCoeff (P : GapParams) {K : Type} (o : BiasOps K) (c : CopySeed P K) (i : ℕ) : ZMod 2 :=
  bitF2 (selected P c.1 i && biasBit o c.2.1 c.2.2 i)

/-- The linear form `Σ_i κ_i Z_i` in the variables `Z_0, …, Z_{L−1}`. -/
noncomputable def parityForm (P : GapParams) {K : Type} (o : BiasOps K) (c : CopySeed P K) (L : ℕ) :
    MvPolynomial (Fin L) (ZMod 2) :=
  ∑ i : Fin L, C (parityCoeff P o c i) * X i

theorem totalDegree_parityForm (P : GapParams) {K : Type} (o : BiasOps K) (c : CopySeed P K) (L : ℕ) :
    (parityForm P o c L).totalDegree ≤ 1 := by
  unfold parityForm
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, totalDegree_X]

theorem bitF2_odd (n : ℕ) : bitF2 (decide (Odd n)) = (n : ZMod 2) := by
  rcases Nat.even_or_odd n with he | ho
  · have : ¬ Odd n := Nat.not_odd_iff_even.mpr he
    simp only [this, decide_false, bitF2]
    exact ((ZMod.natCast_eq_zero_iff_even).mpr he).symm
  · simp only [ho, decide_true, bitF2, if_true]
    exact (ZMod.natCast_eq_one_iff_odd.mpr ho).symm

/-- **The parity of one copy is the linear form** at every `Z ∈ {0,1}^L`. -/
theorem eval_parityForm (P : GapParams) {K : Type} (o : BiasOps K) (c : CopySeed P K) (L : ℕ)
    (z : Fin L → Bool) :
    eval (fun i => bitF2 (z i)) (parityForm P o c L) = bitF2 (copyParity P o c (List.ofFn z)) := by
  unfold copyParity parityForm
  rw [bitF2_odd]
  simp only [map_sum, map_mul, eval_C, eval_X]
  rw [Finset.card_filter, selectedActive, Finset.sum_filter]
  push_cast
  rw [List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hget : (List.ofFn z).getD (i : ℕ) false = z i := by
    simp [List.getD_eq_getElem?_getD]
  rw [hget]
  simp only [parityCoeff, bitF2]
  cases z i <;> cases selected P c.1 i <;> cases biasBit o c.2.1 c.2.2 i <;> simp

/-! ## The filter's polynomial -/

/-- The filter's outer function of its `t × 128` parity bits: majority over the walk of the `≤ 32` threshold. -/
def filterOuter (P : GapParams) (y : Fin P.walkLen × Fin 128 → Bool) : Bool :=
  decide (majorityThreshold P.walkLen ≤
    (univ.filter fun time : Fin P.walkLen =>
      decide ((univ.filter fun j : Fin 128 => y (time, j) = true).card ≤ 32) = true).card)

theorem gapFilter_degree (P : GapParams) (e : GapSeed P) (L : ℕ) :
    ∃ p : MvPolynomial (Fin L) (ZMod 2), p.totalDegree ≤ 128 * P.walkLen ∧
      ∀ z : Fin L → Bool, eval (fun i => bitF2 (z i)) p = bitF2 (gapFilter P e (List.ofFn z)) := by
  set o := galoisOps P.fieldBits
  set kEq := galoisEquiv P.fieldBits P.fieldBits_ne_zero
  let seedAt : Fin P.walkLen × Fin 128 → CopySeed P (GaloisField 2 P.fieldBits) :=
    fun q => vertexSeed P kEq (e.vertex q.1) q.2
  refine ⟨polyOfForms (filterOuter P) (fun q => parityForm P o (seedAt q) L), ?_, ?_⟩
  · refine (totalDegree_polyOfForms _ _ fun q => totalDegree_parityForm P o _ L).trans ?_
    simp [Fintype.card_prod, mul_comm]
  · intro z
    rw [eval_polyOfForms (filterOuter P) _ _ (fun q => copyParity P o (seedAt q) (List.ofFn z))
      (fun q => eval_parityForm P o (seedAt q) L z)]
    rfl

/-- The degree is `O(log(1/ε))`: `128·t ≤ 64·log₂(1/ε) + 128`. -/
theorem degree_le_errExp (P : GapParams) : 128 * P.walkLen ≤ 64 * P.errExp + 128 := by
  unfold GapParams.walkLen; omega

end NearCubicWires.WireExponent3_5.Filters
