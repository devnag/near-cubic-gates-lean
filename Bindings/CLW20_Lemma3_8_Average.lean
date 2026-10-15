import Bindings.CLW20_Lemma3_8_Sampling
import Bindings.CLW20_Lemma3_8_Split

/-! # CLW20 Lemma 3.8, Appendix A: agreement bookkeeping and the sampled sum's value

CLW20 (ECCC TR20-150), Appendix A, PDF p.50, printed p.49:

> "We define T(y) := Pr_z[C(y,z) = f^{⊕k}(y,z)] = Pr_z[C(y,z) = f(y) ⊕ f^{⊕(k−1)}(z)]."

> "Also, since C approximates f^{⊕k} on at least 1/2 + ε_k fraction of inputs, we have
> E_y[T(y)] ≥ 1/2 + ε_k. (25)"

PDF p.51, printed p.50:

> "Q can be implemented as a sum of ℓ + 1 C circuits (one for the constant function 1), as
> f^{⊕(k−1)}(z_i) can all be replaced by the corresponding constants."

`fiberAgreement` is `T(y)`; `agreement_eq_average` is (25) as an identity; `fiber_eq_agreement` is
the second equality defining `T(y)`, read as the agreement of `z ↦ f(y) ⊕ C(y,z)` with
`f^{⊕(k−1)}` (this is what makes Case 1's `C′` or `¬C′` inherit the fiber's advantage).
`sampled_value` evaluates the imported `foldl` value of the affine term list of `SampleForm`, and
`alphaQ_cast` identifies the rational `alphaQ δ j` with the printed `1/r`, `r = (2ε+δε)/(1−δ)`.
`l1_of_boolean` is Definition 3.2's remark "when g is Boolean function ... Pr[f(x) ≠ g(x)] =
‖f − g‖_1". -/
namespace NearCubicWires.Bindings.CLW20Lemma38
open NearCubicWires SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bitAsReal_decide_eq_ite (p : Prop) [Decidable p] :
    bitAsReal (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [bitAsReal, h]

/-- `agreement` as a mean of indicators. -/
theorem agreement_eq_sum {m : ℕ} (l r : BoolFunction m) :
    agreement l r = (∑ x, bitAsReal (decide (l x = r x))) / (Fintype.card (BitInput m) : ℝ) := by
  classical
  unfold agreement
  congr 1
  rw [Finset.card_filter]
  push_cast
  simp only [bitAsReal_decide_eq_ite]

theorem agreement_not {m : ℕ} (l r : BoolFunction m) :
    agreement (fun x => !l x) r = 1 - agreement l r := by
  have hc : (Fintype.card (BitInput m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpt : ∀ x, bitAsReal (decide ((!l x) = r x)) = 1 - bitAsReal (decide (l x = r x)) := by
    intro x
    cases l x <;> cases r x <;> simp [bitAsReal]
  rw [agreement_eq_sum, agreement_eq_sum]
  simp only [hpt, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp

theorem agreement_comp_equiv {a b : ℕ} (e : BitInput a ≃ BitInput b) (F G : BoolFunction b) :
    agreement (fun x => F (e x)) (fun x => G (e x)) = agreement F G := by
  rw [agreement_eq_sum, agreement_eq_sum,
    e.sum_comp (fun y => bitAsReal (decide (F y = G y))), Fintype.card_congr e]

/-- For a Boolean approximation, ℓ1 distance is the disagreement fraction. -/
theorem l1_of_boolean {m : ℕ} (f g : BoolFunction m) :
    l1DistanceFromBoolean f (fun y => bitAsReal (g y)) = 1 - agreement g f := by
  have hc : (Fintype.card (BitInput m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpt : ∀ y, |bitAsReal (g y) - bitAsReal (f y)| = 1 - bitAsReal (decide (g y = f y)) := by
    intro y
    cases g y <;> cases f y <;> simp [bitAsReal]
  unfold l1DistanceFromBoolean
  rw [agreement_eq_sum]
  simp only [hpt, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp

/-- The inverse of `joinInput`. -/
def splitInput {n k : ℕ} (x : BitInput ((k + 1) * n)) : BitInput n × BitInput (k * n) :=
  (fun i => x ⟨i.val, by have h1 := i.isLt; have h2 := succ_mul_eq k n; omega⟩,
   fun j => x ⟨j.val + n, by have h1 := j.isLt; have h2 := succ_mul_eq k n; omega⟩)

def joinEquiv (n k : ℕ) : BitInput n × BitInput (k * n) ≃ BitInput ((k + 1) * n) where
  toFun p := joinInput p.1 p.2
  invFun := splitInput
  left_inv p := by
    obtain ⟨y, z⟩ := p
    ext i
    · simp [splitInput, joinInput]
    · simp only [splitInput, joinInput]
      rw [dif_neg (by omega)]
      congr 2
      simp
  right_inv x := by
    funext c
    simp only [splitInput, joinInput]
    split
    · rfl
    · congr 1
      ext
      simp only
      omega

/-- The `k = 1` reindexing as an equivalence of cubes. -/
def oneBlockEquiv (n : ℕ) : BitInput n ≃ BitInput (1 * n) where
  toFun := oneBlock
  invFun x := fun i => x ⟨i.val, by have h := i.isLt; omega⟩
  left_inv y := rfl
  right_inv x := rfl

/-- `T(y)`: the fraction of `z` with `C(y,z) = g(y,z)`. -/
noncomputable def fiberAgreement {n k : ℕ} (C : BoolFunction ((k + 1) * n))
    (g : BoolFunction ((k + 1) * n)) (y : BitInput n) : ℝ :=
  ((Finset.univ.filter fun z : BitInput (k * n) =>
      C (joinInput y z) = g (joinInput y z)).card : ℝ) / (Fintype.card (BitInput (k * n)) : ℝ)

theorem fiberAgreement_eq_mean {n k : ℕ} (C g : BoolFunction ((k + 1) * n)) (y : BitInput n) :
    fiberAgreement C g y = mean (fun z : BitInput (k * n) =>
      decide (C (joinInput y z) = g (joinInput y z))) := by
  classical
  unfold fiberAgreement mean
  congr 1
  rw [Finset.card_filter]
  push_cast
  simp only [bitAsReal_decide_eq_ite]

/-- (25): agreement over the split cube is the average of `T(y)`. -/
theorem agreement_eq_average {n k : ℕ} (C g : BoolFunction ((k + 1) * n)) :
    agreement C g = (∑ y : BitInput n, fiberAgreement C g y) / (Fintype.card (BitInput n) : ℝ) := by
  classical
  unfold agreement fiberAgreement
  rw [← Finset.sum_div, div_div]
  have hcard : (Fintype.card (BitInput ((k + 1) * n)) : ℝ) =
      (Fintype.card (BitInput (k * n)) : ℝ) * (Fintype.card (BitInput n) : ℝ) := by
    rw [card_bitInput, card_bitInput, card_bitInput, succ_mul_eq, pow_add]
  rw [hcard, mul_comm (Fintype.card (BitInput (k * n)) : ℝ)]
  congr 1
  simp only [Finset.card_filter]
  push_cast
  rw [← (joinEquiv n k).sum_comp, Fintype.sum_prod_type]
  rfl

/-- `T(y) = Pr_z[C(y,z) = f(y) ⊕ f^{⊕(k−1)}(z)]`, read as the agreement of `z ↦ f(y) ⊕ C(y,z)`
with `f^{⊕(k−1)}`. -/
theorem fiber_eq_agreement {n k : ℕ} (f : BoolFunction n) (C : BoolFunction ((k + 1) * n))
    (y : BitInput n) :
    fiberAgreement C (xorPower f (k + 1)) y =
      agreement (fun z => xor (f y) (C (joinInput y z))) (xorPower f k) := by
  have hset : (Finset.univ.filter fun z : BitInput (k * n) =>
        C (joinInput y z) = xorPower f (k + 1) (joinInput y z)) =
      Finset.univ.filter (fun z : BitInput (k * n) =>
        xor (f y) (C (joinInput y z)) = xorPower f k z) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [xorPower_join]
    cases f y <;> cases C (joinInput y z) <;> cases xorPower f k z <;> simp
  unfold fiberAgreement agreement
  rw [hset]

/-- The imported `foldl` value is a plain sum. -/
theorem foldl_value {β : Type*} (φ : β → ℝ) (s : ℝ) (l : List β) :
    l.foldl (fun total term => total + φ term) s = s + (l.map φ).sum := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; ring

/-- The affine term list of `SampleForm` evaluates to `α·(average atom) + (1 − α)/2`. -/
theorem sampled_value {n ell : ℕ} (hell : 0 < ell) (alpha : ℚ) (atoms : Fin ell → BoolFunction n)
    (one : BoolFunction n) (hone : ∀ x, one x = true) (y : BitInput n) :
    ((List.ofFn atoms).map (fun f => (alpha / (List.ofFn atoms).length, f)) ++
        [((1 - alpha) / 2, one)]).foldl
      (fun total term => total + (term.1 : ℝ) * bitAsReal (term.2 y)) 0 =
      (alpha : ℝ) * ((∑ i, bitAsReal (atoms i y)) / ell) + (1 - (alpha : ℝ)) / 2 := by
  have hell' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  rw [foldl_value (fun term : ℚ × BoolFunction n => (term.1 : ℝ) * bitAsReal (term.2 y))]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_ofFn, Function.comp_def, hone, bitAsReal,
    if_true, mul_one, add_zero, zero_add, List.map_ofFn, List.sum_ofFn]
  push_cast
  rw [← Finset.mul_sum]
  field_simp

/-- The rational `alphaQ δ j` is the printed `1/r = (1 − δ)/((2 + δ)ε_j)`. -/
theorem alphaQ_cast (delta : ℚ) (j : ℕ) :
    ((alphaQ delta j : ℚ) : ℝ) =
      (1 - (delta : ℝ)) / ((2 + (delta : ℝ)) * xorEpsilon (delta : ℝ) j) := by
  simp [alphaQ, epsilonQ, xorEpsilon]

end NearCubicWires.Bindings.CLW20Lemma38
