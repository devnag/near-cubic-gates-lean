import Proof.Wire_3_5.StarRange

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires Finset

variable {n : ℕ}

/-- Flip coordinate `i`. -/
def flipAt (i : Fin n) (x : BitInput n) : BitInput n := Function.update x i (!x i)

theorem flipAt_flipAt (i : Fin n) (x : BitInput n) : flipAt i (flipAt i x) = x := by
  funext j; by_cases h : j = i
  · subst h; simp [flipAt]
  · simp [flipAt, Function.update_of_ne h]

/-- Flipping is a permutation of the cube. -/
def flipEquiv (i : Fin n) : BitInput n ≃ BitInput n :=
  ⟨flipAt i, flipAt i, flipAt_flipAt i, flipAt_flipAt i⟩

/-- `±1` spin of a bit. -/
def spin (b : Bool) : ℤ := if b then 1 else -1

/-- The unate spin of coordinate `i` for gate `g`. -/
def unateSpin (g : NormalizedThresholdGate n) (i : Fin n) (x : BitInput n) : ℤ :=
  if 0 ≤ g.weight i then spin (x i) else -spin (x i)

/-- `i` is pivotal for `g` at `x`. -/
def pivotal (g : NormalizedThresholdGate n) (i : Fin n) (x : BitInput n) : Bool :=
  g.eval x != g.eval (flipAt i x)

/-- `2^n · Inf_i(T)`: the number of inputs at which `i` is pivotal. -/
def pivCount (g : NormalizedThresholdGate n) (i : Fin n) : ℕ :=
  (univ.filter fun x => pivotal g i x = true).card

def gateSupport (g : NormalizedThresholdGate n) : Finset (Fin n) := univ.filter fun i => g.weight i ≠ 0

theorem gateScore_flipAt (g : NormalizedThresholdGate n) (i : Fin n) (x : BitInput n) :
    gateScore g (flipAt i x) = gateScore g x + g.weight i * (if x i then -1 else 1) := by
  unfold gateScore
  have h : ∀ j, g.weight j * (if flipAt i x j then (1 : ℤ) else 0) =
      g.weight j * (if x j then 1 else 0) + if j = i then g.weight i * (if x i then -1 else 1) else 0 := by
    intro j
    simp only [flipAt, Function.update_apply]
    by_cases hj : j = i
    · subst hj; cases x j <;> simp
    · simp [hj]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem unateSpin_flipAt_self (g : NormalizedThresholdGate n) (i : Fin n) (x : BitInput n) :
    unateSpin g i (flipAt i x) = -unateSpin g i x := by
  unfold unateSpin spin flipAt; rw [Function.update_apply, if_pos rfl]
  cases x i <;> by_cases hw : 0 ≤ g.weight i <;> simp [hw]

theorem unateSpin_flipAt_ne (g : NormalizedThresholdGate n) {i j : Fin n} (h : j ≠ i) (x : BitInput n) :
    unateSpin g j (flipAt i x) = unateSpin g j x := by
  unfold unateSpin flipAt; rw [Function.update_of_ne h]

theorem unate_pointwise (g : NormalizedThresholdGate n) (i : Fin n) (x : BitInput n) :
    unateSpin g i x * (spin (g.eval x) - spin (g.eval (flipAt i x))) = 2 * bitZ (pivotal g i x) := by
  have hs := gateScore_flipAt g i x
  simp only [eval_eq_decide, pivotal, unateSpin, spin, bitZ]
  by_cases hw : 0 ≤ g.weight i <;>
  by_cases h1 : g.threshold ≤ gateScore g x <;>
  by_cases h2 : g.threshold ≤ gateScore g (flipAt i x) <;>
  cases hx : x i <;> simp [hw, h1, h2, hx] at hs ⊢ <;> omega

theorem sum_spin_mul_unate (g : NormalizedThresholdGate n) (i : Fin n) :
    ∑ x, spin (g.eval x) * unateSpin g i x = (pivCount g i : ℤ) := by
  have hflip : ∑ x, spin (g.eval x) * unateSpin g i x =
      ∑ x, spin (g.eval (flipAt i x)) * unateSpin g i (flipAt i x) :=
    (Equiv.sum_comp (flipEquiv i) (fun x => spin (g.eval x) * unateSpin g i x)).symm
  have h2 : 2 * ∑ x, spin (g.eval x) * unateSpin g i x = ∑ x, 2 * bitZ (pivotal g i x) := by
    calc 2 * ∑ x, spin (g.eval x) * unateSpin g i x
        = ∑ x, spin (g.eval x) * unateSpin g i x + ∑ x, spin (g.eval (flipAt i x)) * unateSpin g i (flipAt i x) := by
          rw [← hflip]; ring
      _ = ∑ x, unateSpin g i x * (spin (g.eval x) - spin (g.eval (flipAt i x))) := by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro x _
          rw [unateSpin_flipAt_self]; ring
      _ = ∑ x, 2 * bitZ (pivotal g i x) := by
          apply Finset.sum_congr rfl; intro x _; exact unate_pointwise g i x
  have h3 : ∑ x, bitZ (pivotal g i x) = (pivCount g i : ℤ) := by
    unfold pivCount bitZ; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]; simp
  rw [← Finset.mul_sum] at h2; omega

/-- Orthogonality of unate spins. -/
theorem sum_unate_mul_unate (g : NormalizedThresholdGate n) (i j : Fin n) :
    ∑ x, unateSpin g i x * unateSpin g j x = if i = j then (2 ^ n : ℤ) else 0 := by
  by_cases hij : i = j
  · subst hij
    have : ∀ x, unateSpin g i x * unateSpin g i x = 1 := by
      intro x; unfold unateSpin spin; cases x i <;> split_ifs <;> simp
    simp [this, Fintype.card_bool, Fintype.card_fin]
  · simp only [hij, if_false]
    have hflip := (Equiv.sum_comp (flipEquiv i) (fun x => unateSpin g i x * unateSpin g j x)).symm
    have hne : j ≠ i := fun h => hij h.symm
    simp only [flipEquiv, Equiv.coe_fn_mk, unateSpin_flipAt_self, unateSpin_flipAt_ne g hne] at hflip
    rw [show (∑ x, -unateSpin g i x * unateSpin g j x) = -∑ x, unateSpin g i x * unateSpin g j x by
      rw [← Finset.sum_neg_distrib]; simp [neg_mul]] at hflip
    linarith

theorem pivCount_eq_zero_of_weight (g : NormalizedThresholdGate n) (i : Fin n) (h : g.weight i = 0) :
    pivCount g i = 0 := by
  unfold pivCount; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  simp [pivotal, eval_eq_decide, gateScore_flipAt, h]

theorem pivCount_sum_sq_le (g : NormalizedThresholdGate n) :
    ((∑ i, pivCount g i : ℕ) : ℤ) ^ 2 ≤ (2 ^ n : ℤ) ^ 2 * (gateSupport g).card := by
  set S := gateSupport g
  have hsupp : ∑ i, pivCount g i = ∑ i ∈ S, pivCount g i := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => g.weight i ≠ 0)]
    have : ∑ i ∈ univ.filter (fun i => ¬g.weight i ≠ 0), pivCount g i = 0 :=
      Finset.sum_eq_zero fun i hi => pivCount_eq_zero_of_weight g i (by simpa using (Finset.mem_filter.mp hi).2)
    rw [this, add_zero]; rfl
  set Y : BitInput n → ℤ := fun x => ∑ i ∈ S, unateSpin g i x
  have hlin : ((∑ i ∈ S, pivCount g i : ℕ) : ℤ) = ∑ x, spin (g.eval x) * Y x := by
    push_cast
    simp only [Y, Finset.mul_sum]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (sum_spin_mul_unate g i).symm
  have habs : ∑ x, spin (g.eval x) * Y x ≤ ∑ x, |Y x| := by
    apply Finset.sum_le_sum; intro x _
    unfold spin; split_ifs
    · simpa using le_abs_self (Y x)
    · simpa using neg_le_abs (Y x)
  have hY2 : ∑ x, Y x ^ 2 = 2 ^ n * S.card := by
    simp only [Y, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i ∈ S, ∑ j ∈ S, ∑ x, unateSpin g i x * unateSpin g j x = 2 ^ n := by
      intro i hi; simp only [sum_unate_mul_unate]; rw [Finset.sum_ite_eq]; simp [hi]
    calc ∑ i ∈ S, ∑ x, ∑ j ∈ S, unateSpin g i x * unateSpin g j x
        = ∑ i ∈ S, ∑ j ∈ S, ∑ x, unateSpin g i x * unateSpin g j x := by
          apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
      _ = ∑ i ∈ S, (2 ^ n : ℤ) := Finset.sum_congr rfl this
      _ = 2 ^ n * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcs : (∑ x, |Y x|) ^ 2 ≤ (2 ^ n : ℤ) * (2 ^ n * S.card) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℤ)) (fun x => |Y x|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, sq_abs, nsmul_eq_mul, mul_one,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    rw [hY2] at this; push_cast at this; exact this
  have hnonneg : (0 : ℤ) ≤ ∑ x, spin (g.eval x) * Y x := by rw [← hlin]; positivity
  rw [hsupp, hlin]
  calc (∑ x, spin (g.eval x) * Y x) ^ 2 ≤ (∑ x, |Y x|) ^ 2 := pow_le_pow_left₀ hnonneg habs 2
    _ ≤ _ := by nlinarith [hcs]

theorem influence_sum_le_sqrt (g : NormalizedThresholdGate n) :
    (∑ i, (pivCount g i : ℝ) / 2 ^ n) ≤ Real.sqrt (gateSupport g).card := by
  have h := pivCount_sum_sq_le g
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [← Finset.sum_div, div_le_iff₀ hpos]
  have hR : ((∑ i, pivCount g i : ℕ) : ℝ) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 * (gateSupport g).card := by
    exact_mod_cast h
  have hsq : Real.sqrt (((2 : ℝ) ^ n) ^ 2 * (gateSupport g).card) = 2 ^ n * Real.sqrt (gateSupport g).card := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hpos.le]
  calc (∑ i, (pivCount g i : ℝ)) = ((∑ i, pivCount g i : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ Real.sqrt (((2 : ℝ) ^ n) ^ 2 * (gateSupport g).card) := Real.le_sqrt_of_sq_le hR
    _ = _ := by rw [hsq, mul_comm]

end NearCubicWires.WireExponent3_5.Shared
