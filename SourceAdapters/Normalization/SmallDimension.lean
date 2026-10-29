import SourceAdapters.Normalization.ThresholdSystem

/-!
# Thresholds on a segment and a square

A square's two diagonals cannot receive opposite constant labels from an affine
threshold. Its remaining labelings have an explicit integer representation.
These small dimensions complement the factorial bound in `lem:integer`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Normalization

/-- Four Boolean labels, excluding the two alternating square labelings, have
an integer affine separator with weights bounded by four. -/
theorem square_labels (a b c d : ℤ)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1)
    (h₀ : ¬(a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0))
    (h₁ : ¬(a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1)) :
    let u := 2 * (b + d - a - c)
    let v := 2 * (c + d - a - b)
    let t := d - 3 * a - b - c + 2
    (a = 1 ↔ t ≤ 0) ∧ (b = 1 ↔ t ≤ u) ∧
    (c = 1 ↔ t ≤ v) ∧ (d = 1 ↔ t ≤ u + v) ∧
    |u| ≤ 4 ∧ |v| ≤ 4 ∧ |t| ≤ 4 := by
  dsimp
  simp only [abs_le]
  omega

theorem exists_integer_threshold_one (w t : ℝ) :
    ∃ a b : ℤ,
      (∀ x : Bool, (t ≤ w * (if x then 1 else 0)) ↔
        (b ≤ a * (if x then 1 else 0))) ∧ |a| ≤ 1 ∧ |b| ≤ 1 := by
  classical
  let p : ℤ := if t ≤ 0 then 1 else 0
  let q : ℤ := if t ≤ w then 1 else 0
  refine ⟨q - p, 1 - p, ?_, ?_, ?_⟩
  · intro x
    cases x <;> simp only [Bool.false_eq_true, if_false, if_true,
      mul_zero, mul_one] <;> dsimp [p, q] <;> split_ifs <;> norm_num at * <;> assumption
  · dsimp [p, q]
    split_ifs <;> norm_num
  · dsimp [p]
    split_ifs <;> norm_num

theorem exists_integer_threshold_two (w v t : ℝ) :
    ∃ a b c : ℤ,
      (∀ x y : Bool, (t ≤ w * (if x then 1 else 0) + v * (if y then 1 else 0)) ↔
        (c ≤ a * (if x then 1 else 0) + b * (if y then 1 else 0))) ∧
      |a| ≤ 4 ∧ |b| ≤ 4 ∧ |c| ≤ 4 := by
  classical
  let p : ℤ := if t ≤ 0 then 1 else 0
  let q : ℤ := if t ≤ w then 1 else 0
  let r : ℤ := if t ≤ v then 1 else 0
  let s : ℤ := if t ≤ w + v then 1 else 0
  have hp : 0 ≤ p ∧ p ≤ 1 := by dsimp [p]; split_ifs <;> omega
  have hq : 0 ≤ q ∧ q ≤ 1 := by dsimp [q]; split_ifs <;> omega
  have hr : 0 ≤ r ∧ r ≤ 1 := by dsimp [r]; split_ifs <;> omega
  have hs : 0 ≤ s ∧ s ≤ 1 := by dsimp [s]; split_ifs <;> omega
  have hp' : p = 1 ↔ t ≤ 0 := by simp [p]
  have hq' : q = 1 ↔ t ≤ w := by simp [q]
  have hr' : r = 1 ↔ t ≤ v := by simp [r]
  have hs' : s = 1 ↔ t ≤ w + v := by simp [s]
  have h₀ : ¬(p = 0 ∧ q = 1 ∧ r = 1 ∧ s = 0) := by
    rintro ⟨hp0, hq1, hr1, hs0⟩
    have ht : ¬t ≤ 0 := by intro h; have := hp'.mpr h; omega
    have htv : ¬t ≤ w + v := by intro h; have := hs'.mpr h; omega
    have := hq'.mp hq1
    have := hr'.mp hr1
    linarith
  have h₁ : ¬(p = 1 ∧ q = 0 ∧ r = 0 ∧ s = 1) := by
    rintro ⟨hp1, hq0, hr0, hs1⟩
    have htw : ¬t ≤ w := by intro h; have := hq'.mpr h; omega
    have htv : ¬t ≤ v := by intro h; have := hr'.mpr h; omega
    have := hp'.mp hp1
    have := hs'.mp hs1
    linarith
  obtain ⟨h00, h10, h01, h11, hu, hv, ht⟩ := square_labels p q r s hp hq hr hs h₀ h₁
  refine ⟨2 * (q + s - p - r), 2 * (r + s - p - q), s - 3 * p - q - r + 2,
    ?_, hu, hv, ht⟩
  intro x y
  cases x <;> cases y <;> simp only [Bool.false_eq_true, if_false,
    if_true, mul_zero, mul_one, zero_add, add_zero]
  · exact hp'.symm.trans h00
  · exact hr'.symm.trans h01
  · exact hq'.symm.trans h10
  · exact hs'.symm.trans h11

end NearCubicGates.Adapters.Normalization
