import SourceAdapters.Joins.AffineRouting

/-! Actual field-size slack for the formal-degree budget.-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.Resources

theorem degreeBudget_bound (m : ℕ) :
    m * 2 ^ (m - 1) + 2 * (2 ^ m - 1) ≤ DegreeBudget m := by
  have hp : 2 ^ (m - 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
  have hm := Nat.mul_le_mul_left m hp
  unfold DegreeBudget
  nlinarith [Nat.sub_le (2 ^ m) 1]

theorem log_slack (m : ℕ) : 2 ≤ Nat.clog 2 (4 * (m + 4)) := by
  have h : 1 < Nat.clog 2 (4 * (m + 4)) :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by norm_num; omega)
  omega

theorem fieldExponent_ge (m : ℕ) : m + 2 ≤ fieldExponent m := by
  exact Nat.add_le_add_left (log_slack m) m

theorem field_card_lower (m : ℕ) : 4 * DegreeBudget m ≤ 2 ^ fieldExponent m := by
  have h := Nat.mul_le_mul_left (2 ^ m) (Nat.le_pow_clog (by decide : 1 < 2) (4 * (m + 4)))
  simpa [fieldExponent, DegreeBudget, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using h

theorem field_card_upper (m : ℕ) : 2 ^ fieldExponent m < 8 * (m + 4) * 2 ^ m := by
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
    (by omega : 1 < 4 * (m + 4))
  simp only [Nat.pred_eq_sub_one] at hp
  have hl := log_slack m
  have he : Nat.clog 2 (4 * (m + 4)) = Nat.clog 2 (4 * (m + 4)) - 1 + 1 := by omega
  have hpow : 2 ^ Nat.clog 2 (4 * (m + 4)) < 8 * (m + 4) := by
    rw [he, Nat.pow_add]
    norm_num
    omega
  have h := Nat.mul_lt_mul_of_pos_left hpow (by positivity : 0 < 2 ^ m)
  simpa [fieldExponent, Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem resourceArithmetic : ResourceArithmetic := by
  intro m _
  exact ⟨degreeBudget_bound m, fieldExponent_ge m, field_card_lower m, field_card_upper m⟩

end NearCubicGates.Adapters.Routing.Resources
