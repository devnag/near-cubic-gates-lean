import Proof.Gates.WorkerArith.RuntimeSplit
import Proof.Gates.Worker.NativeLower
import Proof.Gates.Worker.Meaning

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.WorkerBounds

open NearCubicWires NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.Close NearCubicGates.Close.Transfer
open NearCubicGates.Close.Worker (width gadgets)

noncomputable section

/-- The per-call hot budget at native width `q`: `⌊2^q / q^{μ(q)}⌋`. -/
def hotCall (q : ℕ) : ℕ := 2 ^ q / q ^ NearCubicGates.Target.mu q

theorem hotCall_mul (q : ℕ) : hotCall q * q ^ NearCubicGates.Target.mu q ≤ 2 ^ q := Nat.div_mul_le_self _ _

/-- `2^{⌈log₂ x⌉} ≤ 2x` for `x ≥ 1`. -/
theorem two_pow_clog_le (x : ℕ) (hx : 1 ≤ x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  rcases Nat.lt_or_ge 1 x with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h
    have h2 := Nat.clog_pos (by norm_num : 1 < 2) h
    have e : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x).pred := by
      rw [← pow_succ']; congr 1; rw [Nat.pred_eq_sub_one]; omega
    omega
  · rw [Nat.clog_of_right_le_one h]; omega

/-- The gadget count is polynomial in the native width: `M = 2^{⌈d lg (q+2)⌉} ≤ 2 (q+2)^d ≤ 2^{d+1} (q+1)^d`. -/
theorem gadgets_le (d q : ℕ) : 2 ^ clauseWidth d q ≤ 2 ^ (d + 1) * (q + 1) ^ d := by
  unfold clauseWidth
  have h1 := two_pow_clog_le ((q + 2) ^ d) (Nat.one_le_pow _ _ (by omega))
  have h2 : (q + 2) ^ d ≤ (2 * (q + 1)) ^ d := Nat.pow_le_pow_left (by omega) d
  rw [mul_pow] at h2
  calc 2 ^ Nat.clog 2 ((q + 2) ^ d) ≤ 2 * (q + 2) ^ d := h1
    _ ≤ 2 * (2 ^ d * (q + 1) ^ d) := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (d + 1) * (q + 1) ^ d := by ring

variable (s : GateSources) (g : GateParams)

/-- **The hot part of the worker's fuel** at source length `N` (`tc` the counter's tape count). -/
def hotOf (tc N : ℕ) : ℕ := (300 * tc + 6000) * (10 * gadgets s g N * hotCall (width s g N))

/-- The native width tends to infinity. -/
theorem width_unbounded (K : ℕ) : ∃ N0, ∀ N, N0 ≤ N → K ≤ width s g N :=
  ⟨2 ^ K, fun N hN => Worker.gate_nativeWidth_ge s g K N hN⟩

theorem hot_bound (tc σ : ℕ) :
    ∃ B onset : ℕ, ∀ N, onset ≤ N → hotOf s g tc N * width s g N ^ σ ≤ B * 2 ^ width s g N := by
  obtain ⟨onset, h⟩ := WorkerArith.hot_split (fun N => width s g N) (fun N => 10 * gadgets s g N)
    (fun N _ => hotCall (width s g N)) (300 * tc + 6000) (10 * 2 ^ (g.clauseDegree + 1)) g.clauseDegree σ
    ⟨0, fun N _ _ _ => hotCall_mul _⟩
    (fun N => by
      have := gadgets_le g.clauseDegree (width s g N)
      simp only [gadgets]
      calc 10 * 2 ^ clauseWidth g.clauseDegree (width s g N)
          ≤ 10 * (2 ^ (g.clauseDegree + 1) * (width s g N + 1) ^ g.clauseDegree) := Nat.mul_le_mul_left _ this
        _ = 10 * 2 ^ (g.clauseDegree + 1) * (width s g N + 1) ^ g.clauseDegree := by ring)
    (width_unbounded s g)
  refine ⟨(300 * tc + 6000) * (10 * 2 ^ (g.clauseDegree + 1)), onset, fun N hN => ?_⟩
  have e := h N hN
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at e
  exact e

end

end NearCubicGates.Close.WorkerArith.WorkerBounds
