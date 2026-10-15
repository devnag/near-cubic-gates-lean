import Proof.Gates.Expand.Cost2

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

section Mono
variable {v p m : ℕ} (hv : 2 ≤ v) (hp : 1 ≤ p) (hm : 1 ≤ m)
include hv hp hm

theorem mono (a b c : ℕ) (ha : a ≤ 2) (hb : b ≤ 3) (hc : c ≤ 8) : m ^ a * v ^ b * p ^ c ≤ m ^ 2 * v ^ 3 * p ^ 8 := by
  have h1 : m ^ a ≤ m ^ 2 := Nat.pow_le_pow_right hm ha
  have h2 : v ^ b ≤ v ^ 3 := Nat.pow_le_pow_right (by omega) hb
  have h3 : p ^ c ≤ p ^ 8 := Nat.pow_le_pow_right hp hc
  exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

theorem monoK (K a b c x : ℕ) (ha : a ≤ 2) (hb : b ≤ 3) (hc : c ≤ 8) (hx : x ≤ K * (m ^ a * v ^ b * p ^ c)) :
    x ≤ K * (m ^ 2 * v ^ 3 * p ^ 8) :=
  le_trans hx (Nat.mul_le_mul_left _ (mono hv hp hm a b c ha hb hc))

end Mono

section Pieces

theorem pk_le {p : ℕ} (hp : 1 ≤ p) (a b : ℕ) (h : a ≤ b) : p ^ a ≤ p ^ b := Nat.pow_le_pow_right hp h

theorem hcost_le {v p : ℕ} (Wb L E V a k : ℕ) (hWb : Wb + L + 2 ≤ a * (v ^ k * p ^ 2))
    (hE : E + L + V + 2 ≤ 2 * (v * p)) :
    hcost Wb L E V ≤ 10000 * a ^ 2 * (v ^ (2 * k + 1) * p ^ 5) := by
  unfold hcost
  calc 5000 * (E + L + V + 2) * (Wb + L + 2) ^ 2 ≤ 5000 * (2 * (v * p)) * (a * (v ^ k * p ^ 2)) ^ 2 := by gcongr
    _ = 10000 * a ^ 2 * (v ^ (2 * k + 1) * p ^ 5) := by ring

/-- `x ≤ p^a` and `a ≤ 6` give `x ≤ X` for `X = v^i p^6`. -/
theorem le_X {v p : ℕ} (hv : 1 ≤ v) (hp : 1 ≤ p) (i a : ℕ) (ha : a ≤ 6) : p ^ a ≤ v ^ i * p ^ 6 :=
  le_trans (pk_le hp a 6 ha) (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))

theorem eval_le {v p : ℕ} (hv : 2 ≤ v) (hp : 1 ≤ p) (Wb c Vn N L K i j : ℕ) (hc : c ≤ K * (v ^ j * p ^ 5))
    (hWb : Wb + 1 ≤ 40 * (v ^ i * p ^ 2)) (hVn : Vn ≤ v) (hN : N ≤ p) (hL : L ≤ p) (hj : 1 ≤ j) (hij : 2 * i ≤ j) :
    evalCost Wb c Vn N L ≤ (2 * K + 4000 + 3200 + 40 + 800000 + 240) * (v ^ j * p ^ 6) := by
  have e0 := evalC Wb c Vn N L
  have hv1 : 1 ≤ v := by omega
  have hvj1 : v ≤ v ^ j := by
    calc v = v ^ 1 := (pow_one v).symm
      _ ≤ v ^ j := Nat.pow_le_pow_right hv1 hj
  set X := v ^ j * p ^ 6 with hX
  have t1 : (N + 1) * (c + 2000) ≤ (2 * K + 4000) * X := by
    have a1 : N + 1 ≤ 2 * p := by omega
    have a2 : c + 2000 ≤ (K + 2000) * (v ^ j * p ^ 5) := by
      have : 1 ≤ v ^ j * p ^ 5 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    calc (N + 1) * (c + 2000) ≤ (2 * p) * ((K + 2000) * (v ^ j * p ^ 5)) := Nat.mul_le_mul a1 a2
      _ = (2 * K + 4000) * X := by rw [hX]; ring
  have t2 : 200 * (N + 3) ^ 2 ≤ 3200 * X := by
    have h1 : (N + 3) ^ 2 ≤ (4 * p) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (4 * p) ^ 2 = 16 * p ^ 2 := by ring
    have h3 := le_X hv1 hp j 2 (by omega)
    omega
  have t3 : 40 * Vn ≤ 40 * X := by
    have : v ≤ X := le_trans hvj1 (Nat.le_mul_of_pos_right _ (by positivity))
    omega
  have t4 : 500 * (Wb + 1) ^ 2 ≤ 800000 * X := by
    have h1 : (Wb + 1) ^ 2 ≤ (40 * (v ^ i * p ^ 2)) ^ 2 := Nat.pow_le_pow_left hWb 2
    have e : (40 * (v ^ i * p ^ 2)) ^ 2 = 1600 * (v ^ (2 * i) * p ^ 4) := by ring
    have h2 : v ^ (2 * i) * p ^ 4 ≤ X :=
      Nat.mul_le_mul (Nat.pow_le_pow_right hv1 hij) (pk_le hp 4 6 (by omega))
    omega
  have t5 : 40 * L + 200 ≤ 240 * X := by
    have h1 := le_X hv1 hp j 1 (by omega)
    have h0 := le_X hv1 hp j 0 (by omega)
    simp only [pow_one, pow_zero] at h1 h0
    omega
  have e : (2 * K + 4000 + 3200 + 40 + 800000 + 240) * X =
      (2 * K + 4000) * X + 3200 * X + 40 * X + 800000 * X + 240 * X := by ring
  omega

end Pieces

end NearCubicGates.Close.Expand.Layout
