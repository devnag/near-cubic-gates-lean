import Proof.Gates.Expand.Cost5

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

theorem stageB_le' (r : FormulaReq) (v p m : ℕ) (hv2 : 2 ≤ v) (hp1 : 1 ≤ p) (hm1 : 1 ≤ m)
    (fL : Lw r ≤ p) (fD : r.2.degree ≤ p) (fV : r.1 + 2 = v) (fWt : Wt r ≤ 3 * p)
    (fwb2 : Wb2 r + 1 ≤ 40 * (v ^ 1 * p ^ 2)) :
    stageBCost r ≤ 10 ^ 8 * (m ^ 2 * v ^ 3 * p ^ 8) := by
  have mk := fun (K a b c x : ℕ) (ha : a ≤ 2) (hb : b ≤ 3) (hc : c ≤ 8) (hx : x ≤ K * (m ^ a * v ^ b * p ^ c)) =>
    monoK hv2 hp1 hm1 K a b c x ha hb hc hx
  set Z := m ^ 2 * v ^ 3 * p ^ 8 with hZd
  have w2 : Wb2 r + 1 ≤ 40 * (v * p ^ 2) := by simpa using fwb2
  have hpp : p ≤ p ^ 2 := by nlinarith
  have hp23 : p ^ 2 ≤ p ^ 3 := pk_le hp1 2 3 (by omega)
  have hvp2 : p ^ 2 ≤ v * p ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have hvp3 : v * p ^ 2 ≤ v * p ^ 3 := Nat.mul_le_mul_left _ hp23
  have hv1 : v ≤ v * p ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have b1 : 53 * (initCost (Wb2 r) + 1) ≤ 90000 * Z := mk 90000 0 1 2 _ (by omega) (by omega) (by omega) (by
    have := initC (Wb2 r); simp only [pow_zero, one_mul, pow_one]; omega)
  have b2 : constB1Cost (Wb2 r) r.1 (Wt r) r.2.degree ≤ 100000 * Z := mk 100000 0 2 3 _ (by omega) (by omega)
    (by omega) (by
    unfold constB1Cost; simp only [pow_zero, one_mul]
    have s1 := shlC (Wb2 r) r.1
    have s2 := shlC (Wb2 r) (Wt r)
    have t1 : 100 * (Wb2 r + 1) * (r.1 + 1) ≤ 100 * (40 * (v * p ^ 2)) * v := by gcongr; omega
    have t2 : 100 * (Wb2 r + 1) * (Wt r + 1) ≤ 100 * (40 * (v * p ^ 2)) * (4 * p) := by gcongr; omega
    have e1 : 100 * (40 * (v * p ^ 2)) * v = 4000 * (v ^ 2 * p ^ 2) := by ring
    have e2 : 100 * (40 * (v * p ^ 2)) * (4 * p) = 16000 * (v * p ^ 3) := by ring
    have u1 : v ^ 2 * p ^ 2 ≤ v ^ 2 * p ^ 3 := Nat.mul_le_mul_left _ hp23
    have u2 : v * p ^ 3 ≤ v ^ 2 * p ^ 3 := Nat.mul_le_mul_right _ (by nlinarith)
    have u3 : v * p ^ 2 ≤ v ^ 2 * p ^ 3 := le_trans hvp3 u2
    omega)
  have b3 : constB2Cost (Wb2 r) ≤ 1000000 * Z := mk 1000000 0 2 4 _ (by omega) (by omega) (by omega) (by
    unfold constB2Cost; simp only [pow_zero, one_mul]
    have m1 := mulC (Wb2 r)
    have t : (Wb2 r + 1) ^ 2 ≤ (40 * (v * p ^ 2)) ^ 2 := Nat.pow_le_pow_left w2 2
    have e : (40 * (v * p ^ 2)) ^ 2 = 1600 * (v ^ 2 * p ^ 4) := by ring
    have u : v * p ^ 2 ≤ v ^ 2 * p ^ 4 := Nat.mul_le_mul (by nlinarith) (by nlinarith)
    omega)
  have b4 : constB3Cost (Wb2 r) ≤ 20000 * Z := mk 20000 0 1 2 _ (by omega) (by omega) (by omega) (by
    unfold constB3Cost; simp only [pow_zero, one_mul, pow_one]; omega)
  have b5 : Lw r * (1 + 2) + 1 + 1 + (Wt r * (1 + 2) + 1 + 1 + (Wb2 r * (1 + 2) + 1 + 1 + ((Lw r + 2) * (1 + 2) + 1)))
      ≤ 500 * Z := mk 500 0 1 2 _ (by omega) (by omega) (by omega) (by
    simp only [pow_zero, one_mul, pow_one]; omega)
  have hZ : 1 ≤ Z := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold stageBCost constBCost
  omega

theorem stageB_le (r : FormulaReq) : stageBCost r ≤ 10 ^ 8 * Zq r :=
  let f := facts r
  stageB_le' r (Vq r) (Pq r) (Mq r) f.v2 f.p1 f.m1 f.L f.D f.V f.Wt f.wb2

theorem cleanup_le (r : FormulaReq) : cleanupCost r ≤ 10 ^ 8 * Zq r := by
  have f := facts r
  have mk := fun (K a b c x : ℕ) (ha : a ≤ 2) (hb : b ≤ 3) (hc : c ≤ 8)
    (hx : x ≤ K * (Mq r ^ a * Vq r ^ b * Pq r ^ c)) => monoK f.v2 f.p1 f.m1 K a b c x ha hb hc hx
  have h := mk 100 0 1 1 (cleanupCost r) (by omega) (by omega) (by omega) (by
    unfold cleanupCost; simp only [pow_zero, one_mul, pow_one]
    have h1 : r.2.degree ≤ Pq r := f.D
    have h2 : Lw r ≤ Pq r := f.L
    have h3 : r.1 + 2 = Vq r := f.V
    have h4 : 1 ≤ Pq r := f.p1
    have h5 : Pq r ≤ Vq r * Pq r := Nat.le_mul_of_pos_left _ (by omega)
    have h6 : Vq r ≤ Vq r * Pq r := Nat.le_mul_of_pos_right _ (by omega)
    omega)
  unfold Zq; omega

end NearCubicGates.Close.Expand.Layout
