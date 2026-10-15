import Proof.Gates.Expand.Cost4

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

def Zq (r : FormulaReq) : ℕ := Mq r ^ 2 * Vq r ^ 3 * Pq r ^ 8

theorem stageA_le' (r : FormulaReq) (v p m : ℕ) (hv2 : 2 ≤ v) (hp1 : 1 ≤ p) (hm1 : 1 ≤ m)
    (fL : Lw r ≤ p) (fwt : r.2.weight ≤ p) (fD : r.2.degree ≤ p) (fN : (toks r.2).length ≤ p)
    (fnb : natBitLength r.1 ≤ p) (fV : r.1 + 2 = v) (fwb1 : Wb1 r + 1 ≤ 40 * (v ^ 0 * p ^ 2))
    (fwb1a : Wb1 r + tokBits r.2 + 2 ≤ 12 * (v ^ 0 * p ^ 2)) (fhE : maxExp r.2 + tokBits r.2 + r.1 + 2 ≤ 2 * (v * p)) :
    stageACost r ≤ 10 ^ 8 * (m ^ 2 * v ^ 3 * p ^ 8) := by
  have mk := fun (K a b c x : ℕ) (ha : a ≤ 2) (hb : b ≤ 3) (hc : c ≤ 8) (hx : x ≤ K * (m ^ a * v ^ b * p ^ c)) =>
    monoK hv2 hp1 hm1 K a b c x ha hb hc hx
  have hpp : p ≤ p ^ 2 := by nlinarith
  have hp23 : p ^ 2 ≤ p ^ 3 := pk_le hp1 2 3 (by omega)
  have hvp : p ≤ v * p := Nat.le_mul_of_pos_left _ (by omega)
  set Z := m ^ 2 * v ^ 3 * p ^ 8 with hZd
  -- measuring
  have a1 : measCost (Lw r) ≤ 42 * Z := mk 42 0 0 1 _ (by omega) (by omega) (by omega) (by
    unfold measCost; simp only [pow_zero, one_mul, pow_one]; omega)
  -- regA
  have a2 : regACost (Lw r) ≤ 400 * Z := mk 400 0 0 2 _ (by omega) (by omega) (by omega) (by
    unfold regACost; simp only [pow_zero, one_mul]
    have h1 : (Lw r + 2) * (18 * (Lw r + 2) + 3 + 8) ≤ (3 * p) * (65 * p) := Nat.mul_le_mul (by omega)
      (by omega)
    have e : (3 * p) * (65 * p) = 195 * p ^ 2 := by ring
    omega)
  -- the number block at Wb1
  have a3 : stageA1Cost (Wb1 r) (Lw r) ≤ 200000 * Z := mk 200000 0 0 3 _ (by omega) (by omega) (by omega) (by
    unfold stageA1Cost; simp only [pow_zero, one_mul]
    have w1 := fwb1; simp only [pow_zero, one_mul] at w1
    have i1 := initC (Wb1 r)
    have s1 := shlC (Wb1 r) (Lw r + 1)
    have h2 : 100 * (Wb1 r + 1) * (Lw r + 1 + 1) ≤ 100 * (40 * p ^ 2) * (3 * p) := by
      gcongr; omega
    have e : 100 * (40 * p ^ 2) * (3 * p) = 12000 * p ^ 3 := by ring
    omega)
  -- the passes
  have hc1 : hcost (Wb1 r) (tokBits r.2) (maxExp r.2) r.1 ≤ 1440000 * (v ^ 1 * p ^ 5) := by
    have := hcost_le (v := v) (p := p) (Wb1 r) (tokBits r.2) (maxExp r.2) r.1 12 0 fwb1a fhE
    simpa using this
  have a4 : evalCost (Wb1 r) (hcost (Wb1 r) (tokBits r.2) (maxExp r.2) r.1) r.1 (toks r.2).length (Lw r) ≤
      3687480 * Z := mk 3687480 0 1 6 _ (by omega) (by omega) (by omega) (by
    have := eval_le hv2 hp1 (Wb1 r) _ r.1 (toks r.2).length (Lw r) 1440000 0 1 hc1 fwb1 (by omega) fN fL
      le_rfl (by omega)
    simpa using this)
  have a5 : ∀ x, x ≤ p → toRegCost (Wb1 r) x ≤ 16000 * Z := fun x hx =>
    mk 16000 0 0 3 _ (by omega) (by omega) (by omega) (by
      have t := toRegC (Wb1 r) x
      have w1 := fwb1; simp only [pow_zero, one_mul] at w1 ⊢
      have : 200 * (Wb1 r + 1) * (x + 1) ≤ 200 * (40 * p ^ 2) * (2 * p) := by gcongr; omega
      have e : 200 * (40 * p ^ 2) * (2 * p) = 16000 * p ^ 3 := by ring
      omega)
  have a6 : readVCost r.1 (Lw r) ≤ 600 * Z := mk 600 0 1 1 _ (by omega) (by omega) (by omega) (by
    unfold readVCost; simp only [pow_zero, one_mul, pow_one]
    have t := two_pow_nbl_le r.1
    have h : (natBitLength r.1 + 2) * (40 * 2 ^ natBitLength r.1 + 40) ≤ (3 * p) * (140 * v) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (3 * p) * (140 * v) = 420 * (v * p) := by ring
    omega)
  have a7 : regB1Cost r.2.weight (Lw r) ≤ 1000 * Z := mk 1000 0 0 2 _ (by omega) (by omega) (by omega) (by
    unfold regB1Cost; simp only [pow_zero, one_mul]
    have h1 : (Lw r + 2) * (Lw r + 2) ≤ 9 * p ^ 2 := by nlinarith
    have h2 : (r.2.weight + 2 + Lw r + 2) * (18 * (Lw r + 2) + 3 + 8) ≤ (6 * p) * (65 * p) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (6 * p) * (65 * p) = 390 * p ^ 2 := by ring
    omega)
  have a8 : regB2Cost r.2.weight (Lw r) r.1 r.2.degree ≤ 300 * Z := mk 300 0 1 1 _ (by omega) (by omega) (by omega)
    (by
    unfold regB2Cost; simp only [pow_zero, one_mul, pow_one]
    have h : (r.2.degree + 1) * (18 * r.1 + 3 + 8) ≤ (2 * p) * (29 * v) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (2 * p) * (29 * v) = 58 * (v * p) := by ring
    omega)
  have hZ : 1 ≤ Z := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold stageACost
  have b5 := a5 _ fD
  have b5' := a5 _ fwt
  omega

theorem stageA_le (r : FormulaReq) : stageACost r ≤ 10 ^ 8 * Zq r :=
  let f := facts r
  stageA_le' r (Vq r) (Pq r) (Mq r) f.v2 f.p1 f.m1 f.L f.wt f.D f.N f.nb f.V f.wb1 f.wb1a f.hE

end NearCubicGates.Close.Expand.Layout
