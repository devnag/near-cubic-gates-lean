import Proof.Gates.CounterMachine.CellTablesCls8

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Cells.PrefixLoader (loadCost)

variable {B1 B2 cT : ℕ}

theorem cst_le (r : CellReq B1 B2 cT) :
    cstCost r.c r.p ≤ 200 * (r.c.n + 1 + (cellInput r).length + 3) ^ 2 := by
  have sz := sizes r
  have hl := lamW_le r
  set Z := r.c.n + 1 + (cellInput r).length + 3 with hZ
  have hZ4 : 4 ≤ Z := by omega
  have hZZ : 4 * Z ≤ Z ^ 2 := by nlinarith
  unfold cstCost
  unfold lamW at hl
  have := sz.P; have := sz.JX; have := sz.D; have := sz.db; have := sz.k
  have hZ2 : 16 ≤ Z ^ 2 := by nlinarith
  omega

theorem load_le (r : CellReq B1 B2 cT) :
    loadCost (callN r.c).length (paramsN r.p).length (witN r.c r.p r.wt).length (srList r.c r.p).length
      (cellInput r).length ≤ 200 * ((cellInput r).length + 2) ^ 3 := by
  set X := (cellInput r).length with hX
  have hc := cellN_len_le r
  have h1 : (callN r.c).length ≤ X := by
    have : (callN r.c).length ≤ (cellN r.c r.p r.wt).length := by unfold cellN; simp only [List.length_append]; omega
    omega
  have h2 : (paramsN r.p).length ≤ X := by
    have : (paramsN r.p).length ≤ (cellN r.c r.p r.wt).length := by unfold cellN; simp only [List.length_append]; omega
    omega
  have h3 : (witN r.c r.p r.wt).length ≤ X := by
    have : (witN r.c r.p r.wt).length ≤ (cellN r.c r.p r.wt).length := by unfold cellN; simp only [List.length_append]; omega
    omega
  have h4 : (srList r.c r.p).length ≤ X := (srList_le_witN r.c r.p r.wt).trans h3
  unfold loadCost
  have m1 : (callN r.c).length * (30 * X + 45) ≤ X * (30 * X + 45) := Nat.mul_le_mul_right _ h1
  have m2 : (paramsN r.p).length * (30 * X + 45) ≤ X * (30 * X + 45) := Nat.mul_le_mul_right _ h2
  have m3 : (witN r.c r.p r.wt).length * (30 * X + 45) ≤ X * (30 * X + 45) := Nat.mul_le_mul_right _ h3
  have m4 : (srList r.c r.p).length * ((witN r.c r.p r.wt).length * (30 * X + 45) + 10 + 4) ≤
      X * (X * (30 * X + 45) + 14) := Nat.mul_le_mul h4 (by omega)
  have q : 3 * (X * (30 * X + 45)) + X * (X * (30 * X + 45) + 14) + 1000 ≤ 200 * (X + 2) ^ 3 := by ring_nf; omega
  omega

def Kst : ℕ := 600 * zeta ^ 3

theorem start_le (r : CellReq B1 B2 cT) : startCost r ≤ Kst * (r.c.n + 1) ^ (3 * b0Of B1 B2) := by
  have hc := cst_le r
  have hl := load_le r
  have hcl := cellN_len_le r
  have hZ := Z_le r
  set T := r.c.n + 1 with hT
  set X := (cellInput r).length with hX
  set Z := T + X + 3 with hZd
  have hZ4 : 4 ≤ Z := by omega
  have hZ3 : Z ^ 3 ≤ zeta ^ 3 * T ^ (3 * b0Of B1 B2) := by
    calc Z ^ 3 ≤ (zeta * T ^ b0Of B1 B2) ^ 3 := Nat.pow_le_pow_left hZ 3
      _ = _ := by ring
  have hX3 : (X + 2) ^ 3 ≤ Z ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hZZ : 4 * Z ≤ Z ^ 2 := by nlinarith
  have hZ16 : 16 ≤ Z ^ 2 := by nlinarith
  have hZ34 : 4 * Z ^ 2 ≤ Z ^ 3 := by nlinarith
  have hZ23 : 200 * Z ^ 2 + 21 * X + 400 ≤ 400 * Z ^ 3 := by omega
  unfold startCost Kst
  rw [← hT, ← hX] at *
  nlinarith

end NearCubicGates.Close.CounterMachine.CellTablesProg
