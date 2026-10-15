import Proof.Gates.CounterMachine.CellTablesCls11

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine

variable {B1 B2 cT : ℕ}

def dE (B1 B2 e0 : ℕ) : ℕ := 7 * b0Of B1 B2 + 3 * e0 + 17

def Kbkc (C0 e0 cT : ℕ) : ℕ := 610 + 12000 * (cT + 11) + 60 * Kbk C0 e0 cT

theorem bk_le (r : CellReq B1 B2 cT) (C0 e0 : ℕ) :
    bkCost (zOf B1 B2 C0 e0) cT r.c.n (natBitLength r.c.n) ≤ Kbkc C0 e0 cT * GT r (e0 + 7) := by
  have sz := sizes r
  have hB := Bk_le r C0 e0
  set T := r.c.n + 1 with hT
  set L := natBitLength r.c.n with hL
  have hT1 : 1 ≤ T := by omega
  have hLT : L ≤ T := sz.L3
  have h2L : 2 ^ L ≤ 2 * T := sz.L2
  set Bk := (zK (zOf B1 B2 C0 e0) cT r.c.n L).Bk L with hBk
  have hG1 := T_GT r 3
  have hG2 := S_GT r (e0 + 7)
  rw [← hT] at hG1 hG2
  have hTT : T ^ 3 ≤ GT r (e0 + 7) := hG1.trans (GT_mono r (by omega))
  have hT3 : T ^ 3 = T * T * T := by ring
  have hT2 : T * T ≤ T * T * T := Nat.le_mul_of_pos_right _ hT1
  have hT11 : T ≤ T * T := Nat.le_mul_of_pos_right _ hT1
  have a1 : bkACost L ≤ 510 * (T * T * T) := by
    unfold bkACost
    have : (L + 2) * (40 * 2 ^ L + 40) ≤ (3 * T) * (120 * T) := Nat.mul_le_mul (by omega) (by omega)
    have e : 3 * T * (120 * T) = 360 * (T * T) := by ring
    omega
  have a2 : 1000 * (L + cT + 10) * (L + 2) * (2 ^ L + 2) ≤ 12000 * (cT + 11) * (T * T * T) := by
    have h1 : L + cT + 10 ≤ (cT + 11) * T := by nlinarith
    calc 1000 * (L + cT + 10) * (L + 2) * (2 ^ L + 2) ≤ 1000 * ((cT + 11) * T) * (3 * T) * (4 * T) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (by omega)) (by omega)
      _ = _ := by ring
  have a3 : (r.c.n + 1) * (60 * Bk + 100) ≤ (60 * Kbk C0 e0 cT + 100) * GT r (e0 + 7) := by
    rw [← hT]
    have hS1 : 1 ≤ 2 ^ (r.c.n - r.p.k) := Nat.one_le_two_pow
    have hB' : Bk ≤ Kbk C0 e0 cT * 2 ^ (r.c.n - r.p.k) * T ^ (e0 + 6) := by
      unfold Kbk; rw [hBk]; exact hB
    have hT6 : 1 ≤ T ^ (e0 + 6) := Nat.one_le_pow _ _ hT1
    calc T * (60 * Bk + 100) ≤ T * (60 * (Kbk C0 e0 cT * 2 ^ (r.c.n - r.p.k) * T ^ (e0 + 6)) +
          100 * (2 ^ (r.c.n - r.p.k) * T ^ (e0 + 6))) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = (60 * Kbk C0 e0 cT + 100) * (2 ^ (r.c.n - r.p.k) * T ^ (e0 + 7)) := by rw [pow_succ]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hG2
  show bkACost L + 1000 * (L + cT + 10) * (L + 2) * (2 ^ L + 2) + (r.c.n + 1) * (60 * Bk + 100) ≤
    Kbkc C0 e0 cT * GT r (e0 + 7)
  unfold Kbkc
  have e : (610 + 12000 * (cT + 11) + 60 * Kbk C0 e0 cT) * GT r (e0 + 7) = 510 * GT r (e0 + 7) +
      12000 * (cT + 11) * GT r (e0 + 7) + (60 * Kbk C0 e0 cT + 100) * GT r (e0 + 7) := by ring
  have f1 : 510 * (T * T * T) ≤ 510 * GT r (e0 + 7) := Nat.mul_le_mul_left _ (hT3 ▸ hTT)
  have f2 : 12000 * (cT + 11) * (T * T * T) ≤ 12000 * (cT + 11) * GT r (e0 + 7) :=
    Nat.mul_le_mul_left _ (hT3 ▸ hTT)
  rw [e]
  clear_value Bk L T
  linarith

end NearCubicGates.Close.CounterMachine.CellTablesProg
