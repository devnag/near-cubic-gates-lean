import Proof.Gates.CounterMachine.CellTablesCls6

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine

variable {B1 B2 cT : ℕ}

theorem tpow (T : ℕ) (hT : 1 ≤ T) {a b : ℕ} (h : a ≤ b) : T ^ a ≤ T ^ b := Nat.pow_le_pow_right hT h

/-- Constants. -/
def Kwb (B1 B2 C0 e0 : ℕ) : ℕ := (C0 + 100 * zeta ^ 2 + 16) * 2 ^ (e0 + 2 * b0Of B1 B2)
def Klb (B1 B2 : ℕ) : ℕ := 20 * zeta ^ 2 * 2 ^ (2 * b0Of B1 B2)
def Kbk (C0 e0 cT : ℕ) : ℕ := (C0 + 1) * 2 ^ (e0 + 8 + cT)
def Kbody (B1 B2 C0 e0 cT : ℕ) : ℕ := Klb B1 B2 + Kbk C0 e0 cT + 100 * (C0 + 10) + 1000 * (zeta + 10) ^ 2
def dB (B1 B2 e0 : ℕ) : ℕ := 2 * b0Of B1 B2 + e0 + 6

theorem W_le (r : CellReq B1 B2 cT) (C0 e0 : ℕ) :
    (zOf B1 B2 C0 e0).W (natBitLength r.c.n) ≤ Kwb B1 B2 C0 e0 * (r.c.n + 1) ^ (e0 + 2 * b0Of B1 B2) := by
  have h := (sizes r).L2
  show 2 ^ ((e0 + 2 * b0Of B1 B2) * natBitLength r.c.n) * (C0 + 100 * zeta ^ 2 + 16) ≤ _
  unfold Kwb
  calc 2 ^ ((e0 + 2 * b0Of B1 B2) * natBitLength r.c.n) * (C0 + 100 * zeta ^ 2 + 16)
      = (2 ^ natBitLength r.c.n) ^ (e0 + 2 * b0Of B1 B2) * (C0 + 100 * zeta ^ 2 + 16) := by
        rw [← pow_mul, mul_comm (natBitLength r.c.n)]
    _ ≤ (2 * (r.c.n + 1)) ^ (e0 + 2 * b0Of B1 B2) * (C0 + 100 * zeta ^ 2 + 16) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h _)
    _ = _ := by rw [mul_pow]; ring

theorem Lk_le (r : CellReq B1 B2 cT) (C0 e0 : ℕ) :
    (zOf B1 B2 C0 e0).Lk (natBitLength r.c.n) ≤ Klb B1 B2 * (r.c.n + 1) ^ (2 * b0Of B1 B2) := by
  have h := (sizes r).L2
  show 2 ^ (2 * b0Of B1 B2 * natBitLength r.c.n) * (20 * zeta ^ 2) ≤ _
  unfold Klb
  calc 2 ^ (2 * b0Of B1 B2 * natBitLength r.c.n) * (20 * zeta ^ 2)
      = (2 ^ natBitLength r.c.n) ^ (2 * b0Of B1 B2) * (20 * zeta ^ 2) := by
        rw [← pow_mul, mul_comm (natBitLength r.c.n)]
    _ ≤ (2 * (r.c.n + 1)) ^ (2 * b0Of B1 B2) * (20 * zeta ^ 2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h _)
    _ = _ := by rw [mul_pow]; ring

theorem le_ST {x A S T a d : ℕ} (h : x ≤ A * T ^ a) (had : a ≤ d) (hS : 1 ≤ S) (hT : 1 ≤ T) :
    x ≤ A * S * T ^ d := by
  have h1 : T ^ a ≤ T ^ d := Nat.pow_le_pow_right hT had
  calc x ≤ A * T ^ a := h
    _ ≤ A * T ^ d := Nat.mul_le_mul_left _ h1
    _ ≤ A * T ^ d * S := Nat.le_mul_of_pos_right _ hS
    _ = A * S * T ^ d := by ring

theorem le_ST' {x A S T a d : ℕ} (h : x ≤ A * S * T ^ a) (had : a ≤ d) (hT : 1 ≤ T) : x ≤ A * S * T ^ d :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hT had))

theorem body_le (r : CellReq B1 B2 cT) (C0 e0 : ℕ) :
    bodyCost ((zOf B1 B2 C0 e0).Lk (natBitLength r.c.n))
      ((zK (zOf B1 B2 C0 e0) cT r.c.n (natBitLength r.c.n)).Bk (natBitLength r.c.n)) (C0 * (r.c.n + 1) ^ e0) r ≤
      Kbody B1 B2 C0 e0 cT * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ dB B1 B2 e0 := by
  have hT1 : 1 ≤ r.c.n + 1 := by omega
  have hS1 : 1 ≤ 2 ^ (r.c.n - r.p.k) := Nat.one_le_two_pow
  have h1 := le_ST (Lk_le r C0 e0) (show 2 * b0Of B1 B2 ≤ dB B1 B2 e0 by unfold dB; omega) hS1 hT1
  have h2 : (zK (zOf B1 B2 C0 e0) cT r.c.n (natBitLength r.c.n)).Bk (natBitLength r.c.n) ≤
      Kbk C0 e0 cT * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ dB B1 B2 e0 :=
    le_ST' (Bk_le r C0 e0) (by unfold dB; omega) hT1
  have hX := Z_le r
  have e4 : 1 ≤ (r.c.n + 1) ^ b0Of B1 B2 := Nat.one_le_pow _ _ hT1
  have hXb : (cellInput r).length + 10 ≤ (zeta + 10) * (r.c.n + 1) ^ b0Of B1 B2 := by nlinarith
  have hX2 : ((cellInput r).length + 10) ^ 2 ≤ (zeta + 10) ^ 2 * (r.c.n + 1) ^ (2 * b0Of B1 B2) := by
    calc _ ≤ ((zeta + 10) * (r.c.n + 1) ^ b0Of B1 B2) ^ 2 := Nat.pow_le_pow_left hXb 2
      _ = _ := by ring
  have h4 := le_ST (show 1000 * ((cellInput r).length + 10) ^ 2 ≤ (1000 * (zeta + 10) ^ 2) *
    (r.c.n + 1) ^ (2 * b0Of B1 B2) by nlinarith) (show 2 * b0Of B1 B2 ≤ dB B1 B2 e0 by unfold dB; omega) hS1 hT1
  have h3 : 100 * 2 ^ (r.c.n - r.p.k) * (C0 * (r.c.n + 1) ^ e0 + 10) ≤
      (100 * (C0 + 10)) * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ dB B1 B2 e0 := by
    have ht : (r.c.n + 1) ^ e0 ≤ (r.c.n + 1) ^ dB B1 B2 e0 := Nat.pow_le_pow_right hT1 (by unfold dB; omega)
    have ht1 : 1 ≤ (r.c.n + 1) ^ dB B1 B2 e0 := Nat.one_le_pow _ _ hT1
    have : C0 * (r.c.n + 1) ^ e0 + 10 ≤ (C0 + 10) * (r.c.n + 1) ^ dB B1 B2 e0 := by nlinarith
    calc 100 * 2 ^ (r.c.n - r.p.k) * (C0 * (r.c.n + 1) ^ e0 + 10)
        ≤ 100 * 2 ^ (r.c.n - r.p.k) * ((C0 + 10) * (r.c.n + 1) ^ dB B1 B2 e0) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  unfold bodyCost Kbody
  have hsum : (Klb B1 B2 + Kbk C0 e0 cT + 100 * (C0 + 10) + 1000 * (zeta + 10) ^ 2) * 2 ^ (r.c.n - r.p.k) *
      (r.c.n + 1) ^ dB B1 B2 e0 = Klb B1 B2 * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ dB B1 B2 e0 +
        Kbk C0 e0 cT * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ dB B1 B2 e0 +
        (100 * (C0 + 10)) * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ dB B1 B2 e0 +
        (1000 * (zeta + 10) ^ 2) * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ dB B1 B2 e0 := by ring
  rw [hsum]
  omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
