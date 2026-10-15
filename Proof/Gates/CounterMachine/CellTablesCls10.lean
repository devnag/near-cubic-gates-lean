import Proof.Gates.CounterMachine.CellTablesCls9

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine

variable {B1 B2 cT : ℕ}

/-- `G·T^d`. -/
def GT (r : CellReq B1 B2 cT) (d : ℕ) : ℕ := Gc r * (r.c.n + 1) ^ d

theorem GT_mono (r : CellReq B1 B2 cT) {d d' : ℕ} (h : d ≤ d') : GT r d ≤ GT r d' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h)

theorem S_GT (r : CellReq B1 B2 cT) (d : ℕ) : 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ d ≤ GT r d := by
  unfold GT Gc
  have : 1 ≤ (r.c.n + 1) ^ (2 * Jmax r.c.n) := Nat.one_le_pow _ _ (by omega)
  exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ this)

theorem J_GT (r : CellReq B1 B2 cT) (d : ℕ) : (r.c.n + 1) ^ (2 * Jmax r.c.n) * (r.c.n + 1) ^ d ≤ GT r d := by
  unfold GT Gc
  have h1 : 1 ≤ 2 ^ (r.c.n - r.p.k) := Nat.one_le_two_pow
  exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ h1)

theorem T_GT (r : CellReq B1 B2 cT) (d : ℕ) : (r.c.n + 1) ^ d ≤ GT r d := by
  have h : 1 ≤ (r.c.n + 1) ^ (2 * Jmax r.c.n) := Nat.one_le_pow _ _ (by omega)
  exact (Nat.le_mul_of_pos_left _ h).trans (J_GT r d)

def dP (B1 B2 e0 : ℕ) : ℕ := dB B1 B2 e0 + 2
def Kpr (B1 B2 C0 e0 cT : ℕ) : ℕ := Kbody B1 B2 C0 e0 cT + 48 + 14 * zeta

theorem prime_le (r : CellReq B1 B2 cT) (C0 e0 : ℕ) :
    r.p.P ^ dOf r.c r.p * (bodyCost ((zOf B1 B2 C0 e0).Lk (natBitLength r.c.n))
      ((zK (zOf B1 B2 C0 e0) cT r.c.n (natBitLength r.c.n)).Bk (natBitLength r.c.n)) (C0 * (r.c.n + 1) ^ e0) r + 4) +
      7 * r.p.e + 7 * dOf r.c r.p + 30 ≤ Kpr B1 B2 C0 e0 cT * GT r (dP B1 B2 e0) := by
  have sz := sizes r
  have hb := body_le r C0 e0
  have hZ := Z_le r
  set T := r.c.n + 1 with hT
  have hT1 : 1 ≤ T := by omega
  have hPD : r.p.P ^ dOf r.c r.p ≤ T ^ (2 * Jmax r.c.n) * T ^ 2 := by
    calc r.p.P ^ dOf r.c r.p ≤ T ^ dOf r.c r.p := Nat.pow_le_pow_left (by have := sz.P; omega) _
      _ ≤ T ^ (2 * Jmax r.c.n + 2) := Nat.pow_le_pow_right hT1 sz.DJ
      _ = _ := by rw [pow_add]
  set TB := bodyCost ((zOf B1 B2 C0 e0).Lk (natBitLength r.c.n))
      ((zK (zOf B1 B2 C0 e0) cT r.c.n (natBitLength r.c.n)).Bk (natBitLength r.c.n)) (C0 * T ^ e0) r with hTB
  have m1 : r.p.P ^ dOf r.c r.p * (TB + 4) ≤ (Kbody B1 B2 C0 e0 cT + 4) * GT r (dP B1 B2 e0) := by
    have : TB + 4 ≤ (Kbody B1 B2 C0 e0 cT + 4) * (2 ^ (r.c.n - r.p.k) * T ^ dB B1 B2 e0) := by
      have hst : 1 ≤ 2 ^ (r.c.n - r.p.k) * T ^ dB B1 B2 e0 :=
        Nat.mul_le_mul (Nat.one_le_two_pow) (Nat.one_le_pow _ _ hT1)
      have e : (Kbody B1 B2 C0 e0 cT + 4) * (2 ^ (r.c.n - r.p.k) * T ^ dB B1 B2 e0) =
          Kbody B1 B2 C0 e0 cT * 2 ^ (r.c.n - r.p.k) * T ^ dB B1 B2 e0 + 4 * (2 ^ (r.c.n - r.p.k) * T ^ dB B1 B2 e0) := by
        ring
      omega
    calc r.p.P ^ dOf r.c r.p * (TB + 4) ≤ (T ^ (2 * Jmax r.c.n) * T ^ 2) *
          ((Kbody B1 B2 C0 e0 cT + 4) * (2 ^ (r.c.n - r.p.k) * T ^ dB B1 B2 e0)) := Nat.mul_le_mul hPD this
      _ = (Kbody B1 B2 C0 e0 cT + 4) * GT r (dP B1 B2 e0) := by unfold GT Gc dP; rw [← hT]; ring
  have m2 : 7 * r.p.e + 7 * dOf r.c r.p + 30 ≤ (44 + 14 * zeta) * GT r (dP B1 B2 e0) := by
    have h1 := T_GT r (dP B1 B2 e0)
    have h2 : T ^ b0Of B1 B2 ≤ T ^ dP B1 B2 e0 := Nat.pow_le_pow_right hT1 (by unfold dP dB; omega)
    rw [← hT] at h1
    have := sz.e; have := sz.k; have := sz.D
    have h3 : 1 ≤ T ^ b0Of B1 B2 := Nat.one_le_pow _ _ hT1
    have h4 : (44 + 14 * zeta) * GT r (dP B1 B2 e0) = 44 * GT r (dP B1 B2 e0) + 14 * (zeta * GT r (dP B1 B2 e0)) := by
      ring
    have h5 : zeta * T ^ b0Of B1 B2 ≤ zeta * GT r (dP B1 B2 e0) := Nat.mul_le_mul_left _ (h2.trans h1)
    rw [h4]
    omega
  unfold Kpr
  have h6 : (Kbody B1 B2 C0 e0 cT + 48 + 14 * zeta) * GT r (dP B1 B2 e0) =
      (Kbody B1 B2 C0 e0 cT + 4) * GT r (dP B1 B2 e0) + (44 + 14 * zeta) * GT r (dP B1 B2 e0) := by ring
  rw [h6]
  omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
