import Proof.Gates.CounterMachine.CellTablesCls10

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine

variable {B1 B2 cT : ℕ}

theorem GT_succ (r : CellReq B1 B2 cT) (d : ℕ) : (r.c.n + 1) * GT r d = GT r (d + 1) := by
  unfold GT; rw [pow_succ]; ring

theorem one_GT (r : CellReq B1 B2 cT) (d : ℕ) : 1 ≤ GT r d :=
  (Nat.one_le_pow _ _ (by omega)).trans (T_GT r d)

def dN (B1 B2 e0 : ℕ) : ℕ := 3 * b0Of B1 B2 + e0 + 9

def KN (B1 B2 C0 e0 cT : ℕ) : ℕ :=
  Kst + 2 * (Kpr B1 B2 C0 e0 cT + 25) + (4 * zeta * (Kbody B1 B2 C0 e0 cT + 9) + 2 * Kbody B1 B2 C0 e0 cT + 22) +
    100 * (8 + 4 * zeta + 1) * (12 * zeta ^ 2 + 10) + 10

theorem main_le (r : CellReq B1 B2 cT) (C0 e0 : ℕ) :
    mainCost ((zOf B1 B2 C0 e0).Lk (natBitLength r.c.n))
      ((zK (zOf B1 B2 C0 e0) cT r.c.n (natBitLength r.c.n)).Bk (natBitLength r.c.n)) (C0 * (r.c.n + 1) ^ e0) r ≤
      KN B1 B2 C0 e0 cT * GT r (dN B1 B2 e0) := by
  have sz := sizes r
  have hst := start_le r
  have hp := prime_le r C0 e0
  have hb := body_le r C0 e0
  have hrq := reqIds_le r
  have hZ := Z_le r
  have hlam := lamW_le r
  set T := r.c.n + 1 with hT
  have hT1 : 1 ≤ T := by omega
  set G := GT r (dN B1 B2 e0) with hG
  set TB := bodyCost ((zOf B1 B2 C0 e0).Lk (natBitLength r.c.n))
      ((zK (zOf B1 B2 C0 e0) cT r.c.n (natBitLength r.c.n)).Bk (natBitLength r.c.n)) (C0 * T ^ e0) r with hTB
  have hb' : TB ≤ Kbody B1 B2 C0 e0 cT * 2 ^ (r.c.n - r.p.k) * T ^ dB B1 B2 e0 := hb
  -- the start
  have a1 : startCost r ≤ Kst * G := by
    calc startCost r ≤ Kst * T ^ (3 * b0Of B1 B2) := hst
      _ ≤ Kst * G := Nat.mul_le_mul_left _ ((T_GT r _).trans (GT_mono r (by unfold dN; omega)))
  -- the parts
  set PC := r.p.P ^ dOf r.c r.p * (TB + 4) + 7 * r.p.e + 7 * dOf r.c r.p + 30 with hPC
  have a2 : partCost ((zOf B1 B2 C0 e0).Lk (natBitLength r.c.n))
      ((zK (zOf B1 B2 C0 e0) cT r.c.n (natBitLength r.c.n)).Bk (natBitLength r.c.n)) (C0 * T ^ e0) r ≤
      (Kpr B1 B2 C0 e0 cT + 25) * G := by
    unfold partCost primeCost
    rw [← hTB, ← hPC]
    have hL := sz.np
    rw [← hT] at hL
    have h1 : (r.p.primes.sort (· ≤ ·)).length * (PC + 4) ≤ T * (Kpr B1 B2 C0 e0 cT * GT r (dP B1 B2 e0) + 4) :=
      Nat.mul_le_mul hL (by omega)
    have h2 : T * GT r (dP B1 B2 e0) ≤ G := by
      rw [GT_succ]; exact GT_mono r (by unfold dP dB dN; omega)
    have h3 : T ≤ G := by
      have := (T_GT r 1).trans (GT_mono r (show 1 ≤ dN B1 B2 e0 by unfold dN; omega))
      rwa [pow_one] at this
    have h4 : T * (Kpr B1 B2 C0 e0 cT * GT r (dP B1 B2 e0) + 4) = Kpr B1 B2 C0 e0 cT * (T * GT r (dP B1 B2 e0)) +
        4 * T := by ring
    have h5 : Kpr B1 B2 C0 e0 cT * (T * GT r (dP B1 B2 e0)) ≤ Kpr B1 B2 C0 e0 cT * G := Nat.mul_le_mul_left _ h2
    have h6 : (Kpr B1 B2 C0 e0 cT + 25) * G = Kpr B1 B2 C0 e0 cT * G + 25 * G := by ring
    have h7 := one_GT r (dN B1 B2 e0)
    rw [← hG] at h7
    rw [h6]
    omega
  -- the moments
  have a3 : roleCount r.c.kind * (r.p.J * (TB + 4) + TB + 5 + 4) + 4 ≤
      (4 * zeta * (Kbody B1 B2 C0 e0 cT + 9) + 2 * Kbody B1 B2 C0 e0 cT + 22) * G := by
    set U := 2 ^ (r.c.n - r.p.k) * T ^ dB B1 B2 e0 with hU
    have hU1 : 1 ≤ U := Nat.mul_le_mul Nat.one_le_two_pow (Nat.one_le_pow _ _ hT1)
    have hTB' : TB + 9 ≤ (Kbody B1 B2 C0 e0 cT + 9) * U := by
      have e : (Kbody B1 B2 C0 e0 cT + 9) * U = Kbody B1 B2 C0 e0 cT * 2 ^ (r.c.n - r.p.k) * T ^ dB B1 B2 e0 + 9 * U := by
        rw [hU]; ring
      have := hb'
      omega
    have hJ : r.p.J + 1 ≤ 2 * (zeta * T ^ b0Of B1 B2) := by have := sz.JX; omega
    have hUG : T ^ b0Of B1 B2 * U ≤ G := by
      calc T ^ b0Of B1 B2 * U = 2 ^ (r.c.n - r.p.k) * T ^ (dB B1 B2 e0 + b0Of B1 B2) := by rw [hU, pow_add]; ring
        _ ≤ GT r (dB B1 B2 e0 + b0Of B1 B2) := S_GT r _
        _ ≤ G := GT_mono r (by unfold dB dN; omega)
    have hUG' : U ≤ G := (Nat.le_mul_of_pos_left U (Nat.one_le_pow _ _ hT1)).trans hUG
    have m1 : r.p.J * (TB + 4) ≤ (2 * zeta * (Kbody B1 B2 C0 e0 cT + 9)) * G := by
      calc r.p.J * (TB + 4) ≤ (2 * (zeta * T ^ b0Of B1 B2)) * ((Kbody B1 B2 C0 e0 cT + 9) * U) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = (2 * zeta * (Kbody B1 B2 C0 e0 cT + 9)) * (T ^ b0Of B1 B2 * U) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hUG
    have m2 : TB + 9 ≤ (Kbody B1 B2 C0 e0 cT + 9) * G := hTB'.trans (Nat.mul_le_mul_left _ hUG')
    have hrc := sz.rc
    have m3 : roleCount r.c.kind * (r.p.J * (TB + 4) + TB + 5 + 4) ≤
        2 * ((2 * zeta * (Kbody B1 B2 C0 e0 cT + 9)) * G + (Kbody B1 B2 C0 e0 cT + 9) * G) :=
      Nat.mul_le_mul hrc (by omega)
    have h7 := one_GT r (dN B1 B2 e0)
    rw [← hG] at h7
    have e : (4 * zeta * (Kbody B1 B2 C0 e0 cT + 9) + 2 * Kbody B1 B2 C0 e0 cT + 22) * G ≥
        2 * ((2 * zeta * (Kbody B1 B2 C0 e0 cT + 9)) * G + (Kbody B1 B2 C0 e0 cT + 9) * G) + 4 := by
      have : (4 * zeta * (Kbody B1 B2 C0 e0 cT + 9) + 2 * Kbody B1 B2 C0 e0 cT + 22) * G =
          2 * ((2 * zeta * (Kbody B1 B2 C0 e0 cT + 9)) * G + (Kbody B1 B2 C0 e0 cT + 9) * G) + 4 * G := by ring
      omega
    omega
  -- the sort and print
  have a4 : 100 * ((reqIds r.c r.p).length * 2 ^ (r.c.n - r.p.k) + 1) * (recWidth r.c r.p r.wt + 10) ≤
      100 * (8 + 4 * zeta + 1) * (12 * zeta ^ 2 + 10) * G := by
    have hcb : cellBits r.wt.I = r.c.n - r.p.k := outerCoords_length r.wt.I (cellReq_hk r)
    have hRW : recWidth r.c r.p r.wt ≤ lamW r.c r.p := by unfold recWidth lamW; rw [hcb]; omega
    have hZ2 : (T + (cellInput r).length + 3) ^ 2 ≤ zeta ^ 2 * T ^ (2 * b0Of B1 B2) := by
      calc _ ≤ (zeta * T ^ b0Of B1 B2) ^ 2 := Nat.pow_le_pow_left hZ 2
        _ = _ := by ring
    have hR : recWidth r.c r.p r.wt + 10 ≤ (12 * zeta ^ 2 + 10) * T ^ (2 * b0Of B1 B2) := by
      have := Nat.one_le_pow (2 * b0Of B1 B2) T hT1
      nlinarith
    have hQ : (reqIds r.c r.p).length * 2 ^ (r.c.n - r.p.k) + 1 ≤ (8 + 4 * zeta + 1) * GT r (b0Of B1 B2 + 3) := by
      have h1 : (reqIds r.c r.p).length * 2 ^ (r.c.n - r.p.k) ≤ (8 + 4 * zeta) * GT r (b0Of B1 B2 + 3) := by
        calc (reqIds r.c r.p).length * 2 ^ (r.c.n - r.p.k) ≤ ((8 + 4 * zeta) * T ^ (2 * Jmax r.c.n) *
              T ^ (b0Of B1 B2 + 3)) * 2 ^ (r.c.n - r.p.k) := Nat.mul_le_mul_right _ hrq
          _ = (8 + 4 * zeta) * GT r (b0Of B1 B2 + 3) := by unfold GT Gc; rw [← hT]; ring
      have h2 := one_GT r (b0Of B1 B2 + 3)
      nlinarith
    calc 100 * ((reqIds r.c r.p).length * 2 ^ (r.c.n - r.p.k) + 1) * (recWidth r.c r.p r.wt + 10)
        ≤ 100 * ((8 + 4 * zeta + 1) * GT r (b0Of B1 B2 + 3)) * ((12 * zeta ^ 2 + 10) * T ^ (2 * b0Of B1 B2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hQ) hR
      _ = 100 * (8 + 4 * zeta + 1) * (12 * zeta ^ 2 + 10) * GT r (b0Of B1 B2 + 3 + 2 * b0Of B1 B2) := by
          unfold GT; rw [pow_add (r.c.n + 1) (b0Of B1 B2 + 3)]; rw [← hT]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (GT_mono r (by unfold dN; omega))
  unfold mainCost KN
  rw [← hTB]
  have h7 := one_GT r (dN B1 B2 e0)
  rw [← hG] at h7
  have e : (Kst + 2 * (Kpr B1 B2 C0 e0 cT + 25) + (4 * zeta * (Kbody B1 B2 C0 e0 cT + 9) + 2 * Kbody B1 B2 C0 e0 cT + 22) +
      100 * (8 + 4 * zeta + 1) * (12 * zeta ^ 2 + 10) + 10) * G = Kst * G + 2 * ((Kpr B1 B2 C0 e0 cT + 25) * G) +
      (4 * zeta * (Kbody B1 B2 C0 e0 cT + 9) + 2 * Kbody B1 B2 C0 e0 cT + 22) * G +
      100 * (8 + 4 * zeta + 1) * (12 * zeta ^ 2 + 10) * G + 10 * G := by ring
  rw [e]
  omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
