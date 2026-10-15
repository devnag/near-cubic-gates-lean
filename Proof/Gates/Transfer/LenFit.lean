import Proof.Gates.Interfaces.Transfer
import Proof.PCP.PCPPNativeCanonicalBounds

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RecoveryScheduleEnvelope

/-- `q(2^ν) + 1 ≤ C (ν + 1)` for a constant `C` depending on the clock and `A_pad` only. -/
theorem widthOf_lin (k A ν : ℕ) : Outer.widthOf k A (2 ^ ν) + 1 ≤ ((A + 1) * (k + 2) + 3 * A + 1) * (ν + 1) := by
  unfold Outer.widthOf
  rw [Outer.clkLog_two_pow]
  have hc : Nat.clog 2 (ν * (k + 2) + 2) ≤ ν * (k + 2) + 2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have h1 : A * Nat.clog 2 (ν * (k + 2) + 2) ≤ A * (ν * (k + 2) + 2) := Nat.mul_le_mul_left _ hc
  nlinarith

/-- **The instance length fits** (paper v2 §11.4's guard, eventually true). -/
theorem lenFit (s : GateSources) (degree : ℕ) :
    ∃ lenRoot : ℕ, ∀ g : GateParams, g.degree = degree → g.lenRoot = lenRoot →
      ∃ ν₀ : ℕ, ∀ ν, ν₀ ≤ ν → ∀ B : BooleanCircuit (g.width s ν), B.size ≤ g.bound s ν →
        Outer.SrcFits g.lenExp ν B := by
  obtain ⟨c, e, hc0, hc⟩ := oracleSizeBound_polynomiallyBounded degree
  refine ⟨2 * e + 2, fun g hdeg hroot => ?_⟩
  set A := Outer.apad s.mw (g.sv s) with hA
  set C1 := (A + 1) * (g.k + 2) + 3 * A + 1 with hC1
  set K0 := 39 * ((c + 6) * C1 ^ (e + 1)) ^ 2 * 2 ^ (2 * e + 2) with hK0
  refine ⟨K0 + 1, fun ν hν B hB => ?_⟩
  have hν1 : 1 ≤ ν := by omega
  have hqν : (g.width s ν) + 1 ≤ C1 * (ν + 1) := widthOf_lin g.k A ν
  have hS : B.size ≤ c * ((g.width s ν) + 1) ^ e := by
    have hB' : B.size ≤ oracleSizeBound degree (g.width s ν) := by
      have h := hB
      unfold GateParams.bound at h
      rw [hdeg] at h
      exact h
    exact hB'.trans (hc (g.width s ν))
  -- the descriptor
  have hd := RepairOrdinary.PCPPNative.descriptor_length_bound B
  have hsum : (g.width s ν) + B.size + 5 ≤ (c + 6) * ((g.width s ν) + 1) ^ (e + 1) := by
    have h1 : ((g.width s ν) + 1) ^ e ≤ ((g.width s ν) + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (g.width s ν) + 1 ≤ ((g.width s ν) + 1) ^ (e + 1) := Nat.le_self_pow (by omega) _
    have h3 : 1 ≤ ((g.width s ν) + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hpow : ((g.width s ν) + 1) ^ (e + 1) ≤ C1 ^ (e + 1) * (ν + 1) ^ (e + 1) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hqν _
  have hν2 : (ν + 1) ^ (e + 1) ≤ 2 ^ (e + 1) * ν ^ (e + 1) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have hdesc : (Outer.srcDescriptor B).length ≤ K0 * ν ^ (2 * e + 2) := by
    unfold Outer.srcDescriptor
    calc (RepairOrdinary.PCPPNative.descriptor B).length ≤ 39 * ((g.width s ν) + B.size + 5) ^ 2 := hd
      _ ≤ 39 * ((c + 6) * (C1 ^ (e + 1) * (2 ^ (e + 1) * ν ^ (e + 1)))) ^ 2 := by
          gcongr
          calc (g.width s ν) + B.size + 5 ≤ (c + 6) * ((g.width s ν) + 1) ^ (e + 1) := hsum
            _ ≤ (c + 6) * (C1 ^ (e + 1) * (ν + 1) ^ (e + 1)) := Nat.mul_le_mul_left _ hpow
            _ ≤ (c + 6) * (C1 ^ (e + 1) * (2 ^ (e + 1) * ν ^ (e + 1))) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hν2)
      _ = K0 * ν ^ (2 * e + 2) := by
          rw [hK0]
          ring
  -- the instance length
  unfold Outer.SrcFits Outer.instLength GateParams.lenExp
  rw [hroot]
  have hexp : 10 * (2 * e + 2) + 8 + 2 = (2 * e + 2) + (18 * e + 28) := by omega
  rw [hexp, pow_add]
  have hbig : K0 ≤ ν ^ (18 * e + 28) := by
    calc K0 ≤ ν := by omega
      _ = ν ^ 1 := (pow_one ν).symm
      _ ≤ ν ^ (18 * e + 28) := Nat.pow_le_pow_right hν1 (by omega)
  calc (Outer.srcDescriptor B).length ≤ K0 * ν ^ (2 * e + 2) := hdesc
    _ ≤ ν ^ (18 * e + 28) * ν ^ (2 * e + 2) := Nat.mul_le_mul_right _ hbig
    _ = ν ^ (2 * e + 2) * ν ^ (18 * e + 28) := by ring

end NearCubicGates.Close.Transfer
