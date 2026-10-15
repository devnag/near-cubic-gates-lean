import Proof.Gates.Expand.Main4

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

section Bounds
variable (Wb : ℕ)

theorem mulC : mulCost Wb ≤ 300 * (Wb + 1) ^ 2 := BinW.mulCost_le Wb
theorem divC : BinW.divCost Wb ≤ 400 * (Wb + 1) ^ 2 := BinW.divCost_le Wb

theorem initC : initCost Wb ≤ 40 * (Wb + 1) := by unfold initCost; omega
theorem vStepC : vStepCost Wb ≤ 300 * (Wb + 1) := by unfold vStepCost; omega
theorem famBodyC (V : ℕ) : famBodyCost Wb V ≤ 500 * (Wb + 1) * (V + 1) := by
  unfold famBodyCost
  have h := vStepC Wb
  have : V * (vStepCost Wb + 8) ≤ V * (300 * (Wb + 1) + 8) := Nat.mul_le_mul_left _ (by omega)
  nlinarith
theorem famLoopC (V n : ℕ) : famLoopCost Wb V n ≤ 600 * (Wb + 1) * (V + 1) * (n + 1) := by
  unfold famLoopCost
  have h := famBodyC Wb V
  have : n * (famBodyCost Wb V + (50 * Wb + 30)) ≤ n * (550 * (Wb + 1) * (V + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
  nlinarith
theorem famTailC (n : ℕ) : famTailCost Wb n ≤ 300 * (Wb + 1) * (n + 1) := by unfold famTailCost; nlinarith
theorem famInitC : famInitCost Wb ≤ 300 * (Wb + 1) := by unfold famInitCost; omega
theorem famPhaseC (V D N : ℕ) : famPhaseCost Wb V D N ≤ 2000 * (Wb + 1) * (V + 1) * (N + 1) * (D + 1) := by
  unfold famPhaseCost
  have h1 := famLoopC Wb V N
  have h2 := famTailC Wb N
  have h3 := famInitC Wb
  have : D * ((famLoopCost Wb V N + 1 + famTailCost Wb N) + 8) ≤ D * (1000 * (Wb + 1) * (V + 1) * (N + 1)) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have h4 : 5 * (N * (2 * Wb + 1)) ≤ 10 * (Wb + 1) * (N + 1) := by nlinarith
  nlinarith

theorem termAddC : termAddCost Wb ≤ 500 * (Wb + 1) := by unfold termAddCost; omega
theorem mobInnerC : mobInnerCost Wb ≤ 800 * (Wb + 1) := by unfold mobInnerCost; have := termAddC Wb; omega
theorem mobLoopInC (n : ℕ) : mobLoopInCost Wb n ≤ 900 * (Wb + 1) * (n + 1) := by
  unfold mobLoopInCost; have := mobInnerC Wb
  have : n * (mobInnerCost Wb + (50 * Wb + 30)) ≤ n * (880 * (Wb + 1)) := Nat.mul_le_mul_left _ (by omega)
  nlinarith
theorem mobSetC : mobSetCost Wb ≤ 1000 * (Wb + 1) ^ 2 := by unfold mobSetCost; have := mulC Wb; nlinarith
theorem mobTestC : mobTestCost Wb ≤ 500 * (Wb + 1) ^ 2 := by
  unfold mobTestCost mobEmitCost; have := mulC Wb; nlinarith
theorem mobOuterC (n : ℕ) : mobOuterCost Wb n ≤ 2500 * (Wb + 1) ^ 2 * (n + 1) := by
  unfold mobOuterCost; have := mobSetC Wb; have := mobTestC Wb; have := mobLoopInC Wb n; nlinarith
theorem mobPhaseC (n m : ℕ) : mobPhaseCost Wb n m ≤ 3000 * (Wb + 1) ^ 2 * (n + 1) * (m + 1) := by
  unfold mobPhaseCost
  have h := mobOuterC Wb n
  have hw : 1 ≤ (Wb + 1) ^ 2 * (n + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have A : m * (mobOuterCost Wb n + (50 * Wb + 30)) ≤ (m + 1) * (2600 * ((Wb + 1) ^ 2 * (n + 1))) :=
    Nat.mul_le_mul (by omega) (by nlinarith)
  have B : 5 * (m * (2 * Wb + 1)) ≤ (m + 1) * (10 * ((Wb + 1) ^ 2 * (n + 1))) := by
    have : 2 * Wb + 1 ≤ 2 * ((Wb + 1) ^ 2 * (n + 1)) := by nlinarith
    calc 5 * (m * (2 * Wb + 1)) ≤ 5 * ((m + 1) * (2 * ((Wb + 1) ^ 2 * (n + 1)))) := by gcongr; omega
      _ = (m + 1) * (10 * ((Wb + 1) ^ 2 * (n + 1))) := by ring
  have C : 1 ≤ (m + 1) * ((Wb + 1) ^ 2 * (n + 1)) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e : 3000 * (Wb + 1) ^ 2 * (n + 1) * (m + 1) = 3000 * ((m + 1) * ((Wb + 1) ^ 2 * (n + 1))) := by ring
  have e1 : (m + 1) * (2600 * ((Wb + 1) ^ 2 * (n + 1))) = 2600 * ((m + 1) * ((Wb + 1) ^ 2 * (n + 1))) := by ring
  have e2 : (m + 1) * (10 * ((Wb + 1) ^ 2 * (n + 1))) = 10 * ((m + 1) * ((Wb + 1) ^ 2 * (n + 1))) := by ring
  omega

theorem natWC : natWCost Wb ≤ 140 * (Wb + 1) ^ 2 := by unfold natWCost; nlinarith
theorem bitBodyC : bitBodyCost Wb ≤ 500 * (Wb + 1) ^ 2 := by
  unfold bitBodyCost setFlagCost; have := natWC Wb; nlinarith
theorem signC : signCost Wb ≤ 500 * (Wb + 1) ^ 2 := by unfold signCost; have := natWC Wb; nlinarith
theorem prRecC (V : ℕ) : prRecCost Wb V ≤ 2500 * (Wb + 1) ^ 2 * (V + 1) := by
  unfold prRecCost setFlagCost
  have h1 := divC Wb; have h2 := natWC Wb; have h3 := bitBodyC Wb; have h4 := signC Wb
  have hw : Wb + 1 ≤ (Wb + 1) ^ 2 := by nlinarith
  have A : V * (bitBodyCost Wb + 2) ≤ 502 * (V * (Wb + 1) ^ 2) := by
    have : bitBodyCost Wb + 2 ≤ 502 * (Wb + 1) ^ 2 := by nlinarith
    calc V * (bitBodyCost Wb + 2) ≤ V * (502 * (Wb + 1) ^ 2) := Nat.mul_le_mul_left _ this
      _ = 502 * (V * (Wb + 1) ^ 2) := by ring
  have e : 2500 * (Wb + 1) ^ 2 * (V + 1) = 2500 * (Wb + 1) ^ 2 + 2500 * (V * (Wb + 1) ^ 2) := by ring
  omega

theorem printC (V n Lo : ℕ) : printCost Wb V n Lo ≤ 3000 * (Wb + 1) ^ 2 * (V + 1) * (n + 1) + 5 * Lo := by
  unfold printCost
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h1 := prRecC Wb V; have h2 := natWC Wb
  have : n * (prRecCost Wb V + (50 * Wb + 30)) ≤ n * (2600 * (Wb + 1) ^ 2 * (V + 1)) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  nlinarith

theorem valBodyC (c : ℕ) : valBodyCost Wb c ≤ c + 500 * (Wb + 1) ^ 2 := by
  unfold valBodyCost; have := mulC Wb; nlinarith
theorem valPhaseC (N c : ℕ) : valPhaseCost Wb N c ≤ (N + 1) * (c + 100 * (Wb + 1)) := by
  unfold valPhaseCost; nlinarith

theorem nbl_le (x : ℕ) : natBitLength x ≤ 2 * x + 2 := by
  have := two_pow_nbl_le x
  have := @Nat.lt_two_pow_self (natBitLength x)
  omega

theorem evalC (c Vn N L : ℕ) : evalCost Wb c Vn N L ≤
    (N + 1) * (c + 2000) + 200 * (N + 3) ^ 2 + 40 * Vn + 500 * (Wb + 1) ^ 2 + 40 * L + 200 := by
  unfold evalCost tagCost
  have h1 := nbl_le Vn; have h2 := nbl_le N; have h3 := two_pow_nbl_le N
  have h4 : popCost Wb ≤ 500 * (Wb + 1) ^ 2 := popCost_le Wb
  have : (natBitLength N + 2) * (40 * 2 ^ natBitLength N + 40) ≤ (2 * N + 4) * (80 * N + 120) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem toRegC (a : ℕ) : toRegCost Wb a ≤ 200 * (Wb + 1) * (a + 1) := by
  unfold toRegCost flagCost
  have : a * ((1 + 1 + ((41 * Wb + 9) + 1 + (3 + 1 + ((41 * Wb + 3) + 1 + ((1 + 1 + 3) + 1))))) + 2) ≤
    a * (100 * (Wb + 1)) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

theorem shlC (n : ℕ) : shlCost Wb n ≤ 100 * (Wb + 1) * (n + 1) := by unfold shlCost; nlinarith

end Bounds

end NearCubicGates.Close.Expand.Layout
