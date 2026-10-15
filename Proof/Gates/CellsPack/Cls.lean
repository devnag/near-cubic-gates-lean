import Proof.Gates.CellsPack.SizeC

set_option autoImplicit false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.CellsPack

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Counter
open NearCubicGates.Close.Cells.SystemsPhase

theorem pow_cL_le (n c D : ℕ) (hc : c ≤ D) : 2 ^ (c * natBitLength n) ≤ 2 ^ D * (n + 1) ^ D := by
  rw [mul_comm, pow_mul]
  calc (2 ^ natBitLength n) ^ c ≤ (2 * (n + 1)) ^ c := Nat.pow_le_pow_left (CounterMachine.PrefixProg.pow_nbl_le n) c
    _ ≤ (2 * (n + 1)) ^ D := Nat.pow_le_pow_right (by omega) hc
    _ = 2 ^ D * (n + 1) ^ D := by rw [mul_pow]

/-- The constants of the class. -/
noncomputable def dOf (S : SolveMachine) (B1 B2 : ℕ) : ℕ := (B1 + B2 + 10) + 9 + 9 * kE S
noncomputable def a3Of (S : SolveMachine) : ℕ := kC S * 2 ^ (13 * kE S)
noncomputable def wSof (S : SolveMachine) (B1 B2 : ℕ) : ℕ := (2 ^ 22 + 2 ^ 12 + a3Of S) * 2 ^ dOf S B1 B2
noncomputable def c0Of (S : SolveMachine) (B1 B2 : ℕ) : ℕ :=
  2 ^ 22 + 2 ^ 12 + a3Of S + dOf S B1 B2 + TSK (Callee.ofSolve S) + 2
noncomputable def AgOf (S : SolveMachine) (B1 B2 : ℕ) : ℕ := wSof S B1 B2 + c0Of S B1 B2

theorem sizes_le (S : SolveMachine) (B1 B2 n : ℕ) :
    (zOf S B1 B2).W (natBitLength n) + (zOf S B1 B2).Lk (natBitLength n) + (zOf S B1 B2).Bk (natBitLength n) ≤
      wSof S B1 B2 * (n + 1) ^ dOf S B1 B2 := by
  have h1 := pow_cL_le n (B1 + B2 + 10) (dOf S B1 B2) (by unfold dOf; omega)
  have h2 := pow_cL_le n 9 (dOf S B1 B2) (by unfold dOf; omega)
  have h3 := pow_cL_le n (9 * kE S) (dOf S B1 B2) (by unfold dOf; omega)
  show 2 ^ ((B1 + B2 + 10) * natBitLength n) * 2 ^ 22 + 2 ^ (9 * natBitLength n) * 2 ^ 12 +
    2 ^ (9 * kE S * natBitLength n) * (kC S * 2 ^ (13 * kE S)) ≤ _
  have e : wSof S B1 B2 * (n + 1) ^ dOf S B1 B2 =
      (2 ^ dOf S B1 B2 * (n + 1) ^ dOf S B1 B2) * 2 ^ 22 + (2 ^ dOf S B1 B2 * (n + 1) ^ dOf S B1 B2) * 2 ^ 12 +
      (2 ^ dOf S B1 B2 * (n + 1) ^ dOf S B1 B2) * (kC S * 2 ^ (13 * kE S)) := by
    unfold wSof a3Of; ring
  rw [e]
  have k1 := Nat.mul_le_mul_right (2 ^ 22) h1
  have k2 := Nat.mul_le_mul_right (2 ^ 12) h2
  have k3 := Nat.mul_le_mul_right (kC S * 2 ^ (13 * kE S)) h3
  generalize 2 ^ dOf S B1 B2 * (n + 1) ^ dOf S B1 B2 = P at *
  generalize 2 ^ ((B1 + B2 + 10) * natBitLength n) = p1 at *
  generalize 2 ^ (9 * natBitLength n) = p2 at *
  generalize 2 ^ (9 * kE S * natBitLength n) = p3 at *
  generalize kC S * 2 ^ (13 * kE S) = q3 at *
  generalize (2 : ℕ) ^ 22 = q1 at *
  generalize (2 : ℕ) ^ 12 = q2 at *
  omega

theorem gof_le (S : SolveMachine) (B1 B2 n : ℕ) :
    Gof (Callee.ofSolve S) (zOf S B1 B2) (natBitLength n) ≤ AgOf S B1 B2 * (n + 1) ^ dOf S B1 B2 := by
  have h := sizes_le S B1 B2 n
  have hL : natBitLength n ≤ n + 1 := nbl_le_self n
  have hY : n + 1 ≤ (n + 1) ^ dOf S B1 B2 := by
    simpa using Nat.pow_le_pow_right (show 1 ≤ n + 1 by omega) (show 1 ≤ dOf S B1 B2 by unfold dOf; omega)
  have hV : 1 ≤ (n + 1) ^ dOf S B1 B2 := Nat.one_le_pow _ _ (by omega)
  unfold Gof
  have e1 : (zOf S B1 B2).a1 + (zOf S B1 B2).a2 + (zOf S B1 B2).a3 + (zOf S B1 B2).c1 + (zOf S B1 B2).c2 +
      (zOf S B1 B2).c3 = 2 ^ 22 + 2 ^ 12 + a3Of S + dOf S B1 B2 := by
    show 2 ^ 22 + 2 ^ 12 + kC S * 2 ^ (13 * kE S) + (B1 + B2 + 10) + 9 + 9 * kE S = _
    unfold a3Of dOf; ring
  have e2 : AgOf S B1 B2 * (n + 1) ^ dOf S B1 B2 = wSof S B1 B2 * (n + 1) ^ dOf S B1 B2 +
      (2 ^ 22 + 2 ^ 12 + a3Of S + dOf S B1 B2 + TSK (Callee.ofSolve S) + 1) * (n + 1) ^ dOf S B1 B2 +
      (n + 1) ^ dOf S B1 B2 := by
    unfold AgOf c0Of; ring
  have e3 : 2 ^ 22 + 2 ^ 12 + a3Of S + dOf S B1 B2 + TSK (Callee.ofSolve S) + 1 ≤
      (2 ^ 22 + 2 ^ 12 + a3Of S + dOf S B1 B2 + TSK (Callee.ofSolve S) + 1) * (n + 1) ^ dOf S B1 B2 :=
    Nat.le_mul_of_pos_right _ hV
  omega

end NearCubicGates.Close.CellsPack
