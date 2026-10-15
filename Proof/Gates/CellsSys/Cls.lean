import Proof.Gates.CellsSys.Asm2

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

theorem boxesCost_le (J : ℕ) : boxesCost J ≤ 1408 * (J + 1) ^ 2 := by
  unfold boxesCost boxCost accCost digCost
  nlinarith

theorem sysCostOf_cls (pr : PrFrag) (cf : CallFrag) : SysClass (sysCostOf pr cf) := by
  obtain ⟨K1, e1, h1⟩ := pr.cls
  obtain ⟨K2, e2, h2⟩ := cf.cls
  refine ⟨2 + 2 * (1414 + K1 + K2) + 33, e1 + e2 + 3, fun S C c p Big => ?_⟩
  set M := c.n + Big + C.Lk + C.Bk + 2 with hM
  set E := e1 + e2 + 3 with hE
  change sysCostOf pr cf S C c p Big ≤ (2 + 2 * (1414 + K1 + K2) + 33) * (BN c p + 1) * M ^ E
  obtain ⟨B, hB⟩ : ∃ B, B = BN c p := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by omega
  have hP1 : 1 ≤ M ^ E := Nat.one_le_pow _ _ (by omega)
  have hp1 : M ^ e1 ≤ M ^ E := Nat.pow_le_pow_right hM1 (by omega)
  have hp2 : M ^ e2 ≤ M ^ E := Nat.pow_le_pow_right hM1 (by omega)
  have hn3 : c.n ^ 3 ≤ M ^ E := (Nat.pow_le_pow_left (show c.n ≤ M by omega) 3).trans
    (Nat.pow_le_pow_right hM1 (by omega))
  have hb : boxesCost (c.n + 1) ≤ 1408 * M ^ E := by
    have := boxesCost_le (c.n + 1)
    have h2' : (c.n + 1 + 1) ^ 2 ≤ M ^ E := (Nat.pow_le_pow_left (show c.n + 1 + 1 ≤ M by omega) 2).trans
      (Nat.pow_le_pow_right hM1 (by omega))
    omega
  have hpr : pr.cost S C c p Big ≤ K1 * M ^ E := (h1 S C c p Big).trans (Nat.mul_le_mul_left _ hp1)
  have hcf : cf.cost S C c p Big ≤ K2 * M ^ E := (h2 S C c p Big).trans (Nat.mul_le_mul_left _ hp2)
  have hs : stepCostN pr cf S C c p Big + 4 ≤ (1414 + K1 + K2) * M ^ E := by
    unfold stepCostN; nlinarith
  have ht : tCostN pr cf S C c p Big ≤ B * ((1414 + K1 + K2) * M ^ E) + 4 := by
    unfold tCostN; rw [← hB]; nlinarith
  have hBn : B * c.n ^ 3 ≤ B * M ^ E := Nat.mul_le_mul_left _ hn3
  unfold sysCostOf
  rw [← hB]
  have key : 2 * (B * M ^ E) + 12 + (2 * (B * ((1414 + K1 + K2) * M ^ E) + 4 + 4) + 4) + 1 ≤
      (2 + 2 * (1414 + K1 + K2) + 33) * (B + 1) * M ^ E := by nlinarith
  omega

end NearCubicGates.Close.Cells.SystemsPhase
