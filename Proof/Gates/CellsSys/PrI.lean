import Proof.Gates.CellsSys.PrH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

theorem pw_mul (N a b : ℕ) : N ^ a * N ^ b = N ^ (a + b) := (pow_add N a b).symm

theorem prCost_le (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) :
    prCost S C c p Big ≤ 100000 * (c.n + 1) ^ 9 := by
  set N := c.n + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hn : c.n ≤ N := by omega
  have e1 : ∀ k, 1 ≤ N ^ k := fun k => Nat.one_le_pow _ _ hN1
  have mono : ∀ a b, a ≤ b → N ^ a ≤ N ^ b := fun a b h => Nat.pow_le_pow_right hN1 h
  have hBw : BwP c = 8 * N := by unfold BwP; omega
  have hA : 40 * BwP c + 40 ≤ 360 * N := by rw [hBw]; omega
  have hpt : ptCost (BwP c) + 4 ≤ 2208 * N := by unfold ptCost; rw [hBw]; omega
  have hPB : 4 * c.n ^ 4 + 1 ≤ 5 * N ^ 4 := by
    have : c.n ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left hn 4
    have := e1 4; omega
  have hX : (4 * c.n ^ 4 + 1) * (ptCost (BwP c) + 4) + 4 + 4 ≤ 11048 * N ^ 5 := by
    have h1 := Nat.mul_le_mul hPB hpt
    have h2 : 5 * N ^ 4 * (2208 * N) = 11040 * N ^ 5 := by ring
    have := e1 5; omega
  have hP : (4 * c.n ^ 4 + 1) * (((4 * c.n ^ 4 + 1) * (ptCost (BwP c) + 4) + 4) + 4) + 4 ≤ 55248 * N ^ 9 := by
    have h1 := Nat.mul_le_mul hPB hX
    have h2 : 5 * N ^ 4 * (11048 * N ^ 5) = 55240 * N ^ 9 := by ring
    have := e1 9; omega
  have hfq : fqCost (100 * (c.n + 1) ^ 5) + 4 + 4 ≤ 628 * N ^ 5 := by
    unfold fqCost; rw [← hN]; have := e1 5; omega
  have hCn : c.n * (fqCost (100 * (c.n + 1) ^ 5) + 4 + 4) ≤ 628 * N ^ 6 := by
    have h1 := Nat.mul_le_mul hn hfq
    have h2 : N * (628 * N ^ 5) = 628 * N ^ 6 := by ring
    omega
  have hrow : rowCost (BwP c) + 4 ≤ 1824 * N := by unfold rowCost; rw [hBw]; omega
  have hs1 : s1Cost c.n (BwP c) + 4 ≤ 1832 * N ^ 2 := by
    unfold s1Cost
    have h1 := Nat.mul_le_mul hn hrow
    have h2 : N * (1824 * N) = 1824 * N ^ 2 := by ring
    have := e1 2; omega
  have hs0 : s0Cost c.n (BwP c) ≤ 1836 * N ^ 3 := by
    unfold s0Cost
    have h1 := Nat.mul_le_mul hn hs1
    have h2 : N * (1832 * N ^ 2) = 1832 * N ^ 3 := by ring
    have := e1 3; omega
  have hRw : c.n * (fqCost (100 * (c.n + 1) ^ 5) + s0Cost c.n (BwP c) + 1 + 4) ≤ 2470 * N ^ 6 := by
    have h3 : N ^ 3 ≤ N ^ 5 := mono 3 5 (by norm_num)
    have h5 := e1 5
    have h1 := Nat.mul_le_mul hn (show fqCost (100 * (c.n + 1) ^ 5) + s0Cost c.n (BwP c) + 1 + 4 ≤ 2470 * N ^ 5 by
      omega)
    have h2 : N * (2470 * N ^ 5) = 2470 * N ^ 6 := by ring
    omega
  have h69 : N ^ 6 ≤ N ^ 9 := mono 6 9 (by norm_num)
  have h19 : N ≤ N ^ 9 := by have := mono 1 9 (by norm_num); simpa using this
  have := e1 9
  unfold prCost
  omega

theorem prCost_cls : FragClass prCost := by
  refine ⟨100000, 9, fun S C c p Big => (prCost_le S C c p Big).trans ?_⟩
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 9)

/-- **Fragment PR.** -/
def prFrag : PrFrag := ⟨prP, prCost, prCost_cls, prP_spec⟩

end NearCubicGates.Close.Cells.SystemsPhase
