import Proof.Gates.CellsSys.CallJ
import Proof.Gates.CellsSys.Cls

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

theorem callCost_le (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) :
    callCost S C c p Big ≤ 60001 * (c.n + Big + C.Lk + C.Bk + 2) ^ 13 := by
  set N := c.n + 1 with hN
  set M := c.n + Big + C.Lk + C.Bk + 2 with hM
  have hN1 : 1 ≤ N := by omega
  have hNM : N ≤ M := by omega
  have e1 : ∀ k, 1 ≤ N ^ k := fun k => Nat.one_le_pow _ _ hN1
  have hn : c.n ≤ N := by omega
  have hBw : BwP c = 8 * N := by unfold BwP; omega
  have hA : 30 * BwP c + 30 ≤ 270 * N := by rw [hBw]; omega
  have hcpt : cptCost (BwP c) (100 * (c.n + 1) ^ 5) + 4 ≤ 2114 * N ^ 5 := by
    unfold cptCost bitsCost; rw [hBw, ← hN]
    have : N ≤ N ^ 5 := by simpa using Nat.pow_le_pow_right hN1 (show 1 ≤ 5 by norm_num)
    have := e1 5; omega
  have hPB : 4 * c.n ^ 4 + 1 ≤ 5 * N ^ 4 := by
    have : c.n ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left hn 4
    have := e1 4; omega
  have hX : (4 * c.n ^ 4 + 1) * (cptCost (BwP c) (100 * (c.n + 1) ^ 5) + 4) + 4 + 4 ≤ 10578 * N ^ 9 := by
    have h1 := Nat.mul_le_mul hPB hcpt
    have h2 : 5 * N ^ 4 * (2114 * N ^ 5) = 10570 * N ^ 9 := by ring
    have := e1 9; omega
  have hP : (4 * c.n ^ 4 + 1) * (((4 * c.n ^ 4 + 1) * (cptCost (BwP c) (100 * (c.n + 1) ^ 5) + 4) + 4) + 4) + 4 ≤
      52894 * N ^ 13 := by
    have h1 := Nat.mul_le_mul hPB hX
    have h2 : 5 * N ^ 4 * (10578 * N ^ 9) = 52890 * N ^ 13 := by ring
    have := e1 13; omega
  have hN13 : N ^ 13 ≤ M ^ 13 := Nat.pow_le_pow_left hNM 13
  have hM13 : M ≤ M ^ 13 := by
    have : 1 ≤ M := by omega
    simpa using Nat.pow_le_pow_right this (show 1 ≤ 13 by norm_num)
  have hNle : N ≤ N ^ 13 := by simpa using Nat.pow_le_pow_right hN1 (show 1 ≤ 13 by norm_num)
  unfold callCost
  omega

theorem callCost_cls : FragClass callCost := ⟨60001, 13, callCost_le⟩

/-- **Fragment CALL.** -/
def callFrag : CallFrag := ⟨callP, callCost, callCost_cls, callP_spec⟩

/-- **The systems phase program.** -/
def sysP : St VV MM := sysPOf prFrag callFrag

/-- **The systems phase cost.** -/
def sysCost : SolveMachine → Ctx → Call → Params → ℕ → ℕ := sysCostOf prFrag callFrag

theorem sysP_spec : SysGoal sysP sysCost :=
  fun S C _cT c p wt y a Big hs hdec hadm ht h0 hbits hwd hcall =>
    sysPOf_run prFrag callFrag S C c p wt y a Big hs hdec hadm ht h0 hbits hwd hcall h0.cntB

theorem sysCost_cls : SysClass sysCost := sysCostOf_cls prFrag callFrag

end NearCubicGates.Close.Cells.SystemsPhase
