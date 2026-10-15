import Proof.Gates.Cells.SysSpec
import Proof.Gates.Cells.Run

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-- `N_unc`: the number of cells failing the strict tests (line 1731), set by `mainP`. -/
def vUnc : Fin VV := ⟨120, by decide⟩

/-- The width the loop may assume (covers `SysGoal`'s `64·(J+4)·(Big+n+16)`, the cell records of width
`recWidth`, the gathering records and every counter). -/
def wdNeed (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) : ℕ :=
  256 * (p.J + 4) * (Big + c.n + 16) + 4 * recWidth c p wt

/-- The cost class of the loop: `2^{n−k}` cells, `(n+1)^{2·Jmax n}` digit vectors and residue requests per cell,
a polynomial in `n`, `Big` and the run bounds otherwise (prop:time 1820–1835). -/
def loopCost (K e : ℕ) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) : ℕ :=
  K * 2 ^ (c.n - p.k) * (c.n + 1) ^ (2 * Jmax c.n) * (c.n + Big + C.Wd + C.Lk + C.Bk + 2) ^ e

def LoopGoal (mainP : St VV MM) (S : SolveMachine) (K e : ℕ) : Prop :=
  ∀ (C : Ctx) {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) (Big : ℕ),
    C.K = Callee.ofSolve S → C.inp = cellInput r ++ cellWord r.c r.p r.wt →
    (∀ x ∈ CounterMachine.cellN r.c r.p r.wt, natBitLength x ≤ Big) →
    wdNeed r.c r.p r.wt Big ≤ C.Wd →
    (∀ (y : Cells r.wt.I) part κ, κ ∈ digitVectors r.c r.p r.wt y →
      (sysWord (sysOf r.c r.p r.wt y κ part)).length ≤ C.Lk ∧ S.budget (sysOf r.c r.p r.wt y κ part) ≤ C.Bk) →
    ∃ b n, Ex C mainP (a0 : DS VV MM) b n ∧ n ≤ loopCost K e C r.c r.p Big ∧
      (b.env vCnt : ℚ) = certainSum r.c r.p r.wt ∧ b.env vUnc = uncCount r.c r.p r.wt ∧ b.out = [] ∧ Cst b

def CellsUniform (B1 B2 : ℕ) : Prop :=
  ∃ CellsProc : ∀ cT, CellsMachine B1 B2 cT, ∃ e, ∀ cT, ∃ C, ∀ r : CellReq B1 B2 cT,
    (CellsProc cT).budget r ≤ C * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e)

def PackGoal : Prop :=
  ∀ (S : SolveMachine) (mainP : St VV MM) (K e : ℕ), LoopGoal mainP S K e → ∀ B1 B2 : ℕ, CellsUniform B1 B2

end NearCubicGates.Close.Cells
