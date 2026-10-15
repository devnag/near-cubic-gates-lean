import Proof.Gates.CellsSys.Box

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-- The variables a fragment may change: `vJ`, `t0 … t9`, `c0 … c5` (indices `3 … 19`) and `87 … 98`. -/
def FragVar (x : Fin VV) : Prop := (3 ≤ x.val ∧ x.val ≤ 19) ∨ (87 ≤ x.val ∧ x.val ≤ 98)

/-- The global hypotheses of `SysGoal` for the cell `y`. -/
structure Glob (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (Big : ℕ) :
    Prop where
  spec : ∃ cT : ℕ, Spec cT (header c) p
  dec : ∃ w, decodeWitness c p w = some wt
  adm : ∃ B1 B2 : ℕ, c.Admitted B1 B2
  tests : CellTests c p wt y
  bits : ∀ x ∈ CounterMachine.cellN c p wt, natBitLength x ≤ Big
  wd : 64 * (p.J + 4) * (Big + c.n + 16) ≤ C.Wd
  call : ∀ part κ, κ ∈ digitVectors c p wt y → (sysWord (sysOf c p wt y κ part)).length ≤ C.Lk ∧
    S.budget (sysOf c p wt y κ part) ≤ C.Bk

/-- Unchanged since the phase entry `a0`. -/
structure Keep (a0 a : DS VV MM) : Prop where
  ram : a.ram = a0.ram
  ip : a.ip = a0.ip
  out : a.out = a0.out
  rc : RcOK a
  env : ∀ x : Fin VV, (x.val < 3 ∨ (20 ≤ x.val ∧ x.val < 50)) → x ≠ vCnt → a.env x = a0.env x

section Box
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ)

/-- Lower end of role `r` (`0` for a missing role). -/
def loR (r : ℕ) : ℤ := if h : r < roleCount c.kind then boxLo c p wt y κ ⟨r, h⟩ else 0

/-- Side length of role `r` (`1` for a missing role). -/
def lenR (r : ℕ) : ℕ :=
  if h : r < roleCount c.kind then (boxHi c p wt y κ ⟨r, h⟩ - boxLo c p wt y κ ⟨r, h⟩ + 1).toNat else 1

/-- The box of `κ` in the variables `l0P l0N n0 l1P l1N n1`. -/
structure BoxV (a : DS VV MM) : Prop where
  l0p : a.env l0P = (loR c p wt y κ 0).toNat
  l0n : a.env l0N = (-loR c p wt y κ 0).toNat
  n0e : a.env n0 = lenR c p wt y κ 0
  l1p : a.env l1P = (loR c p wt y κ 1).toNat
  l1n : a.env l1N = (-loR c p wt y κ 1).toNat
  n1e : a.env n1 = lenR c p wt y κ 1

end Box

/-- The cost class of a fragment (per system step). -/
def FragClass (t : SolveMachine → Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (Big : ℕ),
    t S C c p Big ≤ K * (c.n + Big + C.Lk + C.Bk + 2) ^ e

def PrGoal (prog : St VV MM) (t : SolveMachine → Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∀ (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (Big : ℕ)
    (a0 a : DS VV MM) (part : Option Bool) (κ : Role c × Fin p.J → ℤ) (rest : List ℕ),
    Glob S C c p wt y Big → SysPre S C c p wt y a0 → Keep a0 a → κ ∈ digitVectors c p wt y → part ∈ parts c →
    BoxV c p wt y κ a → a.kin = [] →
    (a.ram sA).drop (a.rc sA) = (rowsOf c p wt y κ part).map (fun row => row.2.2) ++ rest →
    Hs C prog a (t S C c p Big) (fun b => b.kin = sysWord (sysOf c p wt y κ part) ∧
      (b.ram sA).drop (b.rc sA) = rest ∧ b.ram = a.ram ∧ b.ip = a.ip ∧ b.out = a.out ∧ RcOK b ∧
      ∀ x : Fin VV, ¬ FragVar x → b.env x = a.env x)

def CallGoal (prog : St VV MM) (t : SolveMachine → Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∀ (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (Big : ℕ)
    (a0 a : DS VV MM) (part : Option Bool) (κ : Role c × Fin p.J → ℤ),
    Glob S C c p wt y Big → SysPre S C c p wt y a0 → Keep a0 a → κ ∈ digitVectors c p wt y → part ∈ parts c →
    BoxV c p wt y κ a → a.env pI = (if part = some true then 1 else 0) →
    a.kin = sysWord (sysOf c p wt y κ part) →
    a.env vCnt + (ptsOf c p wt y κ).length * 2 ^ c.n < 2 ^ C.Wd →
    Hs C prog a (t S C c p Big) (fun b => ((b.env vCnt : ℕ) : ℚ) = (a.env vCnt : ℚ) +
        ((ptsOf c p wt y κ).map fun u => trueDist c p wt y part κ u * predW c wt y part u).sum ∧
      b.kin = [] ∧ b.ram = a.ram ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.rc sA = a.rc sA ∧ RcOK b ∧
      ∀ x : Fin VV, ¬ FragVar x → x ≠ vCnt → b.env x = a.env x)

/-- Fragment PR as a value: program, cost, class, spec. -/
structure PrFrag where
  prog : St VV MM
  cost : SolveMachine → Ctx → Call → Params → ℕ → ℕ
  cls : FragClass cost
  spec : PrGoal prog cost

/-- Fragment CALL as a value: program, cost, class, spec. -/
structure CallFrag where
  prog : St VV MM
  cost : SolveMachine → Ctx → Call → Params → ℕ → ℕ
  cls : FragClass cost
  spec : CallGoal prog cost

end NearCubicGates.Close.Cells.SystemsPhase
