import Proof.Gates.Cells.PackSpec

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

def vKB : Fin VV := ⟨28, by decide⟩

def vNL : Fin VV := ⟨118, by decide⟩

/-- A bound on the stale lengths of the workspace stores `sG`, `sB`. -/
noncomputable def gWork (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) : ℕ :=
  (reqIds c p).length + (rowVals c p wt y).length + (CounterMachine.cellN c p wt).length

/-- **The state at the start of the gathering phase** (cell index `i`, `y = cellOf wt.I i`). -/
structure GatherPre (c : Call) (p : Params) (wt : Wit c.n) (i : ℕ) (a : DS VV MM) : Prop where
  cst : Cst a
  cellN : a.ram sN = CounterMachine.cellN c p wt
  blk : a.ram sCT = blk c p wt i
  ctrs : a.ram sE = ctrL c p wt (cellOf wt.I i)
  gLen : (a.ram sG).length ≤ gWork c p wt (cellOf wt.I i)
  bLen : (a.ram sB).length ≤ gWork c p wt (cellOf wt.I i)
  aLen : (a.ram sA).length ≤ (rowVals c p wt (cellOf wt.I i)).length
  rcur : ∀ m, a.rc m ≤ (a.ram m).length
  n : a.env gN = c.n
  kind : a.env gKd = kindTag c.kind
  J : a.env gJ = p.J
  rc : a.env gRC = roleCount c.kind
  hE : a.env vHE = p.hE
  BN : a.env vBN = (wWin p) ^ (nDig c p)
  NP : a.env vNP = (p.primes.sort (· ≤ ·)).length
  IPr : (CounterMachine.cellN c p wt).drop (a.env vIPr) = p.primes.sort (· ≤ ·) ++
    (CounterMachine.cellN c p wt).drop (a.env vIPr + (p.primes.sort (· ≤ ·)).length)
  VW : a.env p2VW = 2 ^ valueWidth c p
  KW : a.env p2K = 2 ^ keyW c p
  KB : a.env vKB = 2 ^ keyBits p

  NL : a.env vNL = (CounterMachine.cellN c p wt).length

/-- The variables the gathering phase may change. -/
def gScratch (x : Fin VV) : Prop :=
  (50 ≤ x.val ∧ x.val ≤ 99) ∨ x = t0 ∨ x = t1 ∨ x = t2 ∨ x = t3 ∨ x = t4 ∨ x = t5 ∨ x = t6 ∨ x = t7 ∨ x = t8 ∨
    x = t9 ∨ x = c0 ∨ x = c1 ∨ x = c2 ∨ x = c3 ∨ x = c4 ∨ x = c5 ∨ x = vJ

def GatherGoal (gP : St VV MM) (t : Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∀ (C : Ctx) {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (i : ℕ) (a : DS VV MM) (Big : ℕ),
    Spec cT (header c) p → (∃ w, decodeWitness c p w = some wt) → (∃ B1 B2 : ℕ, c.Admitted B1 B2) →
    i < 2 ^ cellBits wt.I → CellTests c p wt (cellOf wt.I i) → GatherPre c p wt i a →
    (∀ x ∈ CounterMachine.cellN c p wt, natBitLength x ≤ Big) → wdNeed c p wt Big ≤ C.Wd →
    ∃ b n, Ex C gP a b n ∧ n ≤ t C c p Big ∧
      b.ram sA = rowVals c p wt (cellOf wt.I i) ∧
      (∀ m, m ≠ sG → m ≠ sB → m ≠ sA → b.ram m = a.ram m) ∧
      (b.ram sG).length ≤ gWork c p wt (cellOf wt.I i) ∧ (b.ram sB).length ≤ gWork c p wt (cellOf wt.I i) ∧
      (∀ m, b.rc m ≤ (b.ram m).length) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ x : Fin VV, ¬ gScratch x → b.env x = a.env x)

/-- **The class of the gathering cost**: one constant, one exponent (no `cT`). -/
def GatherClass (t : Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (C : Ctx) (c : Call) (p : Params) (Big : ℕ),
    t C c p Big ≤ K * ((reqIds c p).length + wWin p ^ nDig c p + 1) * (c.n + Big + C.Wd + 2) ^ e

end NearCubicGates.Close.Cells
