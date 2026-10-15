import Proof.Gates.Cells.Digits
import Proof.Gates.Cells.Zb
import Proof.Gates.Cells.Idx

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

def vCnt : Fin VV := ⟨42, by decide⟩   -- the cell count accumulator (phase adds `N_y`)
def vOP : Fin VV := ⟨43, by decide⟩    -- outerParity c wt y as 0/1
def vRC : Fin VV := gRC                -- roleCount (from the loader)
def vJ' : Fin VV := gJ                 -- J (from the loader)
def vHE : Fin VV := ⟨44, by decide⟩    -- h_E
def vM1 : Fin VV := ⟨45, by decide⟩    -- M₁
def vA : Fin VV := ⟨46, by decide⟩     -- A
def vLam : Fin VV := ⟨47, by decide⟩   -- Λ
def vBN : Fin VV := ⟨48, by decide⟩    -- (2h_E − 1)^{roleCount·J}: the number of digit vectors
def vNP : Fin VV := ⟨49, by decide⟩    -- number of primes
def vIPr : Fin VV := ⟨36, by decide⟩   -- index in `sN` of the first prime (primes increasing)
def vTS0 : Fin VV := ⟨37, by decide⟩   -- index in `sN` of the first table entry of `circ c 0`
def vTS1 : Fin VV := ⟨38, by decide⟩   -- index in `sN` of the first table entry of `circ c 1`
def vTW0 : Fin VV := ⟨39, by decide⟩   -- topWeight (circ c 0)
def vTW1 : Fin VV := ⟨29, by decide⟩   -- topWeight (circ c 1)
def vKd : Fin VV := gKd                -- kindTag c.kind (from the loader)

/-! ## Store contents -/

section Layout
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

noncomputable def rowVals : List ℕ :=
  (parts c).flatMap fun part => (vecsM (List.replicate (nDig c p) (wWin p))).flatMap fun v =>
    (p.primes.sort (· ≤ ·)).flatMap fun q => (vecs q (roleCount c.kind)).map fun σl =>
      jointCount c p wt q part y (kappaOf c p wt y v) (fun r => (σl.getD r.val 0 : ℤ))

/-- An integer as a pair `(pos, neg)` of naturals. -/
def pairOf (z : ℤ) : List ℕ := [z.toNat, (-z).toNat]

noncomputable def ctrL : List ℕ :=
  (List.finRange (roleCount c.kind)).flatMap fun r => (List.finRange p.J).flatMap fun j => pairOf (ctr c p wt y (r, j))

/-- `sX`: per role, `K_{J−1}^r(z_y)` then `X^r(z_y)`, two records each. -/
noncomputable def kxL : List ℕ :=
  (List.finRange (roleCount c.kind)).flatMap fun r =>
    pairOf (stageForm c wt r.val (p.J - 1) (extend wt.I y (zeroPoint wt.I))) ++
      pairOf (scoreForm c r.val (extend wt.I y (zeroPoint wt.I)))

/-- `sP`: `A_j = Π_{t<J−1, t≥j} a_t` for `j < J`. -/
noncomputable def tailL : List ℕ := (List.range p.J).map fun j => (tailProd p j).toNat

end Layout

/-- **The state at the start of the systems phase.** -/
structure SysPre (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)
    (a : DS VV MM) : Prop where
  callee : C.K = Callee.ofSolve S
  cst : Cst a
  cellN : a.ram sN = CounterMachine.cellN c p wt
  rows : a.ram sA = rowVals c p wt y
  ctrs : a.ram sE = ctrL c p wt y
  kx : a.ram sX = kxL c p wt y
  tails : a.ram sP = tailL p
  kin : a.kin = []
  kc : a.kc ≤ a.kout.length
  op : a.env vOP = if outerParity c wt y then 1 else 0
  rc : a.env vRC = roleCount c.kind
  J : a.env vJ' = p.J
  hE : a.env vHE = p.hE
  M1 : a.env vM1 = p.M1
  A : a.env vA = p.A
  Lam : a.env vLam = p.Lambda
  BN : a.env vBN = (wWin p) ^ (nDig c p)
  NP : a.env vNP = (p.primes.sort (· ≤ ·)).length
  IPr : (CounterMachine.cellN c p wt).drop (a.env vIPr) = p.primes.sort (· ≤ ·) ++
    (CounterMachine.cellN c p wt).drop (a.env vIPr + (p.primes.sort (· ≤ ·)).length)
  TS0 : (CounterMachine.cellN c p wt).drop (a.env vTS0) = (circ c 0).table.map CounterMachine.bitN ++
    (CounterMachine.cellN c p wt).drop (a.env vTS0 + (circ c 0).table.length)
  TS1 : (CounterMachine.cellN c p wt).drop (a.env vTS1) = (circ c 1).table.map CounterMachine.bitN ++
    (CounterMachine.cellN c p wt).drop (a.env vTS1 + (circ c 1).table.length)
  TW0 : a.env vTW0 = (circ c 0).topWeight
  TW1 : a.env vTW1 = (circ c 1).topWeight
  kind : a.env vKd = kindTag c.kind

  rcur : ∀ m, a.rc m ≤ (a.ram m).length

  cntB : a.env vCnt ≤ 2 ^ c.n

def SysGoal (sysP : St VV MM) (t : SolveMachine → Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∀ (S : SolveMachine) (C : Ctx) {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (a : DS VV MM)
    (Big : ℕ),
    Spec cT (header c) p → (∃ w, decodeWitness c p w = some wt) → (∃ B1 B2 : ℕ, c.Admitted B1 B2) →
    CellTests c p wt y → SysPre S C c p wt y a →
    (∀ x ∈ CounterMachine.cellN c p wt, natBitLength x ≤ Big) →
    64 * (p.J + 4) * (Big + c.n + 16) ≤ C.Wd →
    (∀ part κ, κ ∈ digitVectors c p wt y → (sysWord (sysOf c p wt y κ part)).length ≤ C.Lk ∧
      S.budget (sysOf c p wt y κ part) ≤ C.Bk) →
    ∃ b n, Ex C sysP a b n ∧ n ≤ t S C c p Big ∧
      ((b.env vCnt : ℚ) = a.env vCnt + cellCount c p wt y) ∧
      b.ram = a.ram ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = [] ∧
      (∀ x : Fin VV, (x.val < 50 ∨ 99 < x.val) → x ≠ t0 → x ≠ t1 → x ≠ t2 → x ≠ t3 → x ≠ t4 → x ≠ t5 → x ≠ t6 →
        x ≠ t7 → x ≠ t8 → x ≠ t9 → x ≠ c0 → x ≠ c1 → x ≠ c2 → x ≠ c3 → x ≠ c4 → x ≠ c5 → x ≠ vCnt → x ≠ vJ →
        b.env x = a.env x)

def SysClass (t : SolveMachine → Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (Big : ℕ),
    t S C c p Big ≤ K * (wWin p ^ nDig c p + 1) * (c.n + Big + C.Lk + C.Bk + 2) ^ e

end NearCubicGates.Close.Cells
