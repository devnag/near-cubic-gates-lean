import Proof.Gates.Cells.Pre3

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

/-- **The state at the start of the constants phase.** -/
structure ConstPre (c : Call) (p : Params) (wt : Wit c.n) (a : DS VV MM) : Prop where
  cst : Cst a
  sN : a.ram sN = cellN c p wt
  sP0 : a.ram sP = []
  sR0 : a.ram sR = []
  rcur : ∀ m, a.rc m ≤ (a.ram m).length
  n : a.env gN = c.n
  kind : a.env gKd = kindTag c.kind
  J : a.env gJ = p.J
  rc : a.env gRC = roleCount c.kind
  hE : a.env vHE = p.hE
  M1 : a.env vM1 = p.M1
  A : a.env vA = p.A
  Lam : a.env vLam = p.Lambda
  NP : a.env vNP = (p.primes.sort (· ≤ ·)).length
  IPr : (cellN c p wt).drop (a.env vIPr) = p.primes.sort (· ≤ ·) ++
    (cellN c p wt).drop (a.env vIPr + (p.primes.sort (· ≤ ·)).length)
  FS : a.env gFS = iPsi (cellN c p wt) + 24 + nPr (cellN c p wt)
  WS : a.env gWS = iOm (cellN c p wt) + 1 + fld (cellN c p wt) (iOm (cellN c p wt))
  W : a.env wW = p.W
  K : a.env wK = p.k
  P : a.env wP = p.P
  NF : a.env wNF = p.factors.length
  Co : a.env wCo = (coordsOf wt.I).length

/-- The variables the constants phase may change: its outputs, `50 … 99`, `t0 … t9`, `c0 … c5`, `vJ`. -/
def cScratch (x : Fin VV) : Prop :=
  x = pTH ∨ x = pTL ∨ x = p2VW ∨ x = p2K ∨ x = p2KF ∨ x = vKB ∨ x = pR ∨ x = vBN ∨ x = gNC ∨ gScratch x

def ConstGoal (constP : St VV MM) (t : Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∀ (C : Ctx) {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (a : DS VV MM) (Big : ℕ),
    Spec cT (header c) p → (∃ w, decodeWitness c p w = some wt) → (∃ B1 B2 : ℕ, c.Admitted B1 B2) →
    ConstPre c p wt a → (∀ x ∈ CounterMachine.cellN c p wt, natBitLength x ≤ Big) → wdNeed c p wt Big ≤ C.Wd →
    ∃ b n, Ex C constP a b n ∧ n ≤ t C c p Big ∧
      b.env pTH = min (p.hE ^ (2 * p.k)) (2 ^ valueWidth c p) ∧
      b.env pTL = min (p.Lambda ^ (2 * p.k)) (2 ^ valueWidth c p) ∧
      b.env p2VW = 2 ^ valueWidth c p ∧ b.env p2K = 2 ^ keyW c p ∧ b.env p2KF = 2 ^ (keyW c p - keyBits p) ∧
      b.env vKB = 2 ^ keyBits p ∧ b.env pR = (reqIds c p).length ∧ b.env vBN = (wWin p) ^ (nDig c p) ∧
      b.env gNC = 2 ^ cellBits wt.I ∧ b.ram sP = tailL p ∧ b.ram sR = membL wt.I ∧
      (∀ m, m ≠ sP → m ≠ sR → b.ram m = a.ram m) ∧ (∀ m, b.rc m ≤ (b.ram m).length) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ x : Fin VV, ¬ cScratch x → b.env x = a.env x)

/-- **The class of the constants cost**: one constant, one exponent. -/
def ConstClass (t : Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (C : Ctx) (c : Call) (p : Params) (Big : ℕ), t C c p Big ≤ K * (c.n + Big + C.Wd + 2) ^ e

end NearCubicGates.Close.Cells
