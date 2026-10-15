import Proof.Gates.CounterMachine.CellTablesWalk
import Proof.Gates.CounterMachine.CellTablesSpec

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Cells.PrefixLoader (sN)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS sREC sTMP)

def kB2 : Fin VV := ⟨77, by decide⟩   -- `2^{keyBits p}`
def kD : Fin VV := ⟨78, by decide⟩    -- `D = roleCount·(J + 1)` (= `keyLen − 3`)
def kVW2 : Fin VV := ⟨79, by decide⟩  -- `2^{valueWidth c p}`
def kPAD : Fin VV := ⟨80, by decide⟩  -- `2^{keyBits·D}·2^{valueWidth}` (the moment key's padding)
def lPC : Fin VV := ⟨91, by decide⟩   -- `partCode part`
def lQ : Fin VV := ⟨92, by decide⟩    -- the prime `q`
def lQE : Fin VV := ⟨93, by decide⟩   -- `q^e`
def lQD : Fin VV := ⟨94, by decide⟩   -- `q^D`
def lT : Fin VV := ⟨95, by decide⟩    -- the residue counter `t < q^D`
def lR : Fin VV := ⟨96, by decide⟩    -- the role `r`
def lJ : Fin VV := ⟨97, by decide⟩    -- the stage `j`

def BodyVar (y : Fin VV) : Prop :=
  (3 ≤ y.val ∧ y.val ≤ 20) ∨ (30 ≤ y.val ∧ y.val ≤ 39) ∨ (44 ≤ y.val ∧ y.val ≤ 46) ∨
    (48 ≤ y.val ∧ y.val ≤ 63) ∨ 100 ≤ y.val

/-! ## The callee and the context -/

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

/-- RK (STATEMENT RK) as the callee of `kcall`. -/
noncomputable def tabCallCallee (RK : TabCallMachine B1 B2 cT PolyTab) : Callee :=
  ⟨TabCallReq B1 B2 cT, tabCallInput, tabCallOutput PolyTab, RK.budget, RK.wf⟩

noncomputable def ctxK (RK : TabCallMachine B1 B2 cT PolyTab) (Wd : ℕ) (inp : List Bool) (Lk Bk : ℕ) : Ctx :=
  ⟨Wd, inp, tabCallCallee RK, Lk, Bk⟩

/-! ## Requests and records -/

/-- The number of residue digits `D = roleCount·(J + 1)` (`κ` then `σ`). -/
def dOf (c : Call) (p : Params) : ℕ := roleCount c.kind * (p.J + 1)

/-- The residue request of counter value `t`: `κ ++ σ` = the `D` digits of `t` in radix `q`. -/
def resId (c : Call) (p : Params) (part : Option Bool) (q t : ℕ) : ReqId :=
  .residue part q ((Cells.digitsM (List.replicate (dOf c p) q) t).take (roleCount c.kind * p.J))
    ((Cells.digitsM (List.replicate (dOf c p) q) t).drop (roleCount c.kind * p.J))

/-- The records of one request, outer indices in printer order. -/
def recsOf (c : Call) (p : Params) (wt : Wit c.n) (id : ReqId) : List ℕ :=
  (printerOrder (c.n - p.k)).map fun i => cellRec c p wt i id

/-- The widest record field sum. -/
def lamW (c : Call) (p : Params) : ℕ := c.n + keyBits p * keyLen c p + valueWidth c p

structure Fit (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk wb : ℕ) : Prop where
  bk : ∀ x : TabCallReq B1 B2 cT, x.r = r → RK.budget x ≤ Bk
  lk : ∀ x : TabCallReq B1 B2 cT, x.r = r → (tabCallInput x).length ≤ Lk
  wid : ∀ x : TabCallReq B1 B2 cT, x.r = r → PolyTab.width (tabCallTab x) ≤ wb
  wd : wb + lamW r.c r.p + 4 ≤ Wd
  qe : ∀ q ∈ r.p.primes, 4 * q ^ r.p.e ≤ 2 ^ Wd
  qd : ∀ q ∈ r.p.primes, 2 * q ^ dOf r.c r.p ≤ 2 ^ Wd

/-- The state before a body: the loaded naturals, their count, the constants of the call, an empty `kin`. -/
structure Pre (C : Ctx) (r : CellReq B1 B2 cT) (a : DS VV MM) : Prop where
  valid : Valid C a
  cst : Cst a
  ramN : a.ram sN = cellN r.c r.p r.wt
  wN : a.env wN = (cellN r.c r.p r.wt).length
  s : a.env vS = r.c.n - r.p.k
  h1 : a.env vH1 = 2 ^ ((r.c.n - r.p.k + 1) / 2)
  h0 : a.env vH0 = 2 ^ ((r.c.n - r.p.k) / 2)
  sh : a.env vSH = 2 ^ (keyBits r.p * keyLen r.c r.p + valueWidth r.c r.p)
  b2 : a.env kB2 = 2 ^ keyBits r.p
  d : a.env kD = dOf r.c r.p
  vw2 : a.env kVW2 = 2 ^ valueWidth r.c r.p
  pad : a.env kPAD = 2 ^ (keyBits r.p * dOf r.c r.p) * 2 ^ valueWidth r.c r.p
  kin : a.kin = []
  rcR : a.rc sREC = (a.ram sREC).length

/-- What a body does: the request's records appended to `sREC`; `sN`'s cursor at its end; only `sREC`, `sTMP`,
the call words and the body variables change. -/
structure Post (C : Ctx) (r : CellReq B1 B2 cT) (a e : DS VV MM) (id : ReqId) : Prop where
  ramR : e.ram sREC = a.ram sREC ++ recsOf r.c r.p r.wt id
  rcR : e.rc sREC = (e.ram sREC).length
  ram : ∀ m, m ≠ sREC → m ≠ sTMP → e.ram m = a.ram m
  rcN : e.rc sN = (cellN r.c r.p r.wt).length
  rc : ∀ m, m ≠ sREC → m ≠ sTMP → m ≠ sN → e.rc m = a.rc m
  out : e.out = a.out
  ip : e.ip = a.ip
  kin : e.kin = []
  valid : Valid C e
  cst : Cst e
  fr : ∀ y, ¬ BodyVar y → e.env y = a.env y

/-- The cost of one body: the call (`1 + Lk + Bk`), `convP`, and the emission. -/
def bodyCost (Lk Bk wb : ℕ) (r : CellReq B1 B2 cT) : ℕ :=
  Lk + Bk + 100 * 2 ^ (r.c.n - r.p.k) * (wb + 10) + 1000 * ((cellInput r).length + 10) ^ 2

def ResBSpec (resB : St VV MM) : Prop :=
  ∀ {B1 B2 cT : ℕ} {PolyTab : TabMachine} (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT)
    (Wd Lk Bk wb : ℕ) (inp : List Bool) (a : DS VV MM) (part : Option Bool) (q t : ℕ),
    Fit RK r Wd Lk Bk wb → Pre (ctxK RK Wd inp Lk Bk) r a →
    part ∈ parts r.c → q ∈ r.p.primes → t < q ^ dOf r.c r.p →
    a.env lPC = partCode part → a.env lQ = q → a.env lQE = q ^ r.p.e → a.env lQD = q ^ dOf r.c r.p →
    a.env lT = t →
    Hs (ctxK RK Wd inp Lk Bk) resB a (bodyCost Lk Bk wb r)
      (fun e => Post (ctxK RK Wd inp Lk Bk) r a e (resId r.c r.p part q t))

def MomBSpec (momB : Bool → St VV MM) : Prop :=
  ∀ {B1 B2 cT : ℕ} {PolyTab : TabMachine} (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT)
    (Wd Lk Bk wb : ℕ) (inp : List Bool) (a : DS VV MM) (phi : Bool) (ro j : ℕ),
    Fit RK r Wd Lk Bk wb → Pre (ctxK RK Wd inp Lk Bk) r a →
    ro < roleCount r.c.kind → (phi = false → j < r.p.J) → a.env lR = ro → a.env lJ = j →
    Hs (ctxK RK Wd inp Lk Bk) (momB phi) a (bodyCost Lk Bk wb r)
      (fun e => Post (ctxK RK Wd inp Lk Bk) r a e (if phi then .phiMoment ro else .digitMoment ro j))

def ValSpec : Prop :=
  ∀ {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT),
    ((reqIds r.c r.p).flatMap (recsOf r.c r.p r.wt)).insertionSort (· ≤ ·) =
      ((List.range (2 ^ cellBits r.wt.I)).flatMap fun i => (reqIds r.c r.p).map (cellRec r.c r.p r.wt i)).insertionSort
        (· ≤ ·)

end NearCubicGates.Close.CounterMachine.CellTablesProg
