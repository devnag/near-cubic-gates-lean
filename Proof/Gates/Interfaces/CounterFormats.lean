import Proof.Gates.Tabulator.Formula
import Proof.Gates.Tabulator.Request
import Proof.Gates.Interfaces.Counter
import Proof.Gates.Counter.Pure
import Proof.Gates.WordPrograms.RecLoop
import Proof.Gates.WordPrograms.SInt

set_option autoImplicit false

namespace NearCubicGates.Close.Interfaces.Formats

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces

/-- One postfix token of a formula. -/
inductive Tok where
  | const (a : ℤ)
  | var (v : ℕ)
  | add
  | neg
  | sub
  | mul
  | pow (e : ℕ)

/-- A token as a word: a `natWord` tag `0…6`, then its payload (`const`: `intWord a`; `var`: `natWord v`;
`pow`: `natWord e`). -/
def tokWord : Tok → List Bool
  | .const a => natWord 0 ++ Interfaces.intWord a
  | .var v => natWord 1 ++ natWord v
  | .add => natWord 2
  | .neg => natWord 3
  | .sub => natWord 4
  | .mul => natWord 5
  | .pow e => natWord 6 ++ natWord e

/-- The postfix (reverse Polish) token list of a formula: operands first, then the operator. -/
def toks {V : ℕ} : Formula V → List Tok
  | .const a => [.const a]
  | .var v => [.var v.val]
  | .add f g => toks f ++ toks g ++ [.add]
  | .neg f => toks f ++ [.neg]
  | .sub f g => toks f ++ toks g ++ [.sub]
  | .mul f g => toks f ++ toks g ++ [.mul]
  | .pow f e => toks f ++ [.pow e]

abbrev FormulaReq := Σ V : ℕ, Formula V

def formulaWord (r : FormulaReq) : List Bool := natWord r.1 ++ listWord tokWord (toks r.2)

/-- One monomial: its variables in increasing order (`listWord natWord`), then its coefficient. -/
def monoWord {V : ℕ} (t : Finset (Fin V) × ℤ) : List Bool :=
  listWord natWord ((t.1.sort (· ≤ ·)).map Fin.val) ++ Interfaces.intWord t.2

def termsWord {V : ℕ} (P : Terms V) : List Bool := listWord monoWord P

structure ExpandOK {V : ℕ} (F : Formula V) (P : Terms V) : Prop where
  eval : ∀ b : Fin V → Bool, Terms.eval b P = F.eval (boolPoint b)
  nodup : (Terms.keys P).Nodup
  degree : ∀ S ∈ Terms.keys P, S.card ≤ F.degree
  mass : Terms.absSum P ≤ F.mass

structure ExpandMachine where
  expand : (r : FormulaReq) → Terms r.1
  ok : ∀ r : FormulaReq, ExpandOK r.2 (expand r)
  budget : FormulaReq → ℕ
  wf : WordFunction FormulaReq formulaWord (fun r => termsWord (expand r)) budget
  cls : ∃ C e : ℕ, ∀ r : FormulaReq,
    budget r ≤ C * (r.1 + 2) ^ (2 * r.2.degree + 3) * ((formulaWord r).length + r.2.size + r.2.weight + 1) ^ e

theorem expandOK_expand {V : ℕ} (F : Formula V) : ExpandOK F F.expand :=
  ⟨fun b => Formula.expand_eval b F, Formula.expand_keys_nodup F, Formula.expand_card_le F,
    Formula.expand_absSum_le F⟩

/-- lem:print's data with `Q` given as a formula, plus the hypotheses of `Tabulator.formulaRequest_value`. -/
structure TabReq where
  n : ℕ
  k : ℕ
  s : ℕ
  G : ℕ
  V : ℕ
  gates : Fin G → NormalizedThresholdGate n
  layout : Fin n ≃ Fin k ⊕ Fin s
  H : Finset (Fin k → Bool)
  role : Fin V → Role G
  F : Formula V
  B : ℕ
  hB : ∀ i, GateBits B (gates i)
  hc : PrintCondition k s F.degree V (mT s (B + Nat.clog 2 (n + 1)))

def tabWord (r : TabReq) : List Bool :=
  natWord r.n ++ natWord r.k ++ natWord r.s ++ natWord r.B ++
    listWord gateWord (List.ofFn r.gates) ++
    listWord natWord (List.ofFn fun j : Fin r.k => (r.layout.symm (.inl j)).val) ++
    listWord natWord (List.ofFn fun t : Fin r.s => (r.layout.symm (.inr t)).val) ++
    listWord bitWord (List.ofFn fun c : Fin (2 ^ r.k) => decide (innerPoint r.k c ∈ r.H)) ++
    listWord (fun ρ : Role r.G => natWord ρ.gate.val ++ bitWord ρ.reference) (List.ofFn r.role) ++
    formulaWord ⟨r.V, r.F⟩

/-- The outer assignment with index `i`: outer coordinate `t` is bit `t` of `i`. -/
def outerOf (s i : ℕ) : Fin s → Bool := fun t => i.testBit t.val

/-- The tabulated integer `∑_{x ∈ H} F(y,x)` at the outer assignment `y` (`lem:print`). -/
def tabTarget (r : TabReq) (y : Fin r.s → Bool) : ℤ :=
  ∑ x ∈ r.H, r.F.eval (boolPoint ((formulaTabulation r.gates r.layout r.H r.role r.F).value y x))

def tableWord (ord : List ℕ) (w : ℕ) (r : TabReq) : List Bool :=
  WordPrograms.recStream (ord.map fun i => SignedSortKey.binary w (WordPrograms.SInt.encS (tabTarget r (outerOf r.s i))))

structure TabMachine where
  order : TabReq → List ℕ
  perm : ∀ r, (order r).Perm (List.range (2 ^ r.s))
  width : TabReq → ℕ
  fits : ∀ r (y : Fin r.s → Bool), WordPrograms.SInt.encS (tabTarget r y) < 2 ^ width r
  budget : TabReq → ℕ
  wf : WordFunction TabReq tabWord (fun r => tableWord (order r) (width r) r) budget
  cls : ∃ C e : ℕ, ∀ r : TabReq, budget r ≤ C * 2 ^ r.s *
    (r.n + r.G + r.B + r.V + (formulaWord ⟨r.V, r.F⟩).length + r.F.size + r.F.weight + 1) ^ e

open NearCubicGates.Close.Counter

def paramsWord (p : Params) : List Bool :=
  natWord p.n ++ bitWord p.pair ++ natWord p.W ++ ratWord p.beta ++ natWord p.k ++ natWord p.T ++ natWord p.m ++
    natWord p.Dmax ++ natWord p.P ++ natWord p.e ++ listWord natWord (p.primes.sort (· ≤ ·)) ++
    natWord p.window ++ natWord p.L2 ++ natWord p.Lw ++ natWord p.hE ++ natWord p.h ++ natWord p.R0 ++
    ratWord p.ell0 ++ natWord p.M1 ++ natWord p.J ++ listWord natWord p.factors ++ natWord p.A ++ natWord p.Lambda

/-- The selected record or the default: `natWord 0`, or `natWord 1 ++ paramsWord p`. -/
def optParamsWord : Option Params → List Bool
  | none => natWord 0
  | some p => natWord 1 ++ paramsWord p

def witWord (c : Call) (p : Params) (wt : Wit c.n) : List Bool :=
  listWord natWord (coordsOf wt.I) ++
    ((List.range p.J).flatMap fun s => (List.range (roleCount c.kind)).map fun r => (s, r)).flatMap
      fun sr => listWord Interfaces.intWord (wt.coef sr.1 sr.2)

/-- A tabulated request of one call: a joint residue count (table (a)) on a part, at a prime `q`, with digit residues
`κ` (role-major: entry `r·J + j` is digit `j` of role `r`) and score residues `σ` (one per role); or a moment
(table (b)). -/
inductive ReqId where
  | residue (part : Option Bool) (q : ℕ) (κ σ : List ℕ)
  | digitMoment (r j : ℕ)
  | phiMoment (r : ℕ)

def partCode : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- Number of key fields: three header fields, then the `roleCount·(J+1)` residues. -/
def keyLen (c : Call) (p : Params) : ℕ := 3 + roleCount c.kind * (p.J + 1)

/-- Bits per key field. -/
def keyBits (p : Params) : ℕ := Nat.size (p.P + p.J + 3)

def keyFields : ReqId → List ℕ
  | .residue part q κ σ => [0, partCode part, q] ++ κ ++ σ
  | .digitMoment r j => [1, r, j]
  | .phiMoment r => [2, r, 0]

/-- Big-endian radix `2^b` number of the fields padded with zeros to `len` fields (numeric order = field order). -/
def radixKey (b len : ℕ) (fs : List ℕ) : ℕ :=
  (fs ++ List.replicate (len - fs.length) 0).foldl (fun acc x => acc * 2 ^ b + x) 0

def reqKey (c : Call) (p : Params) (id : ReqId) : ℕ := radixKey (keyBits p) (keyLen c p) (keyFields id)

/-- All vectors of length `d` with entries `< q`. -/
def vecs (q : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | d + 1 => (List.range q).flatMap fun a => (vecs q d).map (a :: ·)

/-- The requests of one call: every part, prime and residue vector; then the `roleCount·(J+1)` moments
(`requestCount` in Counter/Main.lean counts exactly these). -/
def reqIds (c : Call) (p : Params) : List ReqId :=
  ((parts c).flatMap fun part => (p.primes.sort (· ≤ ·)).flatMap fun q =>
    (vecs q (roleCount c.kind * p.J)).flatMap fun κ => (vecs q (roleCount c.kind)).map fun σ =>
      ReqId.residue part q κ σ) ++
  ((List.range (roleCount c.kind)).flatMap fun r =>
    (List.range p.J).map (fun j => ReqId.digitMoment r j) ++ [ReqId.phiMoment r])

/-- The outer coordinates `[n] ∖ I`, increasing; cell index `i` sets the `t`-th of them to bit `t` of `i`. -/
def outerCoords {n : ℕ} (I : Finset (Fin n)) : List (Fin n) := (Finset.univ.filter (· ∉ I)).sort (· ≤ ·)

def cellOf {n : ℕ} (I : Finset (Fin n)) (i : ℕ) : Cells I := fun t => i.testBit ((outerCoords I).idxOf t.val)

def reqValue (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) : ReqId → ℕ
  | .residue part q κ σ => jointCount c p wt q part y
      (fun rj => (κ.getD (rj.1.val * p.J + rj.2.val) 0 : ℤ)) (fun r => (σ.getD r.val 0 : ℤ))
  | .digitMoment r j => (digitMoment c p wt r j y).toNat
  | .phiMoment r => (phiMoment c p wt r y).toNat

/-- A bound on every `|ΔE_j^r|` and `|ΔΦ^r|` (`|coef| ≤ |w|` by `decodeWitness`, so stage forms are at most `W`). -/
def deltaBound (c : Call) (p : Params) : ℕ := 2 * (p.M1 + p.A + p.factors.sum + 1) * (c.W + 1)

/-- Value width: counts are at most `2^k`, moments at most `2^k·deltaBound^{2k}`. -/
def valueWidth (c : Call) (p : Params) : ℕ := p.k + 2 * p.k * Nat.size (deltaBound c p) + 1

/-- Record widths: cell index, key, value. -/
def cellBits {n : ℕ} (I : Finset (Fin n)) : ℕ := (outerCoords I).length
def recWidth (c : Call) (p : Params) (wt : Wit c.n) : ℕ :=
  cellBits wt.I + keyBits p * keyLen c p + valueWidth c p

/-- The record of request `id` on cell index `i`: cell index, key, value (high to low bits). -/
def cellRec (c : Call) (p : Params) (wt : Wit c.n) (i : ℕ) (id : ReqId) : ℕ :=
  (i * 2 ^ (keyBits p * keyLen c p) + reqKey c p id) * 2 ^ valueWidth c p + reqValue c p wt (cellOf wt.I i) id

def cellWord (c : Call) (p : Params) (wt : Wit c.n) : List Bool :=
  WordPrograms.recStream ((((List.range (2 ^ cellBits wt.I)).flatMap fun i =>
    (reqIds c p).map (cellRec c p wt i)).insertionSort (· ≤ ·)).map (SignedSortKey.binary (recWidth c p wt)))

/-- One admitted, nonzero-weight counter call with its selected parameters and a decoded witness. -/
structure CellReq (B1 B2 cT : ℕ) where
  c : Call
  p : Params
  wt : Wit c.n
  adm : c.Admitted B1 B2
  hW : c.W ≠ 0
  hp : selectParams cT (header c) = some p
  hw : ∃ w, decodeWitness c p w = some wt

def cellInput {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : List Bool :=
  callWord r.c ++ paramsWord r.p ++ witWord r.c r.p r.wt

structure TablesMachine (B1 B2 cT : ℕ) where
  budget : CellReq B1 B2 cT → ℕ
  wf : WordFunction (CellReq B1 B2 cT) cellInput (fun r => cellWord r.c r.p r.wt) budget
  cls : ∃ C e : ℕ, ∀ r : CellReq B1 B2 cT,
    budget r ≤ C * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e)

/-- A residue system: one rational unknown per point of `pts` (each point a list of integer coordinates, one per
role); one row `(q, σ, b)` per prime and residue vector: the unknowns at the points `u ≡ σ (mod q)` sum to `b`. -/
structure SysReq where
  pts : List (List ℤ)
  rows : List (ℕ × List ℕ × ℕ)

/-- Point `u` lies in the residue class `σ` modulo `q`. -/
def inClass (q : ℕ) (σ : List ℕ) (u : List ℤ) : Bool :=
  (List.range σ.length).all fun i => decide (u.getD i 0 % (q : ℤ) = (σ.getD i 0 : ℤ) % (q : ℤ))

/-- `F` (one value per point, in `pts` order) solves every row. -/
def SysSolves (s : SysReq) (F : List ℚ) : Prop :=
  F.length = s.pts.length ∧ ∀ row ∈ s.rows,
    (((s.pts.zip F).filter fun uf => inClass row.1 row.2.1 uf.1).map Prod.snd).sum = (row.2.2 : ℚ)

def sysWord (s : SysReq) : List Bool :=
  listWord (listWord Interfaces.intWord) s.pts ++
    listWord (fun row : ℕ × List ℕ × ℕ => natWord row.1 ++ listWord natWord row.2.1 ++ natWord row.2.2) s.rows

def solveWord : Option (List ℚ) → List Bool
  | none => natWord 0
  | some F => natWord 1 ++ listWord ratWord F

structure SolveMachine where
  solve : SysReq → Option (List ℚ)
  sound : ∀ s F, solve s = some F → SysSolves s F
  complete : ∀ s, solve s = none → ∀ F, ¬ SysSolves s F
  budget : SysReq → ℕ
  wf : WordFunction SysReq sysWord (fun s => solveWord (solve s)) budget
  cls : ∃ C e : ℕ, ∀ s : SysReq, budget s ≤ C * ((sysWord s).length + 1) ^ e

open Classical in
/-- `Σ_{y certain} N_y` (eq:output 1733). -/
noncomputable def certainSum (c : Call) (p : Params) (wt : Wit c.n) : ℚ :=
  ∑ y ∈ (Finset.univ : Finset (Cells wt.I)).filter (fun y => Certain c p wt y), cellCount c p wt y

open Classical in
/-- `N_unc` (`sec:algorithm`, "Reconstruction inside a certified cell"). -/
noncomputable def uncCount (c : Call) (p : Params) (wt : Wit c.n) : ℕ :=
  ((Finset.univ : Finset (Cells wt.I)).filter fun y => ¬ Certain c p wt y).card

theorem outputOf_eq (c : Call) (p : Params) (wt : Wit c.n) :
    outputOf c p wt = ((certainSum c p wt + 2 ^ (p.k - 1) * uncCount c p wt) / 2 ^ c.n,
      2 ^ (p.k - 1) * (uncCount c p wt : ℚ) / 2 ^ c.n) := rfl

structure CellsMachine (B1 B2 cT : ℕ) where
  budget : CellReq B1 B2 cT → ℕ
  wf : WordFunction (CellReq B1 B2 cT) (fun r => cellInput r ++ cellWord r.c r.p r.wt)
    (fun r => ratWord (certainSum r.c r.p r.wt) ++ natWord (uncCount r.c r.p r.wt)) budget
  cls : ∃ C e : ℕ, ∀ r : CellReq B1 B2 cT,
    budget r ≤ C * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e)

/-- The dispatch outcome: `natWord 1 ++ cellInput` when the call proceeds to the cell pipeline, otherwise
`natWord 0 ++ outputWord (counterOnCall …)` (the final answer). -/
noncomputable def dispatchWord (B1 B2 cT : ℕ) (c : Call) (w : List Bool) : List Bool := by
  classical
  exact
    if c.Admitted B1 B2 ∧ c.W ≠ 0 then
      match selectParams cT (header c) with
      | none => natWord 0 ++ outputWord (counterOnCall B1 B2 cT c w)
      | some p => match decodeWitness c p w with
        | none => natWord 0 ++ outputWord (counterOnCall B1 B2 cT c w)
        | some wt => natWord 1 ++ (callWord c ++ paramsWord p ++ witWord c p wt)
    else natWord 0 ++ outputWord (counterOnCall B1 B2 cT c w)

structure DispatchMachine (B1 B2 cT : ℕ) where
  budget : Call → List Bool → ℕ
  wf : WordFunction (Call × List Bool) (fun r => RepairOrdinary.frame (callWord r.1) ++ RepairOrdinary.frame r.2)
    (fun r => dispatchWord B1 B2 cT r.1 r.2) (fun r => budget r.1 r.2)
  cls : ∃ C e : ℕ, ∀ (c : Call) (w : List Bool), budget c w ≤ C * ((callWord c).length + 1) ^ e

end NearCubicGates.Close.Interfaces.Formats
