import SourceAdapters.ACSP.Model
import Mathlib.Algebra.CharP.Defs
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The RAM event-trace constraint system (route B, machine side)

Paper: `def:event-trace` and `app:affine-embedding`, Placement.
The equations (G), (T1)–(T10), (S1)–(S5), (B1)–(B5) and (P) are
expression trees over the active slots, with coefficients in {0,1}.
They evaluate over any commutative ring of characteristic two. The same trees
are emitted into the affine constraint circuit, and `Expr.deg` measures their
assignment degree for `lem:acsp-degree`.

**Slots.** A vertex is split as `app:affine-embedding`'s catalog splits it:
- the routed record `REC` (area `0`): `RecField × ℕ` (field, bit index), stored in `Trace.src` (stage `0`, lane `x`:
  `rec(ρ_x)` for `x < T`, `ι_{x−T}` for `T ≤ x < T + N_A`, dummies above) and `Trace.dst` (final stage, lane `j`:
  `σ_j.REC`);
- the non-routed machine slots (area `1`): `TSlot` of a time row (`Trace.time i`), `SSlot` of a sorted vertex
  (`Trace.sort j`). Constructor names follow the catalog's field names; `CA j`, `BO j`, `TC j`, `AC j`, `BC j` hold
  the carries `ca_{j+1}`, `bo_{j+1}`, `tc_{j+1}`, `ac_{j+1}`, `bc_{j+1}` as the catalog stores them, `ob l` holds
  `ob_{l+1}`.
Only the slots with `Active` hold for are slots of `def:event-trace`; the others are never read by an active equation
(`TEq.reads_active`, `SEq.reads_active` below) and carry no constraint.

Notation (`app:event-trace`): `w = M.w`, `K = M.k`, `L = |code|`, `τ` the time exponent, `T = 2^τ`, `N = 2T`,
`β = τ − log₂ w`, `κ = w + τ + 2`, `N_A = |x̄| / w`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP

/-! ## The arithmetic unit `𝖠 = (add, sub, and, cmp)` (`app:event-trace` Setting) -/

/-- The four supported operations of the arithmetic unit. -/
inductive AluOp where
  | add
  | sub
  | and
  | cmp
  deriving DecidableEq

/-- `cmp(X, Y)`: `1` if `X < Y`, `0` if `X = Y`, all ones otherwise (`lem:trace-gadgets`). -/
def cmpWord {w : ℕ} (x y : BitVec w) : BitVec w :=
  if x.toNat < y.toNat then 1 else if x = y then 0 else -1

/-- The function of an operation on `w`-bit words. -/
def AluOp.fn {w : ℕ} : AluOp → BitVec w → BitVec w → BitVec w
  | .add => fun x y => x + y
  | .sub => fun x y => x - y
  | .and => fun x y => x &&& y
  | .cmp => cmpWord

/-- The arithmetic unit of P02's `M_n` (`ShortPCP.mnAlu`: `0 = add`, `1 = sub`, `2 = and`, `3 = cmp`). -/
def mnKind : Fin 4 → AluOp := ![.add, .sub, .and, .cmp]

/-! ## Expressions: polynomials with coefficients in `{0, 1}` -/

/-- A polynomial with coefficients in `{0, 1}` in variables `ι`, as an expression tree. -/
inductive Expr (ι : Type) where
  | zero
  | one
  | var (i : ι)
  | add (a b : Expr ι)
  | mul (a b : Expr ι)

namespace Expr

variable {ι : Type}

/-- The value in a commutative ring. -/
def eval {F : Type} [CommRing F] (v : ι → F) : Expr ι → F
  | zero => 0
  | one => 1
  | var i => v i
  | add a b => eval v a + eval v b
  | mul a b => eval v a * eval v b

/-- The value at a bit assignment (`add` is exclusive or). -/
def evalB (v : ι → Bool) : Expr ι → Bool
  | zero => false
  | one => true
  | var i => v i
  | add a b => Bool.xor (evalB v a) (evalB v b)
  | mul a b => evalB v a && evalB v b

/-- The formal degree in the variables (an upper bound for the degree of the expanded polynomial). -/
def deg : Expr ι → ℕ
  | zero => 0
  | one => 0
  | var _ => 1
  | add a b => max (deg a) (deg b)
  | mul a b => deg a + deg b

/-- The variables read, with repetitions. -/
def vars : Expr ι → List ι
  | zero => []
  | one => []
  | var i => [i]
  | add a b => vars a ++ vars b
  | mul a b => vars a ++ vars b

/-- A sum. -/
def sum : List (Expr ι) → Expr ι
  | [] => zero
  | a :: l => add a (sum l)

/-- A constant bit. -/
def bit (b : Bool) : Expr ι := if b then one else zero

/-- `1 + a`. -/
def compl (a : Expr ι) : Expr ι := add one a

/-- The full-adder carry (majority) `ab + ac + bc`. -/
def maj (a b c : Expr ι) : Expr ι := add (add (mul a b) (mul a c)) (mul b c)

/-- A sum over the code: `Σ_{p} f p I_p`, positions counted from `p₀`. -/
def sumCode {α : Type} (f : ℕ → α → Expr ι) : ℕ → List α → Expr ι
  | _, [] => zero
  | p, I :: l => add (f p I) (sumCode f (p + 1) l)

end Expr

open Expr

/-! ## Slots (`def:event-trace`) -/

/-- The record fields with their catalog field tags `va 0, ad 1, ts 2, ph 3, rgn 4, act 5, st 6`. -/
inductive RecField where
  | va
  | ad
  | ts
  | ph
  | rgn
  | act
  | st
  deriving DecidableEq

/-- The catalog field tag. -/
def RecField.tag : RecField → ℕ
  | .va => 0
  | .ad => 1
  | .ts => 2
  | .ph => 3
  | .rgn => 4
  | .act => 5
  | .st => 6

/-- The number of semantic bits of a field (`c_R = 2w + τ + 4` in all). -/
def RecField.width (w τ : ℕ) : RecField → ℕ
  | .va => w
  | .ad => w
  | .ts => τ
  | _ => 1

/-- A record slot: field and bit index. -/
abbrev RecSlot := RecField × ℕ

/-- The non-routed slots of a time row `ρ_i` (the slot catalog of `def:event-trace`, catalog area `1`, stage `0`): role `0` (current and
local values) and role `1` (`npc`, `nfl`, `nrg`, `ncA`, `ncB`: the `nxt` configuration and next counters; `TSN`). -/
inductive TSlot where
  | pc (j : ℕ)
  | fl (r : ℕ)
  | rg (r j : ℕ)
  | e (p : ℕ)
  | o (p : ℕ)
  | X (j : ℕ)
  | XF
  | Y (j : ℕ)
  | AD (j : ℕ)
  | CA (j : ℕ)
  | SB (j : ℕ)
  | BO (j : ℕ)
  | AN (j : ℕ)
  | OZ (j : ℕ)
  | GT
  | Z (j : ℕ)
  | ZF
  | RV (j : ℕ)
  | RF
  | MV (j : ℕ)
  | TC (j : ℕ)
  | cA (j : ℕ)
  | cB (j : ℕ)
  | AC (j : ℕ)
  | BC (j : ℕ)
  | aA
  | aB
  | npc (j : ℕ)
  | nfl (r : ℕ)
  | nrg (r j : ℕ)
  | ncA (j : ℕ)
  | ncB (j : ℕ)
  | TSN (j : ℕ)
  deriving DecidableEq

/-- The non-routed slots of a sorted vertex `σ_j` (catalog area `1`, final stage): the predecessor copy `PREV`
(role `1`, fields `va, ad, ts, ph, rgn, act`) and the auxiliaries (role `0`). -/
inductive SSlot where
  | prev (f : RecField) (j : ℕ)
  | ob (l : ℕ)
  | both
  | so (l : ℕ)
  | u
  | g
  | ev (j : ℕ)
  | gA1
  | gA
  deriving DecidableEq

/-- The size parameters of the event trace of `M` at time exponent `τ`. -/
structure Dims where
  w : ℕ
  K : ℕ
  L : ℕ
  τ : ℕ
  β : ℕ

/-- `w = M.w`, `K = M.k`, `L = |C|`, `τ`, `β = τ − log₂ w` (`app:event-trace`). -/
def dims (M : Ram) (τ : ℕ) : Dims := ⟨M.w, M.k, M.code.length, τ, τ - Nat.log 2 M.w⟩

/-- `κ = w + τ + 2`, the number of key bits. -/
def Dims.κ (d : Dims) : ℕ := d.w + d.τ + 2

/-- The slots of `def:event-trace` among `RecSlot`. -/
def RecSlot.Active (d : Dims) (s : RecSlot) : Prop := s.2 < s.1.width d.w d.τ

/-- The slots of `def:event-trace` among `TSlot` (the exact widths of the time-row table). -/
def TSlot.Active (d : Dims) : TSlot → Prop
  | .pc j => j < d.w
  | .fl r => r < d.K
  | .rg r j => r < d.K ∧ j < d.w
  | .e p => p < d.L
  | .o p => p < d.L
  | .X j => j < d.w
  | .XF => True
  | .Y j => j < d.w
  | .AD j => j < d.w
  | .CA j => j + 1 < d.w
  | .SB j => j < d.w
  | .BO j => j < d.w
  | .AN j => j < d.w
  | .OZ j => j < d.w
  | .GT => True
  | .Z j => j < d.w
  | .ZF => True
  | .RV j => j < d.w
  | .RF => True
  | .MV j => j < d.w
  | .TC j => j + 1 < d.τ
  | .cA j => j < d.τ
  | .cB j => j ≤ d.β
  | .AC j => j + 1 < d.τ
  | .BC j => j < d.β
  | .aA => True
  | .aB => True
  | .npc j => j < d.w
  | .nfl r => r < d.K
  | .nrg r j => r < d.K ∧ j < d.w
  | .ncA j => j < d.τ
  | .ncB j => j ≤ d.β
  | .TSN j => j < d.τ

/-- The slots of `def:event-trace` among `SSlot` (the exact widths of the sorted-vertex table). -/
def SSlot.Active (d : Dims) : SSlot → Prop
  | .prev f j => f ≠ .st ∧ j < f.width d.w d.τ
  | .ob l => l < d.κ
  | .both => True
  | .so l => l ≤ d.w
  | .u => True
  | .g => True
  | .ev j => j < d.w
  | .gA1 => True
  | .gA => True

/-- The variables of a time-row equation: its own slots and its routed record. -/
abbrev TVar := TSlot ⊕ RecSlot

/-- The variables of a sorted-vertex equation: its own slots and its routed record. -/
abbrev SVar := SSlot ⊕ RecSlot

/-- Variables of time-row equations that are slots of `def:event-trace`. -/
def TVar.Active (d : Dims) : TVar → Prop
  | .inl s => s.Active d
  | .inr s => s.Active d

/-- Variables of sorted-vertex equations that are slots of `def:event-trace`. -/
def SVar.Active (d : Dims) : SVar → Prop
  | .inl s => s.Active d
  | .inr s => s.Active d

/-! ## Code tables (`app:event-trace` Code tables) -/

section Code

variable {w k ops : ℕ}

/-- `Ld`. -/
def isLd : Instr w k ops → Bool
  | .load _ _ => true
  | _ => false

/-- `St`. -/
def isSt : Instr w k ops → Bool
  | .store _ _ => true
  | _ => false

/-- `RdA`. -/
def isRdA : Instr w k ops → Bool
  | .readA _ => true
  | _ => false

/-- `RdB`. -/
def isRdB : Instr w k ops → Bool
  | .readB _ => true
  | _ => false

/-- `Rd = RdA ∪ RdB`. -/
def isRd (I : Instr w k ops) : Bool := isRdA I || isRdB I

/-- `Eof`. -/
def isEof : Instr w k ops → Bool
  | .iseof _ _ => true
  | _ => false

/-- `Out`. -/
def isOut : Instr w k ops → Bool
  | .out _ => true
  | _ => false

/-- `Acc`. -/
def isAcc : Instr w k ops → Bool
  | .out b => b
  | _ => false

/-- `Ar_o`, for an arithmetic unit read through `kind`. -/
def isAr (kind : Fin ops → AluOp) (o : AluOp) : Instr w k ops → Bool
  | .arith op _ _ _ => decide (kind op = o)
  | _ => false

/-- `Wr_r`: the instruction writes register `r`. -/
def writes (r : ℕ) : Instr w k ops → Bool
  | .readA i => decide (i.val = r)
  | .readB i => decide (i.val = r)
  | .load _ j => decide (j.val = r)
  | .iseof i _ => decide (i.val = r)
  | .arith _ i _ _ => decide (i.val = r)
  | _ => false

end Code

/-! ## Time-row equations (T1)–(T10) -/

section Time

variable (M : Ram) (kind : Fin M.ops → AluOp) (τ : ℕ)

/-- A slot of the row. -/
abbrev tv (s : TSlot) : Expr TVar := .var (.inl s)

/-- A slot of the row's routed record. -/
abbrev rv (f : RecField) (j : ℕ) : Expr TVar := .var (.inr (f, j))

/-- Bit `j` of an operand: `val (reg r) = rg_r`, `val pc = pc`, `val (const c) =` the bits of `c`. -/
def opnd : Operand M.w M.k → ℕ → Expr TVar
  | .reg r, j => tv (.rg r.val j)
  | .pc, j => tv (.pc j)
  | .const c, j => bit (c.getLsbD j)

/-- `srcX_p[j]` (`app:event-trace` operand sources). -/
def srcX : Instr M.w M.k M.ops → ℕ → Expr TVar
  | .arith _ _ x _, j => opnd M x j
  | .je i _, j => tv (.rg i.val j)
  | .jne i _, j => tv (.rg i.val j)
  | .load i _, j => tv (.rg i.val j)
  | .store i _, j => tv (.rg i.val j)
  | _, _ => zero

/-- `srcY_p[j]`. -/
def srcY : Instr M.w M.k M.ops → ℕ → Expr TVar
  | .arith _ _ _ y, j => opnd M y j
  | .store _ x, j => opnd M x j
  | _, _ => zero

/-- The flag operand of `iseof i j`: `fl_j`. -/
def srcXF : Instr M.w M.k M.ops → Expr TVar
  | .iseof _ j => tv (.fl j.val)
  | _ => zero

/-- `e(Q) = Σ_{p ∈ Q} e_p`. -/
def eSet (Q : Instr M.w M.k M.ops → Bool) : Expr TVar :=
  sumCode (fun p I => if Q I then tv (.e p) else zero) 0 M.code

/-- `Σ_p e_p · s_p`. -/
def eDot (s : Instr M.w M.k M.ops → Expr TVar) : Expr TVar :=
  sumCode (fun p I => mul (tv (.e p)) (s I)) 0 M.code

/-- `ca_j` (`ca_0 = 0`, `ca_j` stored in `CA (j − 1)`). -/
def caE (j : ℕ) : Expr TVar := if j = 0 then zero else tv (.CA (j - 1))

/-- `bo_j` (`bo_0 = 0`, `bo_j` stored in `BO (j − 1)`). -/
def boE (j : ℕ) : Expr TVar := if j = 0 then zero else tv (.BO (j - 1))

/-- `tc_j` (`tc_0 = 1`). -/
def tcE (j : ℕ) : Expr TVar := if j = 0 then one else tv (.TC (j - 1))

/-- `ac_j` (`ac_0 = aA`). -/
def acE (j : ℕ) : Expr TVar := if j = 0 then tv .aA else tv (.AC (j - 1))

/-- `bc_j` (`bc_0 = aB`). -/
def bcE (j : ℕ) : Expr TVar := if j = 0 then tv .aB else tv (.BC (j - 1))

/-- `CMP_j`: `CMP_0 = bo_w + gt`, `CMP_j = gt` (`j ≥ 1`). -/
def cmpE (j : ℕ) : Expr TVar := if j = 0 then add (tv (.BO (M.w - 1))) (tv .GT) else tv .GT

/-- The term of position `p` in (T8): `nxt.pc[j]` contributed by `I_p` (`oz := oz_{w−1}`, `p⁺ = p + 1`). -/
def pcTerm (p : ℕ) : Instr M.w M.k M.ops → ℕ → Expr TVar
  | .out _, j => mul (tv (.e p)) (bit (p.testBit j))
  | .jmp c, j => mul (tv (.e p)) (bit (c.testBit j))
  | .je _ c, j => add (mul (mul (tv (.e p)) (tv (.OZ (M.w - 1)))) (bit ((p + 1).testBit j)))
      (mul (add (tv (.e p)) (mul (tv (.e p)) (tv (.OZ (M.w - 1))))) (bit (c.testBit j)))
  | .jne _ c, j => add (mul (mul (tv (.e p)) (tv (.OZ (M.w - 1)))) (bit (c.testBit j)))
      (mul (add (tv (.e p)) (mul (tv (.e p)) (tv (.OZ (M.w - 1))))) (bit ((p + 1).testBit j)))
  | _, j => mul (tv (.e p)) (bit ((p + 1).testBit j))

/-- The time-row equations, one constructor per template of `app:affine-embedding`'s TIME catalog (bit index `j`, register `r`,
code position `p`). -/
inductive TEq where
  | flag (r j : ℕ)
  | decFirst
  | decRec (p : ℕ)
  | decExcl (p : ℕ)
  | decLast
  | decPc (j : ℕ)
  | opX (j : ℕ)
  | opY (j : ℕ)
  | opXF
  | sumAD (j : ℕ)
  | carry (j : ℕ)
  | sumSB (j : ℕ)
  | borrow (j : ℕ)
  | andAN (j : ℕ)
  | ozFirst
  | ozRec (j : ℕ)
  | gt
  | rfFlag (j : ℕ)
  | store (j : ℕ)
  | res (j : ℕ)
  | resF
  | reg (r j : ℕ)
  | regF (r : ℕ)
  | pcNext (j : ℕ)
  | recAct
  | recRgn
  | recAd (j : ℕ)
  | recPh
  | recVa (j : ℕ)
  | recSt
  | tsn (j : ℕ)
  | tc (j : ℕ)
  | aA
  | can (j : ℕ)
  | ac (j : ℕ)
  | aB
  | cbn (j : ℕ)
  | bc (j : ℕ)
  | bound
  deriving DecidableEq

/-- The equations that exist (the index ranges of `app:event-trace`). -/
def TEq.Active (d : Dims) : TEq → Prop
  | .flag r j => r < d.K ∧ j < d.w
  | .decFirst => True
  | .decRec p => 1 ≤ p ∧ p < d.L
  | .decExcl p => 1 ≤ p ∧ p < d.L
  | .decLast => True
  | .decPc j => j < d.w
  | .opX j => j < d.w
  | .opY j => j < d.w
  | .opXF => True
  | .sumAD j => j < d.w
  | .carry j => j + 1 < d.w
  | .sumSB j => j < d.w
  | .borrow j => j < d.w
  | .andAN j => j < d.w
  | .ozFirst => True
  | .ozRec j => 1 ≤ j ∧ j < d.w
  | .gt => True
  | .rfFlag j => j < d.w
  | .store j => j < d.w
  | .res j => j < d.w
  | .resF => True
  | .reg r j => r < d.K ∧ j < d.w
  | .regF r => r < d.K
  | .pcNext j => j < d.w
  | .recAct => True
  | .recRgn => True
  | .recAd j => j < d.w
  | .recPh => True
  | .recVa j => j < d.w
  | .recSt => True
  | .tsn j => j < d.τ
  | .tc j => j + 1 < d.τ
  | .aA => True
  | .can j => j < d.τ
  | .ac j => j + 1 < d.τ
  | .aB => True
  | .cbn j => j ≤ d.β
  | .bc j => j < d.β
  | .bound => True

/-- **(T1)–(T10)** (`app:event-trace`), each written `lhs + rhs` (`= 0` means `lhs = rhs` in characteristic two). -/
def timeEq : TEq → Expr TVar
  -- (T1) `fl_r · rg_r[j] = 0`
  | .flag r j => mul (tv (.fl r)) (tv (.rg r j))
  -- (T2) `o_0 = e_0`; `o_p = o_{p−1} + e_p`; `e_p · o_{p−1} = 0`; `o_{L−1} = 1`; `pc[j] = Σ_p bit_j(p) e_p`
  | .decFirst => add (tv (.o 0)) (tv (.e 0))
  | .decRec p => add (add (tv (.o p)) (tv (.o (p - 1)))) (tv (.e p))
  | .decExcl p => mul (tv (.e p)) (tv (.o (p - 1)))
  | .decLast => add (tv (.o (M.code.length - 1))) one
  | .decPc j => add (tv (.pc j)) (sumCode (fun p _ => if p.testBit j then tv (.e p) else zero) 0 M.code)
  -- (T3) operand buses
  | .opX j => add (tv (.X j)) (eDot M fun I => srcX M I j)
  | .opY j => add (tv (.Y j)) (eDot M fun I => srcY M I j)
  | .opXF => add (tv .XF) (eDot M fun I => srcXF M I)
  -- (T4) adder, subtractor, and, zero test, comparison
  | .sumAD j => add (add (add (tv (.AD j)) (tv (.X j))) (tv (.Y j))) (caE j)
  | .carry j => add (tv (.CA j)) (maj (tv (.X j)) (tv (.Y j)) (caE j))
  | .sumSB j => add (add (add (tv (.SB j)) (tv (.X j))) (tv (.Y j))) (boE j)
  | .borrow j => add (tv (.BO j))
      (add (mul (compl (tv (.X j))) (add (tv (.Y j)) (boE j))) (mul (tv (.Y j)) (boE j)))
  | .andAN j => add (tv (.AN j)) (mul (tv (.X j)) (tv (.Y j)))
  | .ozFirst => add (tv (.OZ 0)) (tv (.SB 0))
  | .ozRec j => add (tv (.OZ j))
      (add (add (tv (.OZ (j - 1))) (tv (.SB j))) (mul (tv (.OZ (j - 1))) (tv (.SB j))))
  | .gt => add (tv .GT) (mul (compl (tv (.BO (M.w - 1)))) (tv (.OZ (M.w - 1))))
  -- (T5) values
  | .rfFlag j => mul (tv .RF) (tv (.RV j))
  | .store j => mul (eSet M isSt) (add (tv (.MV j)) (tv (.Y j)))
  -- (T6) result
  | .res j => add (tv (.Z j)) (sum
      [mul (eSet M (isAr kind .add)) (tv (.AD j)),
       mul (eSet M (isAr kind .sub)) (tv (.SB j)),
       mul (eSet M (isAr kind .and)) (tv (.AN j)),
       mul (eSet M (isAr kind .cmp)) (cmpE M j),
       mul (eSet M isLd) (tv (.MV j)),
       mul (eSet M isRd) (tv (.RV j)),
       if j = 0 then mul (eSet M isEof) (tv .XF) else zero])
  | .resF => add (tv .ZF) (mul (eSet M isRd) (tv .RF))
  -- (T7) registers
  | .reg r j => add (tv (.nrg r j))
      (add (mul (eSet M (writes r)) (tv (.Z j))) (mul (compl (eSet M (writes r))) (tv (.rg r j))))
  | .regF r => add (tv (.nfl r))
      (add (mul (eSet M (writes r)) (tv .ZF)) (mul (compl (eSet M (writes r))) (tv (.fl r))))
  -- (T8) program counter
  | .pcNext j => add (tv (.npc j)) (sumCode (fun p I => pcTerm M p I j) 0 M.code)
  -- (T9) record
  | .recAct => add (rv .act 0) (add (add (eSet M isLd) (eSet M isSt)) (tv .aA))
  | .recRgn => add (rv .rgn 0) (tv .aA)
  | .recAd j => add (rv .ad j) (add (mul (add (eSet M isLd) (eSet M isSt)) (tv (.X j)))
      (if j < τ then mul (tv .aA) (tv (.cA j)) else zero))
  | .recPh => add (rv .ph 0) one
  | .recVa j => add (rv .va j) (add (mul (add (eSet M isLd) (eSet M isSt)) (tv (.MV j)))
      (mul (tv .aA) (tv (.RV j))))
  | .recSt => add (rv .st 0) (eSet M isSt)
  -- (T10) counters and the witness bound
  | .tsn j => add (add (tv (.TSN j)) (rv .ts j)) (tcE j)
  | .tc j => add (tv (.TC j)) (mul (rv .ts j) (tcE j))
  | .aA => add (tv .aA) (mul (eSet M isRdA) (compl (tv .RF)))
  | .can j => add (add (tv (.ncA j)) (tv (.cA j))) (acE j)
  | .ac j => add (tv (.AC j)) (mul (tv (.cA j)) (acE j))
  | .aB => add (tv .aB) (mul (eSet M isRdB) (compl (tv .RF)))
  | .cbn j => add (add (tv (.ncB j)) (tv (.cB j))) (bcE j)
  | .bc j => add (tv (.BC j)) (mul (tv (.cB j)) (bcE j))
  | .bound => mul (tv .aB) (tv (.cB (dims M τ).β))

/-- (B3): `e(Out)` (must vanish at `ρ_i`, `i < T − 1`). -/
def outE : Expr TVar := eSet M isOut

/-- (B3): `e(Acc) + 1` (must vanish at `ρ_{T−1}`). -/
def accE : Expr TVar := add (eSet M isAcc) one

end Time

/-! ## Time copies (B1), (B2) -/

/-- The copied slots of a time row: `ρ_{i+1}.(cur, ts, cA, cB) = ρ_i.(nxt, TSN, cAN, cBN)`. -/
inductive TCopy where
  | pc (j : ℕ)
  | fl (r : ℕ)
  | rg (r j : ℕ)
  | ts (j : ℕ)
  | cA (j : ℕ)
  | cB (j : ℕ)

/-- The copies that exist. -/
def TCopy.Active (d : Dims) : TCopy → Prop
  | .pc j => j < d.w
  | .fl r => r < d.K
  | .rg r j => r < d.K ∧ j < d.w
  | .ts j => j < d.τ
  | .cA j => j < d.τ
  | .cB j => j ≤ d.β

/-- The destination slot (at `ρ_{i+1}`; at `ρ_0` it must be `0`, (B1)). -/
def TCopy.dst : TCopy → TVar
  | .pc j => .inl (.pc j)
  | .fl r => .inl (.fl r)
  | .rg r j => .inl (.rg r j)
  | .ts j => .inr (.ts, j)
  | .cA j => .inl (.cA j)
  | .cB j => .inl (.cB j)

/-- The source slot (at `ρ_i`). -/
def TCopy.src : TCopy → TSlot
  | .pc j => .npc j
  | .fl r => .nfl r
  | .rg r j => .nrg r j
  | .ts j => .TSN j
  | .cA j => .ncA j
  | .cB j => .ncB j

/-! ## Sorted-vertex equations (S1)–(S5) -/

section Sorted

variable (d : Dims)

/-- A slot of the sorted vertex. -/
abbrev sv (s : SSlot) : Expr SVar := .var (.inl s)

/-- A slot of its routed record. -/
abbrev srv (f : RecField) (j : ℕ) : Expr SVar := .var (.inr (f, j))

/-- Key bit `l` (least significant first: `ts`, then `ph`, then `ad`, then `rgn`). -/
def keySlot (l : ℕ) : RecSlot :=
  if l < d.τ then (.ts, l) else if l = d.τ then (.ph, 0) else if l < d.τ + 1 + d.w then (.ad, l - d.τ - 1)
  else (.rgn, 0)

/-- `K_l` (the record's key bit). -/
def keyE (l : ℕ) : Expr SVar := .var (.inr (keySlot d l))

/-- `P_l` (the predecessor's key bit). -/
def pkeyE (l : ℕ) : Expr SVar := sv (.prev (keySlot d l).1 (keySlot d l).2)

/-- `ob_l` (`ob_0 = 0`, `ob_l` stored in `ob (l − 1)`). -/
def obE (l : ℕ) : Expr SVar := if l = 0 then zero else sv (.ob (l - 1))

/-- The sorted-vertex equations, one constructor per template of `app:affine-embedding`'s SORT catalog. -/
inductive SEq where
  | act
  | both
  | borrow (l : ℕ)
  | strict
  | soFirst
  | soNext (j : ℕ)
  | u
  | g
  | ev (j : ℕ)
  | load (j : ℕ)
  | gA1
  | gA
  | same
  | phase
  | value (j : ℕ)
  deriving DecidableEq

/-- The equations that exist. -/
def SEq.Active : SEq → Prop
  | .borrow l => l < d.κ
  | .soNext j => j < d.w
  | .ev j => j < d.w
  | .load j => j < d.w
  | .value j => j < d.w
  | _ => True

/-- **(S1)–(S5)** (`app:event-trace`). -/
def sortEq : SEq → Expr SVar
  -- (S1) `(1 + pact)·act = 0`; `both = act·pact`
  | .act => mul (compl (sv (.prev .act 0))) (srv .act 0)
  | .both => add (sv .both) (mul (srv .act 0) (sv (.prev .act 0)))
  -- (S2) `ob_{l+1} = (1 + P_l)(K_l + ob_l) + K_l·ob_l`; `both·(1 + ob_κ) = 0`
  | .borrow l => add (sv (.ob l))
      (add (mul (compl (pkeyE d l)) (add (keyE d l) (obE l))) (mul (keyE d l) (obE l)))
  | .strict => mul (sv .both) (compl (obE d.κ))
  -- (S3) `so_0 = prgn + rgn`; `so_{j+1} = so_j + d_{j+1} + so_j·d_{j+1}`, `d_{1+j} = pad[j] + ad[j]`
  | .soFirst => add (sv (.so 0)) (add (sv (.prev .rgn 0)) (srv .rgn 0))
  | .soNext j => add (sv (.so (j + 1)))
      (add (add (sv (.so j)) (add (sv (.prev .ad j)) (srv .ad j)))
        (mul (sv (.so j)) (add (sv (.prev .ad j)) (srv .ad j))))
  -- (S4) memory loads
  | .u => add (sv .u) (mul (srv .act 0) (compl (srv .rgn 0)))
  | .g => add (sv .g) (mul (sv .u) (compl (srv .st 0)))
  | .ev j => add (sv (.ev j)) (mul (compl (sv (.so d.w))) (sv (.prev .va j)))
  | .load j => mul (sv .g) (add (srv .va j) (sv (.ev j)))
  -- (S5) tape-A reads
  | .gA1 => add (sv .gA1) (mul (srv .act 0) (srv .rgn 0))
  | .gA => add (sv .gA) (mul (sv .gA1) (srv .ph 0))
  | .same => mul (sv .gA) (sv (.so d.w))
  | .phase => mul (sv .gA) (sv (.prev .ph 0))
  | .value j => mul (sv .gA) (add (srv .va j) (sv (.prev .va j)))

end Sorted

/-! ## Assignments and the system `ET(M, τ, x̄)` (`def:event-trace`) -/

/-- An assignment of field elements to all slots: routed records at stage `0` (`src`, by lane) and at the final
stage (`dst`), the non-routed slots of the time rows (`time`) and of the sorted vertices (`sort`). -/
structure Trace (F : Type) where
  src : ℕ → RecField → ℕ → F
  dst : ℕ → RecField → ℕ → F
  time : ℕ → TSlot → F
  sort : ℕ → SSlot → F

namespace Trace

variable {F : Type} (a : Trace F)

/-- The slots of time row `ρ_i`: its machine slots and its routed record `rec(ρ_i)` (stage `0`, lane `i`). -/
def timeRead (i : ℕ) : TVar → F
  | .inl s => a.time i s
  | .inr (f, j) => a.src i f j

/-- The slots of sorted vertex `σ_j`: its machine slots and its routed record (final stage, lane `j`). -/
def sortRead (j : ℕ) : SVar → F
  | .inl s => a.sort j s
  | .inr (f, k) => a.dst j f k

end Trace

/-- A bit of a ring. -/
def IsBit {F : Type} [CommRing F] (z : F) : Prop := z = 0 ∨ z = 1

/-- The value of the sentinel `(1, 0, 0, 0, 0, 0)` on a `PREV` field. -/
def sentinel {F : Type} [CommRing F] : RecField → F
  | .act => 1
  | _ => 0

/-- **`def:event-trace`: the event-trace system `ET(M, τ, x̄)` holds at the assignment `a`.** Notation: `T = 2^τ`
time rows, `N = 2T` lanes and sorted vertices, `N_A = |x̄| / w` input records at lanes `T, …, T + N_A − 1`, dummies
at lanes `T + N_A, …, N − 1`. -/
def Holds {F : Type} [CommRing F] (M : Ram) (kind : Fin M.ops → AluOp) (τ : ℕ) (xbar : List Bool)
    (a : Trace F) : Prop :=
  let d := dims M τ
  let T := 2 ^ τ
  let N := 2 ^ (τ + 1)
  let NA := xbar.length / M.w
  -- (G) every slot is a bit
  (∀ x < N, ∀ s : RecSlot, s.Active d → IsBit (a.src x s.1 s.2)) ∧
  (∀ x < N, ∀ s : RecSlot, s.Active d → IsBit (a.dst x s.1 s.2)) ∧
  (∀ i < T, ∀ s : TSlot, s.Active d → IsBit (a.time i s)) ∧
  (∀ j < N, ∀ s : SSlot, s.Active d → IsBit (a.sort j s)) ∧
  -- (T1)–(T10) at every time row
  (∀ i < T, ∀ q : TEq, q.Active d → (timeEq M kind τ q).eval (a.timeRead i) = 0) ∧
  -- (B1) `ρ_0`: `pc = 0`, `fl_r = 0`, `rg_r = 0`, `ts = 0`, `cA = 0`, `cB = 0`
  (∀ c : TCopy, c.Active d → a.timeRead 0 c.dst = 0) ∧
  -- (B2) the copies `ρ_{i+1}.(cur, ts, cA, cB) = ρ_i.(nxt, TSN, cAN, cBN)`
  (∀ i, i + 1 < T → ∀ c : TCopy, c.Active d → a.timeRead (i + 1) c.dst = a.time i c.src) ∧
  -- (B2) `e(Out) = 0` at `ρ_i`, `i < T − 1`; (B3) `e(Acc) = 1` at `ρ_{T−1}`
  (∀ i, i + 1 < T → (outE M).eval (a.timeRead i) = 0) ∧
  (accE M).eval (a.timeRead (T - 1)) = 0 ∧
  -- (S1)–(S5) at every sorted vertex
  (∀ j < N, ∀ q : SEq, q.Active d → (sortEq d q).eval (a.sortRead j) = 0) ∧
  -- (B4) `σ_0.PREV` = the sentinel; `σ_{j+1}.PREV = σ_j.(act, rgn, ad, ph, ts, va)`
  (∀ f k, (SSlot.prev f k).Active d → a.sort 0 (.prev f k) = sentinel f) ∧
  (∀ j, j + 1 < N → ∀ f k, (SSlot.prev f k).Active d → a.sort (j + 1) (.prev f k) = a.dst j f k) ∧
  -- (B5) input records `ι_c` at lane `T + c`: `act = 1`, `rgn = 1`, `ad = c`, `ph = 0`, `ts = 0`, `st = 0`,
  -- `va[b] = x̄_{cw+b}` (the input clause, `app:event-trace` Input positions)
  (∀ c < NA,
    a.src (T + c) .act 0 = 1 ∧ a.src (T + c) .rgn 0 = 1 ∧ a.src (T + c) .ph 0 = 0 ∧ a.src (T + c) .st 0 = 0 ∧
    (∀ j < τ, a.src (T + c) .ts j = 0) ∧
    (∀ j < M.w, a.src (T + c) .ad j = if c.testBit j then 1 else 0) ∧
    (∀ b < M.w, a.src (T + c) .va b = if xbar.getD (c * M.w + b) false then 1 else 0)) ∧
  -- (B5) every dummy has `REC = 0`
  (∀ x, T + NA ≤ x → x < N → ∀ s : RecSlot, s.Active d → a.src x s.1 s.2 = 0) ∧
  -- (P) the source list and `(σ_0.REC, …, σ_{N−1}.REC)` are equal as multisets
  (∃ π : Equiv.Perm (Fin N), ∀ x : Fin N, ∀ s : RecSlot, s.Active d → a.dst (π x) s.1 s.2 = a.src x s.1 s.2)

/-- **`ET(M, τ, x̄)` is satisfiable** (`def:event-trace`), over a ring `F` of characteristic two. -/
def Satisfiable (F : Type) [CommRing F] (M : Ram) (kind : Fin M.ops → AluOp) (τ : ℕ) (xbar : List Bool) :
    Prop :=
  ∃ a : Trace F, Holds M kind τ xbar a

end NearCubicGates.Adapters.RAMTrace
