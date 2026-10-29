import SourceAdapters.Joins.AffineRouting
import SourceAdapters.RAMTrace.Defs

/-!
# The machine catalog placed in `H`: one guarded term per equation instance

Paper context and implementation details:
- `app:event-trace` Realization in `H` and `app:affine-embedding` Complete field catalog (time values area `1`, stage `0`; sorted values area `1`,
  final stage `2k_N − 1`; routed `REC` area `0`, role `0`, field tags `va 0, ad 1, ts 2, ph 3, rgn 4, act 5, st 6`;
  time role `0` tags `PC 8`, `FL_r 9+2r`, `RG_r 10+2r`, `E_p 9+2K+2p`, `O_p 10+2K+2p`, then the 22 blocks
  `X … aB` from `A0 = 9+2K+2L`; role `1` the next versions at the same tags and `TSN` at tag `2`; sorted role `1`
  `PREV` at `REC`'s tags `0..5`, role `0` `OB_0..OB_2, BOTH, SO_0, SO_1, U, G, EV, GA1, GA` at tags `8..18`);
- `app:affine-embedding` Complete machine equation catalog, area1 role2 (TIME templates `3K + 2L + 32`, SORT templates `17`, in the
  displayed order, bit index `j`), Copies, boundary checks, and access census (Booleanity at role `3`/`4`, time copies
  at role `5` with `FIRST`/`PREV_t`, sorted copies at role `6`, `B3` at role `7` tag `7`, `B5` at role `7` on the
  `REC` columns with `INPUT`/`DUMMY`), and Exact selector emitter and polynomial guard-list bound (the guard
  library `HOST`, `TIME`, `INPUT`, `DUMMY`, `FIRST`, `LAST_TIME`, `EARLY_TIME`, `PREV_t`).

Every machine equation is the `RAMTrace` data tree (`timeEq`, `sortEq`, `outE`, `accE`, the `Joins.RAMEventTrace`
definitions) with each slot read replaced by the translation from the host point to that slot's catalog point
(`localOffset`, in the `16C` local bank) or by one of the two predecessor families of the bank. Nothing here
enumerates lanes, `H`, or the computation: every list ranges over `j < w`, `r < K`, `p < L`, `l < κ`, `t < k_N`.

Within these counts, the implementation orders the templates as follows: inside the row `T7.RG.r, T7.FL.r` the `K` register templates precede the
`K` flag templates; the sorted `S2` borrow template of key bit `l` has tag `2 + ⌊l/w⌋` and bit `l mod w`.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.RAMTrace

/-! ## Catalog cells -/

/-- A point of one vertex: field/template tag, bit index, role, area (`app:affine-embedding` `E(x, s, (f, j), r, a)` without the lane
and stage). -/
structure Cell where
  tag : ℕ
  bit : ℕ
  role : ℕ
  area : ℕ

/-- The column code `(tag << ω) | bit`. -/
def Cell.col (om : ℕ) (c : Cell) : ℕ := c.bit + 2 ^ om * c.tag

/-- The translation from host `h` to cell `c` of the same lane and stage (`app:affine-embedding`: `column(c ⊕ c') + role(r ⊕ r') +
area(a ⊕ a')`). -/
def localOffset (l : Routing.Layout) (om : ℕ) (h c : Cell) : ℕ :=
  Routing.cellMask l 0 0 (h.col om ^^^ c.col om) (h.role ^^^ c.role) (h.area ^^^ c.area)

/-- The first of the 22 blocks of the time role-`0` catalog, `A0 = 9 + 2K + 2L`. -/
def blockBase (K L : ℕ) : ℕ := 9 + 2 * K + 2 * L

/-- The catalog cell of a time-row slot (`app:affine-embedding` Time values, area1, stage0). -/
def tCell (K L : ℕ) : TSlot → Cell
  | .pc j => ⟨8, j, 0, 1⟩
  | .fl r => ⟨9 + 2 * r, 0, 0, 1⟩
  | .rg r j => ⟨10 + 2 * r, j, 0, 1⟩
  | .e p => ⟨9 + 2 * K + 2 * p, 0, 0, 1⟩
  | .o p => ⟨10 + 2 * K + 2 * p, 0, 0, 1⟩
  | .X j => ⟨blockBase K L, j, 0, 1⟩
  | .XF => ⟨blockBase K L + 1, 0, 0, 1⟩
  | .Y j => ⟨blockBase K L + 2, j, 0, 1⟩
  | .AD j => ⟨blockBase K L + 3, j, 0, 1⟩
  | .CA j => ⟨blockBase K L + 4, j, 0, 1⟩
  | .SB j => ⟨blockBase K L + 5, j, 0, 1⟩
  | .BO j => ⟨blockBase K L + 6, j, 0, 1⟩
  | .AN j => ⟨blockBase K L + 7, j, 0, 1⟩
  | .OZ j => ⟨blockBase K L + 8, j, 0, 1⟩
  | .GT => ⟨blockBase K L + 9, 0, 0, 1⟩
  | .Z j => ⟨blockBase K L + 10, j, 0, 1⟩
  | .ZF => ⟨blockBase K L + 11, 0, 0, 1⟩
  | .RV j => ⟨blockBase K L + 12, j, 0, 1⟩
  | .RF => ⟨blockBase K L + 13, 0, 0, 1⟩
  | .MV j => ⟨blockBase K L + 14, j, 0, 1⟩
  | .TC j => ⟨blockBase K L + 15, j, 0, 1⟩
  | .cA j => ⟨blockBase K L + 16, j, 0, 1⟩
  | .cB j => ⟨blockBase K L + 17, j, 0, 1⟩
  | .AC j => ⟨blockBase K L + 18, j, 0, 1⟩
  | .BC j => ⟨blockBase K L + 19, j, 0, 1⟩
  | .aA => ⟨blockBase K L + 20, 0, 0, 1⟩
  | .aB => ⟨blockBase K L + 21, 0, 0, 1⟩
  | .npc j => ⟨8, j, 1, 1⟩
  | .nfl r => ⟨9 + 2 * r, 0, 1, 1⟩
  | .nrg r j => ⟨10 + 2 * r, j, 1, 1⟩
  | .ncA j => ⟨blockBase K L + 16, j, 1, 1⟩
  | .ncB j => ⟨blockBase K L + 17, j, 1, 1⟩
  | .TSN j => ⟨2, j, 1, 1⟩

/-- The catalog cell of a routed-record slot (`app:affine-embedding` Routed REC, area0 role0). -/
def recCell (s : RecSlot) : Cell := ⟨s.1.tag, s.2, 0, 0⟩

/-- The catalog cell of a sorted-vertex slot (`app:affine-embedding` Sorted values; `ob l` holds `ob_{l+1}`, at tag
`8 + ⌊l/w⌋`, bit `l mod w`; `so l` at `SO_0` bit `l` for `l < w`, `so_w` at `SO_1` bit `0`). -/
def sCell (w : ℕ) : SSlot → Cell
  | .prev f j => ⟨f.tag, j, 1, 1⟩
  | .ob l => ⟨8 + l / w, l % w, 0, 1⟩
  | .both => ⟨11, 0, 0, 1⟩
  | .so l => if l < w then ⟨12, l, 0, 1⟩ else ⟨13, 0, 0, 1⟩
  | .u => ⟨14, 0, 0, 1⟩
  | .g => ⟨15, 0, 0, 1⟩
  | .ev j => ⟨16, j, 0, 1⟩
  | .gA1 => ⟨17, 0, 0, 1⟩
  | .gA => ⟨18, 0, 0, 1⟩

/-- The destination cell of a time copy (`ρ_{i+1}.(cur, ts, cA, cB)`; `ts` is the routed record's). -/
def dstCell (K L : ℕ) (cp : TCopy) : Cell :=
  match cp.dst with
  | .inl s => tCell K L s
  | .inr s => recCell s

/-! ## Template tags (`app:affine-embedding` TIME and SORT catalogs, in the displayed order) -/

/-- The TIME template tag of an equation (`3K + 2L + 32` tags). -/
def tTag (K L : ℕ) : TEq → ℕ
  | .flag r _ => r
  | .decFirst => K
  | .decRec p => K + p
  | .decExcl p => K + L - 1 + p
  | .decLast => K + 2 * L - 1
  | .decPc _ => K + 2 * L
  | .opX _ => K + 2 * L + 1
  | .opY _ => K + 2 * L + 2
  | .opXF => K + 2 * L + 3
  | .sumAD _ => K + 2 * L + 4
  | .carry _ => K + 2 * L + 5
  | .sumSB _ => K + 2 * L + 6
  | .borrow _ => K + 2 * L + 7
  | .andAN _ => K + 2 * L + 8
  | .ozFirst => K + 2 * L + 9
  | .ozRec _ => K + 2 * L + 10
  | .gt => K + 2 * L + 11
  | .rfFlag _ => K + 2 * L + 12
  | .store _ => K + 2 * L + 13
  | .res _ => K + 2 * L + 14
  | .resF => K + 2 * L + 15
  | .reg r _ => K + 2 * L + 16 + r
  | .regF r => 2 * K + 2 * L + 16 + r
  | .pcNext _ => 3 * K + 2 * L + 16
  | .recAct => 3 * K + 2 * L + 17
  | .recRgn => 3 * K + 2 * L + 18
  | .recAd _ => 3 * K + 2 * L + 19
  | .recPh => 3 * K + 2 * L + 20
  | .recVa _ => 3 * K + 2 * L + 21
  | .recSt => 3 * K + 2 * L + 22
  | .tsn _ => 3 * K + 2 * L + 23
  | .tc _ => 3 * K + 2 * L + 24
  | .aA => 3 * K + 2 * L + 25
  | .can _ => 3 * K + 2 * L + 26
  | .ac _ => 3 * K + 2 * L + 27
  | .aB => 3 * K + 2 * L + 28
  | .cbn _ => 3 * K + 2 * L + 29
  | .bc _ => 3 * K + 2 * L + 30
  | .bound => 3 * K + 2 * L + 31

/-- The bit index of a TIME equation (its `j`; `0` for scalar templates). -/
def tBit : TEq → ℕ
  | .flag _ j | .decPc j | .opX j | .opY j | .sumAD j | .carry j | .sumSB j | .borrow j | .andAN j | .ozRec j
  | .rfFlag j | .store j | .res j | .reg _ j | .pcNext j | .recAd j | .recVa j | .tsn j | .tc j | .can j | .ac j
  | .cbn j | .bc j => j
  | _ => 0

/-- The SORT template tag (`17` tags). -/
def sTag (w : ℕ) : SEq → ℕ
  | .act => 0
  | .both => 1
  | .borrow l => 2 + l / w
  | .strict => 5
  | .soFirst => 6
  | .soNext _ => 7
  | .u => 8
  | .g => 9
  | .ev _ => 10
  | .load _ => 11
  | .gA1 => 12
  | .gA => 13
  | .same => 14
  | .phase => 15
  | .value _ => 16

/-- The bit index of a SORT equation. -/
def sBit (w : ℕ) : SEq → ℕ
  | .borrow l => l % w
  | .soNext j | .ev j | .load j | .value j => j
  | _ => 0

/-! ## The active instances, as explicit lists (the index ranges of `app:event-trace`) -/

/-- The active time-row equations (`TEq.Active`), in template order. -/
def timeEqList (d : Dims) : List TEq :=
  (List.range d.K).flatMap (fun r => (List.range d.w).map (TEq.flag r)) ++ [TEq.decFirst] ++
  (List.range (d.L - 1)).map (fun p => TEq.decRec (p + 1)) ++
  (List.range (d.L - 1)).map (fun p => TEq.decExcl (p + 1)) ++ [TEq.decLast] ++
  (List.range d.w).map TEq.decPc ++ (List.range d.w).map TEq.opX ++ (List.range d.w).map TEq.opY ++
  [TEq.opXF] ++ (List.range d.w).map TEq.sumAD ++ (List.range (d.w - 1)).map TEq.carry ++
  (List.range d.w).map TEq.sumSB ++ (List.range d.w).map TEq.borrow ++ (List.range d.w).map TEq.andAN ++
  [TEq.ozFirst] ++ (List.range (d.w - 1)).map (fun j => TEq.ozRec (j + 1)) ++ [TEq.gt] ++
  (List.range d.w).map TEq.rfFlag ++ (List.range d.w).map TEq.store ++ (List.range d.w).map TEq.res ++
  [TEq.resF] ++ (List.range d.K).flatMap (fun r => (List.range d.w).map (TEq.reg r)) ++
  (List.range d.K).map TEq.regF ++ (List.range d.w).map TEq.pcNext ++ [TEq.recAct, TEq.recRgn] ++
  (List.range d.w).map TEq.recAd ++ [TEq.recPh] ++ (List.range d.w).map TEq.recVa ++ [TEq.recSt] ++
  (List.range d.τ).map TEq.tsn ++ (List.range (d.τ - 1)).map TEq.tc ++ [TEq.aA] ++
  (List.range d.τ).map TEq.can ++ (List.range (d.τ - 1)).map TEq.ac ++ [TEq.aB] ++
  (List.range (d.β + 1)).map TEq.cbn ++ (List.range d.β).map TEq.bc ++ [TEq.bound]

/-- The active time-row slots (`TSlot.Active`). -/
def timeSlotList (d : Dims) : List TSlot :=
  (List.range d.w).map TSlot.pc ++ (List.range d.K).map TSlot.fl ++
  (List.range d.K).flatMap (fun r => (List.range d.w).map (TSlot.rg r)) ++
  (List.range d.L).map TSlot.e ++ (List.range d.L).map TSlot.o ++
  (List.range d.w).map TSlot.X ++ [TSlot.XF] ++ (List.range d.w).map TSlot.Y ++ (List.range d.w).map TSlot.AD ++
  (List.range (d.w - 1)).map TSlot.CA ++ (List.range d.w).map TSlot.SB ++ (List.range d.w).map TSlot.BO ++
  (List.range d.w).map TSlot.AN ++ (List.range d.w).map TSlot.OZ ++ [TSlot.GT] ++ (List.range d.w).map TSlot.Z ++
  [TSlot.ZF] ++ (List.range d.w).map TSlot.RV ++ [TSlot.RF] ++ (List.range d.w).map TSlot.MV ++
  (List.range (d.τ - 1)).map TSlot.TC ++ (List.range d.τ).map TSlot.cA ++ (List.range (d.β + 1)).map TSlot.cB ++
  (List.range (d.τ - 1)).map TSlot.AC ++ (List.range d.β).map TSlot.BC ++ [TSlot.aA, TSlot.aB] ++
  (List.range d.w).map TSlot.npc ++ (List.range d.K).map TSlot.nfl ++
  (List.range d.K).flatMap (fun r => (List.range d.w).map (TSlot.nrg r)) ++
  (List.range d.τ).map TSlot.ncA ++ (List.range (d.β + 1)).map TSlot.ncB ++ (List.range d.τ).map TSlot.TSN

/-- The active copies (`TCopy.Active`). -/
def copyList (d : Dims) : List TCopy :=
  (List.range d.w).map TCopy.pc ++ (List.range d.K).map TCopy.fl ++
  (List.range d.K).flatMap (fun r => (List.range d.w).map (TCopy.rg r)) ++
  (List.range d.τ).map TCopy.ts ++ (List.range d.τ).map TCopy.cA ++ (List.range (d.β + 1)).map TCopy.cB

/-- The record fields with their semantic widths. -/
def recFields : List RecField := [.va, .ad, .ts, .ph, .rgn, .act, .st]

/-- The active routed-record slots (`RecSlot.Active`). -/
def recSlotList (d : Dims) : List RecSlot :=
  recFields.flatMap fun f => (List.range (f.width d.w d.τ)).map fun j => (f, j)

/-- The active sorted-vertex equations (`SEq.Active`), in template order. -/
def sortEqList (d : Dims) : List SEq :=
  [SEq.act, SEq.both] ++ (List.range d.κ).map SEq.borrow ++ [SEq.strict, SEq.soFirst] ++
  (List.range d.w).map SEq.soNext ++ [SEq.u, SEq.g] ++ (List.range d.w).map SEq.ev ++
  (List.range d.w).map SEq.load ++ [SEq.gA1, SEq.gA, SEq.same, SEq.phase] ++ (List.range d.w).map SEq.value

/-- The active sorted-vertex slots (`SSlot.Active`). -/
def sortSlotList (d : Dims) : List SSlot :=
  ([RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
    (List.range (f.width d.w d.τ)).map fun j => SSlot.prev f j) ++
  (List.range d.κ).map SSlot.ob ++ [SSlot.both] ++ (List.range (d.w + 1)).map SSlot.so ++
  [SSlot.u, SSlot.g] ++ (List.range d.w).map SSlot.ev ++ [SSlot.gA1, SSlot.gA]

/-! ## Expressions and guards -/

section Emit

variable {F : Type} [Field F] [CharP F 2]

/-- An event-trace equation tree as a routing expression, each slot read through `rd` (an offset of the bank). -/
def toRouting {ι : Type} (rd : ι → ℕ) : RAMTrace.Expr ι → Routing.Expr F
  | .zero => .const 0
  | .one => .const 1
  | .var i => .read (some (rd i))
  | .add a b => .add (toRouting rd a) (toRouting rd b)
  | .mul a b => .mul (toRouting rd a) (toRouting rd b)

variable (l : Routing.Layout) (om K L : ℕ)

/-- The reads of a time-row equation hosted at `h`. -/
def tRead (h : Cell) : TVar → ℕ
  | .inl s => localOffset l om h (tCell K L s)
  | .inr s => localOffset l om h (recCell s)

/-- The reads of a sorted-vertex equation hosted at `h`. -/
def sRead (w : ℕ) (h : Cell) : SVar → ℕ
  | .inl s => localOffset l om h (sCell w s)
  | .inr s => localOffset l om h (recCell s)

/-- A normalized guard (`app:affine-embedding` Exact selector emitter): the host's stage, column, role and area (`HOST`), and the lane
bits `laneKnown` fixed to `laneValue`. -/
def guardAt (laneKnown laneValue stage : ℕ) (h : Cell) : Routing.Pattern l.m :=
  Routing.patternMasks l.m (Routing.cellMask l laneKnown (2 ^ l.ell - 1) (2 ^ l.q - 1) 7 1)
    (Routing.cellMask l laneValue stage (h.col om) h.role h.area)

/-- The (B5) input-record equations on a record slot with value `Y` (`va` is bound by the input clause, not here). -/
def inputEqs (τ : ℕ) (lam : ℕ → Routing.Expr F) (Y : Routing.Expr F) (s : RecSlot) : List (Routing.Expr F) :=
  match s.1 with
  | .va => []
  | .act | .rgn => [.add Y (.const 1)]
  | .ad => [if s.2 < τ then .add Y (lam s.2) else Y]
  | .ts | .ph | .st => [Y]

/-- `Y² + Y` (Booleanity). -/
def boolExpr (b : ℕ) : Routing.Expr F := .add (.square (.read (some b))) (.read (some b))

variable (M : Ram) (kind : Fin M.ops → AluOp) (τ a : ℕ)

/-- **The machine terms** (`app:affine-embedding` machine catalog + copies, boundary checks, Booleanity; `app:event-trace` Realization in `H`), for
the RAM `M`, time exponent `τ`, input-record exponent `a = log₂ N_A`, and the coordinate expressions `lam j = λ_j(X)`
used by the input records' address check (B5). Stage `0` hosts time/input/dummy lanes, stage `2k − 1` the sorted
lanes. -/
def machineItems (lam : ℕ → Routing.Expr F) : List (Routing.Pattern l.m × Routing.Expr F) :=
  let d := dims M τ
  let w := M.w
  let k := l.k
  let fin := 2 * k - 1
  let timeKnown := 2 ^ τ
  let firstKnown := 2 ^ k - 1
  -- (T1)–(T10): own point per template and bit index, on time lanes
  ((timeEqList d).map fun q =>
    let h : Cell := ⟨tTag K L q, tBit q, 2, 1⟩
    (guardAt l om timeKnown 0 0 h, toRouting (tRead l om K L h) (timeEq M kind τ q))) ++
  -- (G) Booleanity of time-row slots at roles 3/4
  ((timeSlotList d).map fun s =>
    let c := tCell K L s
    let h : Cell := ⟨c.tag, c.bit, c.role + 3, 1⟩
    (guardAt l om timeKnown 0 0 h, boolExpr (localOffset l om h c))) ++
  -- (B1) at the first lane, (B2) copies from the previous lane (least set lane bit `t < τ`), at role 5
  ((copyList d).flatMap fun cp =>
    let dc : Cell := dstCell K L cp
    let h : Cell := ⟨dc.tag, dc.bit, 5, 1⟩
    (guardAt l om firstKnown 0 0 h, .read (some (localOffset l om h dc))) ::
    (List.range τ).map fun t =>
      (guardAt l om (2 ^ (t + 1) - 1 + 2 ^ τ) (2 ^ t) 0 h,
        .add (.read (some (localOffset l om h dc)))
          (.read (some (Routing.laneCarry t ^^^ Routing.eta l 5 ^^^ Routing.eta l 1))))) ++
  -- (B2) `e(Out) = 0` on time lanes other than the last (EARLY_TIME), (B3) `e(Acc) = 1` on the last (LAST_TIME)
  (let h : Cell := ⟨7, 0, 7, 1⟩
   ((List.range τ).map fun b =>
     (guardAt l om (2 ^ τ + (2 ^ (b + 1) - 1)) (2 ^ b - 1) 0 h, toRouting (tRead l om K L h) (outE M))) ++
   [(guardAt l om firstKnown (2 ^ τ - 1) 0 h, toRouting (tRead l om K L h) (accE M))]) ++
  -- (S1)–(S5) at every sorted lane
  ((sortEqList d).map fun q =>
    let h : Cell := ⟨sTag w q, sBit w q, 2, 1⟩
    (guardAt l om 0 0 fin h, toRouting (sRead l om w h) (sortEq d q))) ++
  -- (G) Booleanity of sorted slots
  ((sortSlotList d).map fun s =>
    let c := sCell w s
    let h : Cell := ⟨c.tag, c.bit, c.role + 3, 1⟩
    (guardAt l om 0 0 fin h, boolExpr (localOffset l om h c))) ++
  -- (B4) the sentinel at the first sorted lane, the predecessor copy from lane `x − 1` otherwise, at role 6
  (([RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
    (List.range (f.width d.w d.τ)).map fun j => (f, j)).flatMap fun s =>
    let pc : Cell := sCell w (.prev s.1 s.2)
    let h : Cell := ⟨pc.tag, pc.bit, 6, 1⟩
    (guardAt l om firstKnown 0 fin h,
      .add (.read (some (localOffset l om h pc))) (.const (if s.1 = .act then 1 else 0))) ::
    (List.range k).map fun t =>
      (guardAt l om (2 ^ (t + 1) - 1) (2 ^ t) fin h,
        .add (.read (some (localOffset l om h pc)))
          (.read (some (Routing.laneCarry t ^^^ Routing.areaMask l ^^^ Routing.eta l 6))))) ++
  -- (B5) input records (lanes `T ≤ x < T + 2^a`) and dummies (`T + 2^a ≤ x < 2T`), at role 7 on the REC columns
  ((recSlotList d).flatMap fun s =>
    let rc := recCell s
    let h : Cell := ⟨rc.tag, rc.bit, 7, 1⟩
    let Y : Routing.Expr F := .read (some (localOffset l om h rc))
    ((inputEqs τ lam Y s).map fun E => (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ a)) (2 ^ τ) 0 h, E)) ++
    ((List.range (τ - a)).map fun i =>
      (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ (a + i))) (2 ^ τ + 2 ^ (a + i)) 0 h, Y)))

end Emit

end NearCubicGates.Adapters.RAMACSP
