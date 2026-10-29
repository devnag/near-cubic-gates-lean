import SourceAdapters.RAMACSP.GenItemsP
import SourceAdapters.RAMACSP.ConstraintCatalog
import SourceAdapters.Joins.TermsCircuit
import SourceAdapters.RAMACSP.CheckReads

/-!
# Printing one item: guard entries, equation tokens, local reads

Paper: "Selectors" and "Neighbors" in `app:affine-embedding`, and
`lem:generator`. A guard fixes host coordinates and selected lane bits.
A same-vertex read uses the XOR of the host and target column, role and area;
the equation printer emits those offsets and the guard pattern literally.

The words of `Joins/TermsCircuit` are concatenations of `natWord`s: an item is the flag `1`, the `mH` guard codes, the
tokens of the equation in postorder (each a tag and one number), and the end token `5 0` (`itemNums`, `itemWord_eq`).

- `SC`, `SX`: a catalog cell with its field tag and bit index given by `FL` expressions, and equation trees over such
  cells with branches (`SX.ev`: the `RAMTrace` tree of cells at a state);
- `offE h c`: the local offset `localOffset l ω h c`, computed from the layout numbers in the program variables
  (`evalE_offE`, for cells inside the catalog, `Cell.Ok`);
- `tokP h x`: the tokens of the equation `x` read from the host `h` (`den_tokP`);
- `guardP`, `itemP`: the guard codes of `patternMasks mH known value` and a whole item (`den_itemP`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMACSP.Gen
open NearCubicWires (natBitLength)
open NearCubicWires.RepairRepresentation (natWord)

/-! ## Words as numbers -/

/-- The numbers of a token. -/
def tokNums : Joins.TermTok → List ℕ
  | .const v => [0, v]
  | .read v => [1, Joins.varCode v]
  | .add => [2, 0]
  | .mul => [3, 0]
  | .square => [4, 0]

theorem termTokWord_eq (t : Joins.TermTok) : Joins.termTokWord t = (tokNums t).flatMap natWord := by
  cases t <;> simp [Joins.termTokWord, tokNums]

/-- The numbers of an item: the flag, the guard codes, the tokens, the end token. -/
def itemNums {F : Type} (mk : F → ℕ) {m : ℕ} (x : Routing.Pattern m × Routing.Expr F) : List ℕ :=
  [1] ++ (List.ofFn x.1).map Joins.guardCode ++ (Joins.exprToks mk x.2).flatMap tokNums ++ [5, 0]

theorem itemWord_eq {F : Type} (mk : F → ℕ) {m : ℕ} (x : Routing.Pattern m × Routing.Expr F) :
    Joins.itemWord mk x = (itemNums mk x).flatMap natWord := by
  have ht : Joins.termTokWord = fun t => (tokNums t).flatMap natWord := funext termTokWord_eq
  simp only [Joins.itemWord, Joins.patternWord, Joins.exprWord, itemNums, List.flatMap_append,
    List.flatMap_map, Function.comp_def, ht]
  simp [List.flatMap_assoc]

/-! ## Trees of cells -/

/-- A map of a `RAMTrace` expression on its variables. -/
def xmap {ι κ : Type} (f : ι → κ) : RAMTrace.Expr ι → RAMTrace.Expr κ
  | .zero => .zero
  | .one => .one
  | .var i => .var (f i)
  | .add a b => .add (xmap f a) (xmap f b)
  | .mul a b => .mul (xmap f a) (xmap f b)

theorem toRouting_xmap {F : Type} [Field F] [CharP F 2] {ι : Type} (rd : Cell → ℕ) (f : ι → Cell) :
    ∀ e : RAMTrace.Expr ι, (toRouting (rd ∘ f) e : Routing.Expr F) = toRouting rd (xmap f e)
  | .zero => rfl
  | .one => rfl
  | .var _ => rfl
  | .add a b => by simp only [toRouting, xmap, toRouting_xmap rd f a, toRouting_xmap rd f b]
  | .mul a b => by simp only [toRouting, xmap, toRouting_xmap rd f a, toRouting_xmap rd f b]

theorem vars_xmap {ι κ : Type} (f : ι → κ) : ∀ e : RAMTrace.Expr ι, (xmap f e).vars = e.vars.map f
  | .zero => rfl
  | .one => rfl
  | .var _ => rfl
  | .add a b => by simp [xmap, RAMTrace.Expr.vars, vars_xmap f a, vars_xmap f b]
  | .mul a b => by simp [xmap, RAMTrace.Expr.vars, vars_xmap f a, vars_xmap f b]

/-- A symbolic cell: the bit index as an `FL` expression; field tag, role and area fixed. -/
structure SC where
  tag : ℕ
  bit : E
  role : ℕ
  area : ℕ

/-- Its cell at a state. -/
def SC.ev (G : Glob) (s : FS) (c : SC) : Cell := ⟨c.tag, evalE G s c.bit, c.role, c.area⟩

/-- Symbolic equation trees: coefficients `0`, `1`, cells, sums, products, and branches (`ite c a b` is `a` when
`c ≠ 0`, the `FL` convention). -/
inductive SX where
  | zero
  | one
  | var (c : SC)
  | add (a b : SX)
  | mul (a b : SX)
  | ite (c : E) (a b : SX)

/-- The tree of cells at a state. -/
def SX.ev (G : Glob) (s : FS) : SX → RAMTrace.Expr Cell
  | .zero => .zero
  | .one => .one
  | .var c => .var (c.ev G s)
  | .add a b => .add (SX.ev G s a) (SX.ev G s b)
  | .mul a b => .mul (SX.ev G s a) (SX.ev G s b)
  | .ite c a b => if evalE G s c = 0 then SX.ev G s b else SX.ev G s a

/-! ## Program variables of the layout -/

/-- Variables of the item printer: `ω` (25), `k` (31), `ℓ` (32), `q` (34), `mH` (35) as set by the parameter
program; `k + ℓ` (44) and the guard mask of the fixed coordinates (45). -/
def vKL : Var := 44
def vUK : Var := 45

/-- The fixed coordinates of every machine guard: stage, column, role, area (`cellMask l 0 (2^ℓ−1) (2^q−1) 7 1`). -/
def upperKnown (l : Routing.Layout) : ℕ := Routing.cellMask l 0 (2 ^ l.ell - 1) (2 ^ l.q - 1) 7 1

/-- The layout in the program variables (`ω = om`, `q = dt + ω`). -/
structure LayV (l : Routing.Layout) (om dt : ℕ) (s : FS) : Prop where
  hom : s.env 25 = om
  hk : s.env 31 = l.k
  hell : s.env 32 = l.ell
  hqv : s.env 34 = l.q
  hmH : s.env 35 = l.m
  hkl : s.env vKL = l.k + l.ell
  huk : s.env vUK = upperKnown l
  hq : l.q = dt + om

/-- The readable variables of the layout. -/
def layA (x : Var) : Prop := x = 25 ∨ x = 31 ∨ x = 32 ∨ x = 34 ∨ x = 35 ∨ x = vKL ∨ x = vUK

theorem LayV.agree {l : Routing.Layout} {om dt : ℕ} {s t : FS} (h : LayV l om dt s) {A : Var → Prop}
    (hA : ∀ x, layA x → A x) (ha : Agree A s t) : LayV l om dt t :=
  ⟨(ha.1 _ (hA _ (by simp [layA]))).trans h.hom, (ha.1 _ (hA _ (by simp [layA]))).trans h.hk,
    (ha.1 _ (hA _ (by simp [layA]))).trans h.hell, (ha.1 _ (hA _ (by simp [layA]))).trans h.hqv,
    (ha.1 _ (hA _ (by simp [layA]))).trans h.hmH, (ha.1 _ (hA _ (by simp [layA]))).trans h.hkl,
    (ha.1 _ (hA _ (by simp [layA]))).trans h.huk, h.hq⟩

/-! ## Local offsets -/

/-- The column `bit + 2^ω·tag` of a symbolic cell. -/
def colE (c : SC) : E := .add (.shl (.k c.tag) (.v 25)) c.bit

/-- **The local offset** from the host `h` to the cell `c`:
`(2^q·((r ⊕ r') + 8(a ⊕ a')) + (col ⊕ col')) · 2^(k+ℓ)`. -/
def offE (h c : SC) : E :=
  .shl (.add (.shl (.k ((h.role ^^^ c.role) + 8 * (h.area ^^^ c.area))) (.v 34)) (.bxor (colE h) (colE c))) (.v vKL)

variable {G : Glob}

theorem xor_lt_pow {a b n : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) : a ^^^ b < 2 ^ n := Nat.xor_lt_two_pow ha hb

theorem min_cap {x : ℕ} (h : x ≤ G.cap) : min x G.cap = x := min_eq_left h

theorem evalE_colE {s : FS} {om dt : ℕ} (hom : s.env 25 = om) (c : SC) (hc : (c.ev G s).Ok om dt)
    (hcap : 2 ^ (dt + om) ≤ G.cap) : evalE G s (colE c) = (c.ev G s).col om := by
  obtain ⟨hb, ht, -, -⟩ := hc
  simp only [SC.ev] at hb ht
  have h1 : c.tag * 2 ^ om < 2 ^ (dt + om) := by
    rw [pow_add]; exact Nat.mul_lt_mul_of_pos_right ht (Nat.two_pow_pos _)
  have h2 : c.tag * 2 ^ om + evalE G s c.bit < 2 ^ (dt + om) := by
    rw [pow_add] at h1 ⊢
    have : (c.tag + 1) * 2 ^ om ≤ 2 ^ dt * 2 ^ om := Nat.mul_le_mul_right _ ht
    nlinarith
  have hp : 1 ≤ 2 ^ om := Nat.one_le_two_pow
  have h3 : c.tag ≤ G.cap := by nlinarith
  simp only [colE, evalE, hom, Cell.col, SC.ev]
  rw [min_cap h3, min_cap (by omega), min_cap (by omega)]
  ring

theorem localOffset_eq (l : Routing.Layout) (om : ℕ) (h c : Cell) :
    localOffset l om h c = ((h.col om ^^^ c.col om) + 2 ^ l.q * ((h.role ^^^ c.role) + 8 * (h.area ^^^ c.area))) *
      2 ^ (l.k + l.ell) := by
  unfold localOffset Routing.cellMask; rw [pow_add]; ring

theorem localOffset_lt (l : Routing.Layout) (om dt : ℕ) (hq : l.q = dt + om) (h c : Cell) (hh : h.Ok om dt)
    (hc : c.Ok om dt) : localOffset l om h c < 2 ^ l.m := by
  rw [localOffset_eq]
  have h1 := Cell.col_lt hh
  have h2 := Cell.col_lt hc
  rw [← hq] at h1 h2
  have h3 : h.col om ^^^ c.col om < 2 ^ l.q := xor_lt_pow h1 h2
  have h4 : h.role ^^^ c.role < 8 := xor_lt_pow (n := 3) hh.2.2.1 hc.2.2.1
  have h5 : h.area ^^^ c.area < 2 := xor_lt_pow (n := 1) hh.2.2.2 hc.2.2.2
  have h6 : (h.col om ^^^ c.col om) + 2 ^ l.q * ((h.role ^^^ c.role) + 8 * (h.area ^^^ c.area)) < 2 ^ (l.q + 4) := by
    rw [pow_add]
    have : (h.role ^^^ c.role) + 8 * (h.area ^^^ c.area) + 1 ≤ 16 := by omega
    nlinarith
  have hm : l.m = (l.q + 4) + (l.k + l.ell) := by unfold Routing.Layout.m; ring
  have := Nat.mul_lt_mul_of_pos_right h6 (Nat.two_pow_pos (l.k + l.ell))
  rw [← pow_add] at this
  rw [hm]; exact this

theorem eE_shl' {s : FS} {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) (h : x * 2 ^ y ≤ G.cap) :
    evalE G s (.shl a b) = x * 2 ^ y := by simp only [evalE, ha, hb]; exact min_cap h

theorem eE_bxor' {s : FS} {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) (h : x ^^^ y < 2 ^ G.K) :
    evalE G s (.bxor a b) = x ^^^ y := by simp only [evalE, ha, hb]; exact Nat.mod_eq_of_lt h

theorem eE_add' {s : FS} {a b : E} {x y : ℕ} (ha : evalE G s a = x) (hb : evalE G s b = y) (h : x + y ≤ G.cap) :
    evalE G s (.add a b) = x + y := by simp only [evalE, ha, hb]; exact min_cap h

/-- **The offset expression computes the local offset** for cells inside the catalog. -/
theorem evalE_offE {l : Routing.Layout} {om dt : ℕ} {s : FS} (hl : LayV l om dt s) (h c : SC)
    (hh : (h.ev G s).Ok om dt) (hc : (c.ev G s).Ok om dt) (hcap : 2 ^ l.m ≤ G.cap) :
    evalE G s (offE h c) = localOffset l om (h.ev G s) (c.ev G s) := by
  have hm4 : 4 ≤ l.m := by unfold Routing.Layout.m; omega
  have hmq : l.m = (l.q + 4) + (l.k + l.ell) := by unfold Routing.Layout.m; ring
  have hqm : 2 ^ (dt + om) ≤ 2 ^ l.m := Nat.pow_le_pow_right (by norm_num) (by have := hl.hq; omega)
  have e1 := evalE_colE hl.hom h hh (hqm.trans hcap)
  have e2 := evalE_colE hl.hom c hc (hqm.trans hcap)
  have hK : l.m < G.K := by
    have := cap_add G
    have : 2 ^ l.m < 2 ^ G.K := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have h1 := Cell.col_lt hh
  have h2 := Cell.col_lt hc
  rw [← hl.hq] at h1 h2
  set X := (h.ev G s).col om ^^^ (c.ev G s).col om with hX
  have hx : X < 2 ^ l.q := xor_lt_pow h1 h2
  have hqK : 2 ^ l.q ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : h.role ^^^ c.role < 8 := xor_lt_pow (n := 3) hh.2.2.1 hc.2.2.1
  have h5 : h.area ^^^ c.area < 2 := xor_lt_pow (n := 1) hh.2.2.2 hc.2.2.2
  set R := (h.role ^^^ c.role) + 8 * (h.area ^^^ c.area) with hR
  have hR16 : R < 16 := by omega
  have h16 : 16 ≤ 2 ^ l.m := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm4 : 2 ^ 4 ≤ 2 ^ l.m)
  have hRq : R * 2 ^ l.q < 2 ^ (l.q + 4) := by rw [pow_add]; nlinarith
  have hq4 : 2 ^ (l.q + 4) ≤ 2 ^ l.m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : R * 2 ^ l.q + X < 2 ^ (l.q + 4) := by
    rw [pow_add] at hRq ⊢
    have : (R + 1) * 2 ^ l.q ≤ 16 * 2 ^ l.q := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hsum' : (R * 2 ^ l.q + X) * 2 ^ (l.k + l.ell) < 2 ^ l.m := by
    have := Nat.mul_lt_mul_of_pos_right hsum (Nat.two_pow_pos (l.k + l.ell))
    rw [← pow_add] at this; rw [hmq]; exact this
  have k1 : evalE G s (.k R) = R := min_cap (by omega)
  have k2 : evalE G s (.shl (.k R) (.v 34)) = R * 2 ^ l.q := eE_shl' k1 hl.hqv (by omega)
  have k3 : evalE G s (.bxor (colE h) (colE c)) = X := eE_bxor' e1 e2 (lt_of_lt_of_le hx hqK)
  have k4 : evalE G s (.add (.shl (.k R) (.v 34)) (.bxor (colE h) (colE c))) = R * 2 ^ l.q + X :=
    eE_add' k2 k3 (by omega)
  have k5 : evalE G s (offE h c) = (R * 2 ^ l.q + X) * 2 ^ (l.k + l.ell) := eE_shl' k4 hl.hkl (by omega)
  rw [k5, localOffset_eq]
  show (R * 2 ^ l.q + X) * 2 ^ (l.k + l.ell) = (X + 2 ^ l.q * ((h.role ^^^ c.role) + 8 * (h.area ^^^ c.area))) * 2 ^ (l.k + l.ell)
  rw [← hR]; ring

/-! ## Tokens of an equation -/

/-- Print the numbers of one token with tag `t` and argument `e`. -/
def tokE (t : ℕ) (e : E) : P := .seq (.num (.k t)) (.num e)

/-- The tokens of a tree read from the host `h`, in postorder. -/
def tokP (h : SC) : SX → P
  | .zero => tokE 0 (.k 0)
  | .one => tokE 0 (.k 1)
  | .var c => tokE 1 (.add (offE h c) (.k 1))
  | .add a b => .seq (tokP h a) (.seq (tokP h b) (tokE 2 (.k 0)))
  | .mul a b => .seq (tokP h a) (.seq (tokP h b) (tokE 3 (.k 0)))
  | .ite c a b => .ite c (tokP h a) (tokP h b)

theorem den_tokE (s : FS) (t : ℕ) (e : E) (ht : t ≤ G.cap) : den G s (tokE t e) = [t, evalE G s e] := by
  simp [tokE, den, evalE, min_cap ht]

/-- **The tokens of a tree** are those of its `RAMTrace` tree of cells written with local reads. -/
theorem den_tokP {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    {l : Routing.Layout} {om dt : ℕ} {s : FS} (hl : LayV l om dt s) (hcap : 2 ^ l.m + 4 ≤ G.cap) (h : SC)
    (hh : (h.ev G s).Ok om dt) :
    ∀ x : SX, (∀ c ∈ (x.ev G s).vars, c.Ok om dt) →
      den G s (tokP h x) = (Joins.exprToks mk (toRouting (localOffset l om (h.ev G s)) (x.ev G s) : Routing.Expr F)).flatMap tokNums
  | .zero, _ => by
    have h4 : 4 ≤ G.cap := le_trans (Nat.le_add_left 4 _) hcap
    rw [tokP, den_tokE s 0 _ (by omega)]
    simp [SX.ev, toRouting, Joins.exprToks, tokNums, hm0, evalE]
  | .one, _ => by
    have h4 : 4 ≤ G.cap := le_trans (Nat.le_add_left 4 _) hcap
    rw [tokP, den_tokE s 0 _ (by omega)]
    simp [SX.ev, toRouting, Joins.exprToks, tokNums, hm1, evalE, min_cap (show 1 ≤ G.cap by omega)]
  | .var c, hv => by
    have h4 : 4 ≤ G.cap := le_trans (Nat.le_add_left 4 _) hcap
    have hc : (c.ev G s).Ok om dt := hv _ (by simp [SX.ev, RAMTrace.Expr.vars])
    rw [tokP, den_tokE s 1 _ (by omega)]
    have ho := evalE_offE hl h c hh hc (by omega)
    have hlt := localOffset_lt l om dt hl.hq _ _ hh hc
    simp only [evalE, ho, min_cap (show 1 ≤ G.cap by omega), min_cap (show localOffset l om (h.ev G s) (c.ev G s) + 1 ≤ G.cap by omega)]
    simp [SX.ev, toRouting, Joins.exprToks, tokNums, Joins.varCode]
  | .add a b, hv => by
    have h4 : 4 ≤ G.cap := le_trans (Nat.le_add_left 4 _) hcap
    have ha := den_tokP mk hm0 hm1 hl hcap h hh a (fun c hc => hv c (by simp [SX.ev, RAMTrace.Expr.vars, hc]))
    have hb := den_tokP mk hm0 hm1 hl hcap h hh b (fun c hc => hv c (by simp [SX.ev, RAMTrace.Expr.vars, hc]))
    simp only [tokP, den, ha, hb, den_tokE s 2 _ (show 2 ≤ G.cap by omega)]
    simp [SX.ev, toRouting, Joins.exprToks, tokNums, evalE]
  | .mul a b, hv => by
    have h4 : 4 ≤ G.cap := le_trans (Nat.le_add_left 4 _) hcap
    have ha := den_tokP mk hm0 hm1 hl hcap h hh a (fun c hc => hv c (by simp [SX.ev, RAMTrace.Expr.vars, hc]))
    have hb := den_tokP mk hm0 hm1 hl hcap h hh b (fun c hc => hv c (by simp [SX.ev, RAMTrace.Expr.vars, hc]))
    simp only [tokP, den, ha, hb, den_tokE s 3 _ (show 3 ≤ G.cap by omega)]
    simp [SX.ev, toRouting, Joins.exprToks, tokNums, evalE]
  | .ite c a b, hv => by
    by_cases hc : evalE G s c = 0
    · have hb := den_tokP mk hm0 hm1 hl hcap h hh b (fun x hx => hv x (by simp only [SX.ev, hc, if_true]; exact hx))
      simp only [tokP, den, hc, if_true, SX.ev, hb]
    · have ha := den_tokP mk hm0 hm1 hl hcap h hh a (fun x hx => hv x (by simp only [SX.ev, hc, if_false]; exact hx))
      simp only [tokP, den, hc, if_false, SX.ev, ha]

/-! ## Guards and items -/

/-- The guard index variable. -/
def vA : Var := 47

/-- The guard code of coordinate `A` for the masks `kn`, `va`: `[kn_A]·(1 + [va_A])`. -/
def gcodeE (kn va : E) : E :=
  .mul (.md (.shr kn (.v vA)) (.k 2)) (.add (.k 1) (.md (.shr va (.v vA)) (.k 2)))

/-- The `mH` guard codes of the masks `kn`, `va`. -/
def guardP (kn va : E) : P := .loop vA (.v 35) (.num (gcodeE kn va))

theorem guardCode_pattern (m kn va : ℕ) (a : Fin m) :
    Joins.guardCode (Routing.patternMasks m kn va a) =
      kn / 2 ^ a.val % 2 * (1 + va / 2 ^ a.val % 2) := by
  simp only [Routing.patternMasks]
  rcases Nat.mod_two_eq_zero_or_one (kn / 2 ^ a.val) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one (va / 2 ^ a.val) with h2 | h2 <;>
  simp [Nat.testBit_eq_decide_div_mod_eq, h1, h2, Joins.guardCode]

theorem ofFn_eq_range_map {α : Type} (m : ℕ) (f : ℕ → α) :
    List.ofFn (fun a : Fin m => f a.val) = (List.range m).map f := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp

theorem flatMap_singleton_eq_map {α β : Type} (l : List α) (f : α → β) : l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Not the guard index. -/
def notA (x : Var) : Prop := x ≠ vA

theorem agree_setA (s : FS) (a : ℕ) : Agree notA s (s.setv vA a) :=
  ⟨fun x hx => by simp [Function.update_of_ne hx], rfl, rfl⟩

theorem den_guardP {s : FS} {m : ℕ} (kn va : E) (hkn : RdE notA kn) (hva : RdE notA va) (hm : s.env 35 = m)
    (hmN : m ≤ G.N) (hcap : 4 ≤ G.cap) :
    den G s (guardP kn va) = (List.ofFn (Routing.patternMasks m (evalE G s kn) (evalE G s va))).map Joins.guardCode := by
  have hmin : min (evalE G s (.v 35)) G.N = m := by simp only [evalE, hm]; omega
  set K := evalE G s kn
  set W := evalE G s va
  rw [guardP, den_loop s vA _ _ m hmin (fun a => [K / 2 ^ a % 2 * (1 + W / 2 ^ a % 2)])]
  · rw [flatMap_singleton_eq_map, List.map_ofFn]
    have : (Joins.guardCode ∘ Routing.patternMasks m K W) = fun a : Fin m => K / 2 ^ a.val % 2 * (1 + W / 2 ^ a.val % 2) := by
      funext a; exact guardCode_pattern m _ _ a
    rw [this, ofFn_eq_range_map m (fun a => K / 2 ^ a % 2 * (1 + W / 2 ^ a % 2))]
  · intro a ha
    have e1 : evalE G (s.setv vA a) kn = K := evalE_agree (agree_setA s a) kn hkn
    have e2 : evalE G (s.setv vA a) va = W := evalE_agree (agree_setA s a) va hva
    have b1 : K / 2 ^ a % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have b2 : W / 2 ^ a % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have c1 : min 1 G.cap = 1 := min_cap (by omega)
    have c2 : min 2 G.cap = 2 := min_cap (by omega)
    have e3 : (s.setv vA a).env vA = a := by simp
    simp only [den, gcodeE, evalE, e1, e2, e3, c1, c2]
    rw [min_cap (show 1 + W / 2 ^ a % 2 ≤ G.cap by omega)]
    have hle : K / 2 ^ a % 2 * (1 + W / 2 ^ a % 2) ≤ 1 * 2 := Nat.mul_le_mul (by omega) (by omega)
    rw [min_cap (show K / 2 ^ a % 2 * (1 + W / 2 ^ a % 2) ≤ G.cap by omega)]

/-- An item: the flag, the guard codes of `kn`, `va`, the equation's numbers, the end token. -/
def itemP (kn va : E) (body : P) : P :=
  .seq (.num (.k 1)) (.seq (guardP kn va) (.seq body (.seq (.num (.k 5)) (.num (.k 0)))))

theorem den_itemP (s : FS) (kn va : E) (body : P) (hkn : RdE notA kn) (hva : RdE notA va) {m : ℕ}
    (hm : s.env 35 = m) (hmN : m ≤ G.N) (hcap : 5 ≤ G.cap) :
    den G s (itemP kn va body) = [1] ++ (List.ofFn (Routing.patternMasks m (evalE G s kn) (evalE G s va))).map
      Joins.guardCode ++ den G s body ++ [5, 0] := by
  simp only [itemP, den]
  rw [den_guardP kn va hkn hva hm hmN (by omega)]
  simp [evalE, min_cap (show 1 ≤ G.cap by omega), min_cap (show 5 ≤ G.cap by omega)]

/-! ## Guard masks -/

/-- The known mask `cellMask l lk (2^ℓ−1) (2^q−1) 7 1` (lane bits `lk` and every non-lane coordinate). -/
def knE (lk : E) : E := .add (.v vUK) lk

/-- The value mask `cellMask l lv st col(h) role(h) area(h)`. -/
def vaE (h : SC) (lv st : E) : E :=
  .add (.shl (.add (.shl (.add (.shl (.k (h.role + 8 * h.area)) (.v 34)) (colE h)) (.v 32)) st) (.v 31)) lv

theorem upperKnown_add (l : Routing.Layout) (x : ℕ) :
    Routing.cellMask l x (2 ^ l.ell - 1) (2 ^ l.q - 1) 7 1 = upperKnown l + x := by
  unfold upperKnown Routing.cellMask; ring

theorem cellMask_lt (l : Routing.Layout) (x s c r a : ℕ) (hx : x < 2 ^ l.k) (hs : s < 2 ^ l.ell) (hc : c < 2 ^ l.q)
    (hr : r < 8) (ha : a < 2) : Routing.cellMask l x s c r a < 2 ^ l.m := by
  unfold Routing.cellMask Routing.Layout.m
  have h1 : c + 2 ^ l.q * (r + 8 * a) < 2 ^ l.q * 16 := by nlinarith
  have h2 : s + 2 ^ l.ell * (c + 2 ^ l.q * (r + 8 * a)) < 2 ^ l.ell * (2 ^ l.q * 16) := by nlinarith
  have h3 : x + 2 ^ l.k * (s + 2 ^ l.ell * (c + 2 ^ l.q * (r + 8 * a))) < 2 ^ l.k * (2 ^ l.ell * (2 ^ l.q * 16)) := by
    nlinarith
  have : 2 ^ l.k * (2 ^ l.ell * (2 ^ l.q * 16)) = 2 ^ (l.k + l.ell + l.q + 4) := by
    simp only [pow_add]; ring
  omega

theorem upperKnown_lt (l : Routing.Layout) : upperKnown l < 2 ^ l.m := by
  unfold upperKnown
  exact cellMask_lt l 0 _ _ 7 1 (Nat.two_pow_pos _) (by have := Nat.one_le_two_pow (n := l.ell); omega)
    (by have := Nat.one_le_two_pow (n := l.q); omega) (by norm_num) (by norm_num)

theorem evalE_knE {l : Routing.Layout} {om dt : ℕ} {s : FS} (hl : LayV l om dt s) (lk : E) (x : ℕ)
    (hx : evalE G s lk = x) (hxr : x < 2 ^ l.k) (hcap : 2 ^ l.m ≤ G.cap) :
    evalE G s (knE lk) = Routing.cellMask l x (2 ^ l.ell - 1) (2 ^ l.q - 1) 7 1 := by
  rw [upperKnown_add]
  have := cellMask_lt l x (2 ^ l.ell - 1) (2 ^ l.q - 1) 7 1 hxr
    (by have := Nat.one_le_two_pow (n := l.ell); omega) (by have := Nat.one_le_two_pow (n := l.q); omega)
    (by norm_num) (by norm_num)
  rw [upperKnown_add] at this
  exact eE_add' (show evalE G s (.v vUK) = upperKnown l from hl.huk) hx (by omega)

theorem evalE_vaE {l : Routing.Layout} {om dt : ℕ} {s : FS} (hl : LayV l om dt s) (h : SC) (lv st : E) (x y : ℕ)
    (hx : evalE G s lv = x) (hy : evalE G s st = y) (hxr : x < 2 ^ l.k) (hyr : y < 2 ^ l.ell)
    (hh : (h.ev G s).Ok om dt) (hcap : 2 ^ l.m ≤ G.cap) :
    evalE G s (vaE h lv st) = Routing.cellMask l x y ((h.ev G s).col om) h.role h.area := by
  have hqm : 2 ^ (dt + om) ≤ 2 ^ l.m := Nat.pow_le_pow_right (by norm_num) (by
    have := hl.hq; unfold Routing.Layout.m; omega)
  have ec := evalE_colE hl.hom h hh (hqm.trans hcap)
  have hcol := Cell.col_lt hh
  rw [← hl.hq] at hcol
  have hr : h.role < 8 := hh.2.2.1
  have ha : h.area < 2 := hh.2.2.2
  have hlt := cellMask_lt l x y ((h.ev G s).col om) h.role h.area hxr hyr hcol hr ha
  unfold Routing.cellMask at hlt ⊢
  set c := (h.ev G s).col om
  have hRA : h.role + 8 * h.area < 16 := by omega
  -- every intermediate value is at most the final one
  set RA := h.role + 8 * h.area with hRAdef
  set Z := c + 2 ^ l.q * RA with hZ
  have m1 : Z ≤ 2 ^ l.ell * Z := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have m2 : y + 2 ^ l.ell * Z ≤ 2 ^ l.k * (y + 2 ^ l.ell * Z) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have e1 : RA * 2 ^ l.q + c = Z := by rw [hZ]; ring
  have e2 : (RA * 2 ^ l.q + c) * 2 ^ l.ell = 2 ^ l.ell * Z := by rw [e1]; ring
  have e3 : ((RA * 2 ^ l.q + c) * 2 ^ l.ell + y) * 2 ^ l.k = 2 ^ l.k * (y + 2 ^ l.ell * Z) := by rw [e2]; ring
  have e4 : RA * 2 ^ l.q ≤ Z := by rw [← e1]; omega
  have b1 : RA * 2 ^ l.q ≤ x + 2 ^ l.k * (y + 2 ^ l.ell * Z) := by omega
  have b2 : RA * 2 ^ l.q + c ≤ x + 2 ^ l.k * (y + 2 ^ l.ell * Z) := by omega
  have b3 : (RA * 2 ^ l.q + c) * 2 ^ l.ell ≤ x + 2 ^ l.k * (y + 2 ^ l.ell * Z) := by omega
  have b4 : (RA * 2 ^ l.q + c) * 2 ^ l.ell + y ≤ x + 2 ^ l.k * (y + 2 ^ l.ell * Z) := by omega
  have b5 : ((RA * 2 ^ l.q + c) * 2 ^ l.ell + y) * 2 ^ l.k ≤ x + 2 ^ l.k * (y + 2 ^ l.ell * Z) := by omega
  have hm4 : 4 ≤ l.m := by unfold Routing.Layout.m; omega
  have h16 : 16 ≤ 2 ^ l.m := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm4 : 2 ^ 4 ≤ 2 ^ l.m)
  have k1 : evalE G s (.k RA) = RA := min_cap (by omega)
  have k2 := eE_shl' k1 (show evalE G s (.v 34) = l.q from hl.hqv) (show RA * 2 ^ l.q ≤ G.cap by omega)
  have k3 := eE_add' k2 ec (show RA * 2 ^ l.q + c ≤ G.cap by omega)
  have k4 := eE_shl' k3 (show evalE G s (.v 32) = l.ell from hl.hell) (show (RA * 2 ^ l.q + c) * 2 ^ l.ell ≤ G.cap by omega)
  have k5 := eE_add' k4 hy (show (RA * 2 ^ l.q + c) * 2 ^ l.ell + y ≤ G.cap by omega)
  have k6 := eE_shl' k5 (show evalE G s (.v 31) = l.k from hl.hk) (show ((RA * 2 ^ l.q + c) * 2 ^ l.ell + y) * 2 ^ l.k ≤ G.cap by omega)
  have k7 := eE_add' k6 hx (show ((RA * 2 ^ l.q + c) * 2 ^ l.ell + y) * 2 ^ l.k + x ≤ G.cap by omega)
  rw [vaE, k7, e3]; ring

/-! ## One item -/

/-- **One item**: the guard `guardAt` at the lane bits `lk`, `lv`, the stage `st` and the host `h`, and the equation
`x` read from `h`. -/
theorem den_item {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    {l : Routing.Layout} {om dt : ℕ} {s : FS} (hl : LayV l om dt s) (hcap : 2 ^ l.m + 8 ≤ G.cap) (hmN : l.m ≤ G.N)
    (h : SC) (x : SX) (lk lv st : E) (vlk vlv vst : ℕ) (hlk : evalE G s lk = vlk) (hlv : evalE G s lv = vlv)
    (hst : evalE G s st = vst) (hlkr : vlk < 2 ^ l.k) (hlvr : vlv < 2 ^ l.k) (hstr : vst < 2 ^ l.ell)
    (hh : (h.ev G s).Ok om dt) (hx : ∀ c ∈ (x.ev G s).vars, c.Ok om dt)
    (rk : RdE notA (knE lk)) (rv : RdE notA (vaE h lv st)) :
    den G s (itemP (knE lk) (vaE h lv st) (tokP h x)) =
      itemNums mk (guardAt l om vlk vlv vst (h.ev G s),
        (toRouting (localOffset l om (h.ev G s)) (x.ev G s) : Routing.Expr F)) := by
  have hp : 0 < 2 ^ l.m := Nat.two_pow_pos _
  rw [den_itemP s _ _ _ rk rv hl.hmH hmN (by omega), evalE_knE hl lk vlk hlk hlkr (by omega),
    evalE_vaE hl h lv st vlv vst hlv hst hlvr hstr hh (by omega), den_tokP mk hm0 hm1 hl (by omega) h hh x hx]
  rfl

/-! ## Variables read and depths -/

/-- A symbolic cell reads only `A`. -/
def SC.Rd (A : Var → Prop) (c : SC) : Prop := RdE A c.bit

/-- A tree reads only `A`. -/
def SX.Rd (A : Var → Prop) : SX → Prop
  | .zero | .one => True
  | .var c => c.Rd A
  | .add a b | .mul a b => SX.Rd A a ∧ SX.Rd A b
  | .ite c a b => RdE A c ∧ SX.Rd A a ∧ SX.Rd A b

theorem RdE_colE {A : Var → Prop} (h25 : A 25) (c : SC) (hc : c.Rd A) : RdE A (colE c) := ⟨⟨trivial, h25⟩, hc⟩

theorem RdE_offE {A : Var → Prop} (hA : ∀ x, layA x → A x) (h c : SC) (hh : h.Rd A) (hc : c.Rd A) :
    RdE A (offE h c) :=
  ⟨⟨⟨trivial, hA 34 (by simp [layA])⟩, RdE_colE (hA 25 (by simp [layA])) h hh,
    RdE_colE (hA 25 (by simp [layA])) c hc⟩, hA vKL (by simp [layA])⟩

theorem WF_tokP {A : Var → Prop} (hA : ∀ x, layA x → A x) (h : SC) (hh : h.Rd A) :
    ∀ x : SX, x.Rd A → WF A (tokP h x)
  | .zero, _ => ⟨trivial, trivial⟩
  | .one, _ => ⟨trivial, trivial⟩
  | .var c, hc => ⟨trivial, RdE_offE hA h c hh hc, trivial⟩
  | .add a b, hx => ⟨WF_tokP hA h hh a hx.1, WF_tokP hA h hh b hx.2, trivial, trivial⟩
  | .mul a b, hx => ⟨WF_tokP hA h hh a hx.1, WF_tokP hA h hh b hx.2, trivial, trivial⟩
  | .ite c a b, hx => ⟨hx.1, WF_tokP hA h hh a hx.2.1, WF_tokP hA h hh b hx.2.2⟩

/-- Leaf expressions of depth at most `3`. -/
def SC.Dp (c : SC) : Prop := dE c.bit ≤ 3

/-- A tree whose leaves and conditions have depth at most `3`. -/
def SX.Dp : SX → Prop
  | .zero | .one => True
  | .var c => c.Dp
  | .add a b | .mul a b => SX.Dp a ∧ SX.Dp b
  | .ite c a b => dE c ≤ 3 ∧ SX.Dp a ∧ SX.Dp b

theorem dE_colE (c : SC) (hc : c.Dp) : dE (colE c) ≤ 4 := by
  have h : dE c.bit ≤ 3 := hc
  simp only [colE, dE]; omega

theorem dE_offE (h c : SC) (hh : h.Dp) (hc : c.Dp) : dE (offE h c) ≤ 6 := by
  have := dE_colE h hh; have := dE_colE c hc
  simp only [offE, dE]; omega

theorem Ok_tokP {d : ℕ} (hd : d < 8) (h : SC) (hh : h.Dp) : ∀ x : SX, x.Dp → Ok d (tokP h x)
  | .zero, _ => ⟨⟨by simp [dE], hd⟩, by simp [dE], hd⟩
  | .one, _ => ⟨⟨by simp [dE], hd⟩, by simp [dE], hd⟩
  | .var c, hc => ⟨⟨by simp [dE], hd⟩, by have := dE_offE h c hh hc; simp only [dE]; omega, hd⟩
  | .add a b, hx => ⟨Ok_tokP hd h hh a hx.1, Ok_tokP hd h hh b hx.2, ⟨by simp [dE], hd⟩, by simp [dE], hd⟩
  | .mul a b, hx => ⟨Ok_tokP hd h hh a hx.1, Ok_tokP hd h hh b hx.2, ⟨by simp [dE], hd⟩, by simp [dE], hd⟩
  | .ite c a b, hx => ⟨by have := hx.1; omega, Ok_tokP hd h hh a hx.2.1, Ok_tokP hd h hh b hx.2.2⟩

theorem dE_vaE (h : SC) (lv st : E) (hh : h.Dp) (hlv : dE lv ≤ 3) (hst : dE st ≤ 3) : dE (vaE h lv st) ≤ 5 := by
  have := dE_colE h hh
  simp only [vaE, dE]; omega

theorem Ok_itemP {d : ℕ} (hd : d + 1 < 8) (kn va : E) (body : P) (hkn : dE kn ≤ 5) (hva : dE va ≤ 5)
    (hb : Ok d body) : Ok d (itemP kn va body) := by
  refine ⟨⟨by simp [dE], by omega⟩, ⟨by simp [dE], by omega, ⟨?_, hd⟩⟩, hb, ⟨by simp [dE], by omega⟩, by simp [dE],
    by omega⟩
  simp only [gcodeE, dE]; omega

theorem WF_itemP {A : Var → Prop} (hA35 : A 35) (hAA : ¬ A vA) (kn va : E) (body : P) (hkn : RdE A kn)
    (hva : RdE A va) (hb : WF A body) : WF A (itemP kn va body) := by
  have hw : ∀ e : E, RdE A e → RdE (fun x => A x ∨ x = vA) e := by
    intro e; induction e <;> simp_all [RdE]
  refine ⟨trivial, ⟨hA35, by decide, hAA, ?_⟩, hb, trivial, trivial⟩
  exact ⟨⟨⟨hw kn hkn, Or.inr rfl⟩, trivial⟩, trivial, ⟨hw va hva, Or.inr rfl⟩, trivial⟩

end NearCubicGates.Adapters.RAMACSP.Gen.Items
