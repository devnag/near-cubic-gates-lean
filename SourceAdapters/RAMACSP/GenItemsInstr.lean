import SourceAdapters.RAMACSP.GenItemsTok
import SourceAdapters.RAMACSP.GenItemsCode

/-!
# The code-dependent parts of the time equations as symbolic trees

Paper: the TIME equations of `def:event-trace` and "Placement" in
`app:affine-embedding`. Each instruction template reads its operand, result,
register and control slots from the local catalog; `lem:generator` prints
these fixed templates at their active bit indices.

With the code written as the reference list (`GenItemsCode.mnCode_eq`), every code-dependent part of an equation is a
symbolic tree fixed by `V`: the decoder sums and the operand buses are sums over `refList V`, whose bits at the bit
index `j` (program variable `vJ`) are branches on `bit_j` of a constant. Each symbolic part evaluates, at bit index
`j < w`, to the catalog cells of the corresponding `RAMTrace` term (`ev_eSetS`, `ev_eDotS`, `ev_srcXS`, …).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.RAMACSP.RamCodeWord
open NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace
open NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

variable {G : Glob}

/-! ## Bit index, bits, slots -/

/-- The bit-index variable. -/
def vJ : Var := 46

/-- The bit index. -/
def jE : E := .v vJ

/-- `bit_j(c)` as a branch. -/
def bitS (c : E) : SX := .ite (.md (.shr c jE) (.k 2)) .one .zero

theorem xmap_bit {ι κ : Type} (f : ι → κ) (b : Bool) : xmap f (Expr.bit b : Expr ι) = Expr.bit b := by
  cases b <;> rfl

theorem ev_bitS {s : FS} (c : E) {j x : ℕ} (hj : s.env vJ = j) (hc : evalE G s c = x) (h2 : 2 ≤ G.cap) :
    SX.ev G s (bitS c) = Expr.bit (x.testBit j) := by
  have e : evalE G s (.md (.shr c jE) (.k 2)) = x / 2 ^ j % 2 := by
    simp only [evalE, hc, jE, hj, min_cap h2]
  simp only [bitS, SX.ev, e]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;>
    simp [h, Expr.bit, Nat.testBit_eq_decide_div_mod_eq]

/-- A time-row slot at the bit index `b` (field tag, role and area of `tCell K L sl`). -/
def tS (K L : ℕ) (sl : TSlot) (b : E) : SX :=
  .var ⟨(tCell K L sl).tag, b, (tCell K L sl).role, (tCell K L sl).area⟩

/-- A slot of the routed record at the bit index `b`. -/
def rS (f : RecField) (b : E) : SX := .var ⟨f.tag, b, 0, 0⟩

/-- The constant `0` as an expression. -/
def k0 : E := .k 0

/-- `w − 1` (`w` in program variable `26`). -/
def wm1E : E := .sub (.v 26) (.k 1)

/-! ## The code: kinds, operands, program-counter terms -/

variable (V : Verifier)

/-- The value of hole `i`: `n` (21), `t` (22), `T − 8` (`T` in 28). -/
def valE : Fin 3 → E
  | 0 => .v 21
  | 1 => .v 22
  | 2 => .sub (.v 28) (.k 8)

/-- An operand bit. -/
def opndS (K L : ℕ) : Operand (refW V) (regCount V) → SX
  | .reg r => tS K L (.rg r.val 0) jE
  | .pc => tS K L (.pc 0) jE
  | .const c => bitS (.k c.toNat)

/-- `srcX_p[j]`. -/
def srcXS (K L : ℕ) : Desc V → SX
  | .ins (.arith _ _ x _) => opndS V K L x
  | .ins (.je i _) => tS K L (.rg i.val 0) jE
  | .ins (.jne i _) => tS K L (.rg i.val 0) jE
  | .ins (.load i _) => tS K L (.rg i.val 0) jE
  | .ins (.store i _) => tS K L (.rg i.val 0) jE
  | .ins _ => .zero
  | .hole r _ => tS K L (.rg r.val 0) jE

/-- `srcY_p[j]`. -/
def srcYS (K L : ℕ) : Desc V → SX
  | .ins (.arith _ _ _ y) => opndS V K L y
  | .ins (.store _ x) => opndS V K L x
  | .ins _ => .zero
  | .hole _ i => bitS (valE i)

/-- The flag operand of `iseof`. -/
def srcXFS (K L : ℕ) : Desc V → SX
  | .ins (.iseof _ j) => tS K L (.fl j.val) k0
  | _ => .zero

/-- The term of position `p` in (T8). -/
def pcTermS (K L : ℕ) (p : ℕ) : Desc V → SX
  | .ins (.out _) => .mul (tS K L (.e p) k0) (bitS (.k p))
  | .ins (.jmp c) => .mul (tS K L (.e p) k0) (bitS (.k c))
  | .ins (.je _ c) => .add (.mul (.mul (tS K L (.e p) k0) (tS K L (.OZ 0) wm1E)) (bitS (.k (p + 1))))
      (.mul (.add (tS K L (.e p) k0) (.mul (tS K L (.e p) k0) (tS K L (.OZ 0) wm1E))) (bitS (.k c)))
  | .ins (.jne _ c) => .add (.mul (.mul (tS K L (.e p) k0) (tS K L (.OZ 0) wm1E)) (bitS (.k c)))
      (.mul (.add (tS K L (.e p) k0) (.mul (tS K L (.e p) k0) (tS K L (.OZ 0) wm1E))) (bitS (.k (p + 1))))
  | _ => .mul (tS K L (.e p) k0) (bitS (.k (p + 1)))

/-- The jump target of a descriptor (`0` if none). -/
def dtgt : Desc V → ℕ
  | .ins (.je _ c) => c
  | .ins (.jne _ c) => c
  | .ins (.jmp c) => c
  | _ => 0

/-- A bound for every constant the symbolic code terms evaluate: reference constants (`< 2^{c_V}`), positions and
jump targets. -/
def cB : ℕ := 2 ^ clockConst V + ((refList V).map (dtgt V)).sum + codeLen V + 16

theorem dtgt_le (d : Desc V) (hd : d ∈ refList V) : dtgt V d ≤ ((refList V).map (dtgt V)).sum :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨d, hd, rfl⟩)

theorem refList_length : (refList V).length = codeLen V := by
  have := mnCode_eq V 0 0 0 0
  rw [← List.length_map (f := realize V 0 ![0, 0, 0 - 8]), ← this, mnCode_length]

/-! ## Sums over the code -/

/-- A sum over a list, as `Expr.sumCode`. -/
def sxSum {α : Type} (f : ℕ → α → SX) : ℕ → List α → SX
  | _, [] => .zero
  | p, a :: l => .add (f p a) (sxSum f (p + 1) l)

theorem ev_sxSum {α : Type} (s : FS) (f : ℕ → α → SX) :
    ∀ (p : ℕ) (l : List α), SX.ev G s (sxSum f p l) = Expr.sumCode (fun p a => SX.ev G s (f p a)) p l
  | _, [] => rfl
  | p, a :: l => by simp only [sxSum, SX.ev, Expr.sumCode, ev_sxSum s f (p + 1) l]

theorem xmap_sumCode {ι κ α : Type} (g : ι → κ) (f : ℕ → α → Expr ι) :
    ∀ (p : ℕ) (l : List α), xmap g (Expr.sumCode f p l) = Expr.sumCode (fun p a => xmap g (f p a)) p l
  | _, [] => rfl
  | p, a :: l => by simp only [Expr.sumCode, xmap, xmap_sumCode g f (p + 1) l]

theorem sumCode_map {ι α β : Type} (f : ℕ → β → Expr ι) (h : α → β) :
    ∀ (p : ℕ) (l : List α), Expr.sumCode f p (l.map h) = Expr.sumCode (fun p a => f p (h a)) p l
  | _, [] => rfl
  | p, a :: l => by simp only [List.map_cons, Expr.sumCode, sumCode_map f h (p + 1) l]

theorem sumCode_congr {ι α : Type} (f g : ℕ → α → Expr ι) :
    ∀ (p : ℕ) (l : List α), (∀ i a, a ∈ l → p ≤ i → i < p + l.length → f i a = g i a) →
      Expr.sumCode f p l = Expr.sumCode g p l
  | _, [], _ => rfl
  | p, a :: l, h => by
    simp only [Expr.sumCode]
    rw [h p a (by simp) le_rfl (by simp), sumCode_congr f g (p + 1) l (fun i b hb h1 h2 =>
      h i b (by simp [hb]) (by omega) (by simp; omega))]

/-! ## Kinds of instructions do not depend on the width -/

section Kinds

variable {w : ℕ}

theorem isLd_realize (vals : Fin 3 → ℕ) (d : Desc V) :
    isLd (realize V w vals d) = isLd (realize V (refW V) ![0, 0, 0] d) := by
  cases d with
  | ins I => cases I <;> rfl
  | hole r i => rfl

theorem isSt_realize (vals : Fin 3 → ℕ) (d : Desc V) :
    isSt (realize V w vals d) = isSt (realize V (refW V) ![0, 0, 0] d) := by
  cases d with
  | ins I => cases I <;> rfl
  | hole r i => rfl

theorem isRdA_realize (vals : Fin 3 → ℕ) (d : Desc V) :
    isRdA (realize V w vals d) = isRdA (realize V (refW V) ![0, 0, 0] d) := by
  cases d with
  | ins I => cases I <;> rfl
  | hole r i => rfl

theorem isRdB_realize (vals : Fin 3 → ℕ) (d : Desc V) :
    isRdB (realize V w vals d) = isRdB (realize V (refW V) ![0, 0, 0] d) := by
  cases d with
  | ins I => cases I <;> rfl
  | hole r i => rfl

theorem isRd_realize (vals : Fin 3 → ℕ) (d : Desc V) :
    isRd (realize V w vals d) = isRd (realize V (refW V) ![0, 0, 0] d) := by
  cases d with
  | ins I => cases I <;> rfl
  | hole r i => rfl

theorem isEof_realize (vals : Fin 3 → ℕ) (d : Desc V) :
    isEof (realize V w vals d) = isEof (realize V (refW V) ![0, 0, 0] d) := by
  cases d with
  | ins I => cases I <;> rfl
  | hole r i => rfl

theorem isOut_realize (vals : Fin 3 → ℕ) (d : Desc V) :
    isOut (realize V w vals d) = isOut (realize V (refW V) ![0, 0, 0] d) := by
  cases d with
  | ins I => cases I <;> rfl
  | hole r i => rfl

theorem isAcc_realize (vals : Fin 3 → ℕ) (d : Desc V) :
    isAcc (realize V w vals d) = isAcc (realize V (refW V) ![0, 0, 0] d) := by
  cases d with
  | ins I => cases I <;> rfl
  | hole r i => rfl

theorem isAr_realize (kind : Fin 4 → AluOp) (o : AluOp) (vals : Fin 3 → ℕ) (d : Desc V) :
    isAr kind o (realize V w vals d) = isAr kind o (realize V (refW V) ![0, 0, 0] d) := by
  cases d with
  | ins I => cases I <;> rfl
  | hole r i => rfl

theorem writes_realize (r : ℕ) (vals : Fin 3 → ℕ) (d : Desc V) :
    writes r (realize V w vals d) = writes r (realize V (refW V) ![0, 0, 0] d) := by
  cases d with
  | ins I => cases I <;> rfl
  | hole r i => rfl

end Kinds

/-! ## Symbolic decoder sums and buses -/

/-- `e(Q) = Σ_{p ∈ Q} e_p` over the reference list (`Q` read at the reference width). -/
def eSetS (K L : ℕ) (Q : MI V (refW V) → Bool) : SX :=
  sxSum (fun p d => if Q (realize V (refW V) ![0, 0, 0] d) then tS K L (.e p) k0 else .zero) 0 (refList V)

/-- `Σ_p e_p · s_p` over the reference list. -/
def eDotS (K L : ℕ) (f : Desc V → SX) : SX := sxSum (fun p d => .mul (tS K L (.e p) k0) (f d)) 0 (refList V)

/-- The cell of a time-row variable. -/
def cellT (K L : ℕ) : TVar → Cell
  | .inl s => tCell K L s
  | .inr s => recCell s

theorem tRead_eq' (l : Routing.Layout) (om K L : ℕ) (h : Cell) (v : TVar) :
    tRead l om K L h v = localOffset l om h (cellT K L v) := by
  cases v <;> rfl

theorem ev_tS0 (K L : ℕ) (s : FS) (sl : TSlot) (hsl : (tCell K L sl).bit = 0) :
    SX.ev G s (tS K L sl k0) = .var (tCell K L sl) := by
  simp only [tS, SX.ev, SC.ev, k0, evalE, Nat.zero_min]
  rw [← hsl]

section Corr

variable {w n t T : ℕ} (hfit : codeLen V ≤ 2 ^ w)

theorem ev_eSetS (K L : ℕ) (s : FS) (Q : MI V w → Bool) (Q' : MI V (refW V) → Bool)
    (hQ : ∀ d, Q (realize V w ![n, t, T - 8] d) = Q' (realize V (refW V) ![0, 0, 0] d)) :
    SX.ev G s (eSetS V K L Q') = xmap (cellT K L) (eSet (mnRam V w n t T hfit) Q) := by
  unfold eSetS eSet
  rw [ev_sxSum, xmap_sumCode]
  show _ = Expr.sumCode _ 0 (mnCode V w n t T)
  rw [mnCode_eq, sumCode_map]
  apply sumCode_congr
  intro i d _ _ _
  rw [hQ d]
  split_ifs
  · rw [ev_tS0 K L s (.e i) rfl]; rfl
  · rfl

theorem ev_eDotS (K L : ℕ) (s : FS) (f : Desc V → SX) (g : MI V w → Expr TVar)
    (hf : ∀ d ∈ refList V, SX.ev G s (f d) = xmap (cellT K L) (g (realize V w ![n, t, T - 8] d))) :
    SX.ev G s (eDotS V K L f) = xmap (cellT K L) (eDot (mnRam V w n t T hfit) g) := by
  unfold eDotS eDot
  rw [ev_sxSum, xmap_sumCode]
  show _ = Expr.sumCode _ 0 (mnCode V w n t T)
  rw [mnCode_eq, sumCode_map]
  apply sumCode_congr
  intro i d hd _ _
  simp only [SX.ev, xmap, hf d hd, ev_tS0 K L s (.e i) rfl]
  rfl

/-- The state facts of the code terms: bit index `j`, the hole values `n, t, T` in `21, 22, 28`, `w` in `26`, and the
constants below the clamp. -/
structure CodeV (G : Glob) (w n t T j : ℕ) (s : FS) : Prop where
  hj : s.env vJ = j
  hn : s.env 21 = n
  ht : s.env 22 = t
  hT : s.env 28 = T
  hw : s.env 26 = w
  hcap : cB V ≤ G.cap

theorem cB_ge (V : Verifier) : 2 ^ clockConst V + codeLen V + 16 ≤ cB V := by unfold cB; omega

theorem cB_16 (V : Verifier) : 16 ≤ cB V := by have := cB_ge V; have := Nat.two_pow_pos (clockConst V); omega

theorem evalE_k_le {s : FS} {c : ℕ} (h : c ≤ G.cap) : evalE G s (.k c) = c := min_cap h

theorem ev_bitS_k {j : ℕ} {s : FS} (hc : CodeV V G w n t T j s) (c : ℕ) (hcc : c ≤ cB V) :
    SX.ev G s (bitS (.k c)) = Expr.bit (c.testBit j) :=
  ev_bitS (.k c) hc.hj (evalE_k_le (hcc.trans hc.hcap)) (by have := cB_16 V; have := hc.hcap; omega)

theorem toNat_le_cB (c : BitVec (refW V)) : c.toNat ≤ cB V := by
  have := c.isLt; have := cB_ge V; simp only [refW] at *; omega

theorem ev_opndS (K L : ℕ) {j : ℕ} {s : FS} (hc : CodeV V G w n t T j s) (hjw : j < w)
    (x : Operand (refW V) (regCount V)) :
    SX.ev G s (opndS V K L x) = xmap (cellT K L) (opnd (mnRam V w n t T hfit) (retagOp x) j) := by
  cases x with
  | reg r => simp [opndS, tS, SX.ev, SC.ev, jE, evalE, hc.hj, opnd, retagOp, xmap, cellT, tCell]
  | pc => simp [opndS, tS, SX.ev, SC.ev, jE, evalE, hc.hj, opnd, retagOp, xmap, cellT, tCell]
  | const c =>
    simp only [opndS, opnd, retagOp]
    rw [ev_bitS_k V hc _ (toNat_le_cB V c), xmap_bit, BitVec.getLsbD_ofNat]
    simp [hjw]

theorem ev_srcXS (K L : ℕ) {j : ℕ} {s : FS} (hc : CodeV V G w n t T j s) (hjw : j < w)
    (d : Desc V) :
    SX.ev G s (srcXS V K L d) = xmap (cellT K L) (srcX (mnRam V w n t T hfit) (realize V w ![n, t, T - 8] d) j) := by
  cases d with
  | ins I =>
    cases I with
    | arith op i x y => exact ev_opndS V hfit K L hc hjw x
    | je i c => simp [srcXS, srcX, realize, retag, tS, SX.ev, SC.ev, jE, evalE, hc.hj, xmap, cellT, tCell]
    | jne i c => simp [srcXS, srcX, realize, retag, tS, SX.ev, SC.ev, jE, evalE, hc.hj, xmap, cellT, tCell]
    | load i j' => simp [srcXS, srcX, realize, retag, tS, SX.ev, SC.ev, jE, evalE, hc.hj, xmap, cellT, tCell]
    | store i x => simp [srcXS, srcX, realize, retag, tS, SX.ev, SC.ev, jE, evalE, hc.hj, xmap, cellT, tCell]
    | _ => rfl
  | hole r i => simp [srcXS, srcX, realize, opnd, tS, SX.ev, SC.ev, jE, evalE, hc.hj, xmap, cellT, tCell]

theorem ev_valE {j : ℕ} {s : FS} (hc : CodeV V G w n t T j s) (i : Fin 3) :
    evalE G s (valE i) = (![n, t, T - 8] : Fin 3 → ℕ) i := by
  have h8 : 8 ≤ G.cap := by have := cB_16 V; have := hc.hcap; omega
  fin_cases i
  · simp [valE, evalE, hc.hn]
  · simp [valE, evalE, hc.ht]
  · simp [valE, evalE, hc.hT, min_cap h8]

theorem ev_srcYS (K L : ℕ) {j : ℕ} {s : FS} (hc : CodeV V G w n t T j s) (hjw : j < w)
    (d : Desc V) :
    SX.ev G s (srcYS V K L d) = xmap (cellT K L) (srcY (mnRam V w n t T hfit) (realize V w ![n, t, T - 8] d) j) := by
  cases d with
  | ins I =>
    cases I with
    | arith op i x y => exact ev_opndS V hfit K L hc hjw y
    | store i x => exact ev_opndS V hfit K L hc hjw x
    | _ => rfl
  | hole r i =>
    have h2 : 2 ≤ G.cap := by have := cB_16 V; have := hc.hcap; omega
    simp only [srcYS, srcY, realize, opnd]
    rw [ev_bitS (valE i) hc.hj (ev_valE V hc i) h2, xmap_bit, BitVec.getLsbD_ofNat]
    simp [hjw]

theorem ev_srcXFS (K L : ℕ) {j : ℕ} {s : FS} (hc : CodeV V G w n t T j s) (d : Desc V) :
    SX.ev G s (srcXFS V K L d) = xmap (cellT K L) (srcXF (mnRam V w n t T hfit) (realize V w ![n, t, T - 8] d)) := by
  cases d with
  | ins I =>
    cases I with
    | iseof i j' => simp [srcXFS, srcXF, realize, retag, tS, SX.ev, SC.ev, k0, evalE, xmap, cellT, tCell]
    | _ => rfl
  | hole r i => rfl

theorem ev_pcTermS (K L : ℕ) {j : ℕ} {s : FS} (hc : CodeV V G w n t T j s) (p : ℕ)
    (hp : p < codeLen V) (d : Desc V) (hd : d ∈ refList V) :
    SX.ev G s (pcTermS V K L p d) =
      xmap (cellT K L) (pcTerm (mnRam V w n t T hfit) p (realize V w ![n, t, T - 8] d) j) := by
  have hb := cB_ge V
  have hpos := Nat.two_pow_pos (clockConst V)
  have hcl : codeLen V ≤ clockConst V := (consts_le V).2.1
  have hp1 : p ≤ cB V := by omega
  have hp2 : p + 1 ≤ cB V := by omega
  have htg : dtgt V d ≤ cB V := by have := dtgt_le V d hd; unfold cB; omega
  have hwm : evalE G s wm1E = w - 1 := by
    simp [wm1E, evalE, hc.hw, min_cap (show 1 ≤ G.cap by have := hc.hcap; omega)]
  have hoz : SX.ev G s (tS K L (.OZ 0) wm1E) = .var (tCell K L (.OZ (w - 1))) := by
    simp only [tS, SX.ev, SC.ev, hwm]; rfl
  have he : SX.ev G s (tS K L (.e p) k0) = .var (tCell K L (.e p)) := ev_tS0 K L s _ rfl
  cases d with
  | ins I =>
    cases I with
    | out b =>
      simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, ev_bitS_k V hc p hp1, xmap, xmap_bit]; rfl
    | jmp c =>
      simp only [dtgt] at htg
      simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, ev_bitS_k V hc c htg, xmap, xmap_bit]; rfl
    | je i c =>
      simp only [dtgt] at htg
      simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, hoz, ev_bitS_k V hc c htg, ev_bitS_k V hc (p + 1) hp2,
        xmap, xmap_bit]; rfl
    | jne i c =>
      simp only [dtgt] at htg
      simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, hoz, ev_bitS_k V hc c htg, ev_bitS_k V hc (p + 1) hp2,
        xmap, xmap_bit]; rfl
    | nop => simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, ev_bitS_k V hc (p + 1) hp2, xmap, xmap_bit]; rfl
    | readA i => simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, ev_bitS_k V hc (p + 1) hp2, xmap, xmap_bit]; rfl
    | readB i => simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, ev_bitS_k V hc (p + 1) hp2, xmap, xmap_bit]; rfl
    | load i j' => simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, ev_bitS_k V hc (p + 1) hp2, xmap, xmap_bit]; rfl
    | pload i j' =>
      simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, ev_bitS_k V hc (p + 1) hp2, xmap, xmap_bit]; rfl
    | store i x => simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, ev_bitS_k V hc (p + 1) hp2, xmap, xmap_bit]; rfl
    | iseof i j' =>
      simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, ev_bitS_k V hc (p + 1) hp2, xmap, xmap_bit]; rfl
    | arith op i x y =>
      simp only [pcTermS, pcTerm, realize, retag, SX.ev, he, ev_bitS_k V hc (p + 1) hp2, xmap, xmap_bit]; rfl
  | hole r i => simp only [pcTermS, pcTerm, realize, SX.ev, he, ev_bitS_k V hc (p + 1) hp2, xmap, xmap_bit]; rfl

end Corr

end NearCubicGates.Adapters.RAMACSP.Gen.Items
