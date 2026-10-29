import SourceAdapters.RAMACSP.GenItemsInstr

/-!
# The TIME templates (T1)–(T10) as symbolic trees

Paper: (T1)–(T10) of `def:event-trace`, placed at stage zero, role two in
machine area according to `app:affine-embedding`. The printer ranges over
the active bit indices of these fixed templates. No time-lane enumeration
is part of the generator of `lem:generator`.

`tmplT q` is the template of the time equation `q` with its bit index read from the program variable `vJ` (registers
`r` and code positions `p` are fixed in the template); `tmplT_ok`: at a state whose bit index is `tBit q` it evaluates
to the catalog cells of `timeEq (M_n) q` (`xmap (cellT K L)`). The branches of the template are exactly the case
distinctions of the equation (`ca_0 = 0`, `tc_0 = 1`, `j < τ` in (T9), the bits of code constants).
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

/-! ## Helpers -/

/-- `j − 1`. -/
def jm1E : E := .sub jE (.k 1)

/-- `β = τ − log₂ w` (`τ` in 27, `ω` in 25). -/
def betaE : E := .sub (.v 27) (.v 25)

/-- `j = 0`. -/
def j0E : E := .eq jE (.k 0)

/-- `1 + a`. -/
def complS (a : SX) : SX := .add .one a

/-- The majority `ab + ac + bc`. -/
def majS (a b c : SX) : SX := .add (.add (.mul a b) (.mul a c)) (.mul b c)

/-- A sum of a list of trees. -/
def sumS : List SX → SX
  | [] => .zero
  | a :: l => .add a (sumS l)

variable (V : Verifier) (K L : ℕ)

/-- A slot at the bit index `j`. -/
abbrev tj (sl : TSlot) : SX := tS K L sl jE

/-- A slot at bit `0`. -/
abbrev t0 (sl : TSlot) : SX := tS K L sl k0

/-- `ca_j`, `bo_j`, `tc_j`, `ac_j`, `bc_j`, `CMP_j`. -/
def caS : SX := .ite j0E .zero (tS K L (.CA 0) jm1E)
def boS : SX := .ite j0E .zero (tS K L (.BO 0) jm1E)
def tcS : SX := .ite j0E .one (tS K L (.TC 0) jm1E)
def acS : SX := .ite j0E (t0 K L .aA) (tS K L (.AC 0) jm1E)
def bcS : SX := .ite j0E (t0 K L .aB) (tS K L (.BC 0) jm1E)
def cmpS : SX := .ite j0E (.add (tS K L (.BO 0) wm1E) (t0 K L .GT)) (t0 K L .GT)

/-- `e(Q)` with `Q` read at the reference width. -/
abbrev eS (Q : MI V (refW V) → Bool) : SX := eSetS V K L Q

/-- **The TIME templates.** -/
def tmplT : TEq → SX
  | .flag r _ => .mul (t0 K L (.fl r)) (tj K L (.rg r 0))
  | .decFirst => .add (t0 K L (.o 0)) (t0 K L (.e 0))
  | .decRec p => .add (.add (t0 K L (.o p)) (t0 K L (.o (p - 1)))) (t0 K L (.e p))
  | .decExcl p => .mul (t0 K L (.e p)) (t0 K L (.o (p - 1)))
  | .decLast => .add (t0 K L (.o (codeLen V - 1))) .one
  | .decPc _ => .add (tj K L (.pc 0))
      (sxSum (fun p (_ : Desc V) => .ite (.md (.shr (.k p) jE) (.k 2)) (t0 K L (.e p)) .zero) 0 (refList V))
  | .opX _ => .add (tj K L (.X 0)) (eDotS V K L (srcXS V K L))
  | .opY _ => .add (tj K L (.Y 0)) (eDotS V K L (srcYS V K L))
  | .opXF => .add (t0 K L .XF) (eDotS V K L (srcXFS V K L))
  | .sumAD _ => .add (.add (.add (tj K L (.AD 0)) (tj K L (.X 0))) (tj K L (.Y 0))) (caS K L)
  | .carry _ => .add (tj K L (.CA 0)) (majS (tj K L (.X 0)) (tj K L (.Y 0)) (caS K L))
  | .sumSB _ => .add (.add (.add (tj K L (.SB 0)) (tj K L (.X 0))) (tj K L (.Y 0))) (boS K L)
  | .borrow _ => .add (tj K L (.BO 0))
      (.add (.mul (complS (tj K L (.X 0))) (.add (tj K L (.Y 0)) (boS K L))) (.mul (tj K L (.Y 0)) (boS K L)))
  | .andAN _ => .add (tj K L (.AN 0)) (.mul (tj K L (.X 0)) (tj K L (.Y 0)))
  | .ozFirst => .add (t0 K L (.OZ 0)) (t0 K L (.SB 0))
  | .ozRec _ => .add (tj K L (.OZ 0))
      (.add (.add (tS K L (.OZ 0) jm1E) (tj K L (.SB 0))) (.mul (tS K L (.OZ 0) jm1E) (tj K L (.SB 0))))
  | .gt => .add (t0 K L .GT) (.mul (complS (tS K L (.BO 0) wm1E)) (tS K L (.OZ 0) wm1E))
  | .rfFlag _ => .mul (t0 K L .RF) (tj K L (.RV 0))
  | .store _ => .mul (eS V K L isSt) (.add (tj K L (.MV 0)) (tj K L (.Y 0)))
  | .res _ => .add (tj K L (.Z 0)) (sumS
      [.mul (eS V K L (isAr mnKind .add)) (tj K L (.AD 0)),
       .mul (eS V K L (isAr mnKind .sub)) (tj K L (.SB 0)),
       .mul (eS V K L (isAr mnKind .and)) (tj K L (.AN 0)),
       .mul (eS V K L (isAr mnKind .cmp)) (cmpS K L),
       .mul (eS V K L isLd) (tj K L (.MV 0)),
       .mul (eS V K L isRd) (tj K L (.RV 0)),
       .ite j0E (.mul (eS V K L isEof) (t0 K L .XF)) .zero])
  | .resF => .add (t0 K L .ZF) (.mul (eS V K L isRd) (t0 K L .RF))
  | .reg r _ => .add (tj K L (.nrg r 0))
      (.add (.mul (eS V K L (writes r)) (tj K L (.Z 0))) (.mul (complS (eS V K L (writes r))) (tj K L (.rg r 0))))
  | .regF r => .add (t0 K L (.nfl r))
      (.add (.mul (eS V K L (writes r)) (t0 K L .ZF)) (.mul (complS (eS V K L (writes r))) (t0 K L (.fl r))))
  | .pcNext _ => .add (tj K L (.npc 0)) (sxSum (fun p d => pcTermS V K L p d) 0 (refList V))
  | .recAct => .add (rS .act k0) (.add (.add (eS V K L isLd) (eS V K L isSt)) (t0 K L .aA))
  | .recRgn => .add (rS .rgn k0) (t0 K L .aA)
  | .recAd _ => .add (rS .ad jE) (.add (.mul (.add (eS V K L isLd) (eS V K L isSt)) (tj K L (.X 0)))
      (.ite (.lt jE (.v 27)) (.mul (t0 K L .aA) (tj K L (.cA 0))) .zero))
  | .recPh => .add (rS .ph k0) .one
  | .recVa _ => .add (rS .va jE) (.add (.mul (.add (eS V K L isLd) (eS V K L isSt)) (tj K L (.MV 0)))
      (.mul (t0 K L .aA) (tj K L (.RV 0))))
  | .recSt => .add (rS .st k0) (eS V K L isSt)
  | .tsn _ => .add (.add (tj K L (.TSN 0)) (rS .ts jE)) (tcS K L)
  | .tc _ => .add (tj K L (.TC 0)) (.mul (rS .ts jE) (tcS K L))
  | .aA => .add (t0 K L .aA) (.mul (eS V K L isRdA) (complS (t0 K L .RF)))
  | .can _ => .add (.add (tj K L (.ncA 0)) (tj K L (.cA 0))) (acS K L)
  | .ac _ => .add (tj K L (.AC 0)) (.mul (tj K L (.cA 0)) (acS K L))
  | .aB => .add (t0 K L .aB) (.mul (eS V K L isRdB) (complS (t0 K L .RF)))
  | .cbn _ => .add (.add (tj K L (.ncB 0)) (tj K L (.cB 0))) (bcS K L)
  | .bc _ => .add (tj K L (.BC 0)) (.mul (tj K L (.cB 0)) (bcS K L))
  | .bound => .mul (t0 K L .aB) (tS K L (.cB 0) betaE)

/-! ## Correspondence -/

section Corr

variable {w n t T : ℕ} (hfit : codeLen V ≤ 2 ^ w) (τ : ℕ)

/-- The state facts of a time template: the code facts at bit index `j`, `τ` in 27, `log₂ w` in 25. -/
structure TimeV (j : ℕ) (s : FS) : Prop where
  code : CodeV V G w n t T j s
  ht : s.env 27 = τ
  hom : s.env 25 = Nat.log 2 w

theorem xmap_sum {ι κ : Type} (f : ι → κ) : ∀ l : List (Expr ι), xmap f (Expr.sum l) = Expr.sum (l.map (xmap f))
  | [] => rfl
  | a :: l => by simp [Expr.sum, xmap, xmap_sum f l]

theorem ev_sumS (s : FS) : ∀ l : List SX, SX.ev G s (sumS l) = Expr.sum (l.map (SX.ev G s))
  | [] => rfl
  | a :: l => by simp [sumS, Expr.sum, SX.ev, ev_sumS s l]

theorem xmap_ite {ι κ : Type} (f : ι → κ) (c : Prop) [Decidable c] (a b : Expr ι) :
    xmap f (if c then a else b) = if c then xmap f a else xmap f b := by split_ifs <;> rfl

theorem ev_iteBit {j : ℕ} {s : FS} (hc : CodeV V G w n t T j s) (c : ℕ) (hcc : c ≤ cB V) (a b : SX) :
    SX.ev G s (.ite (.md (.shr (.k c) jE) (.k 2)) a b) = if c.testBit j then SX.ev G s a else SX.ev G s b := by
  have h2 : 2 ≤ G.cap := by have := cB_16 V; have := hc.hcap; omega
  have e : evalE G s (.md (.shr (.k c) jE) (.k 2)) = c / 2 ^ j % 2 := by
    simp only [evalE, jE, hc.hj, min_cap h2, min_cap (hcc.trans hc.hcap)]
  simp only [SX.ev, e]
  rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ j) with h | h <;> simp [h, Nat.testBit_eq_decide_div_mod_eq]

theorem ev_decPcSum (K L : ℕ) {j : ℕ} {s : FS} (hc : CodeV V G w n t T j s) :
    SX.ev G s (sxSum (fun p (_ : Desc V) => .ite (.md (.shr (.k p) jE) (.k 2)) (t0 K L (.e p)) .zero) 0 (refList V)) =
      xmap (cellT K L) (Expr.sumCode (fun p _ => if p.testBit j then tv (.e p) else .zero) 0
        (mnCode V w n t T)) := by
  rw [ev_sxSum, xmap_sumCode, mnCode_eq, sumCode_map]
  apply sumCode_congr
  intro i d _ _ hi
  rw [refList_length] at hi
  have hb := cB_ge V
  have hcl : codeLen V ≤ clockConst V := (consts_le V).2.1
  have hpos := Nat.two_pow_pos (clockConst V)
  rw [ev_iteBit V hc i (by omega)]
  split_ifs
  · rw [ev_tS0 K L s (.e i) rfl]; rfl
  · rfl

theorem ev_pcNextSum (K L : ℕ) {j : ℕ} {s : FS} (hc : CodeV V G w n t T j s) :
    SX.ev G s (sxSum (fun p d => pcTermS V K L p d) 0 (refList V)) =
      xmap (cellT K L) (Expr.sumCode (fun p I => pcTerm (mnRam V w n t T hfit) p I j) 0 (mnCode V w n t T)) := by
  rw [ev_sxSum, xmap_sumCode, mnCode_eq, sumCode_map]
  apply sumCode_congr
  intro i d hd _ hi
  rw [refList_length] at hi
  exact ev_pcTermS V hfit K L hc i (by omega) d hd

/-- **The TIME templates evaluate to the catalog cells of the time equations.** -/
theorem tmplT_ok (q : TEq) (hq : q.Active (dims (mnRam V w n t T hfit) τ)) {s : FS}
    (hs : TimeV V (G := G) (w := w) (n := n) (t := t) (T := T) τ (tBit q) s) :
    SX.ev G s (tmplT V K L q) = xmap (cellT K L) (timeEq (mnRam V w n t T hfit) mnKind τ q) := by
  have hc := hs.code
  have h16 : 16 ≤ G.cap := by have := cB_16 V; have := hc.hcap; omega
  have hjE : evalE G s jE = tBit q := hc.hj
  have hk0 : evalE G s k0 = 0 := Nat.zero_min _
  have hjm1 : evalE G s jm1E = tBit q - 1 := by simp [jm1E, evalE, hjE, min_cap (show 1 ≤ G.cap by omega)]
  have hwm1 : evalE G s wm1E = w - 1 := by simp [wm1E, evalE, hc.hw, min_cap (show 1 ≤ G.cap by omega)]
  have hbeta : evalE G s betaE = τ - Nat.log 2 w := by simp [betaE, evalE, hs.ht, hs.hom]
  have hj0 : evalE G s j0E = if tBit q = 0 then 1 else 0 := by
    simp [j0E, evalE, hjE, Nat.zero_min]
  have hlt : evalE G s (.lt jE (.v 27)) = if tBit q < τ then 1 else 0 := by simp [evalE, hjE, hs.ht]
  have hSt := ev_eSetS V hfit (n := n) (t := t) (T := T) K L (G := G) s isSt isSt (fun d => isSt_realize V _ d)
  have hLd := ev_eSetS V hfit (n := n) (t := t) (T := T) K L (G := G) s isLd isLd (fun d => isLd_realize V _ d)
  have hRd := ev_eSetS V hfit (n := n) (t := t) (T := T) K L (G := G) s isRd isRd (fun d => isRd_realize V _ d)
  have hRdA := ev_eSetS V hfit (n := n) (t := t) (T := T) K L (G := G) s isRdA isRdA (fun d => isRdA_realize V _ d)
  have hRdB := ev_eSetS V hfit (n := n) (t := t) (T := T) K L (G := G) s isRdB isRdB (fun d => isRdB_realize V _ d)
  have hEof := ev_eSetS V hfit (n := n) (t := t) (T := T) K L (G := G) s isEof isEof (fun d => isEof_realize V _ d)
  have hAr : ∀ o, SX.ev G s (eSetS V K L (isAr mnKind o)) = xmap (cellT K L) (eSet (mnRam V w n t T hfit) (isAr mnKind o)) :=
    fun o => ev_eSetS V hfit (n := n) (t := t) (T := T) K L s _ _ (fun d => isAr_realize V mnKind o _ d)
  have hWr : ∀ r, SX.ev G s (eSetS V K L (writes r)) = xmap (cellT K L) (eSet (mnRam V w n t T hfit) (writes r)) :=
    fun r => ev_eSetS V hfit (n := n) (t := t) (T := T) K L s _ _ (fun d => writes_realize V r _ d)
  have hcodeLen : (mnRam V w n t T hfit).code.length = codeLen V := mnCode_length V w n t T
  cases q
  case decPc j =>
    have hd : SX.ev G s (sxSum (fun p (_ : Desc V) => .ite (.md (.shr (.k p) jE) (.k 2)) (t0 K L (.e p)) .zero) 0
        (refList V)) = xmap (cellT K L) (Expr.sumCode (fun p _ => if p.testBit j then tv (.e p) else .zero) 0
        (mnRam V w n t T hfit).code) := ev_decPcSum V (n := n) (t := t) (T := T) K L (j := j) (s := s) hc
    simp only [tmplT, timeEq, SX.ev, xmap, hd]
    simp [SX.ev, SC.ev, cellT, tCell, tS, tj, hjE, tBit]
  case opX j =>
    have hjw : j < w := hq
    have hd := ev_eDotS V hfit K L (G := G) s (srcXS V K L) (fun I => srcX (mnRam V w n t T hfit) I j)
      (fun d _ => ev_srcXS V hfit K L hc hjw d)
    simp [tmplT, timeEq, SX.ev, SC.ev, xmap, cellT, tCell, tS, tj, hjE, tBit, hd]
  case opY j =>
    have hjw : j < w := hq
    have hd := ev_eDotS V hfit K L (G := G) s (srcYS V K L) (fun I => srcY (mnRam V w n t T hfit) I j)
      (fun d _ => ev_srcYS V hfit K L hc hjw d)
    simp [tmplT, timeEq, SX.ev, SC.ev, xmap, cellT, tCell, tS, tj, hjE, tBit, hd]
  case opXF =>
    have hd := ev_eDotS V hfit K L (G := G) s (srcXFS V K L) (fun I => srcXF (mnRam V w n t T hfit) I)
      (fun d _ => ev_srcXFS V hfit K L hc d)
    simp [tmplT, timeEq, SX.ev, SC.ev, xmap, cellT, tCell, tS, t0, hk0, hd]
  case pcNext j =>
    have hd := ev_pcNextSum V hfit K L (G := G) (j := j) (s := s) hc
    simp [tmplT, timeEq, SX.ev, SC.ev, xmap, cellT, tCell, tS, tj, hjE, tBit, hd]
  all_goals (simp only [tBit] at hjE hjm1 hj0 hlt)
  all_goals
    simp [tmplT, timeEq, SX.ev, SC.ev, xmap, cellT, tCell, recCell, RecField.tag, tS, t0, tj, rS, hjE, hk0, hjm1,
      hwm1, hbeta, hj0, hlt, caS, boS, tcS, acS, bcS, cmpS, complS, majS, Expr.compl, Expr.maj, RAMTrace.caE,
      RAMTrace.boE, RAMTrace.tcE, RAMTrace.acE, RAMTrace.bcE, RAMTrace.cmpE, hSt, hLd, hRd, hRdA, hRdB, hEof, hAr, hWr,
      eS, blockBase, xmap_ite, mnCode_length, ev_sumS, xmap_sum, dims]
  all_goals (split_ifs <;> first | rfl | omega)

end Corr

end NearCubicGates.Adapters.RAMACSP.Gen.Items
