import SourceAdapters.Refuter.CheckerPrims
import SourceAdapters.Refuter.FaithfulPrefix

/-!
# The checking machine's layout and its display read (input 7, F01 machine layer, part 4)

One fixed layout for the hierarchy verifier `𝒟` of proof of `lem:multitape-refuter`: 24 streams, 40 registers. The
verifier's input is stream `0` and its witness stream `1` (`Verifier.inputTapes`, framed).

`dispLoop` reads the `t` bits of one guessed display (SFM78 l.222–224, "displays") from the witness
into the display stream and accumulates the entry index `MK = Σ d_j 2^j` (`dispLoop_spec`).
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

abbrev NS : ℕ := 23
abbrev NR : ℕ := 40
abbrev St := WState NS NR
abbrev Pg := WMX NS NR

/-! ## Streams -/
@[simp] abbrev sIN : Fin (NS + 1) := 0
@[simp] abbrev sWIT : Fin (NS + 1) := 1
@[simp] abbrev sCODE : Fin (NS + 1) := 2
@[simp] abbrev sXS : Fin (NS + 1) := 3
@[simp] abbrev sYS : Fin (NS + 1) := 4
@[simp] abbrev sSIM : Fin (NS + 1) := 5
@[simp] abbrev sRS : Fin (NS + 1) := 6
@[simp] abbrev sDISP : Fin (NS + 1) := 7
@[simp] abbrev sZ : Fin (NS + 1) := 8

/-! ## Registers -/
@[simp] abbrev rT : Fin NR := 0
@[simp] abbrev rS : Fin NR := 1
@[simp] abbrev rWD : Fin NR := 2
@[simp] abbrev rEW : Fin NR := 3
@[simp] abbrev rHB : Fin NR := 4
@[simp] abbrev rAT : Fin NR := 5
@[simp] abbrev rBS : Fin NR := 6
@[simp] abbrev rSTART : Fin NR := 7
@[simp] abbrev rR0 : Fin NR := 8
@[simp] abbrev rVD : Fin NR := 9
@[simp] abbrev rI : Fin NR := 10
@[simp] abbrev rOK : Fin NR := 11
@[simp] abbrev rQ : Fin NR := 12
@[simp] abbrev rQN : Fin NR := 13
@[simp] abbrev rH : Fin NR := 14
@[simp] abbrev rMK : Fin NR := 15
@[simp] abbrev rP : Fin NR := 16
@[simp] abbrev rOFF : Fin NR := 17
@[simp] abbrev rBIT : Fin NR := 18
@[simp] abbrev rTA : Fin NR := 19
@[simp] abbrev rTB : Fin NR := 20
@[simp] abbrev rTC : Fin NR := 21
@[simp] abbrev rPT : Fin NR := 22
@[simp] abbrev rCONT : Fin NR := 23
@[simp] abbrev rWP : Fin NR := 24
@[simp] abbrev rW0 : Fin NR := 25
@[simp] abbrev rW1 : Fin NR := 26
@[simp] abbrev rM0 : Fin NR := 27
@[simp] abbrev rM1 : Fin NR := 28
@[simp] abbrev rDI : Fin NR := 29
@[simp] abbrev rA2 : Fin NR := 30
@[simp] abbrev rTD : Fin NR := 31
@[simp] abbrev rTE : Fin NR := 32
@[simp] abbrev rALL : Fin NR := 33
@[simp] abbrev rI1 : Fin NR := 34
@[simp] abbrev rWS : Fin NR := 35
@[simp] abbrev rTI : Fin NR := 36
@[simp] abbrev rTG : Fin NR := 37

/-- Unfold every layout name to its numeral (so `omega` sees one atom per register). -/
macro "unfold_layout" : tactic =>
  `(tactic| simp only [sIN, sWIT, sCODE, sXS, sYS, sSIM, sRS, sDISP, sZ, rALL, rI1, rWS, rTI, rTG, rT, rS, rWD, rEW, rHB, rAT, rBS,
    rSTART, rR0, rVD, rI, rOK, rQ, rQN, rH, rMK, rP, rOFF, rBIT, rTA, rTB, rTC, rPT, rCONT, rWP, rW0,
    rW1, rM0, rM1, rDI, rA2, rTD, rTE] at *)

/-- `omega` after unfolding the layout names. -/
macro "lomega" : tactic => `(tactic| ((try unfold_layout) <;> (try simp only [Bool.toNat, Bool.cond_eq_ite]) <;>
  (try split_ifs) <;> omega))

/-- `wst` with sums normalized to the right. -/
macro "wsta" : tactic =>
  `(tactic| (apply WState.eq <;> (try funext _) <;> simp [Function.update_apply, Nat.add_assoc] <;>
    (try split_ifs) <;> (try omega) <;> (try simp_all [Nat.add_assoc]) <;> (try omega)))

variable (cap : ℕ)

/-! ## Reading one display -/

/-- One display bit: read it, write it to the display stream, add `P` to `MK` if it is set, double
`P`. -/
def dispBit : Pg :=
  .seq (readG sWIT rBIT rWP)
  (.seq (.ifr rBIT (WMX.wr sDISP true) (WMX.wr sDISP false))
  (.seq (WMX.fwd sDISP)
  (.seq (.ifr rBIT (addR rP rMK rTA) WMX.skip)
  (.seq (clr rBIT)
  (dbl rP rPT rTA)))))

/-- The advance of the witness head, in cells, between logical positions `p` and `p'`. -/
def witMoves (wD : List Bool) (p p' : ℕ) : ℕ := 2 * (min p' wD.length - min p wD.length)

theorem witMoves_add (wD : List Bool) {p p' p'' : ℕ} (h1 : p ≤ p') (h2 : p' ≤ p'') :
    witMoves wD p p' + witMoves wD p' p'' = witMoves wD p p'' := by
  unfold witMoves
  have : min p wD.length ≤ min p' wD.length := min_le_min_right _ h1
  have : min p' wD.length ≤ min p'' wD.length := min_le_min_right _ h2
  omega

theorem dispBit_spec (σ : St) (wD : List Bool) (p : ℕ) (hst : σ.st sWIT = RepairOrdinary.frame wD)
    (hsh : σ.sh sWIT = 2 * min p wD.length) (hBIT : σ.val rBIT = 0) (hPT : σ.val rPT = 0)
    (hTA : σ.val rTA = 0) (hcap : 2 * (σ.val rMK + σ.val rP) + σ.val rWP + 4 ≤ cap) :
    WXExec cap dispBit σ
      (((((σ.setv rMK (σ.val rMK + if gbit wD p then σ.val rP else 0)).setv rP (2 * σ.val rP)).setv rWP
        (σ.val rWP + witMoves wD p (p + 1))).seth sWIT (2 * min (p + 1) wD.length)).sets sDISP
          (writeTapeBit (σ.st sDISP) (σ.sh sDISP) (gbit wD p)) |>.seth sDISP (σ.sh sDISP + 1))
      (57 * σ.val rP + 50) := by
  have e1 := readG_spec cap (W := sWIT) (B := rBIT) (WP := rWP) (by decide) σ wD p hst hsh (by lomega)
    (by lomega)
  set σ1 := ((σ.setv rBIT (σ.val rBIT + (gbit wD p).toNat)).setv rWP
    (σ.val rWP + 2 * (min (p + 1) wD.length - min p wD.length))).seth sWIT
      (2 * min (p + 1) wD.length) with hσ1
  cases hg : gbit wD p
  · have hb : σ1.val rBIT = 0 := by simp [σ1, hBIT, hg, Function.update_apply]
    have e2 : WXExec cap (.ifr rBIT (WMX.wr sDISP true) (WMX.wr sDISP false)) σ1
        (σ1.sets sDISP (writeTapeBit (σ1.st sDISP) (σ1.sh sDISP) false)) 2 :=
      WXExec.ifrF hb (WXExec.wr cap sDISP false σ1)
    set σ2 := σ1.sets sDISP (writeTapeBit (σ1.st sDISP) (σ1.sh sDISP) false) with hσ2
    have e3 := WXExec.fwd cap sDISP σ2
    set σ3 := σ2.seth sDISP (σ2.sh sDISP + 1) with hσ3
    have e4 : WXExec cap (.ifr rBIT (addR rP rMK rTA) WMX.skip) σ3 σ3 1 :=
      WXExec.ifrF (by simp [σ3, σ2, hb, Function.update_apply]) (WXExec.skip cap σ3)
    have e5 := clr_spec cap rBIT σ3 (by simp [σ3, σ2, hb, Function.update_apply])
    set σ5 := σ3.setv rBIT 0 with hσ5
    have e6 := dbl_spec cap (P := rP) (PT := rPT) (TA := rTA) (by decide) (by decide) (by decide) σ5
      (by simp [σ5, σ3, σ2, σ1, hPT, Function.update_apply]) (by simp [σ5, σ3, σ2, σ1, hTA, Function.update_apply])
      (by simp [σ5, σ3, σ2, σ1, Function.update_apply]; lomega)
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))).cast cap ?_
      (by simp [σ5, σ3, σ2, σ1, hb, Function.update_apply]; lomega)
    simp only [σ5, σ3, σ2, σ1, witMoves]
    wst
  · have hb : σ1.val rBIT = 1 := by simp [σ1, hBIT, hg, Function.update_apply]
    have e2 : WXExec cap (.ifr rBIT (WMX.wr sDISP true) (WMX.wr sDISP false)) σ1
        (σ1.sets sDISP (writeTapeBit (σ1.st sDISP) (σ1.sh sDISP) true)) 2 :=
      WXExec.ifrT (by lomega) (WXExec.wr cap sDISP true σ1)
    set σ2 := σ1.sets sDISP (writeTapeBit (σ1.st sDISP) (σ1.sh sDISP) true) with hσ2
    have e3 := WXExec.fwd cap sDISP σ2
    set σ3 := σ2.seth sDISP (σ2.sh sDISP + 1) with hσ3
    have ea := addR_spec cap (A := rP) (B := rMK) (T := rTA) (by decide) (by decide) (by decide) σ3
      (by simp [σ3, σ2, σ1, hTA, Function.update_apply]) (by simp [σ3, σ2, σ1, Function.update_apply]; lomega)
    have e4 : WXExec cap (.ifr rBIT (addR rP rMK rTA) WMX.skip) σ3
        (σ3.setv rMK (σ3.val rMK + σ3.val rP)) (18 * σ3.val rP + 4) :=
      WXExec.ifrT (by simp [σ3, σ2, hb, Function.update_apply]) ea
    set σ4 := σ3.setv rMK (σ3.val rMK + σ3.val rP) with hσ4
    have e5 := clr_spec cap rBIT σ4 (by simp [σ4, σ3, σ2, hb, Function.update_apply]; lomega)
    set σ5 := σ4.setv rBIT 0 with hσ5
    have e6 := dbl_spec cap (P := rP) (PT := rPT) (TA := rTA) (by decide) (by decide) (by decide) σ5
      (by simp [σ5, σ4, σ3, σ2, σ1, hPT, Function.update_apply]) (by simp [σ5, σ4, σ3, σ2, σ1, hTA, Function.update_apply])
      (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))).cast cap ?_
      (by simp [σ5, σ4, σ3, σ2, σ1, hb, Function.update_apply]; lomega)
    simp only [σ5, σ4, σ3, σ2, σ1, witMoves]
    wst

/-- The entry index accumulated after `k` display bits from position `p`. -/
def mkA (wD : List Bool) (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => mkA wD p k + if gbit wD (p + k) then 2 ^ k else 0

/-- The display stream after `k` display bits from position `p`, written over `D0`. -/
def dispA (wD : List Bool) (p : ℕ) (D0 : List Bool) : ℕ → List Bool
  | 0 => D0
  | k + 1 => writeTapeBit (dispA wD p D0 k) k (gbit wD (p + k))

/-- The guessed display at position `p` (`t` bits, tape `0` first). -/
def gdisp (wD : List Bool) (p t : ℕ) : Fin t → Bool := fun j => gbit wD (p + j.val)

theorem dispA_read (wD : List Bool) (p : ℕ) (D0 : List Bool) :
    ∀ k j, j < k → readTapeBit (dispA wD p D0 k) j = gbit wD (p + j)
  | 0, j, h => absurd h (Nat.not_lt_zero _)
  | k + 1, j, h => by
    simp only [dispA]
    rw [readTapeBit_writeTapeBit]
    by_cases hj : j = k
    · subst hj; simp
    · rw [if_neg hj]; exact dispA_read wD p D0 k j (by omega)

theorem mkA_eq (wD : List Bool) (p : ℕ) :
    ∀ t, mkA wD p t = maskL (List.ofFn (gdisp wD p t))
  | 0 => rfl
  | t + 1 => by
    rw [List.ofFn_succ', List.concat_eq_append, maskL_append_single, mkA, mkA_eq wD p t]
    have e : (fun i : Fin t => gdisp wD p (t + 1) i.castSucc) = gdisp wD p t := by funext i; rfl
    rw [e]
    simp [gdisp]

theorem mkA_lt (wD : List Bool) (p t : ℕ) : mkA wD p t < 2 ^ t := by
  rw [mkA_eq]; exact maskL_ofFn_lt _

/-- Read one display: `t` bits from position `p` into the display stream (head back at `0`), the
entry index `MK = Σ d_j 2^j`. -/
def dispLoop : Pg :=
  .seq (WMX.inc rP) (.seq (repK rT rTC dispBit) (.seq (bwdK sDISP rT rTB) (clr rP)))

theorem dispLoop_spec (σ : St) (wD : List Bool) (p t : ℕ) (hst : σ.st sWIT = RepairOrdinary.frame wD)
    (hsh : σ.sh sWIT = 2 * min p wD.length) (hT : σ.val rT = t) (hBIT : σ.val rBIT = 0)
    (hPT : σ.val rPT = 0) (hTA : σ.val rTA = 0) (hMK : σ.val rMK = 0) (hP : σ.val rP = 0)
    (hTC : σ.val rTC = 0) (hTB : σ.val rTB = 0) (hDh : σ.sh sDISP = 0)
    (hcap : 4 * 2 ^ t + σ.val rWP + 2 * wD.length + 2 * t + 8 ≤ cap) :
    WXExec cap dispLoop σ
      (((σ.setv rMK (mkA wD p t)).setv rWP (σ.val rWP + witMoves wD p (p + t))).seth sWIT
        (2 * min (p + t) wD.length) |>.sets sDISP (dispA wD p (σ.st sDISP) t))
      (t * (57 * 2 ^ t + 65) + 7 * t + 3 + 16 * t + 3 + 3 * 2 ^ t + 10) := by
  have hw : witMoves wD p (p + t) ≤ 2 * wD.length := by unfold witMoves; omega
  have e1 := WXExec.inc cap rP σ (by rw [hP]; lomega)
  set σ1 := σ.setv rP (σ.val rP + 1) with hσ1
  let st : ℕ → St := fun k =>
    ((((σ1.setv rMK (mkA wD p k)).setv rP (2 ^ k)).setv rWP (σ.val rWP + witMoves wD p (p + k))).seth sWIT
      (2 * min (p + k) wD.length)).sets sDISP (dispA wD p (σ.st sDISP) k) |>.seth sDISP k
  have hst0 : st 0 = σ1 := by
    simp only [st, σ1, mkA, dispA, pow_zero, witMoves, Nat.add_zero, Nat.sub_self, Nat.mul_zero]
    wst
  have hloop := Runs.repE (cap := cap) (K := rT) (K2 := rTC) (body := dispBit) (by decide)
    (57 * 2 ^ t + 50) t st (by lomega) (fun k => by simp [st, Function.update_apply])
    (fun k => by simp [st, Function.update_apply])
    (fun k hk v1 v2 => by
      have hb := dispBit_spec cap (((st k).setv rT v1).setv rTC v2) wD (p + k)
        (by simp [st, σ1, hst]) (by simp [st]) (by simp [st, σ1, Function.update_apply, hBIT])
        (by simp [st, σ1, Function.update_apply, hPT]) (by simp [st, σ1, Function.update_apply, hTA])
        (by
          simp [st, Function.update_apply]
          have := mkA_lt wD p k
          have : 2 ^ k ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hk.le
          have : witMoves wD p (p + k) ≤ 2 * wD.length := by unfold witMoves; omega
          lomega)
      refine hb.cast cap ?_ (by
        have : 2 ^ k ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hk.le
        simp [st, Function.update_apply]; lomega)
      have hwm := witMoves_add wD (Nat.le_add_right p k) (show p + k ≤ p + k + 1 by omega)
      simp only [st, mkA, dispA, pow_succ, ← add_assoc] at hwm ⊢
      wst)
    (by simp [st, σ1, Function.update_apply, hT]) (by simp [st, σ1, Function.update_apply, hTC])
  rw [hst0] at hloop
  have e3 := bwdK_spec cap (S := sDISP) (K := rT) (K2 := rTB) (by decide) (st t)
    (by simp [st, σ1, Function.update_apply, hTB]) (by simp [st, σ1, Function.update_apply, hT]; lomega)
  have e4 := clr_spec cap rP ((st t).seth sDISP ((st t).sh sDISP - (st t).val rT))
    (by simp [st, Function.update_apply]; lomega)
  have hm : t * (57 * 2 ^ t + 50 + 8) ≤ t * (57 * 2 ^ t + 65) := Nat.mul_le_mul_left _ (by omega)
  refine (WXExec.seq e1 (WXExec.seq hloop (WXExec.seq e3 e4))).cast cap ?_ (by
    simp [st, σ1, Function.update_apply, hT, hP]; lomega)
  simp only [st, σ1]
  wst

end NearCubicGates.Adapters.Refuter.Mach
