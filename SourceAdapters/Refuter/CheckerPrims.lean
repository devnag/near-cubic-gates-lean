import Proof.Gates.WordPrograms.RegArith
import SourceAdapters.Refuter.CodeTable

/-!
# Word-program primitives of the checking machine (input 7, F01 machine layer, part 3)

Platform: `L/Proof/Gates/WordPrograms/` (process.md §4: control in `WMX`, costs from `WXExec`).
Each primitive has an exact-state specification (`WXExec cap P σ τ c` with `τ` an explicit update
of `σ`), so the checker's step body is a straight chain of these facts.

* `fwdK`, `bwdK`: move a stream head by a register's value (register kept).
* `peek`: add the cell of a stream at `head + K` to a register (head returns): the checker's table
  read (proof of `lem:multitape-refuter`, "the code of `P`").
* `clr`, `dbl`, `ifClr`, `ifNotClr`: register clear, doubling, conditional clears (the flag).
* `readG`: read one guessed bit from a framed witness stream (`frame wD`, proof of `cor:framed-refuter`: "reads
  those choices from a framed witness, decoding each requested bit in constant time"); bits beyond
  the witness read as `0` and do not move the head.
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

variable {ns nr : ℕ} (cap : ℕ)

/-- Close a `WState` equality field by field. -/
macro "wst" : tactic =>
  `(tactic| (apply WState.eq <;> (try funext _) <;> simp [Function.update_apply] <;>
    (try split_ifs) <;> (try omega) <;> (try simp_all) <;> (try omega)))

/-! ## Moving a head by a register -/

def fwdK (S : Fin (ns + 1)) (K K2 : Fin nr) : WMX ns nr := repK K K2 (WMX.fwd S)

def bwdK (S : Fin (ns + 1)) (K K2 : Fin nr) : WMX ns nr := repK K K2 (WMX.bwd S)

theorem fwdK_spec {S : Fin (ns + 1)} {K K2 : Fin nr} (hKK : K ≠ K2) (σ : WState ns nr)
    (hK2 : σ.val K2 = 0) (hcap : 2 * σ.val K ≤ cap) :
    WXExec cap (fwdK S K K2) σ (σ.seth S (σ.sh S + σ.val K)) (16 * σ.val K + 3) := by
  have h := Runs.repE (cap := cap) (K := K) (K2 := K2) (body := WMX.fwd S) hKK 1 (σ.val K)
    (fun k => σ.seth S (σ.sh S + k)) hcap (fun k => by simp) (fun k => by simp)
    (fun k _ v1 v2 => by
      refine (WXExec.fwd cap S _).cast cap ?_ le_rfl
      wst)
    (by simp) (by simp [hK2])
  have e0 : σ.seth S (σ.sh S + 0) = σ := by wst
  rw [e0] at h
  exact h.mono (by ring_nf; omega)

theorem bwdK_spec {S : Fin (ns + 1)} {K K2 : Fin nr} (hKK : K ≠ K2) (σ : WState ns nr)
    (hK2 : σ.val K2 = 0) (hcap : 2 * σ.val K ≤ cap) :
    WXExec cap (bwdK S K K2) σ (σ.seth S (σ.sh S - σ.val K)) (16 * σ.val K + 3) := by
  have h := Runs.repE (cap := cap) (K := K) (K2 := K2) (body := WMX.bwd S) hKK 1 (σ.val K)
    (fun k => σ.seth S (σ.sh S - k)) hcap (fun k => by simp) (fun k => by simp)
    (fun k _ v1 v2 => by
      refine (WXExec.bwd cap S _).cast cap ?_ le_rfl
      wst)
    (by simp) (by simp [hK2])
  have e0 : σ.seth S (σ.sh S - 0) = σ := by wst
  rw [e0] at h
  exact h.mono (by ring_nf; omega)

/-! ## Reading a cell at an offset -/

/-- `RES += cell(S, head + K)`; the head returns, `K` is kept. -/
def peek (S : Fin (ns + 1)) (K K2 RES : Fin nr) : WMX ns nr :=
  .seq (fwdK S K K2) (.seq (.ifs S (WMX.inc RES) WMX.skip) (bwdK S K K2))

theorem peek_spec {S : Fin (ns + 1)} {K K2 RES : Fin nr} (hKK : K ≠ K2) (hRK : RES ≠ K)
    (hRK2 : RES ≠ K2) (σ : WState ns nr) (hK2 : σ.val K2 = 0) (hcap : 2 * σ.val K ≤ cap)
    (hR : σ.val RES < cap) :
    WXExec cap (peek S K K2 RES) σ
      (σ.setv RES (σ.val RES + (readTapeBit (σ.st S) (σ.sh S + σ.val K)).toNat))
      (32 * σ.val K + 12) := by
  have h1 := fwdK_spec cap (S := S) hKK σ hK2 hcap
  set σ1 := σ.seth S (σ.sh S + σ.val K) with hσ1
  have hb : wbit σ1 S = readTapeBit (σ.st S) (σ.sh S + σ.val K) := by simp [σ1, wbit]
  cases hc : readTapeBit (σ.st S) (σ.sh S + σ.val K)
  · have h2 : WXExec cap (.ifs S (WMX.inc RES) WMX.skip) σ1 σ1 1 :=
      WXExec.ifsF (by rw [hb, hc]) (WXExec.skip cap σ1)
    have h3 := bwdK_spec cap (S := S) hKK σ1 (by simp [σ1, hK2]) (by simp [σ1]; omega)
    refine (WXExec.seq h1 (WXExec.seq h2 h3)).cast cap ?_ (by simp [σ1]; omega)
    wst
  · have hi := WXExec.inc cap RES σ1 (by simp [σ1]; omega)
    have h2 : WXExec cap (.ifs S (WMX.inc RES) WMX.skip) σ1 (σ1.setv RES (σ1.val RES + 1)) 4 :=
      WXExec.ifsT (by rw [hb, hc]) hi
    have h3 := bwdK_spec cap (S := S) hKK (σ1.setv RES (σ1.val RES + 1))
      (by simp [σ1, Function.update_apply, Ne.symm hRK2, hK2])
      (by simp [σ1, Function.update_apply, Ne.symm hRK]; omega)
    refine (WXExec.seq h1 (WXExec.seq h2 h3)).cast cap ?_
      (by simp [σ1, Function.update_apply, Ne.symm hRK]; omega)
    wst

/-! ## Register operations -/

def clr (R : Fin nr) : WMX ns nr := .wm (WM.clear R)

theorem clr_spec (R : Fin nr) (σ : WState ns nr) (h : σ.val R ≤ cap) :
    WXExec cap (clr R) σ (σ.setv R 0) (3 * σ.val R + 1) :=
  WXExec.wm (wclear_spec (cap := cap) R (σ.val R) σ rfl h)

/-- `P := 2P` (`PT`, `TA` zero scratch). -/
def dbl (P PT TA : Fin nr) : WMX ns nr := .seq (addR P PT TA) (.seq (addR PT P TA) (clr PT))

theorem dbl_spec {P PT TA : Fin nr} (h1 : P ≠ PT) (h2 : P ≠ TA) (h3 : PT ≠ TA) (σ : WState ns nr)
    (hPT : σ.val PT = 0) (hTA : σ.val TA = 0) (hcap : 2 * σ.val P ≤ cap) :
    WXExec cap (dbl P PT TA) σ (σ.setv P (2 * σ.val P)) (39 * σ.val P + 9) := by
  have e1 := addR_spec cap (A := P) (B := PT) (T := TA) h1 h2 h3 σ hTA (by omega)
  set σ1 := σ.setv PT (σ.val PT + σ.val P) with hσ1
  have e2 := addR_spec cap (A := PT) (B := P) (T := TA) (Ne.symm h1) h3 h2 σ1
    (by simp [σ1, Function.update_apply, Ne.symm h3, hTA]) (by simp [σ1, Function.update_apply, h1, hPT]; omega)
  set σ2 := σ1.setv P (σ1.val P + σ1.val PT) with hσ2
  have e3 := clr_spec cap PT σ2 (by simp [σ2, σ1, Function.update_apply, Ne.symm h1, hPT]; omega)
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by
    simp [σ2, σ1, Function.update_apply, Ne.symm h1, h1, hPT]; omega)
  wst

/-- `F := 0` if `B ≠ 0`. -/
def ifClr (B F : Fin nr) : WMX ns nr := .ifr B (clr F) WMX.skip

theorem ifClr_spec (B F : Fin nr) (σ : WState ns nr) (hF : σ.val F ≤ 1) (hc : 1 ≤ cap) :
    WXExec cap (ifClr B F) σ (σ.setv F (if σ.val B ≠ 0 then 0 else σ.val F)) 5 := by
  by_cases hB : σ.val B = 0
  · refine (WXExec.ifrF hB (WXExec.skip cap σ)).cast cap ?_ (by omega)
    simp [hB, wsetv_same]
  · refine (WXExec.ifrT hB (clr_spec cap F σ (by omega))).cast cap ?_ (by omega)
    simp [hB]

/-- `F := 0` if `B = 0`. -/
def ifNotClr (B F : Fin nr) : WMX ns nr := .ifr B WMX.skip (clr F)

theorem ifNotClr_spec (B F : Fin nr) (σ : WState ns nr) (hF : σ.val F ≤ 1) (hc : 1 ≤ cap) :
    WXExec cap (ifNotClr B F) σ (σ.setv F (if σ.val B = 0 then 0 else σ.val F)) 5 := by
  by_cases hB : σ.val B = 0
  · refine (WXExec.ifrF hB (clr_spec cap F σ (by omega))).cast cap ?_ (by omega)
    simp [hB]
  · refine (WXExec.ifrT hB (WXExec.skip cap σ)).cast cap ?_ (by omega)
    simp [hB, wsetv_same]

/-- `F := 0` if the scanned cell of `S` is `0`. -/
def ifCellClr (S : Fin (ns + 1)) (F : Fin nr) : WMX ns nr := .ifs S WMX.skip (clr F)

theorem ifCellClr_spec (S : Fin (ns + 1)) (F : Fin nr) (σ : WState ns nr) (hF : σ.val F ≤ 1) (hc : 1 ≤ cap) :
    WXExec cap (ifCellClr S F) σ (σ.setv F (if wbit σ S = false then 0 else σ.val F)) 5 := by
  cases hB : wbit σ S
  · refine (WXExec.ifsF hB (clr_spec cap F σ (by omega))).cast cap ?_ (by omega)
    simp
  · refine (WXExec.ifsT hB (WXExec.skip cap σ)).cast cap ?_ (by omega)
    simp [wsetv_same]

/-! ## Framed words, cell by cell -/

theorem frame_length (l : List Bool) : (RepairOrdinary.frame l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [RepairOrdinary.frame, ih]; ring

/-- The marker cell `2j` of a framed word says whether bit `j` exists. -/
theorem rd_frame_even : ∀ (l : List Bool) (j : ℕ), j ≤ l.length →
    readTapeBit (RepairOrdinary.frame l) (2 * j) = decide (j < l.length)
  | [], 0, _ => rfl
  | [], _ + 1, h => by simp at h
  | b :: l, 0, _ => by simp [RepairOrdinary.frame, readTapeBit]
  | b :: l, j + 1, h => by
    have := rd_frame_even l j (by simpa using h)
    simp only [RepairOrdinary.frame, readTapeBit] at this ⊢
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ, this]
    simp

/-- The data cell `2j+1` of a framed word is bit `j`. -/
theorem rd_frame_odd : ∀ (l : List Bool) (j : ℕ), j < l.length →
    readTapeBit (RepairOrdinary.frame l) (2 * j + 1) = l.getD j false
  | [], _, h => by simp at h
  | b :: l, 0, _ => by simp [RepairOrdinary.frame, readTapeBit]
  | b :: l, j + 1, h => by
    have := rd_frame_odd l j (by simpa using h)
    simp only [RepairOrdinary.frame, readTapeBit] at this ⊢
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_cons_succ, this]

/-- The guessed bit at position `p` (bits beyond the witness are `0`). -/
def gbit (wD : List Bool) (p : ℕ) : Bool := wD.getD p false

/-- Read one guessed bit: `B += bit`, the head advances past it (two cells, counted in `WP`) if it
exists. -/
def readG (W : Fin (ns + 1)) (B WP : Fin nr) : WMX ns nr :=
  .ifs W (.seq (WMX.fwd W) (.seq (WMX.inc WP) (.seq (.ifs W (WMX.inc B) WMX.skip)
    (.seq (WMX.fwd W) (WMX.inc WP))))) WMX.skip

theorem readG_spec {W : Fin (ns + 1)} {B WP : Fin nr} (hB : B ≠ WP) (σ : WState ns nr)
    (wD : List Bool) (p : ℕ) (hst : σ.st W = RepairOrdinary.frame wD)
    (hsh : σ.sh W = 2 * min p wD.length) (hBc : σ.val B < cap) (hWc : σ.val WP + 2 < cap) :
    WXExec cap (readG W B WP) σ
      (((σ.setv B (σ.val B + (gbit wD p).toNat)).setv WP
        (σ.val WP + 2 * (min (p + 1) wD.length - min p wD.length))).seth W
          (2 * min (p + 1) wD.length)) 17 := by
  have hB' := Ne.symm hB
  by_cases hp : p < wD.length
  · have hm : min p wD.length = p := by omega
    have hm1 : min (p + 1) wD.length = p + 1 := by omega
    have hw0 : wbit σ W = true := by
      simp [wbit, hst, hsh, hm, rd_frame_even wD p (by omega), hp]
    have e1 := WXExec.fwd cap W σ
    set σ1 := σ.seth W (σ.sh W + 1) with hσ1
    have e2 := WXExec.inc cap WP σ1 (by simp [σ1]; omega)
    set σ2 := σ1.setv WP (σ1.val WP + 1) with hσ2
    have hw1 : wbit σ2 W = gbit wD p := by
      simp [σ2, σ1, wbit, hst, hsh, hm, rd_frame_odd wD p hp, gbit]
    have e4 := fun τ : WState ns nr => WXExec.fwd cap W τ
    cases hg : gbit wD p
    · have e3 : WXExec cap (.ifs W (WMX.inc B) WMX.skip) σ2 σ2 1 :=
        WXExec.ifsF (by rw [hw1, hg]) (WXExec.skip cap σ2)
      have e5 := WXExec.inc cap WP (σ2.seth W (σ2.sh W + 1)) (by simp [σ2, σ1]; omega)
      refine (WXExec.ifsT hw0 (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3
        (WXExec.seq (e4 σ2) e5))))).cast cap ?_ (by omega)
      rw [hm, hm1]
      wst
    · have e3 : WXExec cap (.ifs W (WMX.inc B) WMX.skip) σ2 (σ2.setv B (σ2.val B + 1)) 4 :=
        WXExec.ifsT (by rw [hw1, hg]) (WXExec.inc cap B σ2 (by simp [σ2, σ1, Function.update_apply, hB]; omega))
      set σ3 := σ2.setv B (σ2.val B + 1) with hσ3
      have e5 := WXExec.inc cap WP (σ3.seth W (σ3.sh W + 1))
        (by simp [σ3, σ2, σ1, Function.update_apply, hB, hB']; omega)
      refine (WXExec.ifsT hw0 (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3
        (WXExec.seq (e4 σ3) e5))))).cast cap ?_ (by omega)
      rw [hm, hm1]
      wst
  · have hm : min p wD.length = wD.length := by omega
    have hm1 : min (p + 1) wD.length = wD.length := by omega
    have hw0 : wbit σ W = false := by
      simp [wbit, hst, hsh, hm, rd_frame_even wD wD.length le_rfl]
    have hg : gbit wD p = false := by
      simp [gbit, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : wD.length ≤ p)]
    refine (WXExec.ifsF hw0 (WXExec.skip cap σ)).cast cap ?_ (by omega)
    rw [hg, hm, hm1]
    wst

end NearCubicGates.Adapters.Refuter.Mach
