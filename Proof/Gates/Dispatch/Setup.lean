import Proof.Gates.Dispatch.Compile
import Proof.Gates.WordPrograms.RegArith
import Proof.Gates.Interfaces.WordFn

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Dispatch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {V : ℕ}

/-! ## The entry tape -/

theorem frame_length (u : List Bool) : (frame u).length = 2 * u.length + 1 := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [frame, ih]; ring

theorem frame_even (u : List Bool) (i : ℕ) : (frame u).getD (2 * i) false = decide (i < u.length) := by
  induction u generalizing i with
  | nil => cases i <;> simp [frame]
  | cons b u ih =>
    cases i with
    | zero => simp [frame]
    | succ i =>
      have := ih i
      simp only [frame, show 2 * (i + 1) = 2 * i + 1 + 1 by ring, List.getD_cons_succ, List.length_cons] at this ⊢
      simpa using this

theorem frame_odd (u : List Bool) (i : ℕ) : (frame u).getD (2 * i + 1) false = u.getD i false := by
  induction u generalizing i with
  | nil => cases i <;> simp [frame]
  | cons b u ih =>
    cases i with
    | zero => simp [frame]
    | succ i =>
      have := ih i
      simp only [frame, show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring, List.getD_cons_succ] at this ⊢
      simpa using this

section Entry
variable (cw wit : List Bool)

/-- The entry tape. -/
def inpOf : List Bool := frame (frame cw ++ frame wit)

/-- The witness start on the entry tape. -/
def p0Of : ℕ := 4 * cw.length + 2

theorem inp_call_mark (j : ℕ) (hj : j ≤ cw.length) :
    readTapeBit (inpOf cw wit) (4 * j + 1) = decide (j < cw.length) := by
  unfold readTapeBit inpOf
  rw [show 4 * j + 1 = 2 * (2 * j) + 1 by ring, frame_odd, List.getD_append _ _ _ _ (by rw [frame_length]; omega),
    frame_even]

theorem inp_call_bit (j : ℕ) (hj : j < cw.length) :
    readTapeBit (inpOf cw wit) (4 * j + 3) = cw.getD j false := by
  unfold readTapeBit inpOf
  rw [show 4 * j + 3 = 2 * (2 * j + 1) + 1 by ring, frame_odd, List.getD_append _ _ _ _ (by rw [frame_length]; omega),
    frame_odd]

theorem inp_layout : WitLayout (inpOf cw wit) (p0Of cw) wit := by
  have key : ∀ j, readTapeBit (inpOf cw wit) (p0Of cw + 4 * j + 1) = decide (j < wit.length) ∧
      readTapeBit (inpOf cw wit) (p0Of cw + 4 * j + 3) = wit.getD j false := by
    intro j
    unfold readTapeBit inpOf p0Of
    constructor
    · rw [show 4 * cw.length + 2 + 4 * j + 1 = 2 * (2 * cw.length + 1 + 2 * j) + 1 by ring, frame_odd,
        List.getD_append_right _ _ _ _ (by rw [frame_length]; omega), frame_length,
        show 2 * cw.length + 1 + 2 * j - (2 * cw.length + 1) = 2 * j by omega, frame_even]
    · rw [show 4 * cw.length + 2 + 4 * j + 3 = 2 * (2 * cw.length + 1 + 2 * j + 1) + 1 by ring, frame_odd,
        List.getD_append_right _ _ _ _ (by rw [frame_length]; omega), frame_length,
        show 2 * cw.length + 1 + 2 * j + 1 - (2 * cw.length + 1) = 2 * j + 1 by omega, frame_odd]
  refine ⟨fun j hj => ⟨by rw [(key j).1]; simp [hj], (key j).2⟩, ?_⟩
  rw [(key wit.length).1]; simp

end Entry

/-! ## Generic loops -/

section Loops
variable (cap : ℕ)

/-- Move stream `X` back by the value of register `Rg` (clearing it). -/
def rewindP (X : Fin (V + 3 + 1)) (Rg : Fin NR) : WMX (V + 3) NR := .whr Rg (.seq (WMX.dec Rg) (WMX.bwd X))

theorem rewind_spec (X : Fin (V + 3 + 1)) (Rg : Fin NR) :
    ∀ (j : ℕ) (σ : WState (V + 3) NR), σ.val Rg = j → σ.sh X = j → j ≤ cap →
      WXExec cap (rewindP X Rg) σ ((σ.setv Rg 0).seth X 0) (5 * j + 1) := by
  intro j
  induction j with
  | zero =>
    intro σ hv hs _
    have e : (σ.setv Rg 0).seth X 0 = σ := by
      refine WState.eq ?_ rfl ?_ rfl
      · funext i; by_cases hi : i = X
        · subst hi; simp [hs]
        · simp [Function.update_of_ne hi]
      · funext r; by_cases hr : r = Rg
        · subst hr; simp [hv]
        · simp [Function.update_of_ne hr]
    rw [e]; exact WXExec.whrF hv
  | succ j ih =>
    intro σ hv hs hj
    have h1 := WXExec.dec cap Rg σ (by omega)
    rw [hv, show j + 1 - 1 = j by omega] at h1
    have h2 := WXExec.bwd cap X (σ.setv Rg j)
    simp only [WState.setv_sh, hs, show j + 1 - 1 = j by omega] at h2
    have h3 := ih ((σ.setv Rg j).seth X j) (by simp) (by simp) (by omega)
    have e : ((((σ.setv Rg j).seth X j).setv Rg 0).seth X 0) = ((σ.setv Rg 0).seth X 0) := by
      refine WState.eq ?_ rfl ?_ rfl
      · funext i; by_cases hi : i = X
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      · funext r; by_cases hr : r = Rg
        · subst hr; simp
        · simp [Function.update_of_ne hr]
    rw [e] at h3
    exact WXExec.mono (WXExec.whrT (by omega) (WXExec.seq h1 h2) h3) (by omega)

/-- Clear a register. -/
def clearR (Rg : Fin NR) : WMX (V + 3) NR := .whr Rg (WMX.dec Rg)

theorem clearR_spec (Rg : Fin NR) :
    ∀ (j : ℕ) (σ : WState (V + 3) NR), σ.val Rg = j → j ≤ cap → WXExec cap (clearR Rg) σ (σ.setv Rg 0) (3 * j + 1) := by
  intro j
  induction j with
  | zero =>
    intro σ hv _
    rw [BinW.setv_same hv]; exact WXExec.whrF hv
  | succ j ih =>
    intro σ hv hj
    have h1 := WXExec.dec cap Rg σ (by omega)
    rw [hv, show j + 1 - 1 = j by omega] at h1
    have h3 := ih (σ.setv Rg j) (by simp) (by omega)
    rw [wsetv_setv] at h3
    exact WXExec.mono (WXExec.whrT (by omega) h1 h3) (by omega)

/-- Add a constant to a register. -/
def incN (Rg : Fin NR) : ℕ → WMX (V + 3) NR
  | 0 => WMX.skip
  | k + 1 => .seq (WMX.inc Rg) (incN Rg k)

theorem incN_spec (Rg : Fin NR) :
    ∀ (k : ℕ) (σ : WState (V + 3) NR), σ.val Rg + k ≤ cap →
      WXExec cap (incN Rg k) σ (σ.setv Rg (σ.val Rg + k)) (4 * k) := by
  intro k
  induction k with
  | zero => intro σ _; simp only [Nat.add_zero, wsetv_same, Nat.mul_zero]; exact WXExec.skip cap σ
  | succ k ih =>
    intro σ hk
    have h1 := WXExec.inc cap Rg σ (by omega)
    have h2 := ih (σ.setv Rg (σ.val Rg + 1)) (by simp; omega)
    simp only [WState.setv_val, Function.update_self, wsetv_setv] at h2
    rw [show σ.val Rg + 1 + k = σ.val Rg + (k + 1) by ring] at h2
    exact WXExec.mono (WXExec.seq h1 h2) (by omega)

end Loops

/-! ## Unframing the call word -/

section Unframe
variable (inp cw : List Bool) (cap : ℕ)

/-- The unframing states: entry head (and `IP`) `h`; the call stream holds the first `k` bits, head (and `CP`, `LR`)
`k`. -/
def Um (h k : ℕ) : WState (V + 3) NR :=
  ⟨fun i => if i = sIN then h else if i = sCW then k else 0,
   fun i => if i = sIN then inp else if i = sCW then cw.take k else [],
   fun r => if r = rIP then h else if r = rCP then k else if r = rLR then k else 0, false⟩

def fi : WMX (V + 3) NR := .seq (WMX.fwd sIN) (WMX.inc rIP)

theorem fi_spec (h k : ℕ) (hc : h < cap) : WXExec cap (fi (V := V)) (Um inp cw h k) (Um inp cw (h + 1) k) 5 := by
  have h1 := WXExec.fwd cap sIN (Um (V := V) inp cw h k)
  have h2 := WXExec.inc cap rIP ((Um (V := V) inp cw h k).seth sIN ((Um (V := V) inp cw h k).sh sIN + 1))
    (by simp [Um, rIP, sIN]; omega)
  have e : ((Um (V := V) inp cw h k).seth sIN ((Um (V := V) inp cw h k).sh sIN + 1)).setv rIP
      (((Um (V := V) inp cw h k).seth sIN ((Um (V := V) inp cw h k).sh sIN + 1)).val rIP + 1) = Um inp cw (h + 1) k := by
    refine WState.eq ?_ rfl ?_ rfl
    · funext i; simp only [WState.setv_sh, WState.seth_sh]
      by_cases hi : i = sIN
      · subst hi; simp [Um]
      · rw [Function.update_of_ne hi]; simp [Um, hi]
    · funext r; simp only [WState.setv_val, WState.seth_val]
      by_cases hr : r = rIP
      · subst hr; simp [Um]
      · rw [Function.update_of_ne hr]; simp [Um, hr]
  rw [e] at h2
  exact WXExec.seq' cap h1 h2 (by omega)

def wcp : WMX (V + 3) NR :=
  .seq (.ifs sIN (WMX.wr sCW true) (WMX.wr sCW false)) (.seq (WMX.fwd sCW) (.seq (WMX.inc rCP) (WMX.inc rLR)))

theorem wcp_spec (h k : ℕ) (hk : k < cw.length) (hb : readTapeBit inp h = cw.getD k false) (hc : k + 1 < cap) :
    WXExec cap (wcp (V := V)) (Um inp cw h k) (Um inp cw h (k + 1)) 12 := by
  have hwb : wbit (Um (V := V) inp cw h k) sIN = cw.getD k false := by simp [wbit, Um, hb]
  have hw : WXExec cap (.ifs sIN (WMX.wr sCW true) (WMX.wr sCW false)) (Um (V := V) inp cw h k)
      ((Um (V := V) inp cw h k).sets sCW (cw.take (k + 1))) 2 := by
    have hst : (Um (V := V) inp cw h k).st sCW = cw.take k := by simp [Um]
    have hsh : (Um (V := V) inp cw h k).sh sCW = k := by simp [Um]
    have htk : cw.take (k + 1) = cw.take k ++ [cw.getD k false] := by
      rw [List.take_add_one, List.getD_eq_getElem _ _ hk]; simp [List.getElem?_eq_getElem hk]
    have hlen : (cw.take k).length = k := by simp; omega
    have hwe : ∀ b : Bool, writeTapeBit (cw.take k) k b = cw.take k ++ [b] := by
      intro b; have := writeTapeBit_end (cw.take k) b; rwa [hlen] at this
    cases hcb : cw.getD k false
    · have := WXExec.wr cap sCW false (Um (V := V) inp cw h k)
      rw [hcb] at htk
      rw [hst, hsh, hwe, ← htk] at this
      exact WXExec.ifsF (by rw [hwb, hcb]) (WXExec.mono this (by omega))
    · have := WXExec.wr cap sCW true (Um (V := V) inp cw h k)
      rw [hcb] at htk
      rw [hst, hsh, hwe, ← htk] at this
      exact WXExec.ifsT (by rw [hwb, hcb]) (WXExec.mono this (by omega))
  set σ1 := (Um (V := V) inp cw h k).sets sCW (cw.take (k + 1))
  have h2 := WXExec.fwd cap sCW σ1
  have h3 := WXExec.inc cap rCP (σ1.seth sCW (σ1.sh sCW + 1)) (by simp [σ1, Um]; omega)
  have h4 := WXExec.inc cap rLR ((σ1.seth sCW (σ1.sh sCW + 1)).setv rCP ((σ1.seth sCW (σ1.sh sCW + 1)).val rCP + 1))
    (by simp [σ1, Um]; omega)
  have e : (((σ1.seth sCW (σ1.sh sCW + 1)).setv rCP ((σ1.seth sCW (σ1.sh sCW + 1)).val rCP + 1)).setv rLR
      (((σ1.seth sCW (σ1.sh sCW + 1)).setv rCP ((σ1.seth sCW (σ1.sh sCW + 1)).val rCP + 1)).val rLR + 1)) =
      Um inp cw h (k + 1) := by
    refine WState.eq ?_ ?_ ?_ rfl
    · funext i; simp only [WState.setv_sh, WState.seth_sh, σ1, WState.sets_sh]
      by_cases hi : i = sCW
      · subst hi; simp [Um]
      · rw [Function.update_of_ne hi]; simp [Um, hi]
    · funext i; simp only [WState.setv_st, WState.seth_st, σ1, WState.sets_st]
      by_cases hi : i = sCW
      · subst hi; simp [Um]
      · rw [Function.update_of_ne hi]; simp [Um, hi]
    · funext r; simp only [WState.setv_val, WState.seth_val, σ1, WState.sets_val]
      by_cases hr : r = rLR
      · subst hr; simp [Um]
      · rw [Function.update_of_ne hr]
        by_cases hr' : r = rCP
        · subst hr'; simp [Um]
        · rw [Function.update_of_ne hr']
          simp [Um, hr, hr']
  rw [e] at h4
  exact WXExec.seq' cap hw (WXExec.seq' cap h2 (WXExec.seq' cap h3 h4 le_rfl) le_rfl) (by omega)

def uBody : WMX (V + 3) NR := .seq fi (.seq fi (.seq wcp (.seq fi fi)))

def unframeP : WMX (V + 3) NR := .seq fi (.seq (.whs sIN uBody) fi)

theorem unframe_spec (wit : List Bool) (hc : 4 * cw.length + 6 ≤ cap) :
    WXExec cap (unframeP (V := V)) (Um (inpOf cw wit) cw 0 0) (Um (inpOf cw wit) cw (p0Of cw) cw.length)
      (40 * cw.length + 20) := by
  have loop : ∀ m k, k + m = cw.length →
      WXExec cap (.whs sIN (uBody (V := V))) (Um (inpOf cw wit) cw (4 * k + 1) k)
        (Um (inpOf cw wit) cw (4 * cw.length + 1) cw.length) (38 * m + 1) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rw [Nat.add_zero] at hk; subst hk
      refine WXExec.whsF ?_
      simp only [wbit, Um, if_true]
      rw [inp_call_mark cw wit cw.length le_rfl]; simp
    | succ m ih =>
      intro k hk
      have hkl : k < cw.length := by omega
      have b1 := fi_spec (V := V) (inpOf cw wit) cw cap (4 * k + 1) k (by omega)
      have b2 := fi_spec (V := V) (inpOf cw wit) cw cap (4 * k + 1 + 1) k (by omega)
      have b3 := wcp_spec (V := V) (inpOf cw wit) cw cap (4 * k + 1 + 1 + 1) k hkl
        (by rw [show 4 * k + 1 + 1 + 1 = 4 * k + 3 by ring]; exact inp_call_bit cw wit k hkl) (by omega)
      have b4 := fi_spec (V := V) (inpOf cw wit) cw cap (4 * k + 1 + 1 + 1) (k + 1) (by omega)
      have b5 := fi_spec (V := V) (inpOf cw wit) cw cap (4 * k + 1 + 1 + 1 + 1) (k + 1) (by omega)
      rw [show 4 * k + 1 + 1 + 1 + 1 + 1 = 4 * (k + 1) + 1 by ring] at b5
      have body := WXExec.seq' cap b1 (WXExec.seq' cap b2 (WXExec.seq' cap b3 (WXExec.seq' cap b4 b5 le_rfl) le_rfl)
        le_rfl) le_rfl
      have rest := ih (k + 1) (by omega)
      refine WXExec.mono (WXExec.whsT ?_ body rest) (by omega)
      simp only [wbit, Um, if_true]
      rw [inp_call_mark cw wit k (le_of_lt hkl)]; simp [hkl]
  have s1 := fi_spec (V := V) (inpOf cw wit) cw cap 0 0 (by omega)
  have s2 := loop cw.length 0 (by omega)
  have s3 := fi_spec (V := V) (inpOf cw wit) cw cap (4 * cw.length + 1) cw.length (by omega)
  rw [show 4 * cw.length + 1 + 1 = p0Of cw by unfold p0Of; ring] at s3
  exact WXExec.seq' cap s1 (WXExec.seq' cap s2 s3 le_rfl) (by omega)

end Unframe

/-! ## Zero words on fresh streams -/

section Init
variable (cap : ℕ)

/-- `[true, false]` repeated `k` times. -/
def zp (k : ℕ) : List Bool := (List.replicate k [true, false]).flatten

theorem zp_succ (k : ℕ) : zp (k + 1) = zp k ++ [true, false] := by
  simp [zp, List.replicate_succ']

theorem zp_length (k : ℕ) : (zp k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [zp_succ]; simp [ih]; ring

theorem binary_zero (W : ℕ) : binary W 0 = List.replicate W false := by
  induction W with
  | zero => rfl
  | succ W ih => simp [binary, ih, List.replicate_succ]

theorem frame_zero (W : ℕ) : frame (binary W 0) = zp W ++ [false] := by
  rw [binary_zero]
  induction W with
  | zero => rfl
  | succ W ih => simp [List.replicate_succ, frame, ih, zp]

def wPair (X : Fin (V + 3 + 1)) : WMX (V + 3) NR :=
  .seq (WMX.wr X true) (.seq (WMX.fwd X) (.seq (WMX.wr X false) (WMX.fwd X)))

def bPair (X : Fin (V + 3 + 1)) : WMX (V + 3) NR := .seq (WMX.bwd X) (WMX.bwd X)

/-- Write the zero word of width `σ.val rG` on a fresh stream `X`. -/
def initNum (X : Fin (V + 3 + 1)) : WMX (V + 3) NR :=
  .seq (repK rG rA2 (wPair X)) (.seq (WMX.wr X false) (repK rG rA2 (bPair X)))

theorem initNum_spec (X : Fin (V + 3 + 1)) (σ : WState (V + 3) NR) (hX : σ.st X = []) (hh : σ.sh X = 0)
    (hA2 : σ.val rA2 = 0) (hcap : 2 * σ.val rG ≤ cap) :
    WXExec cap (initNum X) σ (σ.sets X (frame (binary (σ.val rG) 0))) (50 * σ.val rG + 10) := by
  set W := σ.val rG with hW
  have hGA : rG ≠ rA2 := by decide
  -- the writing loop
  let st1 : ℕ → WState (V + 3) NR := fun k => (σ.sets X (zp k)).seth X (2 * k)
  have l1 := Runs.repE (cap := cap) (K := rG) (K2 := rA2) (body := wPair X) hGA 7 W st1 (by omega)
    (fun k => by simp [st1]) (fun k => by simp [st1])
    (by
      intro k _ v1 v2
      set τ := ((st1 k).setv rG v1).setv rA2 v2 with hτ
      have hτs : τ.st X = zp k := by simp [τ, st1]
      have hτh : τ.sh X = 2 * k := by simp [τ, st1]
      have w1 : WXExec cap (WMX.wr X true) τ (τ.sets X (zp k ++ [true])) 1 := by
        have := WXExec.wr cap X true τ
        rwa [hτs, hτh, ← zp_length, writeTapeBit_end] at this
      set τ1 := τ.sets X (zp k ++ [true]) with hτ1
      have w2 : WXExec cap (WMX.fwd X) τ1 (τ1.seth X (2 * k + 1)) 1 := by
        have := WXExec.fwd cap X τ1
        have hh : τ1.sh X = 2 * k := by simp [τ1, hτh]
        rwa [hh] at this
      set τ2 := τ1.seth X (2 * k + 1) with hτ2
      have w3 : WXExec cap (WMX.wr X false) τ2 (τ2.sets X (zp k ++ [true] ++ [false])) 1 := by
        have := WXExec.wr cap X false τ2
        have hs : τ2.st X = zp k ++ [true] := by simp [τ2, τ1]
        have hh : τ2.sh X = (zp k ++ [true]).length := by simp [τ2, zp_length]
        rwa [hs, hh, writeTapeBit_end] at this
      set τ3 := τ2.sets X (zp k ++ [true] ++ [false]) with hτ3
      have w4 : WXExec cap (WMX.fwd X) τ3 (τ3.seth X (2 * k + 2)) 1 := by
        have := WXExec.fwd cap X τ3
        have hh : τ3.sh X = 2 * k + 1 := by simp [τ3, τ2]
        rwa [hh] at this
      refine WXExec.cast cap (WXExec.seq w1 (WXExec.seq w2 (WXExec.seq w3 w4))) ?_ (by omega)
      refine WState.eq ?_ ?_ ?_ rfl
      · funext i; by_cases hi : i = X
        · subst hi; simp [τ3, τ2, τ1, τ, st1]; ring
        · simp [τ3, τ2, τ1, τ, st1, Function.update_of_ne hi]
      · funext i; by_cases hi : i = X
        · subst hi; simp [τ3, τ2, τ1, τ, st1, zp_succ]
        · simp [τ3, τ2, τ1, τ, st1, Function.update_of_ne hi]
      · rfl)
    (by simp [st1, hW]) (by simp [st1, hA2])
  have e0 : st1 0 = σ := by
    refine WState.eq ?_ ?_ rfl rfl
    · funext i; by_cases hi : i = X
      · subst hi; simp [st1, hh]
      · simp [st1, Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [st1, hX, zp]
      · simp [st1, Function.update_of_ne hi]
  rw [e0] at l1
  -- the final mark
  have m1 := WXExec.wr cap X false (st1 W)
  have hs1 : (st1 W).st X = zp W := by simp [st1]
  have hh1 : (st1 W).sh X = 2 * W := by simp [st1]
  rw [hs1, hh1, ← zp_length, writeTapeBit_end, ← frame_zero] at m1
  -- the rewinding loop
  let st2 : ℕ → WState (V + 3) NR := fun k => (σ.sets X (frame (binary W 0))).seth X (2 * (W - k))
  have l2 := Runs.repE (cap := cap) (K := rG) (K2 := rA2) (body := bPair X) hGA 3 W st2 (by omega)
    (fun k => by simp [st2]) (fun k => by simp [st2])
    (by
      intro k hk v1 v2
      set τ := ((st2 k).setv rG v1).setv rA2 v2
      have w1 := WXExec.bwd cap X τ
      have w2 := WXExec.bwd cap X (τ.seth X (τ.sh X - 1))
      refine WXExec.cast cap (WXExec.seq w1 w2) ?_ (by omega)
      refine WState.eq ?_ rfl rfl rfl
      funext i; by_cases hi : i = X
      · subst hi; simp [τ, st2]; omega
      · simp [τ, st2, Function.update_of_ne hi])
    (by simp [st2, hW]) (by simp [st2, hA2])
  have e1 : (st1 W).sets X (frame (binary W 0)) = st2 0 := by
    refine WState.eq ?_ ?_ rfl rfl
    · funext i; by_cases hi : i = X
      · subst hi; simp [st1, st2]
      · simp [st1, st2, Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [st1, st2]
      · simp [st1, st2, Function.update_of_ne hi]
  have e2 : st2 W = σ.sets X (frame (binary W 0)) := by
    refine WState.eq ?_ rfl rfl rfl
    funext i; by_cases hi : i = X
    · subst hi; simp [st2, hh]
    · simp [st2, Function.update_of_ne hi]
  rw [e1] at m1
  rw [e2] at l2
  exact WXExec.seq' cap l1 (WXExec.seq' cap m1 l2 le_rfl) (by ring_nf; omega)

/-- Streams `3 … V + 3`: the zero scratch word and the variables. -/
def numStreams (V : ℕ) : List (Fin (V + 3 + 1)) :=
  (List.range (V + 1)).map fun j => (⟨(j + 3) % (V + 4), Nat.mod_lt _ (by omega)⟩ : Fin (V + 3 + 1))

theorem mem_numStreams (i : Fin (V + 3 + 1)) : i ∈ numStreams V ↔ 3 ≤ i.val := by
  simp only [numStreams, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; simp; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · intro h; refine ⟨i.val - 3, by have := i.isLt; omega, ?_⟩
    ext; simp; rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]; omega

theorem numStreams_nodup : (numStreams V).Nodup := by
  unfold numStreams
  refine List.Nodup.map_on ?_ List.nodup_range
  intro a ha b hb e
  simp only [List.mem_range] at ha hb
  have := congrArg Fin.val e
  simp only at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

def initAll : List (Fin (V + 3 + 1)) → WMX (V + 3) NR
  | [] => WMX.skip
  | X :: xs => .seq (initNum X) (initAll xs)

/-- `σ` with the zero word on every stream of `xs`. -/
def setZ (σ : WState (V + 3) NR) (W : ℕ) (xs : List (Fin (V + 3 + 1))) : WState (V + 3) NR :=
  ⟨σ.sh, fun i => if i ∈ xs then frame (binary W 0) else σ.st i, σ.val, σ.cell⟩

theorem initAll_spec (W : ℕ) (hcap : 2 * W ≤ cap) :
    ∀ (xs : List (Fin (V + 3 + 1))) (σ : WState (V + 3) NR), xs.Nodup → (∀ X ∈ xs, σ.st X = [] ∧ σ.sh X = 0) →
      σ.val rG = W → σ.val rA2 = 0 →
      WXExec cap (initAll xs) σ (setZ σ W xs) (xs.length * (50 * W + 11)) := by
  intro xs
  induction xs with
  | nil =>
    intro σ _ _ _ _
    have e : setZ σ W [] = σ := WState.eq rfl (by funext i; simp [setZ]) rfl rfl
    rw [e]; exact WXExec.mono (WXExec.skip cap σ) (by simp)
  | cons X xs ih =>
    intro σ hnd hf hW hA2
    have hX := hf X (by simp)
    have h1 := initNum_spec cap X σ hX.1 hX.2 hA2 (by omega)
    rw [hW] at h1
    have hnd' := List.nodup_cons.mp hnd
    have h2 := ih (σ.sets X (frame (binary W 0))) hnd'.2
      (fun Y hY => by
        have hYX : Y ≠ X := fun e => hnd'.1 (e ▸ hY)
        simp [Function.update_of_ne hYX, hf Y (by simp [hY])])
      (by simp [hW]) (by simp [hA2])
    have e : setZ (σ.sets X (frame (binary W 0))) W xs = setZ σ W (X :: xs) := by
      refine WState.eq rfl ?_ rfl rfl
      funext i; simp only [setZ, WState.sets_st, List.mem_cons]
      by_cases hi : i = X
      · subst hi; simp
      · simp [hi]
    rw [e] at h2
    refine WXExec.seq' cap h1 h2 ?_
    simp only [List.length_cons]; ring_nf; omega

end Init

/-! ## The whole program -/

section Whole

theorem OpEx.wq_le {C : Ctx} {o : Op V} {a b : DS V} (h : OpEx C o a b) : b.wq ≤ a.wq + 1 := by
  cases h <;> simp [DS.set] <;> split_ifs <;> omega

theorem Ex.wq_le {C : Ctx} {s : St V} {a b : DS V} {n : ℕ} (h : Ex C s a b n) : b.wq ≤ a.wq + n := by
  induction h with
  | op h => exact h.wq_le
  | seq _ _ ih1 ih2 => omega
  | iteT _ _ _ ih => omega
  | iteF _ _ _ ih => omega
  | loopF _ _ => omega
  | loopT _ _ _ _ ih1 ih2 => omega
  | mono _ hnm ih => omega

/-- The width: `(|cw| + K)^4`. -/
def wdOf (K L : ℕ) : ℕ := (L + K) ^ 4

/-- The run's fixed data. -/
def ctxOf (K : ℕ) (cw wit : List Bool) : Ctx := ⟨wdOf K cw.length, cw, wit⟩

/-- The initial language state. -/
def a0 : DS V := ⟨fun _ => 0, 0, 0, []⟩

/-- The width into register `G`. -/
def widthP (K : ℕ) : WMX (V + 3) NR :=
  .seq (incN rLR K) (.seq (addR rLR rG rT2) (.seq (mulR rLR rA2 rG rWR rT2)
    (.seq (clearR rLR) (.seq (clearR rG) (.seq (addR rWR rLR rT2) (.seq (mulR rWR rA2 rLR rG rT2)
      (.seq (clearR rWR) (clearR rLR))))))))

def setupP (K : ℕ) : WMX (V + 3) NR :=
  .seq unframeP (.seq (rewindP sCW rCP) (.seq (widthP K) (.seq (initAll (numStreams V)) (clearR rG))))

def teardownP : WMX (V + 3) NR :=
  .seq (rewindP sOUT rOP) (.seq (rewindP sIN rIP) (rewindP sCW rCP))

/-- **The whole program.** -/
def prog (K : ℕ) (main : St V) : WMX (V + 3) NR := .seq (setupP K) (.seq (comp main) teardownP)

/-- Register capacity of a run. -/
def capOf (K : ℕ) (cw wit : List Bool) (n : ℕ) : ℕ := 2 * wdOf K cw.length + 4 * (cw.length + wit.length) + n + 100

/-- The set-up's cost bound. -/
def setupCost (V K L : ℕ) : ℕ := 200 * (V + 2) * (L + K + 1) ^ 4

/-- **The step budget** (independent of the witness). -/
def budgetOf (V K L n : ℕ) : ℕ := setupCost V K L + n * KC (wdOf K L) + 30 * n + 50 * L + 300

/-! ### The width, on registers only -/

/-- A state with its registers replaced. -/
def regs (σ : WState (V + 3) NR) (f : Fin NR → ℕ) : WState (V + 3) NR := ⟨σ.sh, σ.st, f, σ.cell⟩

/-- The set-up registers: `IP`, `LR`, `G`, `WR`; all others `0`. -/
def rv (p lr g wr : ℕ) : Fin NR → ℕ :=
  fun r => if r = rIP then p else if r = rLR then lr else if r = rG then g else if r = rWR then wr else 0

theorem regs_setv (σ : WState (V + 3) NR) (f : Fin NR → ℕ) (r : Fin NR) (v : ℕ) :
    (regs σ f).setv r v = regs σ (Function.update f r v) := rfl

theorem rv_LR (p lr g wr v : ℕ) : Function.update (rv p lr g wr) rLR v = rv p v g wr := by
  funext r; by_cases h : r = rLR
  · subst h; simp [rv]
  · rw [Function.update_of_ne h]; simp only [rv, if_neg h]

theorem rv_G (p lr g wr v : ℕ) : Function.update (rv p lr g wr) rG v = rv p lr v wr := by
  funext r; by_cases h : r = rG
  · subst h; simp [rv]
  · rw [Function.update_of_ne h]; simp only [rv, if_neg h]

theorem rv_WR (p lr g wr v : ℕ) : Function.update (rv p lr g wr) rWR v = rv p lr g v := by
  funext r; by_cases h : r = rWR
  · subst h; simp [rv]
  · rw [Function.update_of_ne h]; simp only [rv, if_neg h]

/-- The width program's cost. -/
def widthCost (K X : ℕ) : ℕ :=
  4 * K + 1 + (18 * X + 3 + 1 + (X * (18 * X + 3 + 8) + 7 * X + 3 + 1 + (3 * X + 1 + 1 + (3 * X + 1 + 1 +
    (18 * (X * X) + 3 + 1 + (X * X * (18 * (X * X) + 3 + 8) + 7 * (X * X) + 3 + 1 + (3 * (X * X) + 1 + 1 +
      (3 * (X * X) + 1))))))))

theorem width_spec (cap : ℕ) (σ : WState (V + 3) NR) (P L K : ℕ) (hK : 1 ≤ K)
    (hcap : 2 * (L + K) ^ 4 + 10 ≤ cap) :
    WXExec cap (widthP K) (regs σ (rv P L 0 0)) (regs σ (rv P 0 ((L + K) ^ 4) 0)) (widthCost K (L + K)) := by
  have hX1 : 1 ≤ L + K := by omega
  have hXX : L + K ≤ (L + K) * (L + K) := by nlinarith
  have hW4 : (L + K) * (L + K) * ((L + K) * (L + K)) = (L + K) ^ 4 := by ring
  have hXXW : (L + K) * (L + K) ≤ (L + K) ^ 4 := by rw [← hW4]; nlinarith
  have w1 := incN_spec (V := V) cap rLR K (regs σ (rv P L 0 0)) (by simp [regs, rv]; omega)
  have e1 : (regs σ (rv P L 0 0)).val rLR = L := by simp [regs, rv]
  rw [e1, regs_setv, rv_LR] at w1
  have w2 := addR_spec cap (A := rLR) (B := rG) (T := rT2) (by decide) (by decide) (by decide)
    (regs σ (rv P (L + K) 0 0)) (by simp [regs, rv]) (by simp [regs, rv]; omega)
  simp only [regs_setv, rv_G] at w2
  have e2 : (regs σ (rv P (L + K) 0 0)).val rG + (regs σ (rv P (L + K) 0 0)).val rLR = L + K := by simp [regs, rv]
  have e2' : (regs σ (rv P (L + K) 0 0)).val rLR = L + K := by simp [regs, rv]
  rw [e2, e2'] at w2
  have w3 := mulR_spec cap (A := rLR) (A2 := rA2) (B := rG) (C := rWR) (T := rT2) (by decide)
    (regs σ (rv P (L + K) (L + K) 0)) (by simp [regs, rv]) (by simp [regs, rv]) (by simp [regs, rv]; omega)
    (by simp [regs, rv]; omega)
  simp only [regs_setv, rv_WR] at w3
  have e3 : (regs σ (rv P (L + K) (L + K) 0)).val rWR + (regs σ (rv P (L + K) (L + K) 0)).val rLR *
      (regs σ (rv P (L + K) (L + K) 0)).val rG = (L + K) * (L + K) := by simp [regs, rv]
  have e3' : (regs σ (rv P (L + K) (L + K) 0)).val rLR = L + K := by simp [regs, rv]
  have e3'' : (regs σ (rv P (L + K) (L + K) 0)).val rG = L + K := by simp [regs, rv]
  rw [e3, e3', e3''] at w3
  have w4 := clearR_spec (V := V) cap rLR (L + K) (regs σ (rv P (L + K) (L + K) ((L + K) * (L + K))))
    (by simp [regs, rv]) (by omega)
  simp only [regs_setv, rv_LR] at w4
  have w5 := clearR_spec (V := V) cap rG (L + K) (regs σ (rv P 0 (L + K) ((L + K) * (L + K))))
    (by simp [regs, rv]) (by omega)
  simp only [regs_setv, rv_G] at w5
  have w6 := addR_spec cap (A := rWR) (B := rLR) (T := rT2) (by decide) (by decide) (by decide)
    (regs σ (rv P 0 0 ((L + K) * (L + K)))) (by simp [regs, rv]) (by simp [regs, rv]; omega)
  simp only [regs_setv, rv_LR] at w6
  have e6 : (regs σ (rv P 0 0 ((L + K) * (L + K)))).val rLR + (regs σ (rv P 0 0 ((L + K) * (L + K)))).val rWR =
      (L + K) * (L + K) := by simp [regs, rv]
  have e6' : (regs σ (rv P 0 0 ((L + K) * (L + K)))).val rWR = (L + K) * (L + K) := by simp [regs, rv]
  rw [e6, e6'] at w6
  have w7 := mulR_spec cap (A := rWR) (A2 := rA2) (B := rLR) (C := rG) (T := rT2) (by decide)
    (regs σ (rv P ((L + K) * (L + K)) 0 ((L + K) * (L + K)))) (by simp [regs, rv]) (by simp [regs, rv])
    (by simp [regs, rv]; omega) (by simp [regs, rv]; omega)
  simp only [regs_setv, rv_G] at w7
  have e7 : (regs σ (rv P ((L + K) * (L + K)) 0 ((L + K) * (L + K)))).val rG +
      (regs σ (rv P ((L + K) * (L + K)) 0 ((L + K) * (L + K)))).val rWR *
      (regs σ (rv P ((L + K) * (L + K)) 0 ((L + K) * (L + K)))).val rLR = (L + K) ^ 4 := by
    simp [regs, rv]; exact hW4
  have e7' : (regs σ (rv P ((L + K) * (L + K)) 0 ((L + K) * (L + K)))).val rWR = (L + K) * (L + K) := by
    simp [regs, rv]
  have e7'' : (regs σ (rv P ((L + K) * (L + K)) 0 ((L + K) * (L + K)))).val rLR = (L + K) * (L + K) := by
    simp [regs, rv]
  rw [e7, e7', e7''] at w7
  have w8 := clearR_spec (V := V) cap rWR ((L + K) * (L + K))
    (regs σ (rv P ((L + K) * (L + K)) ((L + K) ^ 4) ((L + K) * (L + K)))) (by simp [regs, rv]) (by omega)
  simp only [regs_setv, rv_WR] at w8
  have w9 := clearR_spec (V := V) cap rLR ((L + K) * (L + K))
    (regs σ (rv P ((L + K) * (L + K)) ((L + K) ^ 4) 0)) (by simp [regs, rv]) (by omega)
  simp only [regs_setv, rv_LR] at w9
  refine WXExec.mono (WXExec.seq w1 (WXExec.seq w2 (WXExec.seq w3 (WXExec.seq w4 (WXExec.seq w5 (WXExec.seq w6
    (WXExec.seq w7 (WXExec.seq w8 w9)))))))) (le_of_eq ?_)
  unfold widthCost; ring

theorem widthCost_le (K X : ℕ) (hK : K ≤ X) : widthCost K X ≤ 100 * (X + 1) ^ 4 := by
  unfold widthCost
  have h1 : X ≤ (X + 1) ^ 4 := by nlinarith [pow_le_pow_left₀ (Nat.zero_le X) (Nat.le_succ X) 4]
  have h2 : X * X ≤ (X + 1) ^ 4 := by nlinarith [pow_le_pow_left₀ (Nat.zero_le X) (Nat.le_succ X) 4]
  have h4 : X * X * (X * X) ≤ (X + 1) ^ 4 := by nlinarith [pow_le_pow_left₀ (Nat.zero_le X) (Nat.le_succ X) 4]
  have h0 : 1 ≤ (X + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-! ### The set-up -/

theorem setup_regs (cw wit : List Bool) :
    ((Um (V := V) (inpOf cw wit) cw (p0Of cw) cw.length).setv rCP 0).seth sCW 0 =
      regs (((Um (V := V) (inpOf cw wit) cw (p0Of cw) cw.length).setv rCP 0).seth sCW 0)
        (rv (p0Of cw) cw.length 0 0) := by
  refine WState.eq rfl rfl ?_ rfl
  funext r
  simp only [regs, WState.seth_val, WState.setv_val, Um, rv]
  by_cases h : r = rCP
  · subst h; simp
  · rw [Function.update_of_ne h]; simp [h]

theorem setup_final (K : ℕ) (cw wit : List Bool) :
    (setZ (regs (((Um (V := V) (inpOf cw wit) cw (p0Of cw) cw.length).setv rCP 0).seth sCW 0)
      (rv (p0Of cw) 0 (wdOf K cw.length) 0)) (wdOf K cw.length) (numStreams V)).setv rG 0 =
      E (ctxOf K cw wit) (inpOf cw wit) (p0Of cw) (a0 (V := V)) := by
  refine WState.eq ?_ ?_ ?_ rfl
  · funext i
    simp only [WState.setv_sh, setZ, regs, WState.seth_sh, WState.setv_sh, E, shF, a0]
    by_cases h2 : i = sCW
    · subst h2; simp [sCW]
    · rw [Function.update_of_ne h2]
      by_cases h0 : i = sIN
      · subst h0; simp [Um, sIN]
      · have h0' : i.val ≠ 0 := fun e => h0 (Fin.ext e)
        have h2' : i.val ≠ 2 := fun e => h2 (Fin.ext e)
        simp [Um, h0, h2, h0', h2']
  · funext i
    simp only [WState.setv_st, setZ, regs, WState.seth_st, WState.setv_st, E, stF, a0, mem_numStreams]
    by_cases h4 : 4 ≤ i.val
    · rw [if_pos (by omega), dif_pos h4]; rfl
    · rw [dif_neg h4]
      by_cases h3 : i.val = 3
      · rw [if_pos (by omega)]; simp [h3, ctxOf]
      · rw [if_neg (by omega)]
        by_cases h0 : i = sIN
        · subst h0; simp [Um, sIN]
        · by_cases h2 : i = sCW
          · subst h2; simp [Um, ctxOf]
          · have h0' : i.val ≠ 0 := fun e => h0 (Fin.ext e)
            have h2' : i.val ≠ 2 := fun e => h2 (Fin.ext e)
            have h1 : i.val = 1 := by omega
            clear h0' h2'
            simp [Um, h0, h2, h1]
  · funext r
    simp only [WState.setv_val, setZ, regs]
    by_cases hG : r = rG
    · subst hG; simp [E, valF]
    · rw [Function.update_of_ne hG]
      simp only [E, valF, a0, rv]
      by_cases hI : r = rIP
      · subst hI; simp
      · have hI' : r.val ≠ 6 := fun e => hI (Fin.ext e)
        by_cases hL : r = rLR
        · subst hL; simp
        · by_cases hW : r = rWR
          · subst hW; simp
          · simp [hI, hG, hI', hL, hW]

theorem setup_arith (V K L w : ℕ) (hw : w ≤ 100 * (L + K + 1) ^ 4) :
    40 * L + 20 + 1 + (5 * L + 1 + 1 + (w + 1 + ((V + 1) * (50 * (L + K) ^ 4 + 11) + 1 + (3 * (L + K) ^ 4 + 1)))) ≤
      setupCost V K L := by
  unfold setupCost
  set Y := (L + K + 1) ^ 4 with hY
  have h1 : (L + K) ^ 4 ≤ Y := Nat.pow_le_pow_left (by omega) 4
  have h2 : L + 1 ≤ Y := le_trans (by omega) (Nat.le_self_pow (by norm_num) (L + K + 1))
  have h3 : V * (L + K) ^ 4 ≤ V * Y := Nat.mul_le_mul_left V h1
  have h4 : V ≤ V * Y := Nat.le_mul_of_pos_right V (by omega)
  nlinarith

theorem setup_spec (K : ℕ) (hK : 1 ≤ K) (cw wit : List Bool) (n : ℕ) :
    ∃ c, c ≤ setupCost V K cw.length ∧
      WXExec (capOf K cw wit n) (setupP K) (Interfaces.startState (V + 3) NR (frame cw ++ frame wit))
        (E (ctxOf K cw wit) (inpOf cw wit) (p0Of cw) (a0 (V := V))) c := by
  have hXW : cw.length + K ≤ wdOf K cw.length := by
    unfold wdOf; exact Nat.le_self_pow (by norm_num) _
  have hc0 : 2 * wdOf K cw.length + 4 * cw.length + 100 ≤ capOf K cw wit n := by unfold capOf; omega
  have e0 : Interfaces.startState (V + 3) NR (frame cw ++ frame wit) = Um (inpOf cw wit) cw 0 0 := by
    refine WState.eq ?_ ?_ ?_ rfl
    · funext i; simp [Interfaces.startState, Um]
    · funext i
      simp only [Interfaces.startState, Um, List.take_zero, inpOf]
      by_cases hi : i = sIN
      · subst hi; simp [sIN]
      · have : i.val ≠ 0 := fun e => hi (Fin.ext e)
        simp [this, hi]
    · funext r; simp [Interfaces.startState, Um]
  have u1 := unframe_spec (V := V) cw (capOf K cw wit n) wit (by omega)
  rw [← e0] at u1
  have u2 := rewind_spec (V := V) (capOf K cw wit n) sCW rCP cw.length
    (Um (inpOf cw wit) cw (p0Of cw) cw.length) (by simp [Um]) (by simp [Um]) (by omega)
  rw [setup_regs] at u2
  set σ2 := ((Um (V := V) (inpOf cw wit) cw (p0Of cw) cw.length).setv rCP 0).seth sCW 0 with hσ2
  have wid := width_spec (capOf K cw wit n) σ2 (p0Of cw) cw.length K hK (by unfold capOf wdOf at *; omega)
  have hstr : ∀ i ∈ numStreams V, (regs σ2 (rv (p0Of cw) 0 ((cw.length + K) ^ 4) 0)).st i = [] ∧
      (regs σ2 (rv (p0Of cw) 0 ((cw.length + K) ^ 4) 0)).sh i = 0 := by
    intro i hi
    rw [mem_numStreams] at hi
    have h0 : i ≠ sIN := fun e => by subst e; simp [sIN] at hi
    have h2 : i ≠ sCW := fun e => by subst e; simp [sCW] at hi
    simp [regs, hσ2, Um, h0, h2]
  have z1 := initAll_spec (V := V) (capOf K cw wit n) (wdOf K cw.length) (by omega) (numStreams V) _
    numStreams_nodup hstr (by simp [regs, rv, wdOf]) (by simp [regs, rv])
  have z2 := clearR_spec (V := V) (capOf K cw wit n) rG (wdOf K cw.length)
    (setZ (regs σ2 (rv (p0Of cw) 0 ((cw.length + K) ^ 4) 0)) (wdOf K cw.length) (numStreams V))
    (by simp [setZ, regs, rv, wdOf]) (by omega)
  have efin := setup_final (V := V) K cw wit
  rw [← hσ2] at efin
  simp only [wdOf] at efin z2 z1
  rw [efin] at z2
  refine ⟨_, ?_, WXExec.seq u1 (WXExec.seq u2 (WXExec.seq wid (WXExec.seq z1 z2)))⟩
  have hlen : (numStreams V).length = V + 1 := by simp [numStreams]
  rw [hlen]
  exact setup_arith V K cw.length _ (widthCost_le K (cw.length + K) (by omega))

end Whole

end NearCubicGates.Close.Dispatch
