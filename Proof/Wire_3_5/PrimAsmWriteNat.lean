import Proof.Wire_3_5.PrimAsmParseNat

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Halving a unary register -/

/-- `w := 0`, `q += ⌊w/2⌋`, `rb := w mod 2` (for `rb = 0` at entry). -/
def halveLoop (w q rb : Fin nr) : WM ns nr := .whr w (.seq (.dec w) (.ifr w (.seq (.dec w) (.inc q)) (.inc rb)))

theorem halveLoop_spec (w q rb : Fin nr) (hwq : w ≠ q) (hwr : w ≠ rb) (hqr : q ≠ rb) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val w = m → σ.val rb = 0 → m ≤ cap → σ.val q + m / 2 ≤ cap → 1 ≤ cap →
      WExec cap (halveLoop w q rb) σ (((σ.setv w 0).setv q (σ.val q + m / 2)).setv rb (m % 2)) (5 * m + 4)
  | 0, σ, h0, hr, _, _, _ => by
    have e : ((σ.setv w 0).setv q (σ.val q + 0 / 2)).setv rb (0 % 2) = σ := by
      refine WState.eq rfl rfl ?_ rfl
      funext j
      by_cases hjr : j = rb
      · subst hjr; simp [hr]
      · by_cases hjq : j = q
        · subst hjq; simp [Function.update_apply, hjr]
        · by_cases hjw : j = w
          · subst hjw; simp [Function.update_apply, hjr, hjq, h0]
          · simp [Function.update_apply, hjr, hjq, hjw]
    rw [e]
    exact WExec.mono (WExec.whrF h0) (by omega)
  | 1, σ, h1, hr, hcap, _, hcap1 => by
    have d1 := WExec.dec (cap := cap) w σ (by omega)
    have hw0 : (σ.setv w (σ.val w - 1)).val w = 0 := by simp [h1]
    have i1 := WExec.inc (cap := cap) rb (σ.setv w (σ.val w - 1))
      (by simp [Function.update_apply, hwr, hwr.symm, hr]; omega)
    have hb := WExec.ifrF (P := .seq (.dec w) (.inc q)) hw0 i1
    set τ := (σ.setv w (σ.val w - 1)).setv rb ((σ.setv w (σ.val w - 1)).val rb + 1) with hτ
    have hτw : τ.val w = 0 := by simp [τ, Function.update_apply, hwr, hwr.symm, h1]
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 hb) (WExec.whrF (P := .seq (.dec w)
      (.ifr w (.seq (.dec w) (.inc q)) (.inc rb))) hτw)) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext j
    by_cases hjr : j = rb
    · subst hjr; simp [τ, Function.update_apply, hwr, hwr.symm, hr]
    · by_cases hjq : j = q
      · subst hjq; simp [τ, Function.update_apply, hjr, hwq, hwq.symm]
      · by_cases hjw : j = w
        · subst hjw; simp [τ, Function.update_apply, hjr, hjq, h1]
        · simp [τ, Function.update_apply, hjr, hjq, hjw]
  | k + 2, σ, hk, hr, hcap, hq, hcap1 => by
    have d1 := WExec.dec (cap := cap) w σ (by omega)
    set σ1 := σ.setv w (σ.val w - 1) with hσ1
    have hσ1w : σ1.val w = k + 1 := by simp [σ1, hk]
    have d2 := WExec.dec (cap := cap) w σ1 (by omega)
    set σ2 := σ1.setv w (σ1.val w - 1) with hσ2
    have hk2 : (k + 2) / 2 = k / 2 + 1 := by omega
    have hσ2q : σ2.val q = σ.val q := by simp [σ2, σ1, Function.update_apply, hwq, hwq.symm]
    have i2 := WExec.inc (cap := cap) q σ2 (by rw [hσ2q]; omega)
    set σ3 := σ2.setv q (σ2.val q + 1) with hσ3
    have hne1 : σ1.val w ≠ 0 := by omega
    have hb := WExec.ifrT (Q := .inc rb) hne1 (WExec.seq d2 i2)
    have hσ3w : σ3.val w = k := by simp [σ3, σ2, Function.update_apply, hwq, hwq.symm, hσ1w]
    have hσ3r : σ3.val rb = 0 := by
      simp [σ3, σ2, σ1, Function.update_apply, hqr, hqr.symm, hwr, hwr.symm, hr]
    have hσ3q : σ3.val q = σ.val q + 1 := by
      simp [σ3, σ2, σ1, Function.update_apply, hwq, hwq.symm]
    have ih := halveLoop_spec w q rb hwq hwr hqr k σ3 hσ3w hσ3r (by omega)
      (by rw [hσ3q]; omega) hcap1
    have hne0 : σ.val w ≠ 0 := by omega
    refine WExec.cast cap (WExec.whrT hne0 (WExec.seq d1 hb) ih) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext j
    by_cases hjr : j = rb
    · subst hjr; simp [Function.update_apply] <;> omega
    · by_cases hjq : j = q
      · subst hjq; simp [Function.update_apply, hjr, hσ3q]; omega
      · by_cases hjw : j = w
        · subst hjw; simp [Function.update_apply, hjr, hjq]
        · simp [σ3, σ2, σ1, Function.update_apply, hjr, hjq, hjw]

/-- `w := ⌊w/2⌋`, `rb := w mod 2` (for `q = rb = 0` at entry); `q = 0` at the end. -/
def halveM (w q rb : Fin nr) : WM ns nr := .seq (halveLoop w q rb) (WM.move q w)

theorem halveM_spec (w q rb : Fin nr) (hwq : w ≠ q) (hwr : w ≠ rb) (hqr : q ≠ rb) (σ : WState ns nr)
    (hq : σ.val q = 0) (hr : σ.val rb = 0) (hcap : σ.val w ≤ cap) (hcap1 : 1 ≤ cap) :
    WExec cap (halveM w q rb) σ ((σ.setv w (σ.val w / 2)).setv rb (σ.val w % 2)) (9 * σ.val w + 6) := by
  have h1 := halveLoop_spec cap w q rb hwq hwr hqr (σ.val w) σ rfl hr hcap (by rw [hq]; omega) hcap1
  set σ1 := ((σ.setv w 0).setv q (σ.val q + σ.val w / 2)).setv rb (σ.val w % 2) with hσ1
  have h2 := wmove_spec cap q w (Ne.symm hwq) (σ.val w / 2) σ1
    (by simp [σ1, Function.update_apply, hqr, hqr.symm, hq]) (by simp [σ1, Function.update_apply, hqr, hq]; omega)
    (by simp [σ1, Function.update_apply, hwq, hwq.symm, hwr, hwr.symm, hqr, hq]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases hjw : j = w
  · subst hjw; simp [σ1, Function.update_apply, hwq, hwq.symm, hwr, hwr.symm, hqr, hq]
  · by_cases hjq : j = q
    · subst hjq; simp [σ1, Function.update_apply, hjw, hqr, hq]
    · by_cases hjr : j = rb
      · subst hjr; simp [σ1, Function.update_apply, hjw, hjq]
      · simp [σ1, Function.update_apply, hjw, hjq, hjr]

/-! ## The bit length -/

/-- The number of halvings to reach `0`: `natBitLength w` for `w ≥ 1`, and `0` for `w = 0`. -/
def halvings (w : ℕ) : ℕ := if w = 0 then 0 else natBitLength w

theorem halvings_succ (w : ℕ) (hw : w ≠ 0) : halvings w = halvings (w / 2) + 1 := by
  unfold halvings natBitLength
  rw [if_neg hw]
  by_cases h2 : w / 2 = 0
  · rw [if_pos h2]
    have : w = 1 := by omega
    subst this; simp
  · rw [if_neg h2]
    have hlog : Nat.log 2 (w / 2) = Nat.log 2 w - 1 := Nat.log_div_base 2 w
    have hpos : 1 ≤ Nat.log 2 w := Nat.le_log_of_pow_le (by norm_num) (by omega)
    omega

theorem natBitLength_eq_halvings (v : ℕ) : natBitLength v = halvings (v / 2) + 1 := by
  by_cases hv : v = 0
  · subst hv; simp [natBitLength, halvings]
  · rw [← halvings_succ v hv]
    simp [halvings, hv]

theorem halvings_le (w : ℕ) : halvings w ≤ w := by
  unfold halvings natBitLength
  split_ifs with h
  · omega
  · have := Nat.log_lt_self 2 h
    omega

/-- The halving loop: while `w ≠ 0`, `L += 1` and halve `w`. -/
def lenLoop (w q rb L : Fin nr) : WM ns nr := .whr w (.seq (.inc L) (.seq (halveM w q rb) (WM.clear rb)))

theorem lenLoop_spec (w q rb L : Fin nr) (hwq : w ≠ q) (hwr : w ≠ rb) (hqr : q ≠ rb) (hwL : w ≠ L) (hqL : q ≠ L)
    (hrL : rb ≠ L) (hcap1 : 1 ≤ cap) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val w = m → σ.val q = 0 → σ.val rb = 0 → m ≤ cap →
      σ.val L + halvings m ≤ cap →
      WExec cap (lenLoop w q rb L) σ ((σ.setv w 0).setv L (σ.val L + halvings m)) (40 * m + 20) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro σ hw hq hr hcap hL
    by_cases hm : m = 0
    · subst hm
      have e : (σ.setv w 0).setv L (σ.val L + halvings 0) = σ := by
        refine WState.eq rfl rfl ?_ rfl
        funext j
        by_cases hjL : j = L
        · subst hjL; simp [halvings]
        · by_cases hjw : j = w
          · subst hjw; simp [Function.update_apply, hjL, hw]
          · simp [Function.update_apply, hjL, hjw]
      rw [e]
      exact WExec.mono (WExec.whrF hw) (by omega)
    · have hsucc := halvings_succ m hm
      have i1 := WExec.inc (cap := cap) L σ (by omega)
      set σ1 := σ.setv L (σ.val L + 1) with hσ1
      have h2 := halveM_spec cap w q rb hwq hwr hqr σ1 (by simp [σ1, Function.update_apply, hqL, hq])
        (by simp [σ1, Function.update_apply, hrL, hr]) (by simp [σ1, Function.update_apply, hwL, hw]; omega) hcap1
      set σ2 := (σ1.setv w (σ1.val w / 2)).setv rb (σ1.val w % 2) with hσ2
      have h3 := wclear_spec cap rb (σ1.val w % 2) σ2 (by simp [σ2]) (by simp [σ2]; omega)
      set σ3 := σ2.setv rb 0 with hσ3
      have hσ1w : σ1.val w = m := by simp [σ1, Function.update_apply, hwL, hw]
      have hσ3w : σ3.val w = m / 2 := by simp [σ3, σ2, Function.update_apply, hwr, hσ1w]
      have ih' := ih (m / 2) (by omega) σ3 hσ3w
        (by simp [σ3, σ2, σ1, Function.update_apply, hqr, hwq.symm, hqL, hq])
        (by simp [σ3]) (by omega)
        (by simp [σ3, σ2, σ1, Function.update_apply, hrL.symm, hwL.symm]; omega)
      have hne : σ.val w ≠ 0 := by omega
      refine WExec.cast cap (WExec.whrT hne (WExec.seq i1 (WExec.seq h2 h3)) ih') ?_ ?_
      · refine WState.eq rfl rfl ?_ rfl
        funext j
        by_cases hjL : j = L
        · subst hjL; simp [σ3, σ2, σ1, Function.update_apply, hrL.symm, hwL.symm]; omega
        · by_cases hjw : j = w
          · subst hjw; simp [Function.update_apply, hjL]
          · by_cases hjr : j = rb
            · subst hjr; simp [σ3, Function.update_apply, hjL, hjw, hr]
            · simp [σ3, σ2, σ1, Function.update_apply, hjL, hjw, hjr]
      · rw [hσ1w]
        have : m % 2 ≤ 1 := by omega
        omega

/-! ## Appending to an output stream -/

/-- The state after appending the word `u` to stream `o` (head at its end), with `u.length` counted in `OP`. -/
def appendO (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (u : List Bool) : WState ns nr :=
  ((σ.sets o (σ.st o ++ u)).seth o (σ.sh o + u.length)).setv OP (σ.val OP + u.length)

@[simp] theorem appendO_st (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (u : List Bool) :
    (appendO σ o OP u).st = Function.update σ.st o (σ.st o ++ u) := by simp [appendO]
@[simp] theorem appendO_sh (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (u : List Bool) :
    (appendO σ o OP u).sh = Function.update σ.sh o (σ.sh o + u.length) := by simp [appendO]
@[simp] theorem appendO_val (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (u : List Bool) :
    (appendO σ o OP u).val = Function.update σ.val OP (σ.val OP + u.length) := by simp [appendO]
@[simp] theorem appendO_cell (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (u : List Bool) :
    (appendO σ o OP u).cell = σ.cell := by simp [appendO]

theorem appendO_nil (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) : appendO σ o OP [] = σ := by
  apply WState.eq <;> simp

theorem appendO_append (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (u u' : List Bool) :
    appendO (appendO σ o OP u) o OP u' = appendO σ o OP (u ++ u') := by
  apply WState.eq
  · funext j; by_cases hj : j = o
    · subst hj; simp; ring
    · simp [Function.update_apply, hj]
  · funext j; by_cases hj : j = o
    · subst hj; simp
    · simp [Function.update_apply, hj]
  · funext j; by_cases hj : j = OP
    · subst hj; simp; ring
    · simp [Function.update_apply, hj]
  · simp

theorem appendO_setv (σ : WState ns nr) (o : Fin (ns + 1)) (OP r : Fin nr) (hr : r ≠ OP) (x : ℕ) (u : List Bool) :
    appendO (σ.setv r x) o OP u = (appendO σ o OP u).setv r x := by
  apply WState.eq
  · simp
  · simp
  · funext j
    by_cases hj : j = r
    · subst hj; simp [Function.update_apply, hr]
    · by_cases hjo : j = OP
      · subst hjo; simp [Function.update_apply, hj, Ne.symm hr]
      · simp [Function.update_apply, hj, hjo]
  · simp

/-- One framed bit `[true, b]`. -/
def emitPair (o : Fin (ns + 1)) (OP : Fin nr) (b : Bool) : WM ns nr := .seq (emitC o OP true) (emitC o OP b)

theorem emitPair_spec (o : Fin (ns + 1)) (OP : Fin nr) (b : Bool) (σ : WState ns nr) (ho : σ.sh o = (σ.st o).length)
    (hc : σ.val OP + 2 ≤ cap) : WExec cap (emitPair o OP b) σ (appendO σ o OP [true, b]) 15 := by
  have h1 := emitC_spec cap o OP true σ ho (by omega)
  have h2 := emitC_spec cap o OP b (((σ.sets o ((σ.st o) ++ [true])).seth o (σ.sh o + 1)).setv OP (σ.val OP + 1))
    (by simp [ho]) (by simp; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = o
    · subst hj; simp [appendO] <;> ring
    · simp [appendO, Function.update_apply, hj]
  · funext j; by_cases hj : j = o
    · subst hj; simp [appendO]
    · simp [appendO, Function.update_apply, hj]
  · funext j; by_cases hj : j = OP
    · subst hj; simp [appendO] <;> ring
    · simp [appendO, Function.update_apply, hj]
  · simp [appendO]

/-! ## The framed natWord writer -/

theorem marks_replicate_succ (k : ℕ) (b : Bool) :
    RepairOrdinary.Streaming.marks (List.replicate (k + 1) b) =
      RepairOrdinary.Streaming.marks (List.replicate k b) ++ [true, b] := by
  rw [List.replicate_succ']
  simp [RepairOrdinary.Streaming.marks]

theorem marks_append (u u' : List Bool) :
    RepairOrdinary.Streaming.marks (u ++ u') = RepairOrdinary.Streaming.marks u ++ RepairOrdinary.Streaming.marks u' := by
  simp [RepairOrdinary.Streaming.marks]

/-- The ones loop: `K` times, append `[true, true]`. -/
def onesLoop (o : Fin (ns + 1)) (OP K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (emitPair o OP true))

theorem onesLoop_spec (o : Fin (ns + 1)) (OP K : Fin nr) (hK : K ≠ OP) (n : ℕ) (σ : WState ns nr) (hKn : σ.val K = n)
    (ho : σ.sh o = (σ.st o).length) (hc : σ.val OP + 2 * n ≤ cap) (hn : n ≤ cap) :
    WExec cap (onesLoop o OP K) σ ((appendO σ o OP (RepairOrdinary.Streaming.marks (List.replicate n true))).setv K 0)
      (n * 19 + 1) := by
  let S : ℕ → WState ns nr := fun k =>
    (appendO σ o OP (RepairOrdinary.Streaming.marks (List.replicate k true))).setv K (n - k)
  have hS0 : S 0 = σ := by
    simp only [S, List.replicate_zero]
    rw [show RepairOrdinary.Streaming.marks ([] : List Bool) = [] from rfl, appendO_nil, Nat.sub_zero, ← hKn,
      wsetv_same]
  have hloop := UnionMachine.Round.wloop cap K (emitPair o OP true) 15 n S
    (fun k _ => by simp [S])
    hn
    (fun k hk => by
      have e1 : (S k).setv K (n - k - 1) =
          (appendO σ o OP (RepairOrdinary.Streaming.marks (List.replicate k true))).setv K (n - k - 1) := by
        simp only [S, wsetv_setv]
      rw [e1]
      have hlen : (RepairOrdinary.Streaming.marks (List.replicate k true)).length = 2 * k := by
        simp [RepairOrdinary.Streaming.marks]; ring
      have h := emitPair_spec cap o OP true
        ((appendO σ o OP (RepairOrdinary.Streaming.marks (List.replicate k true))).setv K (n - k - 1))
        (by simp [ho]) (by simp [Function.update_apply, Ne.symm hK, hlen]; omega)
      refine WExec.cast cap h ?_ le_rfl
      simp only [S]
      rw [← appendO_setv _ o OP K hK, appendO_append, ← marks_replicate_succ]
      rw [appendO_setv _ o OP K hK, show n - k - 1 = n - (k + 1) by omega])
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ (by omega)
  simp [S]

/-! ### The registers of the writer

`R 0 = v` (the value, kept), `R 1 = w`, `R 2 = q`, `R 3 = rb`, `R 4 = L`, `R 5 = K`, `R 6 = t` (scratch, `0` at entry
and exit), `R 7 = OP` (the output position counter). -/

section Writer
variable (o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr)

theorem Rne {i j : Fin 8} (h : i ≠ j) : R i ≠ R j := R.injective.ne h

/-- **Phase A**: `L := natBitLength v` (through `w`, `q`, `rb`, `t`). -/
def bitLenM : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 0) (R 1) (R 6)) (.seq (.inc (R 4)) (.seq (halveM (R 1) (R 2) (R 3))
    (.seq (WM.clear (R 3)) (lenLoop (R 1) (R 2) (R 3) (R 4)))))

theorem bitLenM_spec (σ : WState ns nr) (hw : σ.val (R 1) = 0) (hq : σ.val (R 2) = 0) (hrb : σ.val (R 3) = 0)
    (hL : σ.val (R 4) = 0) (ht : σ.val (R 6) = 0) (hcap : σ.val (R 0) + 2 ≤ cap) :
    WExec cap (bitLenM R) σ (σ.setv (R 4) (natBitLength (σ.val (R 0)))) (60 * σ.val (R 0) + 60) := by
  set v := σ.val (R 0) with hv
  have hbl := natBitLength_eq_halvings v
  have hhl := halvings_le (v / 2)
  have h1 := FinalPass.Hash4.wcopyR_spec cap (R 0) (R 1) (R 6) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) σ hw ht (by omega)
  set σ1 := σ.setv (R 1) v with hσ1
  have h2 := WExec.inc (cap := cap) (R 4) σ1 (by simp [σ1, Function.update_apply, Rne R (show (4 : Fin 8) ≠ 1 by decide), hL]; omega)
  set σ2 := σ1.setv (R 4) (σ1.val (R 4) + 1) with hσ2
  have h3 := halveM_spec cap (R 1) (R 2) (R 3) (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) σ2
    (by simp [σ2, σ1, Function.update_apply, Rne R (show (2 : Fin 8) ≠ 4 by decide), Rne R (show (2 : Fin 8) ≠ 1 by decide), hq])
    (by simp [σ2, σ1, Function.update_apply, Rne R (show (3 : Fin 8) ≠ 4 by decide), Rne R (show (3 : Fin 8) ≠ 1 by decide), hrb])
    (by simp [σ2, σ1, Function.update_apply, Rne R (show (1 : Fin 8) ≠ 4 by decide)]; omega) (by omega)
  have hσ2w : σ2.val (R 1) = v := by simp [σ2, σ1, Function.update_apply, Rne R (show (1 : Fin 8) ≠ 4 by decide)]
  set σ3 := (σ2.setv (R 1) (σ2.val (R 1) / 2)).setv (R 3) (σ2.val (R 1) % 2) with hσ3
  have h4 := wclear_spec cap (R 3) (σ2.val (R 1) % 2) σ3 (by simp [σ3]) (by simp [σ3]; omega)
  set σ4 := σ3.setv (R 3) 0 with hσ4
  have h5 := lenLoop_spec cap (R 1) (R 2) (R 3) (R 4) (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (by omega) (v / 2) σ4
    (by simp [σ4, σ3, Function.update_apply, Rne R (show (1 : Fin 8) ≠ 3 by decide), hσ2w])
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Rne R (show (2 : Fin 8) ≠ 3 by decide),
      Rne R (show (2 : Fin 8) ≠ 1 by decide), Rne R (show (2 : Fin 8) ≠ 4 by decide), hq])
    (by simp [σ4]) (by omega)
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Rne R (show (4 : Fin 8) ≠ 3 by decide),
      Rne R (show (4 : Fin 8) ≠ 1 by decide), hL]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 h5)))) ?_ ?_
  · refine WState.eq rfl rfl ?_ rfl
    funext j
    by_cases hj4 : j = R 4
    · subst hj4; simp [σ4, σ3, σ2, σ1, Function.update_apply, Rne R (show (4 : Fin 8) ≠ 3 by decide),
        Rne R (show (4 : Fin 8) ≠ 1 by decide), hL, hbl]; omega
    · by_cases hj1 : j = R 1
      · subst hj1; simp [Function.update_apply, hj4, hw]
      · by_cases hj3 : j = R 3
        · subst hj3; simp [σ4, Function.update_apply, hj4, hj1, hrb]
        · simp [σ4, σ3, σ2, σ1, Function.update_apply, hj4, hj1, hj3]
  · rw [hσ2w]
    have : v % 2 ≤ 1 := by omega
    have : v / 2 ≤ v := Nat.div_le_self v 2
    omega

/-- **Phase B**: append `marks (1^L 0)` (through `K`, `t`). -/
def prefixM : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 4) (R 5) (R 6)) (.seq (onesLoop o (R 7) (R 5)) (emitPair o (R 7) false))

theorem prefixM_spec (σ : WState ns nr) (hK : σ.val (R 5) = 0) (ht : σ.val (R 6) = 0)
    (ho : σ.sh o = (σ.st o).length) (hcap : σ.val (R 7) + 2 * σ.val (R 4) + 2 + σ.val (R 4) ≤ cap) :
    WExec cap (prefixM o R) σ (appendO σ o (R 7)
      (RepairOrdinary.Streaming.marks (List.replicate (σ.val (R 4)) true ++ [false])))
      (40 * σ.val (R 4) + 40) := by
  set ℓ := σ.val (R 4) with hℓ
  have h1 := FinalPass.Hash4.wcopyR_spec cap (R 4) (R 5) (R 6) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) σ hK ht (by omega)
  have h2 := onesLoop_spec cap o (R 7) (R 5) (Rne R (by decide)) ℓ (σ.setv (R 5) ℓ) (by simp)
    (by simpa using ho) (by simp [Function.update_apply, Rne R (show (7 : Fin 8) ≠ 5 by decide)]; omega) (by omega)
  have hlen : (RepairOrdinary.Streaming.marks (List.replicate ℓ true)).length = 2 * ℓ := by
    simp [RepairOrdinary.Streaming.marks]; ring
  have h3 := emitPair_spec cap o (R 7) false
    ((appendO (σ.setv (R 5) ℓ) o (R 7) (RepairOrdinary.Streaming.marks (List.replicate ℓ true))).setv (R 5) 0)
    (by simp [ho]) (by simp [Function.update_apply, Rne R (show (7 : Fin 8) ≠ 5 by decide), hlen]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  rw [← appendO_setv _ o (R 7) (R 5) (Rne R (by decide)), appendO_append, marks_append, wsetv_setv]
  have e : σ.setv (R 5) 0 = σ := by rw [← hK, wsetv_same]
  rw [e]
  rfl

/-- The payload body: halve `w`, append its remainder as a framed bit, clear the remainder. -/
def payBody : WM ns nr :=
  .seq (halveM (R 1) (R 2) (R 3)) (.seq (.ifr (R 3) (emitPair o (R 7) true) (emitPair o (R 7) false))
    (WM.clear (R 3)))

/-- The payload writer's state after `k` bits. -/
def payWState (σ : WState ns nr) (v ℓ : ℕ) (k : ℕ) : WState ns nr :=
  ((appendO σ o (R 7) (RepairOrdinary.Streaming.marks ((WilliamsPublishedForm.fixedWidthNatBits ℓ v).take k))).setv
    (R 1) (v / 2 ^ k)).setv (R 5) (ℓ - k)

/-- **Phase C**: append `marks (fixedWidthNatBits ℓ v)` (the payload, least significant first). -/
def payM : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 0) (R 1) (R 6)) (.seq (FinalPass.Hash4.wcopyR (R 4) (R 5) (R 6))
    (.whr (R 5) (.seq (.dec (R 5)) (payBody o R))))

theorem payM_spec (σ : WState ns nr) (hw : σ.val (R 1) = 0) (hq : σ.val (R 2) = 0) (hrb : σ.val (R 3) = 0)
    (hK : σ.val (R 5) = 0) (ht : σ.val (R 6) = 0) (ho : σ.sh o = (σ.st o).length)
    (hℓ : σ.val (R 0) < 2 ^ σ.val (R 4))
    (hcap : σ.val (R 0) + σ.val (R 4) + σ.val (R 7) + 2 * σ.val (R 4) + 2 ≤ cap) :
    WExec cap (payM o R) σ (appendO σ o (R 7)
      (RepairOrdinary.Streaming.marks (WilliamsPublishedForm.fixedWidthNatBits (σ.val (R 4)) (σ.val (R 0)))))
      (σ.val (R 4) * (10 * σ.val (R 0) + 40) + 40 * σ.val (R 0) + 40 * σ.val (R 4) + 20) := by
  set v := σ.val (R 0) with hv
  set ℓ := σ.val (R 4) with hℓdef
  have h1 := FinalPass.Hash4.wcopyR_spec cap (R 0) (R 1) (R 6) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) σ hw ht (by omega)
  have h2 := FinalPass.Hash4.wcopyR_spec cap (R 4) (R 5) (R 6) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) (σ.setv (R 1) v) (by simp [Function.update_apply, Rne R (show (5 : Fin 8) ≠ 1 by decide), hK])
    (by simp [Function.update_apply, Rne R (show (6 : Fin 8) ≠ 1 by decide), ht])
    (by simp [Function.update_apply, Rne R (show (4 : Fin 8) ≠ 1 by decide)]; omega)
  set σ0 := (σ.setv (R 1) v).setv (R 5) ((σ.setv (R 1) v).val (R 4)) with hσ0
  have hσ0L : (σ.setv (R 1) v).val (R 4) = ℓ := by
    simp [Function.update_apply, Rne R (show (4 : Fin 8) ≠ 1 by decide), hℓdef]
  have hS0 : payWState o R σ v ℓ 0 = σ0 := by
    simp only [payWState, List.take_zero, pow_zero, Nat.div_one, Nat.sub_zero]
    rw [show RepairOrdinary.Streaming.marks ([] : List Bool) = [] from rfl, appendO_nil, hσ0, hσ0L]
  have hbits_len : (WilliamsPublishedForm.fixedWidthNatBits ℓ v).length = ℓ := by
    simp [WilliamsPublishedForm.fixedWidthNatBits]
  have hloop := UnionMachine.Round.wloop cap (R 5) (payBody o R) (10 * v + 40) ℓ (payWState o R σ v ℓ)
    (fun k _ => by simp [payWState, Function.update_apply, Rne R (show (5 : Fin 8) ≠ 1 by decide),
      Rne R (show (5 : Fin 8) ≠ 7 by decide)])
    (by omega)
    (fun k hk => by
      -- the state at round k
      set T := (payWState o R σ v ℓ k).setv (R 5) (ℓ - k - 1) with hT
      have hTw : T.val (R 1) = v / 2 ^ k := by
        simp [T, payWState, Function.update_apply, Rne R (show (1 : Fin 8) ≠ 5 by decide),
          Rne R (show (1 : Fin 8) ≠ 7 by decide)]
      have hTq : T.val (R 2) = 0 := by
        simp [T, payWState, Function.update_apply, Rne R (show (2 : Fin 8) ≠ 5 by decide),
          Rne R (show (2 : Fin 8) ≠ 1 by decide), Rne R (show (2 : Fin 8) ≠ 7 by decide), hq]
      have hTr : T.val (R 3) = 0 := by
        simp [T, payWState, Function.update_apply, Rne R (show (3 : Fin 8) ≠ 5 by decide),
          Rne R (show (3 : Fin 8) ≠ 1 by decide), Rne R (show (3 : Fin 8) ≠ 7 by decide), hrb]
      have hTo : T.sh o = (T.st o).length := by
        simp [T, payWState, ho]
      have hlenk : (RepairOrdinary.Streaming.marks ((WilliamsPublishedForm.fixedWidthNatBits ℓ v).take k)).length =
          2 * k := by
        simp [RepairOrdinary.Streaming.marks, List.length_take, hbits_len]; omega
      have hTop : T.val (R 7) = σ.val (R 7) + 2 * k := by
        simp [T, payWState, Function.update_apply, Rne R (show (7 : Fin 8) ≠ 5 by decide),
          Rne R (show (7 : Fin 8) ≠ 1 by decide), hlenk]
      have hdivle : v / 2 ^ k ≤ v := Nat.div_le_self v _
      have ha := halveM_spec cap (R 1) (R 2) (R 3) (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) T
        hTq hTr (by rw [hTw]; omega) (by omega)
      set U := (T.setv (R 1) (T.val (R 1) / 2)).setv (R 3) (T.val (R 1) % 2) with hU
      set b := (v / 2 ^ k % 2 = 1 : Bool) with hb
      have hUo : U.sh o = (U.st o).length := by simp [U, hTo]
      have hUop : U.val (R 7) = σ.val (R 7) + 2 * k := by
        simp [U, Function.update_apply, Rne R (show (7 : Fin 8) ≠ 3 by decide),
          Rne R (show (7 : Fin 8) ≠ 1 by decide), hTop]
      have he : WExec cap (.ifr (R 3) (emitPair o (R 7) true) (emitPair o (R 7) false)) U
          (appendO U o (R 7) [true, b]) 16 := by
        by_cases hbit : v / 2 ^ k % 2 = 1
        · have hb1 : b = true := by simp [b, hbit]
          rw [hb1]
          exact WExec.ifrT (by simp [U, hTw, hbit]) (emitPair_spec cap o (R 7) true U hUo (by rw [hUop]; omega))
        · have hb0 : b = false := by simp [b, hbit]
          rw [hb0]
          exact WExec.ifrF (by simp [U, hTw]; omega) (emitPair_spec cap o (R 7) false U hUo (by rw [hUop]; omega))
      have hc := wclear_spec cap (R 3) (T.val (R 1) % 2) (appendO U o (R 7) [true, b])
        (by simp [U, Function.update_apply, Rne R (show (3 : Fin 8) ≠ 7 by decide)])
        (by simp [U, Function.update_apply, Rne R (show (3 : Fin 8) ≠ 7 by decide)]; omega)
      refine WExec.cast cap (WExec.seq ha (WExec.seq he hc)) ?_ (by rw [hTw]; omega)
      -- the next payload state
      have htake : (WilliamsPublishedForm.fixedWidthNatBits ℓ v).take (k + 1) =
          (WilliamsPublishedForm.fixedWidthNatBits ℓ v).take k ++ [b] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by rw [hbits_len]; exact hk)]
        simp [WilliamsPublishedForm.fixedWidthNatBits, b, Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : v / 2 ^ (k + 1) = v / 2 ^ k / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
      apply WState.eq
      · funext j; by_cases hj : j = o
        · subst hj; simp [U, T, payWState, hlenk, htake, marks_append]; ring
        · simp [U, T, payWState, Function.update_apply, hj]
      · funext j; by_cases hj : j = o
        · subst hj; simp [U, T, payWState, htake, marks_append, RepairOrdinary.Streaming.marks]
        · simp [U, T, payWState, Function.update_apply, hj]
      · funext j
        by_cases h7 : j = R 7
        · subst h7; simp [U, T, payWState, Function.update_apply, Rne R (show (7 : Fin 8) ≠ 3 by decide),
            Rne R (show (7 : Fin 8) ≠ 1 by decide), Rne R (show (7 : Fin 8) ≠ 5 by decide), hlenk, htake,
            marks_append, RepairOrdinary.Streaming.marks]; ring
        · by_cases h3 : j = R 3
          · subst h3; simp [U, T, payWState, Function.update_apply, h7, Rne R (show (3 : Fin 8) ≠ 1 by decide),
              Rne R (show (3 : Fin 8) ≠ 5 by decide), hrb]
          · by_cases h1 : j = R 1
            · subst h1; simp [U, T, payWState, Function.update_apply, h7, h3, Rne R (show (1 : Fin 8) ≠ 5 by decide),
                hdiv]
            · by_cases h5 : j = R 5
              · subst h5; simp [U, T, payWState, Function.update_apply, h7, h3, h1]; omega
              · simp [U, T, payWState, Function.update_apply, h7, h3, h1, h5]
      · simp [U, T, payWState])
  rw [hS0] at hloop
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 hloop)) ?_ (by nlinarith)
  -- the final state: w = 0, K = 0, the whole payload appended
  have hv0 : v / 2 ^ ℓ = 0 := Nat.div_eq_of_lt hℓ
  have htk : (WilliamsPublishedForm.fixedWidthNatBits ℓ v).take ℓ = WilliamsPublishedForm.fixedWidthNatBits ℓ v :=
    List.take_of_length_le (le_of_eq hbits_len)
  apply WState.eq
  · simp [payWState, hbits_len, htk]
  · simp [payWState, hbits_len, htk]
  · funext j
    by_cases h1 : j = R 1
    · subst h1; simp [payWState, Function.update_apply, Rne R (show (1 : Fin 8) ≠ 5 by decide),
        Rne R (show (1 : Fin 8) ≠ 7 by decide), hv0, hw]
    · by_cases h5 : j = R 5
      · subst h5; simp [payWState, Function.update_apply, h1, Rne R (show (5 : Fin 8) ≠ 7 by decide), hK]
      · simp [payWState, Function.update_apply, h1, h5, htk]
  · simp [payWState]

/-- **The framed natWord writer**: append `marks (natWord v)` to stream `o` (head at its end), `v = R 0` kept, every
scratch register `0` again, the output position counter `R 7` advanced by the field's length. -/
def writeNatM : WM ns nr := .seq (bitLenM R) (.seq (prefixM o R) (.seq (payM o R) (WM.clear (R 4))))

theorem writeNatM_spec (σ : WState ns nr) (hw : σ.val (R 1) = 0) (hq : σ.val (R 2) = 0) (hrb : σ.val (R 3) = 0)
    (hL : σ.val (R 4) = 0) (hK : σ.val (R 5) = 0) (ht : σ.val (R 6) = 0) (ho : σ.sh o = (σ.st o).length)
    (hcap : σ.val (R 0) + σ.val (R 7) + 6 * natBitLength (σ.val (R 0)) + 6 ≤ cap) :
    WExec cap (writeNatM o R) σ (appendO σ o (R 7) (RepairRepresentation.natWord (σ.val (R 0)) |>
      RepairOrdinary.Streaming.marks))
      ((natBitLength (σ.val (R 0)) + 10) * (100 * σ.val (R 0) + 200)) := by
  set v := σ.val (R 0) with hv
  set ℓ := natBitLength v with hℓ
  have hvℓ : v < 2 ^ ℓ := Nat.lt_pow_succ_log_self (by norm_num) v
  have hℓv : ℓ ≤ v + 1 := by
    have := Nat.log_lt_self 2 (show v + 1 ≠ 0 by omega)
    have := Nat.log_mono_right (show v ≤ v + 1 by omega) (b := 2)
    simp only [hℓ, natBitLength]; omega
  have hA := bitLenM_spec cap R σ hw hq hrb hL ht (by omega)
  set σA := σ.setv (R 4) ℓ with hσA
  have hB := prefixM_spec cap o R σA
    (by simp [σA, Function.update_apply, Rne R (show (5 : Fin 8) ≠ 4 by decide), hK])
    (by simp [σA, Function.update_apply, Rne R (show (6 : Fin 8) ≠ 4 by decide), ht])
    (by simpa [σA] using ho)
    (by simp [σA, Function.update_apply, Rne R (show (7 : Fin 8) ≠ 4 by decide)]; omega)
  have hσAL : σA.val (R 4) = ℓ := by simp [σA]
  rw [hσAL] at hB
  set σB := appendO σA o (R 7) (RepairOrdinary.Streaming.marks (List.replicate ℓ true ++ [false])) with hσB
  have hlenB : (RepairOrdinary.Streaming.marks (List.replicate ℓ true ++ [false])).length = 2 * ℓ + 2 := by
    simp [RepairOrdinary.Streaming.marks]; ring
  have hC := payM_spec cap o R σB
    (by simp [σB, σA, Function.update_apply, Rne R (show (1 : Fin 8) ≠ 7 by decide),
      Rne R (show (1 : Fin 8) ≠ 4 by decide), hw])
    (by simp [σB, σA, Function.update_apply, Rne R (show (2 : Fin 8) ≠ 7 by decide),
      Rne R (show (2 : Fin 8) ≠ 4 by decide), hq])
    (by simp [σB, σA, Function.update_apply, Rne R (show (3 : Fin 8) ≠ 7 by decide),
      Rne R (show (3 : Fin 8) ≠ 4 by decide), hrb])
    (by simp [σB, σA, Function.update_apply, Rne R (show (5 : Fin 8) ≠ 7 by decide),
      Rne R (show (5 : Fin 8) ≠ 4 by decide), hK])
    (by simp [σB, σA, Function.update_apply, Rne R (show (6 : Fin 8) ≠ 7 by decide),
      Rne R (show (6 : Fin 8) ≠ 4 by decide), ht])
    (by simp [σB, σA, ho])
    (by simp [σB, σA, Function.update_apply, Rne R (show (0 : Fin 8) ≠ 7 by decide),
      Rne R (show (0 : Fin 8) ≠ 4 by decide), Rne R (show (4 : Fin 8) ≠ 7 by decide)]; exact hvℓ)
    (by simp [σB, σA, Function.update_apply, Rne R (show (0 : Fin 8) ≠ 7 by decide),
      Rne R (show (0 : Fin 8) ≠ 4 by decide), Rne R (show (4 : Fin 8) ≠ 7 by decide),
      Rne R (show (7 : Fin 8) ≠ 4 by decide), hlenB]; omega)
  have hσB0 : σB.val (R 0) = v := by
    simp [σB, σA, Function.update_apply, Rne R (show (0 : Fin 8) ≠ 7 by decide), Rne R (show (0 : Fin 8) ≠ 4 by decide),
      hv]
  have hσB4 : σB.val (R 4) = ℓ := by
    simp [σB, σA, Function.update_apply, Rne R (show (4 : Fin 8) ≠ 7 by decide)]
  rw [hσB0, hσB4] at hC
  set σC := appendO σB o (R 7) (RepairOrdinary.Streaming.marks (WilliamsPublishedForm.fixedWidthNatBits ℓ v))
    with hσC
  have hσC4 : σC.val (R 4) = ℓ := by
    simp [σC, Function.update_apply, Rne R (show (4 : Fin 8) ≠ 7 by decide), hσB4]
  have hD := wclear_spec cap (R 4) ℓ σC hσC4 (by rw [hσC4]; omega)
  refine WExec.cast cap (WExec.seq hA (WExec.seq hB (WExec.seq hC hD))) ?_ ?_
  · -- the three appended pieces are `marks (natWord v)`, and `L` is `0` again
    rw [hσC, hσB, appendO_append, hσA, ← appendO_setv _ o (R 7) (R 4) (Rne R (by decide)), wsetv_setv]
    have e : σ.setv (R 4) 0 = σ := by rw [← hL, wsetv_same]
    rw [e, ← marks_append, List.append_assoc, List.singleton_append, ParseNat.natWord_eq]
  · nlinarith

end Writer

end NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
