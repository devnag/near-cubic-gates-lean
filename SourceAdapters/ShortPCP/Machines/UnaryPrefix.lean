import Proof.Gates.Cells.Setup

/-!
# The unary width prefix

Part of the verifier's ordinary implementation in the proof of `thm:short-pcp-ours` (Step 3, the listing of the
multiset `S`). A cell program takes its width `64·2^s` from the leading ones of its input (`ctxOf`, `Cells/Run.lean`).
The prefix is the ordinary word function `w ↦ frame (1^{size |w|} 0 ++ w)` (`prefixWF`): a word program (`WMX`) with
five unary registers that counts `|w|`, halves it to print `size |w|` framed ones, copies `w` framed, and rewinds
(`rewindR_spec`, `Cells/Setup.lean`). The frame is the one `Code.composeFramed` (`Code/Composition.lean`) needs
between two ordinary programs.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.UnaryPrefix

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (startState wordFunction_of_wmx)

/-- The prefixed word `1^{size |w|} 0 ++ w`. -/
def prefixWord (w : List Bool) : List Bool := List.replicate (Nat.size w.length) true ++ false :: w

abbrev PS : Type := WState 1 5

/-- The input stream and the output stream. -/
def S0 : Fin 2 := 0
def SO : Fin 2 := 1
def R0 : Fin 5 := 0
def R1 : Fin 5 := 1
def R2 : Fin 5 := 2
def R3 : Fin 5 := 3
def R4 : Fin 5 := 4

/-- The states of stage P: input `w` (framed) at head `h0`, output `o` at head `h1`, the five registers. -/
def mk (w : List Bool) (h0 h1 : ℕ) (o : List Bool) (r0 r1 r2 r3 r4 : ℕ) : PS :=
  ⟨![h0, h1], ![frame w, o], ![r0, r1, r2, r3, r4], false⟩

section Mk
variable (w : List Bool) (h0 h1 : ℕ) (o : List Bool) (r0 r1 r2 r3 r4 x : ℕ)

theorem mk_v0 : (mk w h0 h1 o r0 r1 r2 r3 r4).setv R0 x = mk w h0 h1 o x r1 r2 r3 r4 :=
  WState.eq rfl rfl (by funext i; fin_cases i <;> rfl) rfl
theorem mk_v1 : (mk w h0 h1 o r0 r1 r2 r3 r4).setv R1 x = mk w h0 h1 o r0 x r2 r3 r4 :=
  WState.eq rfl rfl (by funext i; fin_cases i <;> rfl) rfl
theorem mk_v2 : (mk w h0 h1 o r0 r1 r2 r3 r4).setv R2 x = mk w h0 h1 o r0 r1 x r3 r4 :=
  WState.eq rfl rfl (by funext i; fin_cases i <;> rfl) rfl
theorem mk_v3 : (mk w h0 h1 o r0 r1 r2 r3 r4).setv R3 x = mk w h0 h1 o r0 r1 r2 x r4 :=
  WState.eq rfl rfl (by funext i; fin_cases i <;> rfl) rfl
theorem mk_v4 : (mk w h0 h1 o r0 r1 r2 r3 r4).setv R4 x = mk w h0 h1 o r0 r1 r2 r3 x :=
  WState.eq rfl rfl (by funext i; fin_cases i <;> rfl) rfl
theorem mk_h0 : (mk w h0 h1 o r0 r1 r2 r3 r4).seth S0 x = mk w x h1 o r0 r1 r2 r3 r4 :=
  WState.eq (by funext i; fin_cases i <;> rfl) rfl rfl rfl
theorem mk_h1 : (mk w h0 h1 o r0 r1 r2 r3 r4).seth SO x = mk w h0 x o r0 r1 r2 r3 r4 :=
  WState.eq (by funext i; fin_cases i <;> rfl) rfl rfl rfl
theorem mk_s1 (o' : List Bool) : (mk w h0 h1 o r0 r1 r2 r3 r4).sets SO o' = mk w h0 h1 o' r0 r1 r2 r3 r4 :=
  WState.eq rfl (by funext i; fin_cases i <;> rfl) rfl rfl

@[simp] theorem mk_val0 : (mk w h0 h1 o r0 r1 r2 r3 r4).val R0 = r0 := rfl
@[simp] theorem mk_val1 : (mk w h0 h1 o r0 r1 r2 r3 r4).val R1 = r1 := rfl
@[simp] theorem mk_val2 : (mk w h0 h1 o r0 r1 r2 r3 r4).val R2 = r2 := rfl
@[simp] theorem mk_val3 : (mk w h0 h1 o r0 r1 r2 r3 r4).val R3 = r3 := rfl
@[simp] theorem mk_val4 : (mk w h0 h1 o r0 r1 r2 r3 r4).val R4 = r4 := rfl
@[simp] theorem mk_sh0 : (mk w h0 h1 o r0 r1 r2 r3 r4).sh S0 = h0 := rfl
@[simp] theorem mk_sh1 : (mk w h0 h1 o r0 r1 r2 r3 r4).sh SO = h1 := rfl
@[simp] theorem mk_st1 : (mk w h0 h1 o r0 r1 r2 r3 r4).st SO = o := rfl
theorem mk_wbit0 : wbit (mk w h0 h1 o r0 r1 r2 r3 r4) S0 = readTapeBit (frame w) h0 := rfl

theorem start_mk : startState 1 5 w = mk w 0 0 [] 0 0 0 0 0 :=
  WState.eq (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl) rfl

end Mk

theorem frame_even (w : List Bool) (j : ℕ) : readTapeBit (frame w) (2 * j) = decide (j < w.length) := by
  induction w generalizing j with
  | nil => cases j <;> rfl
  | cons b w ih =>
    cases j with
    | zero => rfl
    | succ j =>
      rw [show 2 * (j + 1) = 2 * j + 2 by ring]
      simp only [readTapeBit, frame, List.getD_cons_succ] at ih ⊢
      rw [ih]; simp

theorem frame_eq (w : List Bool) : frame w = w.flatMap (fun b => [true, b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, ih]

/-- One framed bit on the output stream. -/
def wpair (b : Bool) : WMX 1 5 := .seq (WMX.wr SO true) (.seq (WMX.fwd SO) (.seq (WMX.wr SO b) (WMX.fwd SO)))

theorem wpair_spec (cap : ℕ) (b : Bool) (w : List Bool) (h0 : ℕ) (o : List Bool) (r0 r1 r2 r3 r4 : ℕ) :
    WXExec cap (wpair b) (mk w h0 o.length o r0 r1 r2 r3 r4) (mk w h0 (o.length + 2) (o ++ [true, b]) r0 r1 r2 r3 r4)
      7 := by
  have e1 := WXExec.wr cap SO true (mk w h0 o.length o r0 r1 r2 r3 r4)
  simp only [mk_st1, mk_sh1, wtb_end, mk_s1] at e1
  have e2 := WXExec.fwd cap SO (mk w h0 o.length (o ++ [true]) r0 r1 r2 r3 r4)
  simp only [mk_sh1, mk_h1] at e2
  have e3 := WXExec.wr cap SO b (mk w h0 (o.length + 1) (o ++ [true]) r0 r1 r2 r3 r4)
  rw [mk_st1, mk_sh1, show writeTapeBit (o ++ [true]) (o.length + 1) b = o ++ [true] ++ [b] by
    rw [show o.length + 1 = (o ++ [true]).length by simp, wtb_end], mk_s1] at e3
  have e4 := WXExec.fwd cap SO (mk w h0 (o.length + 1) (o ++ [true] ++ [b]) r0 r1 r2 r3 r4)
  simp only [mk_sh1, mk_h1] at e4
  have := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))
  rw [show o.length + 1 + 1 = o.length + 2 by ring, List.append_assoc] at this
  exact this

theorem mk_eq {w : List Bool} {h0 h1 h0' h1' : ℕ} {o o' : List Bool} {r0 r1 r2 r3 r4 r0' r1' r2' r3' r4' : ℕ}
    (e0 : h0 = h0') (e1 : h1 = h1') (eo : o = o') (f0 : r0 = r0') (f1 : r1 = r1') (f2 : r2 = r2') (f3 : r3 = r3')
    (f4 : r4 = r4') : mk w h0 h1 o r0 r1 r2 r3 r4 = mk w h0' h1' o' r0' r1' r2' r3' r4' := by
  subst e0 e1 eo f0 f1 f2 f3 f4; rfl

section Ops
variable (cap : ℕ) (w : List Bool) (h0 h1 : ℕ) (o : List Bool) (r0 r1 r2 r3 r4 : ℕ)

theorem x_fwd0 : WXExec cap (WMX.fwd S0) (mk w h0 h1 o r0 r1 r2 r3 r4) (mk w (h0 + 1) h1 o r0 r1 r2 r3 r4) 1 := by
  have := WXExec.fwd cap S0 (mk w h0 h1 o r0 r1 r2 r3 r4); rwa [mk_sh0, mk_h0] at this
theorem x_inc0 (h : r0 < cap) :
    WXExec cap (WMX.inc R0) (mk w h0 h1 o r0 r1 r2 r3 r4) (mk w h0 h1 o (r0 + 1) r1 r2 r3 r4) 3 := by
  have := WXExec.inc cap R0 (mk w h0 h1 o r0 r1 r2 r3 r4) h; rwa [mk_val0, mk_v0] at this
theorem x_inc1 (h : r1 < cap) :
    WXExec cap (WMX.inc R1) (mk w h0 h1 o r0 r1 r2 r3 r4) (mk w h0 h1 o r0 (r1 + 1) r2 r3 r4) 3 := by
  have := WXExec.inc cap R1 (mk w h0 h1 o r0 r1 r2 r3 r4) h; rwa [mk_val1, mk_v1] at this
theorem x_inc2 (h : r2 < cap) :
    WXExec cap (WMX.inc R2) (mk w h0 h1 o r0 r1 r2 r3 r4) (mk w h0 h1 o r0 r1 (r2 + 1) r3 r4) 3 := by
  have := WXExec.inc cap R2 (mk w h0 h1 o r0 r1 r2 r3 r4) h; rwa [mk_val2, mk_v2] at this
theorem x_inc3 (h : r3 < cap) :
    WXExec cap (WMX.inc R3) (mk w h0 h1 o r0 r1 r2 r3 r4) (mk w h0 h1 o r0 r1 r2 (r3 + 1) r4) 3 := by
  have := WXExec.inc cap R3 (mk w h0 h1 o r0 r1 r2 r3 r4) h; rwa [mk_val3, mk_v3] at this
theorem x_inc4 (h : r4 < cap) :
    WXExec cap (WMX.inc R4) (mk w h0 h1 o r0 r1 r2 r3 r4) (mk w h0 h1 o r0 r1 r2 r3 (r4 + 1)) 3 := by
  have := WXExec.inc cap R4 (mk w h0 h1 o r0 r1 r2 r3 r4) h; rwa [mk_val4, mk_v4] at this
theorem x_dec0 (h : r0 ≤ cap) :
    WXExec cap (WMX.dec R0) (mk w h0 h1 o r0 r1 r2 r3 r4) (mk w h0 h1 o (r0 - 1) r1 r2 r3 r4) 1 := by
  have := WXExec.dec cap R0 (mk w h0 h1 o r0 r1 r2 r3 r4) h; rwa [mk_val0, mk_v0] at this

end Ops

/-! ## Phase 1: count `|w|` (twice doubled, for the two rewinds) -/

def countP : WMX 1 5 :=
  .whs S0 (.seq (WMX.fwd S0) (.seq (WMX.fwd S0) (.seq (WMX.inc R0) (.seq (WMX.inc R2) (.seq (WMX.inc R2)
    (.seq (WMX.inc R4) (WMX.inc R4)))))))

theorem countP_spec (cap : ℕ) (w : List Bool) (hcap : 2 * w.length < cap) :
    ∀ r j, j + r = w.length → WXExec cap countP (mk w (2 * j) 0 [] j 0 (2 * j) 0 (2 * j))
      (mk w (2 * w.length) 0 [] w.length 0 (2 * w.length) 0 (2 * w.length)) (r * 25 + 1) := by
  intro r
  induction r with
  | zero =>
    intro j hj
    rw [Nat.add_zero] at hj; subst hj
    exact WXExec.whsF (by rw [mk_wbit0, frame_even]; simp)
  | succ r ih =>
    intro j hj
    have hb : wbit (mk w (2 * j) 0 [] j 0 (2 * j) 0 (2 * j)) S0 = true := by
      rw [mk_wbit0, frame_even]; simp; omega
    have e1 := x_fwd0 cap w (2 * j) 0 [] j 0 (2 * j) 0 (2 * j)
    have e2 := x_fwd0 cap w (2 * j + 1) 0 [] j 0 (2 * j) 0 (2 * j)
    have e3 := x_inc0 cap w (2 * j + 1 + 1) 0 [] j 0 (2 * j) 0 (2 * j) (by omega)
    have e4 := x_inc2 cap w (2 * j + 1 + 1) 0 [] (j + 1) 0 (2 * j) 0 (2 * j) (by omega)
    have e5 := x_inc2 cap w (2 * j + 1 + 1) 0 [] (j + 1) 0 (2 * j + 1) 0 (2 * j) (by omega)
    have e6 := x_inc4 cap w (2 * j + 1 + 1) 0 [] (j + 1) 0 (2 * j + 1 + 1) 0 (2 * j) (by omega)
    have e7 := x_inc4 cap w (2 * j + 1 + 1) 0 [] (j + 1) 0 (2 * j + 1 + 1) 0 (2 * j + 1) (by omega)
    have body := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 e7)))))
    have hst : mk w (2 * j + 1 + 1) 0 [] (j + 1) 0 (2 * j + 1 + 1) 0 (2 * j + 1 + 1) =
        mk w (2 * (j + 1)) 0 [] (j + 1) 0 (2 * (j + 1)) 0 (2 * (j + 1)) :=
      mk_eq (by ring) rfl rfl rfl rfl (by ring) rfl (by ring)
    rw [hst] at body
    exact WXExec.mono (WXExec.whsT hb body (ih (j + 1) (by omega))) (by ring_nf; omega)

/-! ## Phase 2: `size |w|` framed ones, by halving -/

def halveLoop : WMX 1 5 :=
  .whr R0 (.seq (WMX.dec R0) (.ifr R0 (.seq (WMX.dec R0) (WMX.inc R1)) WMX.skip))

theorem halveLoop_spec (cap : ℕ) (w : List Bool) (h0 h1 : ℕ) (o : List Bool) (r2 r3 r4 : ℕ) :
    ∀ r u, u + r < cap → WXExec cap halveLoop (mk w h0 h1 o r u r2 r3 r4) (mk w h0 h1 o 0 (u + r / 2) r2 r3 r4)
      (5 * r + 6) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro u hu
    rcases r with _ | _ | r
    · exact WXExec.mono (WXExec.whrF (by simp)) (by omega)
    · have e1 := x_dec0 cap w h0 h1 o 1 u r2 r3 r4 (by omega)
      have e2 : WXExec cap (.ifr R0 (.seq (WMX.dec R0) (WMX.inc R1)) WMX.skip) (mk w h0 h1 o (1 - 1) u r2 r3 r4)
          (mk w h0 h1 o 0 u r2 r3 r4) 1 := WXExec.ifrF (by simp) (WXExec.skip cap _)
      have e3 : WXExec cap halveLoop (mk w h0 h1 o 0 u r2 r3 r4) (mk w h0 h1 o 0 (u + 1 / 2) r2 r3 r4) 1 :=
        WXExec.whrF (by simp)
      exact WXExec.mono (WXExec.whrT (by simp) (WXExec.seq e1 e2) e3) (by omega)
    · have e1 := x_dec0 cap w h0 h1 o (r + 2) u r2 r3 r4 (by omega)
      have e2 := x_dec0 cap w h0 h1 o (r + 2 - 1) u r2 r3 r4 (by omega)
      have e3 := x_inc1 cap w h0 h1 o (r + 2 - 1 - 1) u r2 r3 r4 (by omega)
      have e23 : WXExec cap (.ifr R0 (.seq (WMX.dec R0) (WMX.inc R1)) WMX.skip) (mk w h0 h1 o (r + 2 - 1) u r2 r3 r4)
          (mk w h0 h1 o (r + 2 - 1 - 1) (u + 1) r2 r3 r4) 6 :=
        WXExec.mono (WXExec.ifrT (by simp) (WXExec.seq e2 e3)) (by omega)
      have hr : r + 2 - 1 - 1 = r := by omega
      rw [hr] at e23
      have e4 := ih r (by omega) (u + 1) (by omega)
      have hst : mk w h0 h1 o 0 (u + 1 + r / 2) r2 r3 r4 = mk w h0 h1 o 0 (u + (r + 2) / 2) r2 r3 r4 :=
        mk_eq rfl rfl rfl rfl (by omega) rfl rfl rfl
      rw [hst] at e4
      exact WXExec.mono (WXExec.whrT (by simp) (WXExec.seq e1 e23) e4) (by omega)

/-- `R0 := R0 / 2` (`R1` scratch at `0`). -/
def halve : WMX 1 5 := .seq halveLoop (.wm (WM.move R1 R0))

theorem halve_spec (cap : ℕ) (w : List Bool) (h0 h1 : ℕ) (o : List Bool) (r r2 r3 r4 : ℕ) (hr : r < cap) :
    WXExec cap halve (mk w h0 h1 o r 0 r2 r3 r4) (mk w h0 h1 o (r / 2) 0 r2 r3 r4) (9 * r + 8) := by
  have e1 := halveLoop_spec cap w h0 h1 o r2 r3 r4 r 0 (by omega)
  have e2 := WXExec.wm (wmove_spec cap R1 R0 (by decide) (0 + r / 2) (mk w h0 h1 o 0 (0 + r / 2) r2 r3 r4) rfl
    (by simp; omega) (by simp; omega))
  simp only [mk_val0, mk_val1, mk_v1, mk_v0] at e2
  rw [mk_eq rfl rfl rfl (show 0 + (0 + r / 2) = r / 2 by omega) rfl rfl rfl rfl] at e2
  exact WXExec.mono (WXExec.seq e1 e2) (by omega)

/-- `t` framed ones. -/
def ones (t : ℕ) : List Bool := (List.replicate t [true, true]).flatten

theorem ones_succ (t : ℕ) : ones (t + 1) = ones t ++ [true, true] := by simp [ones, List.replicate_succ']

theorem length_ones (t : ℕ) : (ones t).length = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [ones_succ, List.length_append, ih]; simp; ring

theorem size_halve (v : ℕ) (hv : v ≠ 0) : Nat.size v = Nat.size (v / 2) + 1 := by
  apply le_antisymm
  · apply Nat.size_le.2
    have := Nat.lt_size_self (v / 2)
    rw [pow_succ]; omega
  · apply Nat.lt_size.2
    rcases Nat.eq_zero_or_pos (Nat.size (v / 2)) with h | h
    · rw [h]; simp; omega
    · have h1 := Nat.lt_size.1 (show Nat.size (v / 2) - 1 < Nat.size (v / 2) by omega)
      have e : 2 ^ Nat.size (v / 2) = 2 * 2 ^ (Nat.size (v / 2) - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega

def onesP : WMX 1 5 := .whr R0 (.seq (wpair true) (.seq (WMX.inc R3) (.seq (WMX.inc R3) halve)))

theorem onesP_spec (cap : ℕ) (w : List Bool) (h0 L r2 r4 : ℕ) (hc : 2 * L + 4 < cap) :
    ∀ v t, v ≤ L → t + Nat.size v ≤ L →
      WXExec cap onesP (mk w h0 (2 * t) (ones t) v 0 r2 (2 * t) r4)
        (mk w h0 (2 * (t + Nat.size v)) (ones (t + Nat.size v)) 0 0 r2 (2 * (t + Nat.size v)) r4)
        ((9 * L + 30) * Nat.size v + 1) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro t hv ht
    by_cases h0v : v = 0
    · subst h0v
      simp only [Nat.size_zero, Nat.add_zero, Nat.mul_zero, Nat.zero_add]
      exact WXExec.whrF (by simp)
    · have hs := size_halve v h0v
      have e1 := wpair_spec cap true w h0 (ones t) v 0 r2 (2 * t) r4
      rw [length_ones, ← ones_succ, show 2 * t + 2 = 2 * (t + 1) by ring] at e1
      have e2 := x_inc3 cap w h0 (2 * (t + 1)) (ones (t + 1)) v 0 r2 (2 * t) r4 (by omega)
      have e3 := x_inc3 cap w h0 (2 * (t + 1)) (ones (t + 1)) v 0 r2 (2 * t + 1) r4 (by omega)
      rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring] at e3
      have e4 := halve_spec cap w h0 (2 * (t + 1)) (ones (t + 1)) v r2 (2 * (t + 1)) r4 (by omega)
      have e5 := ih (v / 2) (by omega) (t + 1) (by omega) (by omega)
      rw [show t + 1 + Nat.size (v / 2) = t + Nat.size v by omega] at e5
      refine WXExec.mono (WXExec.whrT (by simpa using h0v) (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))) e5) ?_
      rw [hs]; nlinarith

/-! ## Phase 5: copy `w`, framed -/

/-- The frame bits of a word. -/
def fl (l : List Bool) : List Bool := l.flatMap (fun b => [true, b])

def copyP : WMX 1 5 :=
  .whs S0 (.seq (WMX.fwd S0) (.seq (.ifs S0 (wpair true) (wpair false)) (.seq (WMX.fwd S0) (.seq (WMX.inc R3)
    (WMX.inc R3)))))

theorem copyP_spec (cap : ℕ) (w pre : List Bool) (r4 : ℕ) (hc : pre.length + 2 * w.length < cap) :
    ∀ r j, j + r = w.length →
      WXExec cap copyP (mk w (2 * j) (pre ++ fl (w.take j)).length (pre ++ fl (w.take j)) 0 0 0
        (pre ++ fl (w.take j)).length r4)
        (mk w (2 * w.length) (pre ++ fl w).length (pre ++ fl w) 0 0 0 (pre ++ fl w).length r4) (r * 22 + 1) := by
  have hfl : ∀ l : List Bool, (fl l).length = 2 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons b l ih => simp [fl] at ih ⊢; omega
  intro r
  induction r with
  | zero =>
    intro j hj
    rw [Nat.add_zero] at hj; subst hj
    rw [List.take_length]
    exact WXExec.whsF (by rw [mk_wbit0, frame_even]; simp)
  | succ r ih =>
    intro j hj
    have hjl : j < w.length := by omega
    have hb : wbit (mk w (2 * j) (pre ++ fl (w.take j)).length (pre ++ fl (w.take j)) 0 0 0
        (pre ++ fl (w.take j)).length r4) S0 = true := by rw [mk_wbit0, frame_even]; simp; omega
    set o := pre ++ fl (w.take j) with ho
    have hol : o.length = pre.length + 2 * j := by
      rw [ho, List.length_append, hfl, List.length_take]; omega
    have e1 := x_fwd0 cap w (2 * j) o.length o 0 0 0 o.length r4
    have hbit : wbit (mk w (2 * j + 1) o.length o 0 0 0 o.length r4) S0 = w[j] := by
      rw [mk_wbit0, frame_odd_rd, List.getD_eq_getElem _ _ hjl]
    have e2 : WXExec cap (.ifs S0 (wpair true) (wpair false)) (mk w (2 * j + 1) o.length o 0 0 0 o.length r4)
        (mk w (2 * j + 1) (o.length + 2) (o ++ [true, w[j]]) 0 0 0 o.length r4) 8 := by
      cases hw : w[j]
      · rw [hw] at hbit; exact WXExec.ifsF hbit (wpair_spec cap false w _ o 0 0 0 _ r4)
      · rw [hw] at hbit; exact WXExec.ifsT hbit (wpair_spec cap true w _ o 0 0 0 _ r4)
    have e3 := x_fwd0 cap w (2 * j + 1) (o.length + 2) (o ++ [true, w[j]]) 0 0 0 o.length r4
    have e4 := x_inc3 cap w (2 * j + 1 + 1) (o.length + 2) (o ++ [true, w[j]]) 0 0 0 o.length r4 (by omega)
    have e5 := x_inc3 cap w (2 * j + 1 + 1) (o.length + 2) (o ++ [true, w[j]]) 0 0 0 (o.length + 1) r4 (by omega)
    have ho' : o ++ [true, w[j]] = pre ++ fl (w.take (j + 1)) := by
      have htk : w.take (j + 1) = w.take j ++ [w[j]] := List.take_succ_eq_append_getElem hjl
      rw [ho, htk, fl, fl, List.flatMap_append, List.append_assoc]; rfl
    have hst : mk w (2 * j + 1 + 1) (o.length + 2) (o ++ [true, w[j]]) 0 0 0 (o.length + 1 + 1) r4 =
        mk w (2 * (j + 1)) (pre ++ fl (w.take (j + 1))).length (pre ++ fl (w.take (j + 1))) 0 0 0
          (pre ++ fl (w.take (j + 1))).length r4 := by
      rw [← ho']; exact mk_eq (by ring) (by simp) rfl rfl rfl rfl (by simp) rfl
    rw [hst] at e5
    exact WXExec.mono (WXExec.whsT hb (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5))))
      (ih (j + 1) (by omega))) (by ring_nf; omega)

/-! ## The whole of stage P -/

/-- **Stage P.** -/
def prefixP : WMX 1 5 :=
  .seq countP (.seq onesP (.seq (.seq (wpair false) (.seq (WMX.inc R3) (WMX.inc R3))) (.seq (rewindR S0 R2)
    (.seq copyP (.seq (WMX.wr SO false) (.seq (rewindR SO R3) (rewindR S0 R4)))))))

theorem fl_replicate (t : ℕ) : fl (List.replicate t true) = ones t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [List.replicate_succ', fl, List.flatMap_append, ← fl, ih, ones_succ]; rfl

theorem frame_prefixWord (w : List Bool) :
    frame (prefixWord w) = ones (Nat.size w.length) ++ [true, false] ++ fl w ++ [false] := by
  rw [frame_eq, prefixWord, List.flatMap_append, ← fl, fl_replicate]
  simp [fl]

theorem prefixP_spec (w : List Bool) :
    WXExec (4 * w.length + 10) prefixP (mk w 0 0 [] 0 0 0 0 0) (mk w 0 0 (frame (prefixWord w)) 0 0 0 0 0)
      (200 * (w.length + 1) ^ 2) := by
  set L := w.length with hL
  set s := Nat.size L with hs
  set cap := 4 * L + 10 with hcap
  have hsL : s ≤ L := Nat.size_le.2 Nat.lt_two_pow_self
  -- count
  have c1 := countP_spec cap w (by omega) L 0 (by omega)
  simp only [Nat.mul_zero] at c1
  -- ones
  have c2 := onesP_spec cap w (2 * L) L (2 * L) (2 * L) (by omega) L 0 le_rfl (by omega)
  simp only [Nat.mul_zero, Nat.zero_add] at c2
  rw [← hs] at c2
  -- `1 0`
  have c3a := wpair_spec cap false w (2 * L) (ones s) 0 0 (2 * L) (2 * s) (2 * L)
  rw [length_ones] at c3a
  have c3b := x_inc3 cap w (2 * L) (2 * s + 2) (ones s ++ [true, false]) 0 0 (2 * L) (2 * s) (2 * L) (by omega)
  have c3c := x_inc3 cap w (2 * L) (2 * s + 2) (ones s ++ [true, false]) 0 0 (2 * L) (2 * s + 1) (2 * L) (by omega)
  set pre := ones s ++ [true, false] with hpre
  have hpl : pre.length = 2 * s + 2 := by rw [hpre, List.length_append, length_ones]; rfl
  -- rewind the input
  have c4 := rewindR_spec cap S0 R2 (2 * L) (mk w (2 * L) (2 * s + 2) pre 0 0 (2 * L) (2 * s + 1 + 1) (2 * L))
    (by simp) (by simp) (by omega)
  rw [mk_v2, mk_h0] at c4
  -- copy
  have c5 := copyP_spec cap w pre (2 * L) (by omega) L 0 (by omega)
  simp only [Nat.mul_zero, List.take_zero, show fl [] = [] from rfl, List.append_nil] at c5
  rw [hpl] at c5
  -- the final `0`
  have c6 := WXExec.wr cap SO false (mk w (2 * L) (pre ++ fl w).length (pre ++ fl w) 0 0 0 (pre ++ fl w).length
    (2 * L))
  rw [mk_st1, mk_sh1, wtb_end, mk_s1] at c6
  -- rewind both streams
  have c7 := rewindR_spec cap SO R3 (pre ++ fl w).length
    (mk w (2 * L) (pre ++ fl w).length (pre ++ fl w ++ [false]) 0 0 0 (pre ++ fl w).length (2 * L)) (by simp)
    (by simp) (by simp [hpl, fl]; omega)
  rw [mk_v3, mk_h1] at c7
  have c8 := rewindR_spec cap S0 R4 (2 * L) (mk w (2 * L) 0 (pre ++ fl w ++ [false]) 0 0 0 0 (2 * L)) (by simp)
    (by simp) (by omega)
  rw [mk_v4, mk_h0] at c8
  have hout : pre ++ fl w ++ [false] = frame (prefixWord w) := by rw [frame_prefixWord, hpre]
  rw [← hout]
  have e3 : WXExec cap (.seq (wpair false) (.seq (WMX.inc R3) (WMX.inc R3)))
      (mk w (2 * L) (2 * s) (ones s) 0 0 (2 * L) (2 * s) (2 * L))
      (mk w (2 * L) (2 * s + 2) pre 0 0 (2 * L) (2 * s + 1 + 1) (2 * L)) 15 :=
    WXExec.seq c3a (WXExec.seq c3b c3c)
  have hfl : (pre ++ fl w).length = 2 * s + 2 + 2 * L := by
    rw [List.length_append, hpl]; simp [fl]; ring
  refine WXExec.mono (WXExec.seq c1 (WXExec.seq c2 (WXExec.seq e3 (WXExec.seq c4 (WXExec.seq c5 (WXExec.seq c6
    (WXExec.seq c7 c8))))))) ?_
  have hm : (9 * L + 30) * s ≤ (9 * L + 30) * L := Nat.mul_le_mul_left _ hsL
  nlinarith

/-- **Stage P as an ordinary word function**: `w ↦ frame (1^{size |w|} 0 ++ w)` within `200·(|w|+1)²` steps. -/
noncomputable def prefixWF : WordFunction (List Bool) id (fun w => frame (prefixWord w))
    (fun w => 200 * (w.length + 1) ^ 2) :=
  wordFunction_of_wmx prefixP SO (by decide) (fun w => 4 * w.length + 10) (fun w => by
    refine ⟨_, by rw [show id w = w from rfl, start_mk]; exact prefixP_spec w, rfl, ?_, ?_⟩
    · intro i; fin_cases i <;> rfl
    · intro q; fin_cases q <;> rfl)

end NearCubicGates.Adapters.ShortPCP.UnaryPrefix
