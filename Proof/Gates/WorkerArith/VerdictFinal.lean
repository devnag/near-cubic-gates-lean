import Proof.Gates.WorkerArith.VerdictLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Worker

section Consts
variable {w : List Bool} {W : ℕ} {pos lp bad : ℕ} (cap : ℕ)

/-- `k` increments. -/
def incs (X Y : Fin 30) : ℕ → WMX 29 16
  | 0 => WMX.skip
  | k + 1 => .seq (incs X Y k) (BinW.inc X Y 0 1)

theorem incsM {X Y : Fin 30} (hX : NumS X) (hY : NumS Y) (hXY : X ≠ Y) (hcap : 2 * W + 1 ≤ cap) :
    ∀ (k : ℕ) (wv : Fin 30 → ℕ), wv X + k < 2 ^ W →
      WXExec cap (incs X Y k) (mk w W wv pos lp bad) (mk w W (Function.update wv X (wv X + k)) pos lp bad)
        (k * (51 * (W + 1) ^ 2))
  | 0, wv, _ => by simpa [incs] using WXExec.skip cap (mk w W wv pos lp bad)
  | k + 1, wv, hk => by
    have e1 := incsM hX hY hXY hcap k wv (by omega)
    have e2 := incM (w := w) (W := W) (wv := Function.update wv X (wv X + k)) (pos := pos) (lp := lp) (bad := bad)
      cap hX hY hXY (by simp; omega) hcap
    rw [Function.update_idem] at e2
    simp only [Function.update_self] at e2
    rw [show wv X + (k + 1) = wv X + k + 1 by ring]
    refine (WXExec.seq e1 e2).mono ?_
    have := one_le_sq W
    nlinarith

/-- `X := k` (a machine constant). -/
def setC (X : Fin 30) (k : ℕ) : WMX 29 16 := .seq (BinW.zero X 4 0 1) (incs X 4 k)

theorem setCM {X : Fin 30} (hX : NumS X) (hX4 : X ≠ 4) (k : ℕ) (wv : Fin 30 → ℕ) (hk : k < 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (setC X k) (mk w W wv pos lp bad) (mk w W (Function.update wv X k) pos lp bad)
      ((51 * k + 51) * (W + 1) ^ 2) := by
  have e1 := zeroM (w := w) (W := W) (wv := wv) (pos := pos) (lp := lp) (bad := bad) cap hX
    (by unfold NumS; decide) hX4 hcap
  have e2 := incsM (w := w) (W := W) (pos := pos) (lp := lp) (bad := bad) cap hX (by unfold NumS; decide) hX4 hcap k
    (Function.update wv X 0) (by simp; omega)
  simp only [Function.update_self, Nat.zero_add, Function.update_idem] at e2
  refine (WXExec.seq e1 e2).mono ?_
  have := one_le_sq W
  nlinarith

/-- `O := a·y + b·z` for constants `a`, `b` (scratch `20`, `24`, `25`, `26`). -/
def lin2 (a b : ℕ) (Y Z O : Fin 30) : WMX 29 16 :=
  .seq (setC 24 a) (.seq (BinW.mul 24 Y 25 20 0 1 2) (.seq (setC 24 b) (.seq (BinW.mul 24 Z 26 20 0 1 2)
    (.seq (BinW.copy O 25 0 1) (BinW.add O 26 0 1)))))

/-- The scratch streams of `lin2`. -/
def Scr (X : Fin 30) : Prop := X ≠ 20 ∧ X ≠ 24 ∧ X ≠ 25 ∧ X ≠ 26

theorem lin2M (a b : ℕ) {Y Z O : Fin 30} (hY : NumS Y) (hZ : NumS Z) (hO : NumS O) (sY : Scr Y) (sZ : Scr Z)
    (sO : Scr O) (wv : Fin 30 → ℕ) (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hy : wv Y < 2 ^ W) (hz : wv Z < 2 ^ W)
    (hab : a * wv Y + b * wv Z < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    ∃ wv' : Fin 30 → ℕ, WXExec cap (lin2 a b Y Z O) (mk w W wv pos lp bad) (mk w W wv' pos lp bad)
        ((51 * (a + b) + 1000) * (W + 1) ^ 2) ∧
      wv' O = a * wv Y + b * wv Z ∧ ∀ X, Scr X → X ≠ O → wv' X = wv X := by
  obtain ⟨sY1, sY2, sY3, sY4⟩ := sY
  obtain ⟨sZ1, sZ2, sZ3, sZ4⟩ := sZ
  obtain ⟨sO1, sO2, sO3, sO4⟩ := sO
  have n20 : NumS 20 := by unfold NumS; decide
  have n24 : NumS 24 := by unfold NumS; decide
  have n25 : NumS 25 := by unfold NumS; decide
  have n26 : NumS 26 := by unfold NumS; decide
  have e1 := setCM (w := w) (W := W) (pos := pos) (lp := lp) (bad := bad) cap n24 (by decide) a wv ha hcap
  set wv1 := Function.update wv 24 a with hwv1
  have e2 := mulM (w := w) (W := W) (wv := wv1) (pos := pos) (lp := lp) (bad := bad) cap n24 hY n25 n20
    (Ne.symm sY2) (by decide) (by decide) sY3 sY1 (by decide) (by simp [hwv1, sY2]; nlinarith)
    (by simp [hwv1, sY2]; exact hy) hcap
  have hv1 : wv1 24 * wv1 Y = a * wv Y := by simp [hwv1, sY2]
  rw [hv1] at e2
  set wv2 := Function.update (Function.update wv1 25 (a * wv Y)) 20 0 with hwv2
  have e3 := setCM (w := w) (W := W) (pos := pos) (lp := lp) (bad := bad) cap n24 (by decide) b wv2 hb hcap
  set wv3 := Function.update wv2 24 b with hwv3
  have e4 := mulM (w := w) (W := W) (wv := wv3) (pos := pos) (lp := lp) (bad := bad) cap n24 hZ n26 n20
    (Ne.symm sZ2) (by decide) (by decide) sZ4 sZ1 (by decide)
    (by simp [hwv3, hwv2, hwv1, sZ1, sZ2, sZ3]; nlinarith) (by simp [hwv3, hwv2, hwv1, sZ1, sZ2, sZ3]; exact hz) hcap
  have hv3 : wv3 24 * wv3 Z = b * wv Z := by simp [hwv3, hwv2, hwv1, sZ1, sZ2, sZ3]
  rw [hv3] at e4
  set wv4 := Function.update (Function.update wv3 26 (b * wv Z)) 20 0 with hwv4
  have e5 := copyM (w := w) (W := W) (wv := wv4) (pos := pos) (lp := lp) (bad := bad) cap hO n25 sO3 hcap
  have hv4 : wv4 25 = a * wv Y := by simp [hwv4, hwv3, hwv2]
  rw [hv4] at e5
  set wv5 := Function.update wv4 O (a * wv Y) with hwv5
  have e6 := addM (w := w) (W := W) (wv := wv5) (pos := pos) (lp := lp) (bad := bad) cap hO n26 sO4
    (by simp [hwv5, hwv4, sO4, Ne.symm sO4]; exact hab) hcap
  have hv5 : wv5 O + wv5 26 = a * wv Y + b * wv Z := by simp [hwv5, hwv4, sO4, Ne.symm sO4]
  rw [hv5] at e6
  refine ⟨Function.update wv5 O (a * wv Y + b * wv Z), ?_, by simp, ?_⟩
  · refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))).mono ?_
    have := one_le_sq W
    nlinarith
  · intro X ⟨x1, x2, x3, x4⟩ xO
    simp [hwv5, hwv4, hwv3, hwv2, hwv1, Function.update_apply, x1, x2, x3, x4, xO]

/-- `23 := N^k` (`N` on stream `6`; scratch `20`, `24`). -/
def powN : ℕ → WMX 29 16
  | 0 => BinW.one 23 4 0 1
  | k + 1 => .seq (powN k) (.seq (BinW.mul 23 6 24 20 0 1 2) (BinW.copy 23 24 0 1))

theorem powNM (hW : 1 ≤ W) (hcap : 2 * W + 1 ≤ cap) :
    ∀ (k : ℕ) (wv : Fin 30 → ℕ), wv 6 ^ k < 2 ^ W → wv 6 < 2 ^ W →
      ∃ wv' : Fin 30 → ℕ, WXExec cap (powN k) (mk w W wv pos lp bad) (mk w W wv' pos lp bad)
          ((401 * k + 50) * (W + 1) ^ 2) ∧
        wv' 23 = wv 6 ^ k ∧ ∀ X : Fin 30, X ≠ 20 → X ≠ 23 → X ≠ 24 → wv' X = wv X
  | 0, wv, _, _ => ⟨Function.update wv 23 1, by
      simpa [powN] using oneM (w := w) (W := W) (wv := wv) (pos := pos) (lp := lp) (bad := bad) cap
        (X := 23) (Y := 4) (by unfold NumS; decide) (by unfold NumS; decide) (by decide) hW hcap, by simp,
      fun X _ h23 _ => by simp [h23]⟩
  | k + 1, wv, hk, hN => by
    have hk' : wv 6 ^ k < 2 ^ W := by
      rcases Nat.eq_zero_or_pos (wv 6) with h0 | h0
      · rw [h0]
        calc 0 ^ k ≤ 1 := by cases k <;> simp
          _ < 2 ^ W := Nat.one_lt_two_pow (by omega)
      · exact lt_of_le_of_lt (Nat.pow_le_pow_right h0 (by omega)) hk
    obtain ⟨wv1, e1, h23, hfr⟩ := powNM hW hcap k wv hk' hN
    have h6 : wv1 6 = wv 6 := hfr 6 (by decide) (by decide) (by decide)
    have e2 := mulM (w := w) (W := W) (wv := wv1) (pos := pos) (lp := lp) (bad := bad) cap (A := 23) (B := 6)
      (C := 24) (S := 20) (by unfold NumS; decide) (by unfold NumS; decide) (by unfold NumS; decide)
      (by unfold NumS; decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [h23, h6, ← pow_succ]; exact hk) (by rw [h6]; exact hN) hcap
    rw [h23, h6, ← pow_succ] at e2
    set wv2 := Function.update (Function.update wv1 24 (wv 6 ^ (k + 1))) 20 0 with hwv2
    have e3 := copyM (w := w) (W := W) (wv := wv2) (pos := pos) (lp := lp) (bad := bad) cap (X := 23) (Y := 24)
      (by unfold NumS; decide) (by unfold NumS; decide) (by decide) hcap
    refine ⟨_, (WXExec.seq e1 (WXExec.seq e2 e3)).mono ?_, by simp [hwv2], ?_⟩
    · have := one_le_sq W; nlinarith
    · intro X h20 h23' h24
      simp [hwv2, h20, h23', h24, hfr X h20 h23' h24]

end Consts

/-! ## The tests -/

section Tests
variable {w : List Bool} {W : ℕ} {pos lp : ℕ} (cap : ℕ)

theorem bumpM (wv : Fin 30 → ℕ) (bad : ℕ) (h : bad < cap) :
    WXExec cap (WMX.inc 12) (mk w W wv pos lp bad) (mk w W wv pos lp (bad + 1)) 3 := by
  have e := WXExec.inc cap 12 (mk w W wv pos lp bad) (by simp [regs]; exact h)
  rwa [mk_val, show regs W w.length lp bad 12 = bad by simp [regs], mk_setv_bad] at e

/-- A test whose flag `b` means failure. -/
theorem failT {r : Fin 16} (hr : ∀ bad, regs W w.length lp bad r = 0) (wv : Fin 30 → ℕ) (bad : ℕ) (b : Bool)
    (h : bad < cap) :
    WXExec cap (.ifr r (.seq (WMX.dec r) (WMX.inc 12)) WMX.skip) ((mk w W wv pos lp bad).setv r b.toNat)
      (mk w W wv pos lp (bad + b.toNat)) 6 :=
  flagM cap (hr bad) b (fun hb => by subst hb; exact bumpM cap wv bad h)
    (fun hb => by subst hb; simpa using (WXExec.skip cap (mk w W wv pos lp bad)).mono (Nat.zero_le 3)) (by omega)

/-- A test whose flag `b` means success. -/
theorem failF {r : Fin 16} (hr : ∀ bad, regs W w.length lp bad r = 0) (wv : Fin 30 → ℕ) (bad : ℕ) (b : Bool)
    (h : bad < cap) :
    WXExec cap (.ifr r (.seq (WMX.dec r) WMX.skip) (WMX.inc 12)) ((mk w W wv pos lp bad).setv r b.toNat)
      (mk w W wv pos lp (bad + (!b).toNat)) 6 :=
  flagM cap (hr bad) b (fun hb => by subst hb; simpa using (WXExec.skip cap (mk w W wv pos lp bad)).mono (Nat.zero_le 3))
    (fun hb => by subst hb; exact bumpM cap wv bad h) (by omega)

/-- `rb ≤ cl` (fails iff `cl < rb`). -/
def g1 : WMX 29 16 := .seq (BinW.lt 8 7 0 1) (.ifr 0 (.seq (WMX.dec 0) (WMX.inc 12)) WMX.skip)

theorem g1M (wv : Fin 30 → ℕ) (bad : ℕ) (h7 : wv 7 < 2 ^ W) (h8 : wv 8 < 2 ^ W) (hb : bad < cap)
    (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap g1 (mk w W wv pos lp bad) (mk w W wv pos lp (bad + (decide (wv 8 < wv 7)).toNat))
      (60 * (W + 1) ^ 2) := by
  have e1 := ltM (w := w) (W := W) (wv := wv) (pos := pos) (lp := lp) (bad := bad) cap (X := 8) (Y := 7)
    (by unfold NumS; decide) (by unfold NumS; decide) (by decide) h8 h7 hcap
  have e2 := failT (w := w) (W := W) (pos := pos) (lp := lp) cap (r := 0) (fun _ => rfl) wv bad
    (decide (wv 8 < wv 7)) hb
  exact (WXExec.seq e1 e2).mono (by have := one_le_sq W; omega)

/-- `2 ≤ q` (fails iff `q < 2`; the constant `2` on stream `29`). -/
def g2 : WMX 29 16 := .seq (setC 29 2) (.seq (BinW.lt 4 29 0 1) (.ifr 0 (.seq (WMX.dec 0) (WMX.inc 12)) WMX.skip))

theorem g2M (wv : Fin 30 → ℕ) (bad : ℕ) (h4 : wv 4 < 2 ^ W) (hW : 2 ≤ W) (hb : bad < cap)
    (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap g2 (mk w W wv pos lp bad)
      (mk w W (Function.update wv 29 2) pos lp (bad + (decide (wv 4 < 2)).toNat)) (300 * (W + 1) ^ 2) := by
  have h2 : 2 < 2 ^ W := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have e0 := setCM (w := w) (W := W) (pos := pos) (lp := lp) (bad := bad) cap (X := 29) (by unfold NumS; decide)
    (by decide) 2 wv h2 hcap
  have e1 := ltM (w := w) (W := W) (wv := Function.update wv 29 2) (pos := pos) (lp := lp) (bad := bad) cap
    (X := 4) (Y := 29) (by unfold NumS; decide) (by unfold NumS; decide) (by decide) (by simpa using h4)
    (by simpa using h2) hcap
  simp only [Function.update_self, ne_eq, show (4 : Fin 30) ≠ 29 by decide, not_false_eq_true,
    Function.update_of_ne] at e1
  have e2 := failT (w := w) (W := W) (pos := pos) (lp := lp) cap (r := 0) (fun _ => rfl) (Function.update wv 29 2)
    bad (decide (wv 4 < 2)) hb
  exact (WXExec.seq e0 (WXExec.seq e1 e2)).mono (by have := one_le_sq W; nlinarith)

/-- `1 ≤ N` (fails iff `N = 0`). -/
def g3 : WMX 29 16 := .seq (nzP 6 4 11 0 1) (.ifr 11 (.seq (WMX.dec 11) WMX.skip) (WMX.inc 12))

theorem g3M (wv : Fin 30 → ℕ) (bad : ℕ) (h6 : wv 6 < 2 ^ W) (hb : bad < cap) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap g3 (mk w W wv pos lp bad) (mk w W wv pos lp (bad + (decide (wv 6 = 0)).toNat)) (60 * (W + 1) ^ 2) := by
  have e1 := nzM (w := w) (W := W) (wv := wv) (pos := pos) (lp := lp) (bad := bad) cap (X := 6) (Z := 4)
    (by unfold NumS; decide) (by unfold NumS; decide) (by decide) h6 hcap
  have e2 := failF (w := w) (W := W) (pos := pos) (lp := lp) cap (r := 11) (fun _ => rfl) wv bad
    (decide (wv 6 ≠ 0)) hb
  have hn : (!decide (wv 6 ≠ 0)) = decide (wv 6 = 0) := by by_cases h : wv 6 = 0 <;> simp [h]
  rw [hn] at e2
  exact (WXExec.seq e1 e2).mono (by have := one_le_sq W; omega)

/-- `A + B·N^{10} < C + D'·N^{10}` (the guard `γ < εT·N^{10}`; fails iff false). -/
def g4 (A B C D' : ℕ) : WMX 29 16 :=
  .seq (powN 10) (.seq (lin2 A B 9 23 27) (.seq (lin2 C D' 9 23 28) (.seq (BinW.lt 27 28 0 1)
    (.ifr 0 (.seq (WMX.dec 0) WMX.skip) (WMX.inc 12)))))

/-- The streams the tests write. -/
def TScr (X : Fin 30) : Prop := X.val < 20 ∧ X ≠ 5

theorem g4M (A B C D' : ℕ) (wv : Fin 30 → ℕ) (bad : ℕ) (h9 : wv 9 = 1) (hN : wv 6 < 2 ^ W)
    (hX : wv 6 ^ 10 < 2 ^ W) (hA : A + B * wv 6 ^ 10 < 2 ^ W) (hC : C + D' * wv 6 ^ 10 < 2 ^ W)
    (hB : B < 2 ^ W) (hD : D' < 2 ^ W) (hW : 1 ≤ W) (hb : bad < cap) (hcap : 2 * W + 1 ≤ cap) :
    ∃ wv' : Fin 30 → ℕ, WXExec cap (g4 A B C D') (mk w W wv pos lp bad)
        (mk w W wv' pos lp (bad + (!decide (A + B * wv 6 ^ 10 < C + D' * wv 6 ^ 10)).toNat))
        ((51 * (A + B + C + D') + 7000) * (W + 1) ^ 2) ∧ ∀ X, TScr X → wv' X = wv X := by
  obtain ⟨wv1, e1, h23, fr1⟩ := powNM (w := w) (W := W) (pos := pos) (lp := lp) (bad := bad) cap hW hcap 10 wv hX hN
  have v9 : wv1 9 = 1 := by rw [fr1 9 (by decide) (by decide) (by decide), h9]
  obtain ⟨wv2, e2, h27, fr2⟩ := lin2M (w := w) (W := W) (pos := pos) (lp := lp) (bad := bad) cap A B (Y := 9)
    (Z := 23) (O := 27) (by unfold NumS; decide) (by unfold NumS; decide) (by unfold NumS; decide)
    (by unfold Scr; decide) (by unfold Scr; decide) (by unfold Scr; decide) wv1 (by omega) hB
    (by rw [v9]; exact Nat.one_lt_two_pow (by omega)) (by rw [h23]; exact hX) (by rw [v9, h23]; simpa using hA) hcap
  have v9' : wv2 9 = 1 := by rw [fr2 9 (by unfold Scr; decide) (by decide), v9]
  have v23 : wv2 23 = wv 6 ^ 10 := by rw [fr2 23 (by unfold Scr; decide) (by decide), h23]
  obtain ⟨wv3, e3, h28, fr3⟩ := lin2M (w := w) (W := W) (pos := pos) (lp := lp) (bad := bad) cap C D' (Y := 9)
    (Z := 23) (O := 28) (by unfold NumS; decide) (by unfold NumS; decide) (by unfold NumS; decide)
    (by unfold Scr; decide) (by unfold Scr; decide) (by unfold Scr; decide) wv2 (by omega) hD
    (by rw [v9']; exact Nat.one_lt_two_pow (by omega)) (by rw [v23]; exact hX) (by rw [v9', v23]; simpa using hC)
    hcap
  have v27 : wv3 27 = A + B * wv 6 ^ 10 := by rw [fr3 27 (by unfold Scr; decide) (by decide), h27, v9, h23]; ring
  have v28 : wv3 28 = C + D' * wv 6 ^ 10 := by rw [h28, v9', v23]; ring
  have e4 := ltM (w := w) (W := W) (wv := wv3) (pos := pos) (lp := lp) (bad := bad) cap (X := 27) (Y := 28)
    (by unfold NumS; decide) (by unfold NumS; decide) (by decide) (by rw [v27]; exact hA) (by rw [v28]; exact hC)
    hcap
  rw [v27, v28] at e4
  have e5 := failF (w := w) (W := W) (pos := pos) (lp := lp) cap (r := 0) (fun _ => rfl) wv3 bad
    (decide (A + B * wv 6 ^ 10 < C + D' * wv 6 ^ 10)) hb
  refine ⟨wv3, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).mono ?_, ?_⟩
  · have := one_le_sq W; nlinarith
  · intro X ⟨hx, _⟩
    have s : Scr X := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> simp at hx
    rw [fr3 X s (by intro e; subst e; simp at hx), fr2 X s (by intro e; subst e; simp at hx),
      fr1 X (by intro e; subst e; simp at hx) (by intro e; subst e; simp at hx) (by intro e; subst e; simp at hx)]

/-- The acceptance test: `M' := max M 1`, `Y := 2M'·D`, `a₁Y + b₁·POS < a₂Y + b₂·NEG`. -/
def fin (a1 b1 a2 b2 : ℕ) : WMX 29 16 :=
  .seq (nzP 5 4 11 0 1) (.seq (.ifr 11 (.seq (WMX.dec 11) WMX.skip) (BinW.one 5 4 0 1))
    (.seq (BinW.mul 5 10 22 20 0 1 2) (.seq (BinW.shl 22 4 0 1) (.seq (lin2 a1 b1 22 11 27) (.seq (lin2 a2 b2 22 12 28)
      (.seq (BinW.lt 27 28 0 1) (.ifr 0 (.seq (WMX.dec 0) WMX.skip) (WMX.inc 12))))))))

theorem finM (a1 b1 a2 b2 : ℕ) (wv : Fin 30 → ℕ) (bad : ℕ) (h5 : wv 5 < 2 ^ W)
    (hY : 2 * (max (wv 5) 1 * wv 10) < 2 ^ W)
    (hL : a1 * (2 * (max (wv 5) 1 * wv 10)) + b1 * wv 11 < 2 ^ W)
    (hR : a2 * (2 * (max (wv 5) 1 * wv 10)) + b2 * wv 12 < 2 ^ W) (h11 : wv 11 < 2 ^ W) (h12 : wv 12 < 2 ^ W)
    (ha1 : a1 < 2 ^ W) (hb1 : b1 < 2 ^ W) (ha2 : a2 < 2 ^ W) (hb2 : b2 < 2 ^ W) (hW : 1 ≤ W) (hb : bad < cap)
    (hcap : 2 * W + 1 ≤ cap) :
    ∃ wv' : Fin 30 → ℕ, WXExec cap (fin a1 b1 a2 b2) (mk w W wv pos lp bad)
        (mk w W wv' pos lp (bad + (!decide (a1 * (2 * (max (wv 5) 1 * wv 10)) + b1 * wv 11 <
          a2 * (2 * (max (wv 5) 1 * wv 10)) + b2 * wv 12)).toNat))
        ((51 * (a1 + b1 + a2 + b2) + 7000) * (W + 1) ^ 2) ∧ ∀ X, TScr X → X ≠ 5 → wv' X = wv X := by
  set m := max (wv 5) 1 with hm
  have e1 := nzM (w := w) (W := W) (wv := wv) (pos := pos) (lp := lp) (bad := bad) cap (X := 5) (Z := 4)
    (by unfold NumS; decide) (by unfold NumS; decide) (by decide) h5 hcap
  have e2 := flagM (w := w) (W := W) (wv := wv) (pos := pos) (lp := lp) (bad := bad) cap (r := 11) rfl
    (decide (wv 5 ≠ 0)) (P := WMX.skip) (Q := BinW.one 5 4 0 1)
    (τ := mk w W (Function.update wv 5 m) pos lp bad) (c := 50 * (W + 1) ^ 2)
    (fun h => by
      have h0 : wv 5 ≠ 0 := by simpa using h
      have : m = wv 5 := by rw [hm]; exact max_eq_left (by omega)
      rw [this, Function.update_eq_self]
      exact (WXExec.skip cap _).mono (Nat.zero_le _))
    (fun h => by
      have h0 : wv 5 = 0 := by simpa using h
      have : m = 1 := by rw [hm, h0]; rfl
      rw [this]
      exact oneM (w := w) (W := W) (wv := wv) (pos := pos) (lp := lp) (bad := bad) cap (X := 5) (Y := 4)
        (by unfold NumS; decide) (by unfold NumS; decide) (by decide) hW hcap) (by omega)
  set wv1 := Function.update wv 5 m with hwv1
  have e3 := mulM (w := w) (W := W) (wv := wv1) (pos := pos) (lp := lp) (bad := bad) cap (A := 5) (B := 10) (C := 22)
    (S := 20) (by unfold NumS; decide) (by unfold NumS; decide) (by unfold NumS; decide) (by unfold NumS; decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [show wv1 5 = m by simp [hwv1], show wv1 10 = wv 10 by simp [hwv1]]; omega)
    (by rw [show wv1 10 = wv 10 by simp [hwv1]]; nlinarith [Nat.le_max_right (wv 5) 1]) hcap
  have v1 : wv1 5 * wv1 10 = m * wv 10 := by simp [hwv1]
  rw [v1] at e3
  set wv2 := Function.update (Function.update wv1 22 (m * wv 10)) 20 0 with hwv2
  have e4 := shlM (w := w) (W := W) (wv := wv2) (pos := pos) (lp := lp) (bad := bad) cap (X := 22) (Y := 4)
    (by unfold NumS; decide) (by unfold NumS; decide) (by decide) hcap
  have v2 : 2 * wv2 22 = 2 * (m * wv 10) := by simp [hwv2]
  rw [v2] at e4
  set wv3 := Function.update wv2 22 (2 * (m * wv 10)) with hwv3
  have y3 : wv3 22 = 2 * (m * wv 10) := by simp [hwv3]
  have p3 : wv3 11 = wv 11 := by simp [hwv3, hwv2, hwv1]
  have n3 : wv3 12 = wv 12 := by simp [hwv3, hwv2, hwv1]
  obtain ⟨wv4, e5, h27, fr4⟩ := lin2M (w := w) (W := W) (pos := pos) (lp := lp) (bad := bad) cap a1 b1 (Y := 22)
    (Z := 11) (O := 27) (by unfold NumS; decide) (by unfold NumS; decide) (by unfold NumS; decide)
    (by unfold Scr; decide) (by unfold Scr; decide) (by unfold Scr; decide) wv3 ha1 hb1 (by rw [y3]; exact hY)
    (by rw [p3]; exact h11) (by rw [y3, p3]; exact hL) hcap
  have y4 : wv4 22 = 2 * (m * wv 10) := by rw [fr4 22 (by unfold Scr; decide) (by decide), y3]
  have n4 : wv4 12 = wv 12 := by rw [fr4 12 (by unfold Scr; decide) (by decide), n3]
  obtain ⟨wv5, e6, h28, fr5⟩ := lin2M (w := w) (W := W) (pos := pos) (lp := lp) (bad := bad) cap a2 b2 (Y := 22)
    (Z := 12) (O := 28) (by unfold NumS; decide) (by unfold NumS; decide) (by unfold NumS; decide)
    (by unfold Scr; decide) (by unfold Scr; decide) (by unfold Scr; decide) wv4 ha2 hb2 (by rw [y4]; exact hY)
    (by rw [n4]; exact h12) (by rw [y4, n4]; exact hR) hcap
  have v27 : wv5 27 = a1 * (2 * (m * wv 10)) + b1 * wv 11 := by
    rw [fr5 27 (by unfold Scr; decide) (by decide), h27, y3, p3]
  have v28 : wv5 28 = a2 * (2 * (m * wv 10)) + b2 * wv 12 := by rw [h28, y4, n4]
  have e7 := ltM (w := w) (W := W) (wv := wv5) (pos := pos) (lp := lp) (bad := bad) cap (X := 27) (Y := 28)
    (by unfold NumS; decide) (by unfold NumS; decide) (by decide) (by rw [v27]; exact hL) (by rw [v28]; exact hR)
    hcap
  rw [v27, v28] at e7
  have e8 := failF (w := w) (W := W) (pos := pos) (lp := lp) cap (r := 0) (fun _ => rfl) wv5 bad
    (decide (a1 * (2 * (m * wv 10)) + b1 * wv 11 < a2 * (2 * (m * wv 10)) + b2 * wv 12)) hb
  refine ⟨wv5, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 e8))))))).mono ?_, ?_⟩
  · have := one_le_sq W; nlinarith
  · intro X ⟨hx, _⟩ h5'
    have s : Scr X := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> simp at hx
    have h22 : X ≠ 22 := by intro e; subst e; simp at hx
    have h20 : X ≠ 20 := by intro e; subst e; simp at hx
    rw [fr5 X s (by intro e; subst e; simp at hx), fr4 X s (by intro e; subst e; simp at hx)]
    simp [hwv3, hwv2, hwv1, h22, h20, h5']

end Tests

end NearCubicGates.Close.WorkerArith
