import Proof.Gates.WorkerArith.VerdictSetup

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

/-! ## `D := 2^L` and the gadget counter -/

section Pre
variable {w : List Bool} {W : ℕ} {pos lp bad : ℕ} (cap : ℕ)

/-- `D := 2^L` on stream `10` (`L` in register `8`). -/
def pow2P : WMX 29 16 := .seq (BinW.one 10 4 0 1) (repK 8 9 (BinW.shl 10 4 0 1))

theorem pow2M (wv : Fin 30 → ℕ) (hW : w.length + 1 ≤ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap pow2P (mk w W wv pos lp bad) (mk w W (Function.update wv 10 (2 ^ w.length)) pos lp bad)
      (100 * (W + 1) ^ 2) := by
  have e1 := oneM (w := w) (W := W) (wv := wv) (pos := pos) (lp := lp) (bad := bad) cap (X := 10) (Y := 4)
    (by unfold NumS; decide) (by unfold NumS; decide) (by decide) (by omega) hcap
  set st : ℕ → WState 29 16 := fun j => mk w W (Function.update wv 10 (2 ^ j)) pos lp bad with hst
  have e2 := Runs.repE (cap := cap) (body := BinW.shl 10 4 0 1) (K := 8) (K2 := 9) (by decide) (41 * W + 8)
    w.length st (by omega) (fun k => by simp [hst]) (fun k => by simp [hst])
    (fun j hj v1 v2 => by
      have n10 : NumOn (st j) 10 W (2 ^ j) := by
        have := mk_numOn w W (Function.update wv 10 (2 ^ j)) pos lp bad (X := 10) (by unfold NumS; decide)
        simpa [hst] using this
      have n4 : NumOn (st j) 4 W (wv 4) := by
        have := mk_numOn w W (Function.update wv 10 (2 ^ j)) pos lp bad (X := 4) (by unfold NumS; decide)
        simpa [hst] using this
      have h := BinW.shl_spec cap W (A := 10) (B := 4) (F := 0) (R := 1) (by decide) (by decide)
        (((st j).setv 8 v1).setv 9 v2) (2 ^ j) (wv 4)
        (BinW.numOn_setv (BinW.numOn_setv n10 _ _) _ _) (BinW.numOn_setv (BinW.numOn_setv n4 _ _) _ _)
        (by simp [hst, regs]) (by simp [hst, regs]) hcap
      refine h.cast cap ?_ le_rfl
      have e : (((st j).setv 8 v1).setv 9 v2).sets 10 (frame (binary W (2 * 2 ^ j))) =
          (((st j).sets 10 (frame (binary W (2 * 2 ^ j)))).setv 8 v1).setv 9 v2 := rfl
      rw [e, hst]
      simp only
      rw [mk_sets _ _ _ _ _ _ (by unfold NumS; decide), Function.update_idem, ← pow_succ']) (by simp [hst, regs])
    (by simp [hst, regs])
  simp only [hst, pow_zero] at e2
  refine (WXExec.seq e1 e2).mono ?_
  have := one_le_sq W
  have h1 : w.length * (41 * W + 8 + 8) ≤ W * (41 * W + 16) := Nat.mul_le_mul (by omega) le_rfl
  nlinarith

/-- The gadget counter: copy `M` (stream `5`) to `22`, count it into register `10`. -/
def counterP : WMX 29 16 := .seq (BinW.copy 22 5 0 1) (toReg 22 9 4 10 11 0 1)

theorem counterM (wv : Fin 30 → ℕ) (h9 : wv 9 = 1) (hM : wv 5 < 2 ^ W) (hMc : wv 5 ≤ W) (hcap : 4 * W + 4 ≤ cap) :
    WXExec cap counterP (mk w W wv pos 0 bad) (mk w W (Function.update wv 22 0) pos (wv 5) bad)
      (200 * (W + 1) ^ 2) := by
  have e1 := copyM (w := w) (W := W) (wv := wv) (pos := pos) (lp := 0) (bad := bad) cap (X := 22) (Y := 5)
    (by unfold NumS; decide) (by unfold NumS; decide) (by decide) (by omega)
  have e2 := toReg_spec cap W (X := 22) (ONE := 9) (Z := 4) (R := 10) (NZ := 11) (F := 0) (Rr := 1) (by decide)
    (by decide) (mk w W (Function.update wv 22 (wv 5)) pos 0 bad) (wv 5) (wv 4) 0
    (by simpa using mk_numOn w W (Function.update wv 22 (wv 5)) pos 0 bad (X := 22) (by unfold NumS; decide))
    (by simpa [h9] using mk_numOn w W (Function.update wv 22 (wv 5)) pos 0 bad (X := 9) (by unfold NumS; decide))
    (by simpa using mk_numOn w W (Function.update wv 22 (wv 5)) pos 0 bad (X := 4) (by unfold NumS; decide))
    (by simp [regs]) (by simp [regs]) (by simp [regs]) (by simp [regs]) hM (by omega) (by omega)
  rw [mk_sets _ _ _ _ _ _ (by unfold NumS; decide), Function.update_idem, Nat.zero_add, mk_setv_lp] at e2
  refine (WXExec.seq e1 e2).mono ?_
  have := one_le_sq W
  have h1 : wv 5 * (83 * W + 30) ≤ W * (83 * W + 30) := Nat.mul_le_mul hMc le_rfl
  nlinarith

end Pre

/-! ## Output and clean-up -/

/-- Write `[true, false, [BAD = 0]]` on stream `1` (`= bitWord`), rewind the raw word, clear the registers. -/
def outP : WMX 29 16 :=
  .seq (WMX.wr 1 true) (.seq (WMX.fwd 1) (.seq (WMX.wr 1 false) (.seq (WMX.fwd 1)
    (.seq (.ifr 12 (.seq (.wm (WM.clear 12)) (WMX.wr 1 false)) (WMX.wr 1 true))
      (.seq (WMX.bwd 1) (.seq (WMX.bwd 1) (.seq (.wm (WM.rewind 2 8)) (.seq (.wm (WM.clear 6))
        (.wm (WM.clear 7))))))))))

theorem outM (cap : ℕ) (w : List Bool) (W : ℕ) (wv : Fin 30 → ℕ) (bad : ℕ) (hb : bad ≤ cap) (hW : w.length ≤ W)
    (hcap : 2 * W + 1 ≤ cap) :
    ∃ τ : WState 29 16, WXExec cap outP (mk w W wv w.length 0 bad) τ (20 * W + 3 * bad + 60) ∧
      τ.st 1 = [true, false, decide (bad = 0)] ∧ (∀ i, τ.sh i = 0) ∧ ∀ q, τ.val q = 0 := by
  set σ := mk w W wv w.length 0 bad with hσ
  have o1 := WXExec.wr cap 1 true σ
  have o2 := WXExec.fwd cap 1 (σ.sets 1 (writeTapeBit (σ.st 1) (σ.sh 1) true))
  have o3 := WXExec.wr cap 1 false ((σ.sets 1 (writeTapeBit (σ.st 1) (σ.sh 1) true)).seth 1
    ((σ.sets 1 (writeTapeBit (σ.st 1) (σ.sh 1) true)).sh 1 + 1))
  set σ3 := ((σ.sets 1 [true, false]).seth 1 1) with hσ3
  have e3 : ((σ.sets 1 (writeTapeBit (σ.st 1) (σ.sh 1) true)).seth 1
      ((σ.sets 1 (writeTapeBit (σ.st 1) (σ.sh 1) true)).sh 1 + 1)).sets 1
      (writeTapeBit (((σ.sets 1 (writeTapeBit (σ.st 1) (σ.sh 1) true)).seth 1
        ((σ.sets 1 (writeTapeBit (σ.st 1) (σ.sh 1) true)).sh 1 + 1)).st 1)
        (((σ.sets 1 (writeTapeBit (σ.st 1) (σ.sh 1) true)).seth 1
        ((σ.sets 1 (writeTapeBit (σ.st 1) (σ.sh 1) true)).sh 1 + 1)).sh 1) false) = σ3 := by
    apply WState.eq
    · funext i; by_cases hi : i = 1
      · subst hi; simp [hσ3, hσ, mk]
      · simp [hσ3, Function.update_of_ne hi]
    · funext i; by_cases hi : i = 1
      · subst hi; simp [hσ3, hσ, mk, writeTapeBit]
      · simp [hσ3, Function.update_of_ne hi]
    · rfl
    · rfl
  rw [e3] at o3
  have o4 := WXExec.fwd cap 1 σ3
  set σ4 := σ3.seth 1 (σ3.sh 1 + 1) with hσ4
  set b := decide (bad = 0) with hbdef
  set σ5 := (σ4.sets 1 [true, false, b]).setv 12 0 with hσ5
  have o5 : WXExec cap (.ifr 12 (.seq (.wm (WM.clear 12)) (WMX.wr 1 false)) (WMX.wr 1 true)) σ4 σ5 (3 * bad + 5) := by
    have hv : σ4.val 12 = bad := by simp [hσ4, hσ3, hσ, regs]
    have hst : σ4.st 1 = [true, false] := by simp [hσ4, hσ3]
    have hsh : σ4.sh 1 = 2 := by simp [hσ4, hσ3]
    by_cases h0 : bad = 0
    · have hb' : b = true := by simp [hbdef, h0]
      have w1 := WXExec.wr cap 1 true σ4
      rw [hst, hsh] at w1
      refine (WXExec.ifrF (by rw [hv, h0]) w1).cast cap ?_ (by omega)
      rw [hσ5, hb']
      have : (σ4.sets 1 (writeTapeBit [true, false] 2 true)) = σ4.sets 1 [true, false, true] := rfl
      rw [this]
      apply WState.eq <;> try rfl
      funext q; by_cases hq : q = 12
      · subst hq; simp [hv, h0]
      · simp [Function.update_of_ne hq]
    · have hb' : b = false := by simp [hbdef, h0]
      have c1 := wclear_spec (cap := cap) (12 : Fin 16) bad σ4 hv (by omega)
      have w1 := WXExec.wr cap 1 false (σ4.setv 12 0)
      simp only [WState.setv_st, WState.setv_sh, hst, hsh] at w1
      refine (WXExec.ifrT (by rw [hv]; exact h0) (WXExec.seq (WXExec.wm c1) w1)).cast cap ?_ (by omega)
      rw [hσ5, hb']
      apply WState.eq <;> rfl
  have o6 := WXExec.bwd cap 1 σ5
  have o7 := WXExec.bwd cap 1 (σ5.seth 1 (σ5.sh 1 - 1))
  set σ7 := (σ5.seth 1 (σ5.sh 1 - 1)).seth 1 ((σ5.seth 1 (σ5.sh 1 - 1)).sh 1 - 1) with hσ7
  have o8 := wrewind_spec (cap := cap) (2 : Fin 30) (8 : Fin 16) w.length σ7 (by simp [hσ7, hσ5, hσ4, hσ3, hσ, regs])
    (by simp [hσ7, hσ5, hσ4, hσ3, hσ, regs]; omega)
  set σ8 := (σ7.setv 8 0).seth 2 (σ7.sh 2 - w.length) with hσ8
  have o9 := wclear_spec (cap := cap) (6 : Fin 16) (2 * W + 1) σ8 (by simp [hσ8, hσ7, hσ5, hσ4, hσ3, hσ, regs])
    (by simp [hσ8, hσ7, hσ5, hσ4, hσ3, hσ, regs]; omega)
  have o10 := wclear_spec (cap := cap) (7 : Fin 16) W (σ8.setv 6 0) (by simp [hσ8, hσ7, hσ5, hσ4, hσ3, hσ, regs])
    (by simp [hσ8, hσ7, hσ5, hσ4, hσ3, hσ, regs]; omega)
  refine ⟨_, (WXExec.seq o1 (WXExec.seq o2 (WXExec.seq o3 (WXExec.seq o4 (WXExec.seq o5 (WXExec.seq o6
    (WXExec.seq o7 (WXExec.seq (WXExec.wm o8) (WXExec.seq (WXExec.wm o9) (WXExec.wm o10)))))))))).mono ?_, ?_, ?_, ?_⟩
  · omega
  · simp [hσ8, hσ7, hσ5]
  · intro i
    by_cases h1 : i = 1
    · subst h1; simp [hσ8, hσ7, hσ5, hσ4, hσ3]
    · by_cases h2 : i = 2
      · subst h2; simp [hσ8, hσ7, hσ5, hσ4, hσ3, hσ, mk]
      · simp [hσ8, hσ7, hσ5, hσ4, hσ3, hσ, mk, Function.update_of_ne h1, Function.update_of_ne h2, h2]
  · intro q
    fin_cases q <;> simp [hσ8, hσ7, hσ5, hσ4, hσ3, hσ, mk, regs]

end NearCubicGates.Close.WorkerArith
