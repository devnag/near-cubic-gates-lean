import Proof.Gates.ENP.ListedEmit
import Proof.Wire_3_5.FinalPassHashTable

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP.EmitNat
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wdup wdup_spec)

variable {ns nr : ℕ} {cap : ℕ}

/-- Append the fixed list `l` to the output stream `O`. -/
def emitList (O : Fin (ns + 1)) (CO : Fin nr) : List Bool → WMX ns nr
  | [] => WMX.skip
  | b :: l => .seq (emitO O CO b) (emitList O CO l)

theorem emitList_exec (O : Fin (ns + 1)) (CO : Fin nr) :
    ∀ (l : List Bool) (σ : WState ns nr) (out L0 : List Bool), OutOn σ O CO out L0 →
      out.length + l.length < cap + 1 →
      WXExec cap (emitList O CO l) σ (outSt σ O CO (out ++ l) L0) (8 * l.length)
  | [], σ, out, L0, hO, _ => by
    simp only [emitList, List.append_nil, List.length_nil, Nat.mul_zero]
    rw [outSt_self σ hO]
    exact WXExec.skip cap σ
  | b :: l, σ, out, L0, hO, hc => by
    have h1 := emitO_spec cap σ out L0 b hO (by simp at hc; omega)
    have h2 := emitList_exec O CO l (outSt σ O CO (out ++ [b]) L0) (out ++ [b]) L0 (outOn_outSt _ _ _ _ _)
      (by simp at hc ⊢; omega)
    rw [outSt_outSt] at h2
    refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 h2) (by simp) le_rfl) ?_
    simp only [List.length_cons]
    omega

/-- One address-bit field: halve `X`, append `qField (X mod 2)` (`sec:all-lengths`: query `i`'s address bit `j`). -/
def qStep (X Y B CO : Fin nr) (O : Fin (ns + 1)) : WMX ns nr :=
  .seq (halve X Y B) (.seq (.ifr B (emitList O CO (qField true)) (emitList O CO (qField false)))
    (.seq (.ifr B (WMX.dec B) WMX.skip) (.wm (WM.move Y X))))

theorem qStep_exec (X Y B CO : Fin nr) (O : Fin (ns + 1)) (hr : ERegs X Y B CO) (u : ℕ) (σ : WState ns nr)
    (out L0 : List Bool) (hX : σ.val X = u) (hY : σ.val Y = 0) (hB : σ.val B = 0) (hO : OutOn σ O CO out L0)
    (hu : u ≤ cap) (hc : out.length + 8 < cap) :
    WXExec cap (qStep X Y B CO O) σ (outSt (σ.setv X (u / 2)) O CO (out ++ qField (decide (u % 2 = 1))) L0)
      (13 * u + 90) := by
  obtain ⟨hxy, hxb, hyb, hxc, hyc, hbc⟩ := hr
  have h1 := halve_exec (cap := cap) X Y B hxy hxb hyb u σ hX hB (by omega) hu (by omega)
  set σ1 := ((σ.setv X 0).setv Y (σ.val Y + u / 2)).setv B (u % 2) with hσ1
  have hO1 : OutOn σ1 O CO out L0 := outOn_setv (outOn_setv (outOn_setv hO X hxc 0) Y hyc _) B hbc _
  have hB1 : σ1.val B = u % 2 := by simp [hσ1]
  have hlen : ∀ b, (qField b).length = 7 := by intro b; cases b <;> rfl
  have h3 : WXExec cap (.ifr B (emitList O CO (qField true)) (emitList O CO (qField false))) σ1
      (outSt σ1 O CO (out ++ qField (decide (u % 2 = 1))) L0) 57 := by
    by_cases hm : u % 2 = 1
    · have := emitList_exec (cap := cap) O CO (qField true) σ1 out L0 hO1 (by rw [hlen]; omega)
      rw [hlen] at this
      simpa [hm] using WXExec.ifrT (Q := emitList O CO (qField false)) (by rw [hB1]; omega) this
    · have := emitList_exec (cap := cap) O CO (qField false) σ1 out L0 hO1 (by rw [hlen]; omega)
      rw [hlen] at this
      simpa [hm] using WXExec.ifrF (P := emitList O CO (qField true)) (by rw [hB1]; omega) this
  set σ3 := outSt σ1 O CO (out ++ qField (decide (u % 2 = 1))) L0 with hσ3
  have hB3 : σ3.val B = u % 2 := by simp [hσ3, outSt, Function.update_of_ne hbc, hB1]
  have h4 : WXExec cap (.ifr B (WMX.dec B) WMX.skip) σ3 (σ3.setv B 0) 2 := by
    by_cases hm : u % 2 = 1
    · have := WXExec.ifrT (Q := WMX.skip) (by rw [hB3]; omega) (WXExec.dec cap B σ3 (by rw [hB3]; omega))
      refine WXExec.cast cap this ?_ le_rfl
      rw [hB3, hm]
    · have hm0 : u % 2 = 0 := by omega
      have := WXExec.ifrF (P := WMX.dec B) (by rw [hB3]; omega) (WXExec.skip cap σ3)
      refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by omega)
      conv_lhs => rw [← wsetv_same σ3 B]
      rw [hB3, hm0]
  set σ4 := σ3.setv B 0 with hσ4
  have hY4 : σ4.val Y = u / 2 := by
    simp [hσ4, hσ3, hσ1, outSt, Function.update_of_ne hyb, Function.update_of_ne hyc, hY]
  have hX4 : σ4.val X = 0 := by
    simp [hσ4, hσ3, hσ1, outSt, Function.update_of_ne hxb, Function.update_of_ne hxc,
      Function.update_of_ne hxy]
  have h5 := WXExec.wm (cap := cap) (wmove_spec (cap := cap) Y X hxy.symm (u / 2) σ4 hY4 (by rw [hY4]; omega)
    (by rw [hY4, hX4]; omega))
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h3 (WXExec.seq h4 h5))) ?_
    le_rfl) (by omega)
  rw [hX4, hY4]
  apply WState.eq
  · funext j
    simp only [hσ4, hσ3, hσ1, outSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    try (split_ifs <;> simp_all)
  · funext j
    simp only [hσ4, hσ3, hσ1, outSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    try (split_ifs <;> simp_all)
  · funext j
    simp only [hσ4, hσ3, hσ1, outSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

/-- `b += a`, keeping `a` (scratch `t`, left `0`). -/
def copyReg (a b t : Fin nr) : WMX ns nr := .seq (.wm (wdup a b t)) (.wm (WM.move t a))

theorem copyReg_exec (a b t : Fin nr) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (n : ℕ) (σ : WState ns nr)
    (ha : σ.val a = n) (ht : σ.val t = 0) (hcap : σ.val b + n ≤ cap) (hn : n ≤ cap) :
    WXExec cap (copyReg a b t) σ (σ.setv b (σ.val b + n)) (18 * n + 3) := by
  have h1 := wdup_spec (cap := cap) a b t hab hat hbt n σ ha hn hcap (by rw [ht]; omega)
  set τ := ((σ.setv a 0).setv b (σ.val b + n)).setv t (σ.val t + n) with hτ
  have h2 := wmove_spec (cap := cap) t a hat.symm n τ (by simp [hτ, ht])
    (by simp [hτ, ht]; omega) (by simp [hτ, Function.update_of_ne hat, Function.update_of_ne hab, ht]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq (WXExec.wm h1) (WXExec.wm h2)) ?_ le_rfl) (by omega)
  apply WState.eq <;> try rfl
  funext j
  simp only [hτ, WState.setv_val, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- `a := 0`. -/
def clearReg (a : Fin nr) : WMX ns nr := .wm (WM.clear a)

theorem clearReg_exec (a : Fin nr) (n : ℕ) (σ : WState ns nr) (ha : σ.val a = n) (hn : n ≤ cap) :
    WXExec cap (clearReg a) σ (σ.setv a 0) (3 * n + 1) :=
  WXExec.wm (wclear_spec (cap := cap) a n σ ha (by omega))

end NearCubicGates.Close.ENP
