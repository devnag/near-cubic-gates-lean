import Proof.Gates.CheckedPCPP.Clear

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms NearCubicWires.RepairRepresentation

namespace EmitNat

variable {ns nr : ℕ} {cap : ℕ}

/-- `X := 0`, `Y += X / 2`, `B := X % 2`. -/
def halve (X Y B : Fin nr) : WMX ns nr :=
  .whr X (.seq (WMX.dec X) (.ifr X (.seq (WMX.dec X) (WMX.inc Y)) (WMX.inc B)))

theorem halve_exec (X Y B : Fin nr) (hXY : X ≠ Y) (hXB : X ≠ B) (hYB : Y ≠ B) :
    ∀ v (σ : WState ns nr), σ.val X = v → σ.val B = 0 → σ.val Y + v ≤ cap → v ≤ cap → 1 ≤ cap →
      WXExec cap (halve X Y B) σ (((σ.setv X 0).setv Y (σ.val Y + v / 2)).setv B (v % 2)) (5 * v + 9)
  | 0, σ, hX, hB, _, _, _ => by
    have e : ((σ.setv X 0).setv Y (σ.val Y + 0 / 2)).setv B (0 % 2) = σ := by
      apply WState.eq <;> try rfl
      funext j; simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    rw [e]
    exact WXExec.mono (WXExec.whrF hX) (by omega)
  | 1, σ, hX, hB, hY, _, hc => by
    let σ1 := σ.setv X (σ.val X - 1)
    have h1 := WXExec.dec (cap := cap) X σ (by omega)
    have h2 := WXExec.inc (cap := cap) B σ1 (by simp [σ1, Function.update_apply, hXB.symm, hB]; omega)
    have hif := WXExec.ifrF (r := X) (P := .seq (WMX.dec X) (WMX.inc Y)) (by simp [σ1, hX]) h2
    let σ2 := σ1.setv B (σ1.val B + 1)
    have hend := WXExec.whrF (cap := cap) (r := X) (P := .seq (WMX.dec X) (.ifr X (.seq (WMX.dec X) (WMX.inc Y))
      (WMX.inc B))) (σ := σ2) (by simp [σ2, σ1, Function.update_apply, hXB, hX])
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq h1 hif) hend) ?_ le_rfl) (by omega)
    apply WState.eq <;> try rfl
    funext j; simp only [σ2, σ1, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  | k + 2, σ, hX, hB, hY, hv, hc => by
    let σ1 := σ.setv X (σ.val X - 1)
    have h1 := WXExec.dec (cap := cap) X σ (by omega)
    let σ2 := σ1.setv X (σ1.val X - 1)
    have h2 := WXExec.dec (cap := cap) X σ1 (by simp [σ1]; omega)
    have h3 := WXExec.inc (cap := cap) Y σ2 (by simp [σ2, σ1, Function.update_apply, hXY.symm]; omega)
    have hif := WXExec.ifrT (r := X) (Q := WMX.inc B) (by simp [σ1, hX]) (WXExec.seq h2 h3)
    let σ3 := σ2.setv Y (σ2.val Y + 1)
    have ih := halve_exec X Y B hXY hXB hYB k σ3 (by simp [σ3, σ2, σ1, Function.update_apply, hXY, hX])
      (by simp [σ3, σ2, σ1, Function.update_apply, hXB.symm, hYB.symm, hB])
      (by simp [σ3, σ2, σ1, Function.update_apply, hXY.symm]; omega) (by omega) hc
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq h1 hif) ih) ?_ le_rfl) (by omega)
    apply WState.eq <;> try rfl
    funext j; simp only [σ3, σ2, σ1, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega

/-- One bit: halve `X`, write the remainder at the buffer head, advance, count. -/
def bitStep (X Y B BL : Fin nr) (BUF : Fin (ns + 1)) : WMX ns nr :=
  .seq (halve X Y B) (.seq (.ifr B (WMX.wr BUF true) (WMX.wr BUF false)) (.seq (WMX.fwd BUF)
    (.seq (WMX.inc BL) (.seq (.ifr B (WMX.dec B) WMX.skip) (.wm (WM.move Y X))))))

/-- The registers of the emitter are pairwise distinct. -/
structure Regs (X Y B BL BL2 : Fin nr) : Prop where
  xy : X ≠ Y
  xb : X ≠ B
  yb : Y ≠ B
  xl : X ≠ BL
  yl : Y ≠ BL
  bl : B ≠ BL
  xl2 : X ≠ BL2
  yl2 : Y ≠ BL2
  bl2 : B ≠ BL2
  ll2 : BL ≠ BL2

theorem bitStep_exec (X Y B BL BL2 : Fin nr) (BUF : Fin (ns + 1)) (hr : Regs X Y B BL BL2) (v k : ℕ)
    (σ : WState ns nr) (hX : σ.val X = v) (hY : σ.val Y = 0) (hB : σ.val B = 0) (hBL : σ.val BL = k)
    (hh : σ.sh BUF = k) (hv : v ≤ cap) (hk : k + 1 ≤ cap) (hc : 1 ≤ cap) :
    WXExec cap (bitStep X Y B BL BUF) σ
      ((((σ.setv X (v / 2)).setv BL (k + 1)).sets BUF (writeTapeBit (σ.st BUF) k (decide (v % 2 = 1)))).seth BUF
        (k + 1)) (9 * v + 30) := by
  obtain ⟨hxy, hxb, hyb, hxl, hyl, hbl, hxl2, hyl2, hbl2, hll2⟩ := hr
  have h1 := halve_exec (cap := cap) X Y B hxy hxb hyb v σ hX hB (by omega) hv hc
  let σ1 := ((σ.setv X 0).setv Y (σ.val Y + v / 2)).setv B (v % 2)
  have hwr : WXExec cap (.ifr B (WMX.wr BUF true) (WMX.wr BUF false)) σ1
      (σ1.sets BUF (writeTapeBit (σ1.st BUF) (σ1.sh BUF) (decide (v % 2 = 1)))) 2 := by
    by_cases hm : v % 2 = 1
    · have := WXExec.ifrT (r := B) (Q := WMX.wr BUF false) (by simp [σ1, hm]) (WXExec.wr (cap := cap) BUF true σ1)
      simpa [hm] using this
    · have := WXExec.ifrF (r := B) (P := WMX.wr BUF true) (by simp [σ1]; omega) (WXExec.wr (cap := cap) BUF false σ1)
      simpa [hm] using this
  let σ2 := σ1.sets BUF (writeTapeBit (σ1.st BUF) (σ1.sh BUF) (decide (v % 2 = 1)))
  have h3 := WXExec.fwd (cap := cap) BUF σ2
  let σ3 := σ2.seth BUF (σ2.sh BUF + 1)
  have hBL3 : σ3.val BL = k := by
    simp [σ3, σ2, σ1, Function.update_apply, hxl.symm, hyl.symm, hbl.symm, hBL]
  have h4 := WXExec.inc (cap := cap) BL σ3 (by omega)
  let σ4 := σ3.setv BL (σ3.val BL + 1)
  have hdec : WXExec cap (.ifr B (WMX.dec B) WMX.skip) σ4 (σ4.setv B 0) 2 := by
    by_cases hm : v % 2 = 1
    · have := WXExec.ifrT (r := B) (Q := WMX.skip) (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hbl, hm])
        (WXExec.dec (cap := cap) B σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hbl, hm]; omega))
      refine WXExec.cast cap this ?_ le_rfl
      simp [σ4, σ3, σ2, σ1, Function.update_apply, hbl, hm]
    · have hm0 : v % 2 = 0 := by omega
      have := WXExec.ifrF (r := B) (P := WMX.dec B) (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hbl, hm0])
        (WXExec.skip (cap := cap) σ4)
      refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by omega)
      apply WState.eq <;> try rfl
      funext j; simp only [σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  let σ5 := σ4.setv B 0
  have hmove := WXExec.wm (cap := cap) (wmove_spec (cap := cap) Y X hxy.symm (v / 2) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hyb, hyl, hxy.symm, hY])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hyb, hyl, hxy.symm, hY]; omega)
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hyb, hyl, hxy, hxy.symm, hxb, hxl, hY]; omega))
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq hwr (WXExec.seq h3 (WXExec.seq h4
    (WXExec.seq hdec hmove))))) ?_ le_rfl) (by omega)
  apply WState.eq
  · funext j; simp only [σ5, σ4, σ3, σ2, σ1, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · funext j; simp only [σ5, σ4, σ3, σ2, σ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · funext j; simp only [σ5, σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega
  · rfl

theorem div_pow_bitLength (v : ℕ) : v / 2 ^ natBitLength v = 0 := by
  apply Nat.div_eq_of_lt
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self (by decide) v

theorem div_pow_pos (v j : ℕ) (hj : j < natBitLength v) (hv : v ≠ 0) : v / 2 ^ j ≠ 0 := by
  unfold natBitLength at hj
  have h1 : 2 ^ j ≤ 2 ^ Nat.log 2 v := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 := Nat.pow_log_le_self 2 hv
  have : 0 < v / 2 ^ j := Nat.div_pos (h1.trans h2) (by positivity)
  omega

/-- The bit loop. -/
def bitLoop (X Y B BL : Fin nr) (BUF : Fin (ns + 1)) : WMX ns nr := .whr X (bitStep X Y B BL BUF)

theorem bitLoop_exec (X Y B BL BL2 : Fin nr) (BUF : Fin (ns + 1)) (hr : Regs X Y B BL BL2) (v : ℕ)
    (hv : v ≤ cap) (hbl : natBitLength v + 1 ≤ cap) (hc : 1 ≤ cap) :
    ∀ s j (σ : WState ns nr), 1 ≤ j → j + s = natBitLength v → σ.val X = v / 2 ^ j → σ.val BL = j →
      σ.sh BUF = j → σ.val Y = 0 → σ.val B = 0 → (∀ i < j, readTapeBit (σ.st BUF) i = v.testBit i) →
      ∃ buf, WXExec cap (bitLoop X Y B BL BUF) σ
        ((((σ.setv X 0).setv BL (natBitLength v)).sets BUF buf).seth BUF (natBitLength v)) (s * (9 * v + 32) + 1) ∧
        ∀ i < natBitLength v, readTapeBit buf i = v.testBit i
  | 0, j, σ, _, hjs, hX, hBL, hh, hY, hB, hbits => by
    have hj : j = natBitLength v := by omega
    subst hj
    have hX0 : σ.val X = 0 := by rw [hX, div_pow_bitLength]
    refine ⟨σ.st BUF, ?_, hbits⟩
    have e : (((σ.setv X 0).setv BL (natBitLength v)).sets BUF (σ.st BUF)).seth BUF (natBitLength v) = σ := by
      apply WState.eq
      · funext i; simp only [WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all
      · funext i; simp only [WState.seth_st, WState.sets_st, WState.setv_st, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all
      · funext i; simp only [WState.seth_val, WState.sets_val, WState.setv_val, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all
      · rfl
    rw [e]
    exact WXExec.mono (WXExec.whrF hX0) (by omega)
  | s + 1, j, σ, hj1, hjs, hX, hBL, hh, hY, hB, hbits => by
    have hv0 : v ≠ 0 := by
      intro h; subst h; simp [natBitLength] at hjs; omega
    have hpos : σ.val X ≠ 0 := by rw [hX]; exact div_pow_pos v j (by omega) hv0
    have hstep := bitStep_exec (cap := cap) X Y B BL BL2 BUF hr (v / 2 ^ j) j σ hX hY hB hBL hh
      ((Nat.div_le_self _ _).trans hv) (by omega) hc
    set σ' := (((σ.setv X (v / 2 ^ j / 2)).setv BL (j + 1)).sets BUF
      (writeTapeBit (σ.st BUF) j (decide (v / 2 ^ j % 2 = 1)))).seth BUF (j + 1)
    obtain ⟨buf, hrun, hbuf⟩ := bitLoop_exec X Y B BL BL2 BUF hr v hv hbl hc s (j + 1) σ' (by omega) (by omega)
      (by simp [σ', Nat.div_div_eq_div_mul, ← pow_succ, Function.update_apply, hr.xl])
      (by simp [σ', Function.update_apply, hr.xl.symm])
      (by simp [σ'])
      (by simp [σ', Function.update_apply, hr.xy.symm, hr.yl, hY])
      (by simp [σ', Function.update_apply, hr.xb.symm, hr.bl, hB])
      (by
        intro i hi
        simp only [σ', WState.seth_st, WState.sets_st, Function.update_self]
        rw [NearCubicWires.WireExponent3_5.PrimT.ReadEq.readTapeBit_write]
        split_ifs with hij
        · subst hij; rw [Nat.testBit_eq_decide_div_mod_eq]
        · exact hbits i (by omega))
    refine ⟨buf, WXExec.mono (WXExec.cast cap (WXExec.whrT hpos hstep hrun) ?_ le_rfl) ?_, hbuf⟩
    · apply WState.eq
      · funext i; simp only [σ', WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_apply]
        split_ifs <;> rfl
      · funext i; simp only [σ', WState.seth_st, WState.sets_st, WState.setv_st, Function.update_apply]
        split_ifs <;> rfl
      · funext i; simp only [σ', WState.seth_val, WState.sets_val, WState.setv_val, Function.update_apply]
        split_ifs <;> rfl
      · rfl
    · have : v / 2 ^ j ≤ v := Nat.div_le_self _ _
      nlinarith

theorem write_end (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [writeTapeBit, ih]

/-- Halve-and-record: the bits of `v` into the buffer, their number into `BL`. -/
def bits (X Y B BL : Fin nr) (BUF : Fin (ns + 1)) : WMX ns nr := .seq (bitStep X Y B BL BUF) (bitLoop X Y B BL BUF)

theorem bits_exec (X Y B BL BL2 : Fin nr) (BUF : Fin (ns + 1)) (hr : Regs X Y B BL BL2) (v : ℕ)
    (hv : v ≤ cap) (hbl : natBitLength v + 1 ≤ cap) (hc : 1 ≤ cap) (σ : WState ns nr)
    (hX : σ.val X = v) (hBL : σ.val BL = 0) (hh : σ.sh BUF = 0) (hY : σ.val Y = 0) (hB : σ.val B = 0) :
    ∃ buf, WXExec cap (bits X Y B BL BUF) σ
      ((((σ.setv X 0).setv BL (natBitLength v)).sets BUF buf).seth BUF (natBitLength v))
        ((natBitLength v + 1) * (9 * v + 32)) ∧
      ∀ i < natBitLength v, readTapeBit buf i = v.testBit i := by
  have hstep := bitStep_exec (cap := cap) X Y B BL BL2 BUF hr v 0 σ hX hY hB hBL hh hv (by
    have : 1 ≤ natBitLength v := by unfold natBitLength; omega
    omega) hc
  set σ' := (((σ.setv X (v / 2)).setv BL (0 + 1)).sets BUF (writeTapeBit (σ.st BUF) 0 (decide (v % 2 = 1)))).seth
    BUF (0 + 1)
  have hl1 : 1 ≤ natBitLength v := by unfold natBitLength; omega
  obtain ⟨buf, hrun, hbuf⟩ := bitLoop_exec (cap := cap) X Y B BL BL2 BUF hr v hv hbl hc (natBitLength v - 1) 1 σ'
    le_rfl (by omega) (by simp [σ', Function.update_apply, hr.xl])
    (by simp [σ', Function.update_apply, hr.xl.symm]) (by simp [σ'])
    (by simp [σ', Function.update_apply, hr.xy.symm, hr.yl, hY])
    (by simp [σ', Function.update_apply, hr.xb.symm, hr.bl, hB])
    (by
      intro i hi
      have : i = 0 := by omega
      subst this
      simp only [σ', WState.seth_st, WState.sets_st, Function.update_self]
      rw [NearCubicWires.WireExponent3_5.PrimT.ReadEq.readTapeBit_write, if_pos rfl, Nat.testBit_zero])
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hl1
  refine ⟨buf, WXExec.mono (WXExec.cast cap (WXExec.seq hstep hrun) ?_ le_rfl) ?_, hbuf⟩
  · apply WState.eq
    · funext i; simp only [σ', WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_apply]
      split_ifs <;> rfl
    · funext i; simp only [σ', WState.seth_st, WState.sets_st, WState.setv_st, Function.update_apply]
      split_ifs <;> rfl
    · funext i; simp only [σ', WState.seth_val, WState.sets_val, WState.setv_val, Function.update_apply]
      split_ifs <;> rfl
    · rfl
  · rw [hm, Nat.add_sub_cancel_left]
    nlinarith

theorem cons_rep (k : ℕ) : true :: List.replicate k true = List.replicate k true ++ [true] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, ih, ← List.cons_append, ih]

section Output
variable (O BUF : Fin (ns + 1)) (BL BL2 : Fin nr) (hll : BL ≠ BL2) (hob : O ≠ BUF)
include hll

def ones : WMX ns nr := .whr BL (.seq (WMX.dec BL) (.seq (WMX.inc BL2) (.seq (WMX.wr O true) (WMX.fwd O))))

theorem ones_exec : ∀ k (σ : WState ns nr) (out : List Bool), σ.val BL = k → σ.st O = out →
    σ.sh O = out.length → σ.val BL2 + k ≤ cap → k ≤ cap →
    WXExec cap (ones O BL BL2) σ ((((σ.setv BL 0).setv BL2 (σ.val BL2 + k)).sets O (out ++ List.replicate k true)).seth
      O (out.length + k)) (11 * k + 1)
  | 0, σ, out, hk, hO, hOh, _, _ => by
    have e : (((σ.setv BL 0).setv BL2 (σ.val BL2 + 0)).sets O (out ++ List.replicate 0 true)).seth O
        (out.length + 0) = σ := by
      apply WState.eq
      · funext i; simp only [WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all
      · funext i; simp only [WState.seth_st, WState.sets_st, WState.setv_st, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all
      · funext i; simp only [WState.seth_val, WState.sets_val, WState.setv_val, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all
      · rfl
    rw [e]
    exact WXExec.whrF hk
  | k + 1, σ, out, hk, hO, hOh, h2, hcap => by
    let σ1 := σ.setv BL (σ.val BL - 1)
    let σ2 := σ1.setv BL2 (σ1.val BL2 + 1)
    let σ3 := σ2.sets O (writeTapeBit (σ2.st O) (σ2.sh O) true)
    let σ4 := σ3.seth O (σ3.sh O + 1)
    have v1 : σ1.val BL2 = σ.val BL2 := by
      simp only [σ1, WState.setv_val]; rw [Function.update_of_ne hll.symm]
    have v4L : σ4.val BL = k := by
      simp only [σ4, σ3, σ2, σ1, WState.seth_val, WState.sets_val, WState.setv_val]
      rw [Function.update_of_ne hll, Function.update_self, hk]; rfl
    have v4L2 : σ4.val BL2 = σ.val BL2 + 1 := by
      simp only [σ4, σ3, σ2, WState.seth_val, WState.sets_val, WState.setv_val, Function.update_self, v1]
    have hbody := WXExec.seq (WXExec.dec (cap := cap) BL σ (by omega)) (WXExec.seq (WXExec.inc (cap := cap) BL2 σ1
      (by rw [v1]; omega)) (WXExec.seq (WXExec.wr (cap := cap) O true σ2)
      (WXExec.fwd (cap := cap) O σ3)))
    have ih := ones_exec k σ4 (out ++ [true]) v4L
      (by simp [σ4, σ3, σ2, σ1, hO, hOh, write_end]) (by simp [σ4, σ3, σ2, σ1, hOh])
      (by rw [v4L2]; omega) (by omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) hbody ih) ?_ le_rfl) (by omega)
    apply WState.eq
    · funext i
      by_cases hi : i = O
      · subst hi; simp; omega
      · simp [σ4, σ3, σ2, σ1, Function.update_apply, hi]
    · funext i
      by_cases hi : i = O
      · subst hi; simp [List.append_assoc, cons_rep, List.replicate_succ']
      · simp [σ4, σ3, σ2, σ1, Function.update_apply, hi]
    · funext i
      by_cases hi : i = BL
      · subst hi; simp [Function.update_apply, hll]
      · by_cases hi2 : i = BL2
        · subst hi2; simp [Function.update_apply, hll.symm, v4L2]; omega
        · simp [σ4, σ3, σ2, σ1, Function.update_apply, hi, hi2]
    · rfl

def back (S : Fin (ns + 1)) : WMX ns nr := .whr BL2 (.seq (WMX.dec BL2) (.seq (WMX.inc BL) (WMX.bwd S)))

theorem back_exec (S : Fin (ns + 1)) : ∀ k (σ : WState ns nr), σ.val BL2 = k → σ.val BL + k ≤ cap → k ≤ cap →
    k ≤ σ.sh S →
    WXExec cap (back BL BL2 S) σ (((σ.setv BL2 0).setv BL (σ.val BL + k)).seth S (σ.sh S - k)) (9 * k + 1)
  | 0, σ, hk, _, _, _ => by
    have e : ((σ.setv BL2 0).setv BL (σ.val BL + 0)).seth S (σ.sh S - 0) = σ := by
      apply WState.eq
      · funext i; by_cases hi : i = S
        · subst hi; simp
        · simp [Function.update_apply, hi]
      · rfl
      · funext i; by_cases hi : i = BL
        · subst hi; simp [Function.update_apply, hll]
        · by_cases hi2 : i = BL2
          · subst hi2; simp [Function.update_apply, hll.symm, hk]
          · simp [Function.update_apply, hi, hi2]
      · rfl
    rw [e]
    exact WXExec.whrF hk
  | k + 1, σ, hk, hcapL, hcap, hS => by
    let σ1 := σ.setv BL2 (σ.val BL2 - 1)
    let σ2 := σ1.setv BL (σ1.val BL + 1)
    let σ3 := σ2.seth S (σ2.sh S - 1)
    have v1 : σ1.val BL = σ.val BL := by simp only [σ1, WState.setv_val]; rw [Function.update_of_ne hll]
    have v3L2 : σ3.val BL2 = k := by
      simp only [σ3, σ2, σ1, WState.seth_val, WState.setv_val]
      rw [Function.update_of_ne hll.symm, Function.update_self, hk]; rfl
    have v3L : σ3.val BL = σ.val BL + 1 := by
      simp only [σ3, σ2, WState.seth_val, WState.setv_val, Function.update_self, v1]
    have hbody := WXExec.seq (WXExec.dec (cap := cap) BL2 σ (by omega)) (WXExec.seq (WXExec.inc (cap := cap) BL σ1
      (by rw [v1]; omega)) (WXExec.bwd (cap := cap) S σ2))
    have hS3 : σ3.sh S = σ.sh S - 1 := by simp [σ3, σ2, σ1]
    have ih := back_exec S k σ3 v3L2 (by rw [v3L]; omega) (by omega) (by rw [hS3]; omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) hbody ih) ?_ le_rfl) (by omega)
    apply WState.eq
    · funext i
      by_cases hi : i = S
      · subst hi; simp; omega
      · simp [σ3, σ2, σ1, Function.update_apply, hi]
    · rfl
    · funext i
      by_cases hi : i = BL
      · subst hi; simp [Function.update_apply, hll, v3L]; omega
      · by_cases hi2 : i = BL2
        · subst hi2; simp [Function.update_apply, hll.symm]
        · simp [σ3, σ2, σ1, Function.update_apply, hi, hi2]
    · rfl

def copyBits : WMX ns nr :=
  .whr BL (.seq (WMX.dec BL) (.seq (WMX.inc BL2) (.seq (.ifs BUF (WMX.wr O true) (WMX.wr O false))
    (.seq (WMX.fwd O) (WMX.fwd BUF)))))

include hob in
theorem copyBits_exec : ∀ k (σ : WState ns nr) (out : List Bool), σ.val BL = k → σ.st O = out →
    σ.sh O = out.length → σ.val BL2 + k ≤ cap → k ≤ cap →
    WXExec cap (copyBits O BUF BL BL2) σ
      (((((σ.setv BL 0).setv BL2 (σ.val BL2 + k)).sets O
        (out ++ List.ofFn fun i : Fin k => readTapeBit (σ.st BUF) (σ.sh BUF + i))).seth O (out.length + k)).seth BUF
          (σ.sh BUF + k)) (14 * k + 1)
  | 0, σ, out, hk, hO, hOh, _, _ => by
    have e : (((((σ.setv BL 0).setv BL2 (σ.val BL2 + 0)).sets O
        (out ++ List.ofFn fun i : Fin 0 => readTapeBit (σ.st BUF) (σ.sh BUF + i))).seth O (out.length + 0)).seth BUF
          (σ.sh BUF + 0)) = σ := by
      apply WState.eq
      · funext i; by_cases hi : i = BUF
        · subst hi; simp
        · by_cases hi2 : i = O
          · subst hi2; simp [Function.update_apply, hi, hOh]
          · simp [Function.update_apply, hi, hi2]
      · funext i; by_cases hi : i = O
        · subst hi; simp [hO]
        · simp [Function.update_apply, hi]
      · funext i; by_cases hi : i = BL
        · subst hi; simp [Function.update_apply, hll, hk]
        · by_cases hi2 : i = BL2
          · subst hi2; simp [Function.update_apply, hll.symm]
          · simp [Function.update_apply, hi, hi2]
      · rfl
    rw [e]
    exact WXExec.whrF hk
  | k + 1, σ, out, hk, hO, hOh, h2, hcap => by
    let b := readTapeBit (σ.st BUF) (σ.sh BUF)
    let σ1 := σ.setv BL (σ.val BL - 1)
    let σ2 := σ1.setv BL2 (σ1.val BL2 + 1)
    have hwr : WXExec cap (.ifs BUF (WMX.wr O true) (WMX.wr O false)) σ2 (σ2.sets O (writeTapeBit (σ2.st O)
        (σ2.sh O) b)) 2 := by
      by_cases hb : b = true
      · have := WXExec.ifsT (i := BUF) (Q := WMX.wr O false) (by simp [wbit, σ2, σ1]; exact hb)
          (WXExec.wr (cap := cap) O true σ2)
        rw [hb]; exact this
      · have hb' : b = false := by simpa using hb
        have := WXExec.ifsF (i := BUF) (P := WMX.wr O true) (by simp [wbit, σ2, σ1]; exact hb')
          (WXExec.wr (cap := cap) O false σ2)
        rw [hb']; exact this
    let σ3 := σ2.sets O (writeTapeBit (σ2.st O) (σ2.sh O) b)
    let σ4 := σ3.seth O (σ3.sh O + 1)
    let σ5 := σ4.seth BUF (σ4.sh BUF + 1)
    have v1 : σ1.val BL2 = σ.val BL2 := by simp only [σ1, WState.setv_val]; rw [Function.update_of_ne hll.symm]
    have v5L : σ5.val BL = k := by
      simp only [σ5, σ4, σ3, σ2, σ1, WState.seth_val, WState.sets_val, WState.setv_val]
      rw [Function.update_of_ne hll, Function.update_self, hk]; rfl
    have v5L2 : σ5.val BL2 = σ.val BL2 + 1 := by
      simp only [σ5, σ4, σ3, σ2, WState.seth_val, WState.sets_val, WState.setv_val, Function.update_self, v1]
    have hbody := WXExec.seq (WXExec.dec (cap := cap) BL σ (by omega)) (WXExec.seq (WXExec.inc (cap := cap) BL2 σ1
      (by rw [v1]; omega)) (WXExec.seq hwr (WXExec.seq (WXExec.fwd (cap := cap) O σ3)
      (WXExec.fwd (cap := cap) BUF σ4))))
    have hO5 : σ5.st O = out ++ [b] := by
      simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hob.symm, hO, hOh, write_end]
    have hBUF5 : σ5.st BUF = σ.st BUF := by
      simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hob.symm]
    have hBh5 : σ5.sh BUF = σ.sh BUF + 1 := by
      simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hob.symm]
    have ih := copyBits_exec k σ5 (out ++ [b]) v5L hO5 (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hob, hOh])
      (by rw [v5L2]; omega) (by omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) hbody ih) ?_ le_rfl) (by omega)
    apply WState.eq
    · funext i
      by_cases hi : i = BUF
      · subst hi; simp [hob.symm, hBh5]; omega
      · by_cases hi2 : i = O
        · subst hi2; simp [Function.update_apply, hi]; omega
        · simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hi, hi2]
    · funext i
      by_cases hi : i = O
      · subst hi
        simp only [WState.seth_st, WState.sets_st, Function.update_self, hBUF5, hBh5, List.append_assoc]
        congr 1
        rw [List.ofFn_succ]
        simp [b, Nat.add_assoc, Nat.add_comm 1]
      · simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hi]
    · funext i
      by_cases hi : i = BL
      · subst hi; simp [Function.update_apply, hll]
      · by_cases hi2 : i = BL2
        · subst hi2; simp [Function.update_apply, hll.symm, v5L2]; omega
        · simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hi, hi2]
    · rfl

end Output

/-- **emitNat.** Append `natWord (val X)` at the head of `O` (consuming `X`). -/
def emitNat (X Y B BL BL2 : Fin nr) (O BUF : Fin (ns + 1)) : WMX ns nr :=
  .seq (bits X Y B BL BUF) (.seq (ones O BL BL2) (.seq (.seq (WMX.wr O false) (WMX.fwd O))
    (.seq (back BL BL2 BUF) (.seq (copyBits O BUF BL BL2) (.seq (back BL BL2 BUF) (.wm (WM.clear BL)))))))

/-- The step bound of `emitNat`. -/
def emitCost (v : ℕ) : ℕ := (natBitLength v + 1) * (9 * v + 32) + 60 * natBitLength v + 30

theorem natWord_eq (v : ℕ) :
    natWord v = List.replicate (natBitLength v) true ++ false :: List.ofFn fun i : Fin (natBitLength v) => v.testBit i :=
  rfl

theorem write_end' (l : List Bool) (n : ℕ) (b : Bool) (h : l.length = n) : writeTapeBit l n b = l ++ [b] := by
  subst h; exact write_end l b

theorem emitNat_exec (X Y B BL BL2 : Fin nr) (O BUF : Fin (ns + 1)) (hr : Regs X Y B BL BL2) (hob : O ≠ BUF)
    (v : ℕ) (hv : v ≤ cap) (hbl : natBitLength v + 1 ≤ cap) (hc : 1 ≤ cap) (σ : WState ns nr) (out : List Bool)
    (hX : σ.val X = v) (hY : σ.val Y = 0) (hB : σ.val B = 0) (hBL : σ.val BL = 0) (hBL2 : σ.val BL2 = 0)
    (hh : σ.sh BUF = 0) (hO : σ.st O = out) (hOh : σ.sh O = out.length) :
    ∃ buf, WXExec cap (emitNat X Y B BL BL2 O BUF) σ
      ((((σ.setv X 0).sets BUF buf).sets O (out ++ natWord v)).seth O (out ++ natWord v).length) (emitCost v) := by
  obtain ⟨buf, h1, hbuf⟩ := bits_exec (cap := cap) X Y B BL BL2 BUF hr v hv hbl hc σ hX hBL hh hY hB
  set bl := natBitLength v
  set σ1 := (((σ.setv X 0).setv BL bl).sets BUF buf).seth BUF bl
  have hO1 : σ1.st O = out := by simp [σ1, Function.update_apply, hob, hO]
  have hOh1 : σ1.sh O = out.length := by simp [σ1, Function.update_apply, hob, hOh]
  have h2 := ones_exec (cap := cap) O BL BL2 hr.ll2 bl σ1 out (by simp [σ1, Function.update_apply, hr.xl.symm])
    hO1 hOh1 (by simp [σ1, Function.update_apply, hr.xl2.symm, hr.ll2.symm, hBL2]; omega) (by omega)
  set σ2 := (((σ1.setv BL 0).setv BL2 (σ1.val BL2 + bl)).sets O (out ++ List.replicate bl true)).seth O
    (out.length + bl)
  have h3 := WXExec.seq (WXExec.wr (cap := cap) O false σ2) (WXExec.fwd (cap := cap) O
    (σ2.sets O (writeTapeBit (σ2.st O) (σ2.sh O) false)))
  set σ3 := (σ2.sets O (writeTapeBit (σ2.st O) (σ2.sh O) false)).seth O
    ((σ2.sets O (writeTapeBit (σ2.st O) (σ2.sh O) false)).sh O + 1)
  have hv1L2 : σ1.val BL2 = 0 := by simp [σ1, Function.update_apply, hr.xl2.symm, hr.ll2.symm, hBL2]
  have h3L2 : σ3.val BL2 = bl := by simp [σ3, σ2, hv1L2]
  have h3L : σ3.val BL = 0 := by simp [σ3, σ2, Function.update_apply, hr.ll2]
  have h3B : σ3.sh BUF = bl := by simp [σ3, σ2, σ1, Function.update_apply, hob.symm]
  have h4 := back_exec (cap := cap) BL BL2 hr.ll2 BUF bl σ3 h3L2 (by rw [h3L]; omega) (by omega) (by rw [h3B])
  set σ4 := ((σ3.setv BL2 0).setv BL (σ3.val BL + bl)).seth BUF (σ3.sh BUF - bl)
  have h4L : σ4.val BL = bl := by simp [σ4, h3L]
  have h4O : σ4.st O = out ++ List.replicate bl true ++ [false] := by
    simp [σ4, σ3, σ2, Function.update_apply]
    rw [write_end' _ _ _ (by simp)]
    simp [List.append_assoc]
  have h4Oh : σ4.sh O = (out ++ List.replicate bl true ++ [false]).length := by
    simp [σ4, σ3, σ2, Function.update_apply, hob]; omega
  have h4B : σ4.sh BUF = 0 := by simp [σ4, h3B]
  have h4BUF : σ4.st BUF = buf := by simp [σ4, σ3, σ2, σ1, Function.update_apply, hob.symm]
  have h5 := copyBits_exec (cap := cap) O BUF BL BL2 hr.ll2 hob bl σ4 _ h4L h4O h4Oh
    (by simp [σ4, Function.update_apply, hr.ll2.symm]; omega) (by omega)
  set σ5 := ((((σ4.setv BL 0).setv BL2 (σ4.val BL2 + bl)).sets O
    (out ++ List.replicate bl true ++ [false] ++ List.ofFn fun i : Fin bl => readTapeBit (σ4.st BUF) (σ4.sh BUF + i))).seth
      O ((out ++ List.replicate bl true ++ [false]).length + bl)).seth BUF (σ4.sh BUF + bl)
  have h5L2 : σ5.val BL2 = bl := by simp [σ5, σ4, Function.update_apply, hr.ll2.symm]
  have h5L : σ5.val BL = 0 := by simp [σ5, Function.update_apply, hr.ll2]
  have h5B : σ5.sh BUF = bl := by simp [σ5, h4B]
  have h6 := back_exec (cap := cap) BL BL2 hr.ll2 BUF bl σ5 h5L2 (by rw [h5L]; omega) (by omega) (by rw [h5B])
  set σ6 := ((σ5.setv BL2 0).setv BL (σ5.val BL + bl)).seth BUF (σ5.sh BUF - bl)
  have h7 := WXExec.wm (cap := cap) (wclear_spec (cap := cap) BL bl σ6 (by simp [σ6, h5L]) (by simp [σ6, h5L]; omega))
  refine ⟨buf, WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4
    (WXExec.seq h5 (WXExec.seq h6 h7)))))) ?_ le_rfl) ?_⟩
  · have hbits : (List.ofFn fun i : Fin bl => readTapeBit (σ4.st BUF) (σ4.sh BUF + i)) =
        List.ofFn fun i : Fin bl => v.testBit i := by
      apply congrArg List.ofFn
      funext i
      rw [h4BUF, h4B, Nat.zero_add]
      exact hbuf i i.isLt
    have hw : out ++ List.replicate bl true ++ [false] ++ (List.ofFn fun i : Fin bl => v.testBit i) =
        out ++ natWord v := by
      rw [natWord_eq]
      show out ++ List.replicate bl true ++ [false] ++ (List.ofFn fun i : Fin bl => v.testBit i) =
        out ++ (List.replicate bl true ++ false :: List.ofFn fun i : Fin bl => v.testBit i)
      simp [List.append_assoc]
    obtain ⟨hxy, hxb, hyb, hxl, hyl, hbl', hxl2, hyl2, hbl2, hll2⟩ := hr
    have s6shO : σ6.sh O = (out ++ natWord v).length := by
      rw [← hw]; simp [σ6, σ5, σ4, Function.update_apply, hob]; omega
    have s6shB : σ6.sh BUF = 0 := by simp [σ6, h5B]
    have s6stO : σ6.st O = out ++ natWord v := by
      rw [← hw, ← hbits]; simp [σ6, σ5, Function.update_apply, hob]
    have s6stB : σ6.st BUF = buf := by
      simp [σ6, σ5, Function.update_apply, hob.symm, h4BUF]
    have s6sh : ∀ i, i ≠ O → i ≠ BUF → σ6.sh i = σ.sh i := by
      intro i h1 h2; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h1, h2]
    have s6st : ∀ i, i ≠ O → i ≠ BUF → σ6.st i = σ.st i := by
      intro i h1 h2; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h1, h2]
    have s6val : ∀ j, j ≠ X → j ≠ BL → j ≠ BL2 → σ6.val j = σ.val j := by
      intro j h1 h2 h3; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h1, h2, h3]
    have s6X : σ6.val X = 0 := by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hxl, hxl2]
    have s6L2 : σ6.val BL2 = 0 := by simp [σ6, Function.update_apply, hll2.symm]
    apply WState.eq
    · funext i
      by_cases hi : i = O
      · subst hi; simp [Function.update_apply, s6shO]
      · by_cases hi2 : i = BUF
        · subst hi2; simp [Function.update_apply, hi, hob.symm, s6shB, hh]
        · simp [Function.update_apply, hi, hi2, s6sh i hi hi2]
    · funext i
      by_cases hi : i = O
      · subst hi; simp [Function.update_apply, s6stO]
      · by_cases hi2 : i = BUF
        · subst hi2; simp [Function.update_apply, hi, hob.symm, s6stB]
        · simp [Function.update_apply, hi, hi2, s6st i hi hi2]
    · funext j
      by_cases h1 : j = X
      · subst h1; simp [Function.update_apply, hxl, s6X]
      · by_cases h2 : j = BL
        · subst h2; simp [Function.update_apply, h1, hBL]
        · by_cases h3 : j = BL2
          · subst h3; simp [Function.update_apply, h1, hll2.symm, hBL2, s6L2]
          · simp [Function.update_apply, h1, h2, h3, s6val j h1 h2 h3]
    · rfl
  · unfold emitCost
    have : 1 ≤ bl := by simp only [bl]; unfold natBitLength; omega
    nlinarith

end EmitNat

end NearCubicGates.Close.CheckedPCPP
