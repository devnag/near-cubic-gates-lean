import Proof.Gates.Recovery.HTParts3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HTParts

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Moving a head -/

/-- Move the head of `S` forward `K` cells, `SC += K`, `K := 0`. -/
def skipN (S : Fin (ns + 1)) (SC K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (WM.fwdC S SC))

theorem skipN_exec (S : Fin (ns + 1)) {SC K : Fin nr} (hKS : K ≠ SC) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val K = k → k ≤ cap → σ.val SC + k ≤ cap →
      WExec cap (skipN S SC K) σ (((σ.seth S (σ.sh S + k)).setv SC (σ.val SC + k)).setv K 0) (k * 9 + 1)
  | 0, σ, hK, _, _ => by
    rw [show ((σ.seth S (σ.sh S + 0)).setv SC (σ.val SC + 0)).setv K 0 = σ by
      rw [Nat.add_zero, Nat.add_zero, wseth_same, wsetv_same, ← hK, wsetv_same]]
    exact WExec.whrF hK
  | k + 1, σ, hK, hk, hS => by
    have e1 := WExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have e2 := wfwdC_spec cap S SC σ1 (by simp [hσ1, Function.update_apply, Ne.symm hKS]; omega)
    set σ2 := (σ1.seth S (σ1.sh S + 1)).setv SC (σ1.val SC + 1) with hσ2
    have ih := skipN_exec S hKS k σ2 (by simp [hσ2, hσ1, Function.update_apply, hKS, hK]) (by omega)
      (by simp [hσ2, hσ1, Function.update_apply, Ne.symm hKS]; omega)
    refine WExec.mono (WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) ih) ?_ le_rfl) (by ring_nf; omega)
    apply WState.eq
    · funext j; by_cases hj : j = S
      · simp [hj, hσ2, hσ1]; ring
      · simp [hσ2, hσ1, Function.update_apply, hj]
    · rfl
    · funext q
      by_cases q1 : q = K
      · simp [q1, hσ2, hσ1, hKS]
      · by_cases q2 : q = SC
        · simp [q2, hσ2, hσ1, Ne.symm hKS]; ring
        · simp [hσ2, hσ1, Function.update_apply, q1, q2]
    · rfl

/-! ## Reading a marked bit -/

theorem rtb_marks : ∀ (u : List Bool) (v : ℕ), readTapeBit (marks u) (2 * v + 1) = u.getD v false
  | [], v => by simp [marks, readTapeBit]
  | b :: u, 0 => by simp [marks, readTapeBit]
  | b :: u, v + 1 => by
    have := rtb_marks u v
    rw [show 2 * (v + 1) + 1 = 2 * v + 1 + 2 by ring]
    simpa [marks, readTapeBit] using this

/-- `Bt += u[v]` from `marks u` on `S` (head `0`), `K = 2v + 1` consumed, `S` back at `0`. -/
def readAt (S : Fin (ns + 1)) (SC K Bt : Fin nr) : WMX ns nr :=
  .seq (.wm (skipN S SC K)) (.seq (.ifs S (WMX.inc Bt) WMX.skip) (.wm (WM.rewind S SC)))

theorem readAt_exec (S : Fin (ns + 1)) {SC K Bt : Fin nr} (hR : [SC, K, Bt].Nodup) (u : List Bool) (v : ℕ)
    (σ : WState ns nr) (hS : RdEq (σ.st S) (marks u)) (hSh : σ.sh S = 0) (hSC : σ.val SC = 0)
    (hK : σ.val K = 2 * v + 1) (hB : σ.val Bt = 0) (hc : 2 * v + 2 ≤ cap) :
    WXExec cap (readAt S SC K Bt) σ ((σ.setv K 0).setv Bt (u.getD v false).toNat) (28 * v + 25) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR'
  obtain ⟨⟨sk, sb⟩, kb⟩ := hR'
  have e1 := skipN_exec (cap := cap) S (Ne.symm sk) (2 * v + 1) σ hK (by omega) (by omega)
  set σ1 := ((σ.seth S (σ.sh S + (2 * v + 1))).setv SC (σ.val SC + (2 * v + 1))).setv K 0 with hσ1
  have hbit : wbit σ1 S = u.getD v false := by
    unfold wbit; simp only [hσ1, WState.setv_st, WState.setv_sh, WState.seth_st, WState.seth_sh, Function.update_self]
    rw [hSh, Nat.zero_add, hS, rtb_marks]
  set σ2 := σ1.setv Bt (u.getD v false).toNat with hσ2
  have e2 : WXExec cap (.ifs S (WMX.inc Bt) WMX.skip) σ1 σ2 4 := by
    cases hu : u.getD v false
    · rw [hu] at hbit
      have e : σ2 = σ1 := by
        rw [hσ2, hu]; simp only [Bool.toNat_false]
        rw [show (0 : ℕ) = σ1.val Bt by simp [hσ1, Function.update_apply, Ne.symm sb, Ne.symm kb, hB]]
        exact wsetv_same σ1 Bt
      rw [e]; exact WXExec.mono (WXExec.ifsF hbit (WXExec.skip cap σ1)) (by omega)
    · rw [hu] at hbit
      have := WXExec.inc (cap := cap) Bt σ1 (by simp [hσ1, Function.update_apply, Ne.symm sb, Ne.symm kb, hB]; omega)
      refine WXExec.ifsT hbit (WXExec.cast cap this ?_ le_rfl)
      rw [hσ2, hu, show σ1.val Bt = 0 by simp [hσ1, Function.update_apply, sk, sb, kb, Ne.symm sk, Ne.symm sb, Ne.symm kb, hB]]; rfl
  have e3 := wrewind_spec (cap := cap) S SC (2 * v + 1) σ2 (by simp [hσ2, hσ1, Function.update_apply, sk, sb, kb, Ne.symm sk, Ne.symm sb, Ne.symm kb, hSC])
    (by simp [hσ2, hσ1, Function.update_apply, sk, sb, kb, Ne.symm sk, Ne.symm sb, Ne.symm kb, hSC]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.wm e3))) ?_ le_rfl)
    (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = S
    · simp [hj, hσ2, hσ1, hSh]
    · simp [hσ2, hσ1, Function.update_apply, hj]
  · rfl
  · funext q
    by_cases q1 : q = Bt
    · simp [q1, hσ2, hσ1, Function.update_apply, sk, sb, kb, Ne.symm sk, Ne.symm sb, Ne.symm kb]
    · by_cases q2 : q = K
      · simp [q2, hσ2, hσ1, Function.update_apply, sk, sb, kb, Ne.symm sk, Ne.symm sb, Ne.symm kb]
      · by_cases q3 : q = SC
        · simp [q3, hσ2, hσ1, Function.update_apply, sk, sb, kb, Ne.symm sk, Ne.symm sb, Ne.symm kb, hSC]
        · simp [hσ2, hσ1, Function.update_apply, q1, q2, q3]
  · rfl

/-! ## The output bit -/

/-- The framed output bit `frame [b].bits`. -/
def outWord (b : Bool) : List Bool := if b then [true, true, false] else [false]

theorem outWord_eq (b : Bool) : outWord b = frame b.toNat.bits := by
  cases b
  · rfl
  · simp [outWord, Nat.one_bits, frame]

theorem appendO_setv (σ : WState ns nr) (o : Fin (ns + 1)) (OP r : Fin nr) (hr : r ≠ OP) (x : ℕ) (u : List Bool) :
    appendO (σ.setv r x) o OP u = (appendO σ o OP u).setv r x := by
  apply WState.eq <;> try rfl
  funext q; simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
  by_cases q1 : q = OP
  · subst q1; simp [Ne.symm hr]
  · by_cases q2 : q = r
    · subst q2; simp [q1]
    · simp [q1, q2]

section Out
variable (O : Fin (ns + 1)) (OP : Fin nr)

/-- Append `[true, true, false]`. -/
def emT : WMX ns nr := .wm (.seq (Codec.emitMarks O OP [true]) (emitC O OP false))
/-- Append `[false]`. -/
def emF : WMX ns nr := .wm (emitC O OP false)

theorem emT_exec (σ : WState ns nr) (hd : σ.sh O = (σ.st O).length) (hc : σ.val OP + 3 ≤ cap) :
    WXExec cap (emT O OP) σ (appendO σ O OP (outWord true)) 24 := by
  have e1 := Codec.emitMarks_spec cap O OP [true] σ hd (by simp; omega)
  have e2 := Codec.emitBit_spec cap O OP false (appendO σ O OP (marks [true])) (by simp [appendO, hd])
    (by simp [appendO, marks]; omega)
  refine WXExec.wm (WExec.cast cap (WExec.seq e1 e2) ?_ (by simp))
  rw [appendO_append]; rfl

theorem emF_exec (σ : WState ns nr) (hd : σ.sh O = (σ.st O).length) (hc : σ.val OP + 3 ≤ cap) :
    WXExec cap (emF O OP) σ (appendO σ O OP (outWord false)) 24 :=
  WXExec.wm (WExec.mono (Codec.emitBit_spec cap O OP false σ hd (by omega)) (by omega))

/-- `frame [Bt = 1].bits`. -/
def selB (Bt : Fin nr) : WMX ns nr := .ifr Bt (emT O OP) (emF O OP)

theorem selB_exec (Bt : Fin nr) (σ : WState ns nr) (hb : σ.val Bt ≤ 1) (hd : σ.sh O = (σ.st O).length)
    (hc : σ.val OP + 3 ≤ cap) :
    WXExec cap (selB O OP Bt) σ (appendO σ O OP (outWord (decide (σ.val Bt = 1)))) 25 := by
  by_cases h : σ.val Bt = 1
  · rw [decide_eq_true h]; exact WXExec.ifrT (by omega) (emT_exec cap O OP σ hd hc)
  · rw [decide_eq_false h]; exact WXExec.ifrF (by omega) (emF_exec cap O OP σ hd hc)

/-- Continue with `Kp` when `[B = 1] xor [N = 1]`, else output `false`. -/
def chk (B N : Fin nr) (Kp : WMX ns nr) : WMX ns nr := .ifr B (.ifr N (emF O OP) Kp) (.ifr N Kp (emF O OP))

theorem chk_exec (B N : Fin nr) {Kp : WMX ns nr} {σ τ : WState ns nr} {c : ℕ} (hK : WXExec cap Kp σ τ c)
    (hb : σ.val B ≤ 1) (hn : σ.val N ≤ 1) (hd : σ.sh O = (σ.st O).length) (hc : σ.val OP + 3 ≤ cap) :
    WXExec cap (chk O OP B N Kp) σ
      (if xor (decide (σ.val B = 1)) (decide (σ.val N = 1)) then τ else appendO σ O OP (outWord false)) (c + 26) := by
  have hF := emF_exec cap O OP σ hd hc
  by_cases h1 : σ.val B = 1 <;> by_cases h2 : σ.val N = 1
  · simp only [h1, h2, decide_true, Bool.xor_self, if_false]
    exact WXExec.mono (WXExec.ifrT (by omega) (WXExec.ifrT (by omega) hF)) (by omega)
  · simp only [h1, h2, decide_true, decide_false, Bool.xor_false, if_true]
    exact WXExec.mono (WXExec.ifrT (by omega) (WXExec.ifrF (by omega) hK)) (by omega)
  · simp only [h1, h2, decide_true, decide_false, Bool.false_xor, if_true]
    exact WXExec.mono (WXExec.ifrF (by omega) (WXExec.ifrT (by omega) hK)) (by omega)
  · simp only [h1, h2, decide_false, Bool.xor_self, if_false]
    exact WXExec.mono (WXExec.ifrF (by omega) (WXExec.ifrF (by omega) hF)) (by omega)

/-- The AND of the three signed literals. -/
def andBr (B0 B1 B2 N0 N1 N2 : Fin nr) : WMX ns nr := chk O OP B0 N0 (chk O OP B1 N1 (chk O OP B2 N2 (emT O OP)))

theorem andBr_exec (B0 B1 B2 N0 N1 N2 : Fin nr) (σ : WState ns nr) (h0 : σ.val B0 ≤ 1) (h1 : σ.val B1 ≤ 1)
    (h2 : σ.val B2 ≤ 1) (g0 : σ.val N0 ≤ 1) (g1 : σ.val N1 ≤ 1) (g2 : σ.val N2 ≤ 1)
    (hd : σ.sh O = (σ.st O).length) (hc : σ.val OP + 3 ≤ cap) :
    WXExec cap (andBr O OP B0 B1 B2 N0 N1 N2) σ (appendO σ O OP (outWord
      ((xor (decide (σ.val B0 = 1)) (decide (σ.val N0 = 1)) && xor (decide (σ.val B1 = 1)) (decide (σ.val N1 = 1))) &&
        xor (decide (σ.val B2 = 1)) (decide (σ.val N2 = 1))))) 102 := by
  have e := chk_exec cap O OP B0 N0 (chk_exec cap O OP B1 N1 (chk_exec cap O OP B2 N2 (emT_exec cap O OP σ hd hc)
    h2 g2 hd hc) h1 g1 hd hc) h0 g0 hd hc
  refine WXExec.cast cap e ?_ (by omega)
  cases xor (decide (σ.val B0 = 1)) (decide (σ.val N0 = 1)) <;>
    cases xor (decide (σ.val B1 = 1)) (decide (σ.val N1 = 1)) <;>
    cases xor (decide (σ.val B2 = 1)) (decide (σ.val N2 = 1)) <;> rfl

/-- The table value from `j mod 5`, the coordinates `b_t` and the signs `n_t`. -/
def outBit (j5 b0 b1 b2 n0 n1 n2 : ℕ) : Bool :=
  if j5 = 0 then decide (b0 = 1) else if j5 = 1 then decide (b1 = 1) else if j5 = 2 then decide (b2 = 1) else
    (xor (decide (b0 = 1)) (decide (n0 = 1)) && xor (decide (b1 = 1)) (decide (n1 = 1))) &&
      xor (decide (b2 = 1)) (decide (n2 = 1))

/-- The output program. -/
def outW (J5 B0 B1 B2 N0 N1 N2 : Fin nr) : WMX ns nr :=
  .ifr J5 (.seq (WMX.dec J5) (.ifr J5 (.seq (WMX.dec J5) (.ifr J5 (andBr O OP B0 B1 B2 N0 N1 N2) (selB O OP B2)))
    (selB O OP B1))) (selB O OP B0)

theorem outW_exec (J5 B0 B1 B2 N0 N1 N2 : Fin nr) (hJ : ∀ r ∈ [B0, B1, B2, N0, N1, N2, OP], J5 ≠ r)
    (hJO : J5 ≠ OP) (σ : WState ns nr) (j5 : ℕ) (hj : σ.val J5 = j5) (hjc : j5 ≤ cap)
    (h0 : σ.val B0 ≤ 1) (h1 : σ.val B1 ≤ 1)
    (h2 : σ.val B2 ≤ 1) (g0 : σ.val N0 ≤ 1) (g1 : σ.val N1 ≤ 1) (g2 : σ.val N2 ≤ 1)
    (hd : σ.sh O = (σ.st O).length) (hc : σ.val OP + 3 ≤ cap) :
    WXExec cap (outW O OP J5 B0 B1 B2 N0 N1 N2) σ
      ((appendO σ O OP (outWord (outBit j5 (σ.val B0) (σ.val B1) (σ.val B2) (σ.val N0) (σ.val N1) (σ.val N2)))).setv
        J5 (j5 - min j5 2)) 112 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hJ
  obtain ⟨j0, j1, j2', k0, k1, k2, jo⟩ := hJ
  have v : ∀ r : Fin nr, J5 ≠ r → ∀ x, (σ.setv J5 x).val r = σ.val r := fun r h x => by
    simp [Function.update_apply, Ne.symm h]
  rcases Nat.lt_or_ge j5 3 with hl | hl
  · interval_cases j5
    · rw [show (0 : ℕ) - min 0 2 = σ.val J5 by simp [hj], ← appendO_setv σ O OP J5 hJO, wsetv_same]
      simp only [outBit, if_true]
      exact WXExec.mono (WXExec.ifrF hj (selB_exec cap O OP B0 σ h0 hd hc)) (by omega)
    · have e1 := WXExec.dec (cap := cap) J5 σ (by omega)
      set σ1 := σ.setv J5 (σ.val J5 - 1) with hσ1
      have hz : σ1.val J5 = 0 := by simp [hσ1, hj]
      have e2 := selB_exec cap O OP B1 σ1 (by rw [hσ1, v B1 j1]; exact h1) (by simpa [hσ1] using hd)
        (by rw [hσ1, v OP jo]; exact hc)
      refine WXExec.mono (WXExec.cast cap (WXExec.ifrT (by omega) (WXExec.seq e1 (WXExec.ifrF hz e2))) ?_ le_rfl)
        (by omega)
      rw [hσ1, v B1 j1, appendO_setv σ O OP J5 hJO, hj]
      simp [outBit]
    · have e1 := WXExec.dec (cap := cap) J5 σ (by omega)
      set σ1 := σ.setv J5 (σ.val J5 - 1) with hσ1
      have e2 := WXExec.dec (cap := cap) J5 σ1 (by simp [hσ1]; omega)
      set σ2 := σ1.setv J5 (σ1.val J5 - 1) with hσ2
      have hσ2' : σ2 = σ.setv J5 0 := by
        rw [hσ2, hσ1, LitDecode.setv_setv]; congr 1; simp [hj]
      have hz : σ2.val J5 = 0 := by simp [hσ2']
      have e3 := selB_exec cap O OP B2 σ2 (by rw [hσ2', v B2 j2']; exact h2)
        (by rw [hσ2']; simpa using hd) (by rw [hσ2', v OP jo]; exact hc)
      refine WXExec.mono (WXExec.cast cap (WXExec.ifrT (by omega) (WXExec.seq e1 (WXExec.ifrT (by simp [hσ1, hj])
        (WXExec.seq e2 (WXExec.ifrF hz e3))))) ?_ le_rfl) (by omega)
      rw [hσ2', v B2 j2', appendO_setv σ O OP J5 hJO]
      simp [outBit]
  · have e1 := WXExec.dec (cap := cap) J5 σ (by omega)
    set σ1 := σ.setv J5 (σ.val J5 - 1) with hσ1
    have e2 := WXExec.dec (cap := cap) J5 σ1 (by simp [hσ1]; omega)
    set σ2 := σ1.setv J5 (σ1.val J5 - 1) with hσ2
    have hσ2' : σ2 = σ.setv J5 (j5 - 2) := by
      rw [hσ2, hσ1, LitDecode.setv_setv]; congr 1; simp [hj]; omega
    have e3 := andBr_exec cap O OP B0 B1 B2 N0 N1 N2 σ2
      (by rw [hσ2', v B0 j0]; exact h0) (by rw [hσ2', v B1 j1]; exact h1) (by rw [hσ2', v B2 j2']; exact h2)
      (by rw [hσ2', v N0 k0]; exact g0) (by rw [hσ2', v N1 k1]; exact g1) (by rw [hσ2', v N2 k2]; exact g2)
      (by rw [hσ2']; simpa using hd) (by rw [hσ2', v OP jo]; exact hc)
    refine WXExec.mono (WXExec.cast cap (WXExec.ifrT (by omega) (WXExec.seq e1 (WXExec.ifrT (by simp [hσ1, hj]; omega)
      (WXExec.seq e2 (WXExec.ifrT (by rw [hσ2']; simp; omega) e3))))) ?_ le_rfl) (by omega)
    rw [hσ2', v B0 j0, v B1 j1, v B2 j2', v N0 k0, v N1 k1, v N2 k2, appendO_setv σ O OP J5 hJO]
    have hn0 : ¬ j5 = 0 := by omega
    have hn1 : ¬ j5 = 1 := by omega
    have hn2 : ¬ j5 = 2 := by omega
    have hm : j5 - min j5 2 = j5 - 2 := by omega
    rw [hm]
    unfold outBit
    rw [if_neg hn0, if_neg hn1, if_neg hn2]

end Out

end NearCubicGates.Close.Recovery.HTParts
