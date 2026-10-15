import Proof.Gates.Recovery.HTParts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HTParts

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.CheckedPCPP.LitDecode (rtb_off rtb_off0)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Unary runs -/

section One
variable {src dst : Fin (ns + 1)} {OP SC : Fin nr}

/-- The cells of a unary run `1^R`, up to its end. -/
def oneLoop (src : Fin (ns + 1)) (SC : Fin nr) (E : Bool → WM ns nr) : WM ns nr := .whs src (cellE src SC E)

theorem oneLoop_spec (hsd : src ≠ dst) (hOS : OP ≠ SC) {e : Bool → List Bool} {E : Bool → WM ns nr} {c : ℕ}
    (hE : Emits cap dst OP e E c) (rest : List Bool) (hrest : rest.headD false = false) :
    ∀ (R : ℕ) (pre : List Bool) (σ : WState ns nr), σ.st src = pre ++ List.replicate R true ++ rest →
      σ.sh src = pre.length → σ.sh dst = (σ.st dst).length → σ.val OP + R * (e true).length ≤ cap →
      σ.val SC + R < cap + 1 →
      WExec cap (oneLoop src SC E) σ (adv src dst OP SC σ ((List.replicate R true).flatMap e) R) (R * (c + 9) + 1)
  | 0, pre, σ, hst, hsh, _, _, _ => by
    simp only [List.replicate_zero, List.flatMap_nil, adv_zero, Nat.zero_mul, Nat.zero_add]
    refine WExec.whsF ?_
    unfold wbit; rw [hst, hsh]; simp [rtb_off0]
    cases rest with
    | nil => rfl
    | cons a r => simp at hrest; subst hrest; rfl
  | R + 1, pre, σ, hst, hsh, hd, hOc, hSc => by
    have hst' : σ.st src = pre ++ (true :: (List.replicate R true ++ rest)) := by
      rw [hst]; simp [List.replicate_succ]
    have hw : wbit σ src = true := by unfold wbit; rw [hst', hsh, rtb_off0]; rfl
    have hm : readTapeBit (σ.st src) (σ.sh src) = true := by rw [hst', hsh, rtb_off0]; rfl
    have x1 := cellE_spec cap hsd hOS hE σ hd (by rw [hm]; nlinarith) (by omega)
    rw [hm] at x1
    set σ1 := adv src dst OP SC σ (e true) 1 with hσ1
    have ih := oneLoop_spec hsd hOS hE rest hrest R (pre ++ [true]) σ1
      (by rw [hσ1, adv_st_src hsd, hst]; simp [List.replicate_succ])
      (by rw [hσ1, adv_sh_src, hsh]; simp)
      (by rw [hσ1, adv_sh_dst hsd, adv_st_dst]; simp [hd])
      (by rw [hσ1, adv_val_OP hOS]; nlinarith)
      (by rw [hσ1, adv_val_SC]; omega)
    refine WExec.mono (WExec.cast cap (WExec.whsT hw x1 ih) ?_ le_rfl) (by ring_nf; omega)
    rw [hσ1, adv_adv hsd hOS]
    simp only [List.replicate_succ, List.flatMap_cons]
    congr 1; ring

end One

/-! ## Bits -/

theorem bits_half (v : ℕ) (hv : v ≠ 0) : v.bits = decide (v % 2 = 1) :: (v / 2).bits := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h
  · have e : v = 2 * (v / 2) := by omega
    have hne : v / 2 ≠ 0 := by omega
    conv_lhs => rw [e]
    rw [Nat.bit0_bits _ hne]; simp [h]
  · have e : v = 2 * (v / 2) + 1 := by omega
    conv_lhs => rw [e]
    rw [Nat.bit1_bits]; simp [h]

section Bits
variable {X H B OP : Fin nr} {dst : Fin (ns + 1)}

/-- Emit the bits of `X` (low first), each as `marks [true, b]`; `X := 0` (`H`, `B` scratch). -/
def bitsQ (X H B : Fin nr) (dst : Fin (ns + 1)) (OP : Fin nr) : WMX ns nr :=
  .whr X (.seq (EmitNat.halve X H B) (.seq (.ifr B (.seq (.wm (Codec.emitMarks dst OP [true, true])) (WMX.dec B))
    (.wm (Codec.emitMarks dst OP [true, false]))) (.wm (WM.move H X))))

theorem bitsQ_exec (hR : [X, H, B, OP].Nodup) (v0 : ℕ) (hv0 : v0 + 1 ≤ cap) :
    ∀ (v : ℕ) (σ : WState ns nr), v ≤ v0 → σ.val X = v → σ.val H = 0 → σ.val B = 0 →
      σ.sh dst = (σ.st dst).length → σ.val OP + 4 * v.bits.length ≤ cap →
      WXExec cap (bitsQ X H B dst OP) σ ((appendO σ dst OP (v.bits.flatMap fun b => marks [true, b])).setv X 0)
        (v.bits.length * (12 * v0 + 60) + 1) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR'
  obtain ⟨⟨xh, xb, xo⟩, ⟨hb, ho⟩, bo⟩ := hR'
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro σ hvle hX hH hB hd hOc
  by_cases hv : v = 0
  · subst hv
    simp only [Nat.zero_bits, List.flatMap_nil, appendO_nil, List.length_nil, Nat.zero_mul, Nat.zero_add]
    rw [show σ.setv X 0 = σ by rw [← hX]; exact wsetv_same σ X]
    exact WXExec.whrF hX
  · have hbits := bits_half v hv
    set b := decide (v % 2 = 1) with hbdef
    have hlen : v.bits.length = (v / 2).bits.length + 1 := by rw [hbits]; rfl
    -- halve
    have e1 := EmitNat.halve_exec (cap := cap) X H B xh xb hb v σ hX hB (by rw [hH]; omega) (by omega) (by omega)
    set σ1 := ((σ.setv X 0).setv H (σ.val H + v / 2)).setv B (v % 2) with hσ1
    -- emit
    have hd1 : σ1.sh dst = (σ1.st dst).length := by simpa [hσ1] using hd
    have hO1 : σ1.val OP = σ.val OP := by simp [hσ1, Function.update_apply, Ne.symm xo, Ne.symm ho, Ne.symm bo]
    set σ2 := appendO σ1 dst OP (marks [true, b]) with hσ2
    have e2 : WXExec cap (.ifr B (.seq (.wm (Codec.emitMarks dst OP [true, true])) (WMX.dec B))
        (.wm (Codec.emitMarks dst OP [true, false]))) σ1 (σ2.setv B 0) 36 := by
      have hm := Codec.emitMarks_spec cap dst OP [true, b] σ1 hd1 (by rw [hO1]; simp; omega)
      rcases Nat.mod_two_eq_zero_or_one v with h2 | h2
      · have hbf : b = false := by simp [hbdef, h2]
        rw [hbf] at hm hσ2
        rw [← hσ2] at hm
        have hB1 : σ1.val B = 0 := by simp [hσ1, h2]
        have e : σ2.setv B 0 = σ2 := by
          rw [show (0 : ℕ) = σ2.val B by simp [hσ2, appendO, Function.update_apply, bo, hB1]]
          exact wsetv_same σ2 B
        rw [e]
        exact WXExec.mono (WXExec.ifrF hB1 (WXExec.wm hm)) (by simp)
      · have hbt : b = true := by simp [hbdef, h2]
        rw [hbt] at hm hσ2
        rw [← hσ2] at hm
        have hB1 : σ1.val B = 1 := by simp [hσ1, h2]
        have hd2 := WXExec.dec (cap := cap) B σ2 (by simp [hσ2, appendO, Function.update_apply, bo, hB1]; omega)
        have e : σ2.setv B (σ2.val B - 1) = σ2.setv B 0 := by
          simp [hσ2, appendO, Function.update_apply, bo, hB1]
        rw [e] at hd2
        exact WXExec.mono (WXExec.ifrT (by rw [hB1]; simp) (WXExec.seq (WXExec.wm hm) hd2)) (by simp)
    -- move
    have hH2 : (σ2.setv B 0).val H = v / 2 := by
      simp [hσ2, hσ1, appendO, Function.update_apply, ho, hb, Ne.symm hb, hH]
    have hX2 : (σ2.setv B 0).val X = 0 := by
      simp [hσ2, hσ1, appendO, Function.update_apply, xo, xb, Ne.symm xb, xh]
    have e3 := wmove_spec (cap := cap) H X (Ne.symm xh) (v / 2) (σ2.setv B 0) hH2 (by rw [hH2]; omega)
      (by rw [hH2, hX2]; omega)
    rw [hH2, hX2, Nat.zero_add] at e3
    set σ3 := ((σ2.setv B 0).setv H 0).setv X (v / 2) with hσ3
    have ih' := ih (v / 2) (by omega) σ3 (by omega) (by simp [hσ3]) (by simp [hσ3, Function.update_apply, hb, Ne.symm xh])
      (by simp [hσ3, Function.update_apply, Ne.symm xb, Ne.symm hb])
      (by simp [hσ3, hσ2, appendO]; rw [hd1])
      (by simp [hσ3, hσ2, appendO, Function.update_apply, Ne.symm xo, Ne.symm ho, Ne.symm bo, hO1, marks]
          rw [hlen] at hOc; omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by rw [hX]; exact hv) (WXExec.seq e1 (WXExec.seq e2
      (WXExec.wm e3))) ih') ?_ le_rfl) (by rw [hlen]; ring_nf; omega)
    rw [hbits]
    apply WState.eq
    · funext j; by_cases hj : j = dst
      · subst hj; simp [hσ3, hσ2, hσ1, appendO, List.flatMap_cons]; omega
      · simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, hj]
    · funext j; by_cases hj : j = dst
      · subst hj; simp [hσ3, hσ2, hσ1, appendO, List.flatMap_cons, List.append_assoc]
      · simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, hj]
    · funext q
      simp only [hσ3, hσ2, hσ1, appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      by_cases q1 : q = X
      · subst q1; simp [xo]
      · by_cases q2 : q = OP
        · subst q2; simp [q1, Ne.symm xo, Ne.symm ho, Ne.symm bo, marks, List.flatMap_cons]; ring
        · by_cases q3 : q = H
          · subst q3; simp [q1, q2, hH]
          · by_cases q4 : q = B
            · subst q4; simp [q1, q2, q3, hB]
            · simp [q1, q2, q3, q4]
    · simp [hσ3, hσ2, hσ1, appendO]

end Bits

end NearCubicGates.Close.Recovery.HTParts
