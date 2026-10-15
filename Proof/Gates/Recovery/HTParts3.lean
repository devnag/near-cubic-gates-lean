import Proof.Gates.Recovery.HTParts2
import Proof.Gates.Recovery.TableSem

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

/-! ## Bit length -/

section Size
variable {X H B C : Fin nr}

/-- `C += size X`, `X := 0` (`H`, `B` scratch). -/
def sizeW (X H B C : Fin nr) : WMX ns nr :=
  .whr X (.seq (EmitNat.halve X H B) (.seq (.wm (WM.clear B)) (.seq (.wm (WM.move H X)) (WMX.inc C))))

theorem size_half (v : ℕ) (hv : v ≠ 0) : v.size = (v / 2).size + 1 := by
  rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len, bits_half v hv]; rfl

theorem sizeW_exec (hR : [X, H, B, C].Nodup) (v0 : ℕ) (hv0 : v0 + 1 ≤ cap) :
    ∀ (v : ℕ) (σ : WState ns nr), v ≤ v0 → σ.val X = v → σ.val H = 0 → σ.val B = 0 →
      σ.val C + v.size ≤ cap →
      WXExec cap (sizeW X H B C) σ ((σ.setv X 0).setv C (σ.val C + v.size)) (v.size * (12 * v0 + 30) + 1) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR'
  obtain ⟨⟨xh, xb, xc⟩, ⟨hb, hc⟩, bc⟩ := hR'
  have hx := Ne.symm xh; have bx := Ne.symm xb; have cx := Ne.symm xc
  have bh := Ne.symm hb; have ch := Ne.symm hc; have cb := Ne.symm bc
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro σ hvle hX hH hB hC
  by_cases hv : v = 0
  · subst hv
    simp only [Nat.size_zero, Nat.add_zero, Nat.zero_mul, Nat.zero_add]
    rw [show (σ.setv X 0).setv C (σ.val C) = σ by rw [← hX, wsetv_same, wsetv_same]]
    exact WXExec.whrF hX
  · have hs := size_half v hv
    have e1 := EmitNat.halve_exec (cap := cap) X H B xh xb hb v σ hX hB (by rw [hH]; omega) (by omega) (by omega)
    set σ1 := ((σ.setv X 0).setv H (σ.val H + v / 2)).setv B (v % 2) with hσ1
    have hm2 : v % 2 < 2 := Nat.mod_lt _ (by decide)
    have e2 := wclear_spec (cap := cap) B (v % 2) σ1 (by simp [hσ1]) (by simp [hσ1]; omega)
    set σ2 := σ1.setv B 0 with hσ2
    have e3 := wmove_spec (cap := cap) H X hx (v / 2) σ2 (by simp [hσ2, hσ1, Function.update_apply, hb, hx, hH])
      (by simp [hσ2, hσ1, Function.update_apply, hb, hx, hH]; omega)
      (by simp [hσ2, hσ1, Function.update_apply, hb, hx, bx, xh, xb, hH]; omega)
    set σ3 := (σ2.setv H 0).setv X (σ2.val X + σ2.val H) with hσ3
    have e4 := WXExec.inc (cap := cap) C σ3 (by simp [hσ3, hσ2, hσ1, Function.update_apply, cx, ch, cb]; omega)
    set σ4 := σ3.setv C (σ3.val C + 1) with hσ4
    have ih' := ih (v / 2) (by omega) σ4 (by omega)
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, xc, xh, xb, hb, hH])
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hc, hx])
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, bc, bh, bx])
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, cx, ch, cb]; omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by rw [hX]; exact hv) (WXExec.seq e1 (WXExec.seq (WXExec.wm e2)
      (WXExec.seq (WXExec.wm e3) e4))) ih') ?_ le_rfl) (by rw [hs]; ring_nf; omega)
    apply WState.eq <;> try rfl
    funext q
    by_cases q1 : q = X
    · simp [q1, hσ4, hσ3, hσ2, hσ1, xc]
    · by_cases q2 : q = C
      · simp [q2, hσ4, hσ3, hσ2, hσ1, cx, ch, cb, hs]; omega
      · by_cases q3 : q = H
        · simp [q3, hσ4, hσ3, hσ2, hσ1, hc, hx, hH]
        · by_cases q4 : q = B
          · simp [q4, hσ4, hσ3, hσ2, hσ1, bc, bh, bx, hB]
          · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, q1, q2, q3, q4]

end Size

/-! ## Comparison -/

section Le
variable {A B U K T F : Fin nr}

/-- `U := U − K` (saturating), `K := 0`. -/
def decLoop (K U : Fin nr) : WMX ns nr := .whr K (.seq (WMX.dec K) (WMX.dec U))

theorem decLoop_exec {K U : Fin nr} (hKU : K ≠ U) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val K = k → k ≤ cap → σ.val U ≤ cap →
      WXExec cap (decLoop K U) σ ((σ.setv K 0).setv U (σ.val U - k)) (k * 5 + 1)
  | 0, σ, hK, _, _ => by
    rw [show (σ.setv K 0).setv U (σ.val U - 0) = σ by rw [Nat.sub_zero, ← hK, wsetv_same, wsetv_same]]
    exact WXExec.whrF hK
  | k + 1, σ, hK, hk, hU => by
    have e1 := WXExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have e2 := WXExec.dec (cap := cap) U σ1 (by simp [hσ1, Function.update_apply, Ne.symm hKU]; omega)
    set σ2 := σ1.setv U (σ1.val U - 1) with hσ2
    have ih := decLoop_exec hKU k σ2 (by simp [hσ2, hσ1, hKU, hK]) (by omega)
      (by simp [hσ2, hσ1, Function.update_apply, Ne.symm hKU]; omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq e1 e2) ih) ?_ le_rfl) (by ring_nf; omega)
    apply WState.eq <;> try rfl
    funext q
    by_cases q1 : q = U
    · simp [q1, hσ2, hσ1, Ne.symm hKU]; omega
    · by_cases q2 : q = K
      · simp [q2, hσ2, hσ1, hKU]
      · simp [hσ2, hσ1, Function.update_apply, q1, q2]

/-- `F := [A ≤ B]` (`U`, `K`, `T` scratch; `A`, `B` kept). -/
def leW (A B U K T F : Fin nr) : WMX ns nr :=
  .seq (addR A U T) (.seq (addR B K T) (.seq (decLoop K U) (.seq (.ifr U WMX.skip (WMX.inc F)) (.wm (WM.clear U)))))

theorem leW_exec (hR : [A, B, U, K, T, F].Nodup) (a b : ℕ) (hab : a + b + 1 ≤ cap) (σ : WState ns nr)
    (hA : σ.val A = a) (hB : σ.val B = b) (hU : σ.val U = 0) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (hF : σ.val F = 0) :
    WXExec cap (leW A B U K T F) σ (σ.setv F (if a ≤ b then 1 else 0)) (25 * a + 25 * b + 30) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR'
  obtain ⟨⟨ab, au, ak, aT, af⟩, ⟨bu, bk, bT, bf⟩, ⟨uk, uT, uf⟩, ⟨kT, kf⟩, Tf⟩ := hR'
  have ba := Ne.symm ab; have ua := Ne.symm au; have ka := Ne.symm ak; have Ta := Ne.symm aT; have fa := Ne.symm af
  have ub := Ne.symm bu; have kb := Ne.symm bk; have Tb := Ne.symm bT; have fb := Ne.symm bf
  have ku := Ne.symm uk; have Tu := Ne.symm uT; have fu := Ne.symm uf; have Tk := Ne.symm kT; have fk := Ne.symm kf
  have fT := Ne.symm Tf
  have e1 := addR_spec cap au aT uT σ hT (by omega)
  rw [hU, hA, Nat.zero_add] at e1
  set σ1 := σ.setv U a with hσ1
  have e2 := addR_spec cap bk bT kT σ1 (by simp [hσ1, Function.update_apply, Tu, hT])
    (by simp [hσ1, Function.update_apply, ku, kb, bu, hK, hB]; omega)
  set σ2 := σ1.setv K (σ1.val K + σ1.val B) with hσ2
  have hK2 : σ2.val K = b := by simp [hσ2, hσ1, Function.update_apply, ku, bu, hK, hB]
  have hU2 : σ2.val U = a := by simp [hσ2, hσ1, Function.update_apply, uk]
  have e3 := decLoop_exec (cap := cap) ku b σ2 hK2 (by omega) (by omega)
  set σ3 := (σ2.setv K 0).setv U (σ2.val U - b) with hσ3
  have hU3 : σ3.val U = a - b := by simp [hσ3, hU2]
  have e4 : WXExec cap (.ifr U WMX.skip (WMX.inc F)) σ3 (σ3.setv F (if a ≤ b then 1 else 0)) 4 := by
    by_cases h : a ≤ b
    · rw [if_pos h]
      have := WXExec.inc (cap := cap) F σ3 (by simp [hσ3, hσ2, hσ1, Function.update_apply, fu, fk, hF]; omega)
      refine WXExec.mono (WXExec.ifrF (by rw [hU3]; omega) (WXExec.cast cap this ?_ le_rfl)) (by omega)
      simp [hσ3, hσ2, hσ1, Function.update_apply, fu, fk, hF]
    · rw [if_neg h]
      have e : σ3.setv F 0 = σ3 := by
        rw [show (0 : ℕ) = σ3.val F by simp [hσ3, hσ2, hσ1, Function.update_apply, fu, fk, hF]]; exact wsetv_same σ3 F
      rw [e]; exact WXExec.mono (WXExec.ifrT (by rw [hU3]; omega) (WXExec.skip cap σ3)) (by omega)
  have e5 := wclear_spec (cap := cap) U (a - b) (σ3.setv F (if a ≤ b then 1 else 0)) (by simp [uf, hU3])
    (by simp [uf, hU3]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.wm e5)))))
    ?_ le_rfl) (by rw [show σ1.val B = b by simp [hσ1, Function.update_apply, bu, hB]]; omega)
  apply WState.eq <;> try rfl
  funext q
  by_cases q1 : q = F
  · simp [q1, hσ3, fu]
  · by_cases q2 : q = U
    · simp [q2, hσ3, uf, hU]
    · by_cases q3 : q = K
      · simp [q3, hσ3, hσ2, hσ1, kf, ku, hK]
      · simp [hσ3, hσ2, hσ1, Function.update_apply, q1, q2, q3]

end Le

end NearCubicGates.Close.Recovery.HTParts
