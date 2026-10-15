import Proof.Gates.CheckedPCPP.EncCols
import Proof.Gates.CheckedPCPP.FramedWord
import Proof.Gates.WordPrograms.RegArith
import Proof.Gates.CheckedPCPP.NodeEmit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.EncSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget

/-! ## The encoder as a word function with a polynomial budget -/

theorem bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem frame_len (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, ih]; ring

theorem messageWord_len (m : MessageRequest) : (messageWord m).length ≤ 8 * (m.1 + 1) := by
  unfold messageWord
  simp only [List.length_append, frame_len, List.length_ofFn]
  have := bits_length_le m.1
  omega

theorem encWord (P : ThreeQueryPCPP) : ∃ K e : ℕ, Nonempty (WordFunction MessageRequest messageWord
    (fun m => FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val))) (fun m => K * (m.1 + 1) ^ e)) := by
  obtain ⟨h⟩ := P.encPoly
  obtain ⟨K, e, hw⟩ := FramedSim.tm2Poly_ordinary h (fun m => m.1) 8 1 (fun m => by simpa using messageWord_len m)
  exact ⟨K, e, hw⟩

/-! ## The bound `B` -/

/-- `B(q) = Cb·(q + 1)^eb` with `Cb = K + 2·Kc + 20`, `eb = e + 1`. -/
def bound (K e Kc q : ℕ) : ℕ := (K + 2 * Kc + 20) * (q + 1) ^ (e + 1)

theorem bound_ok (E : LinearCodeFamily) (K e Kc : ℕ) (hKc : ∀ n, 2 ≤ n → E.length n ≤ Kc * (n + 1)) (q : ℕ)
    (hq : 2 ≤ q) (i : ℕ) (hn : 2 ≤ q) :
    (frame (messageWord (unitReq q i hn))).length + K * ((unitReq q i hn).1 + 1) ^ e + 1 ≤ bound K e Kc q ∧
      2 * E.length q ≤ bound K e Kc q := by
  have hm := messageWord_len (unitReq q i hn)
  have hL := hKc q hq
  have hp1 : (q + 1) ^ e ≤ (q + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hp2 : q + 1 ≤ (q + 1) ^ (e + 1) := by
    calc q + 1 = (q + 1) ^ 1 := by ring
      _ ≤ (q + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [unitReq] at hm ⊢
  rw [frame_len]
  unfold bound
  constructor <;> nlinarith

/-! ## Computing `B` in a register -/

variable {ns nr : ℕ} (cap : ℕ)

def mulStep (X Y Z A2 T : Fin nr) : WMX ns nr :=
  .seq (mulR Y A2 X Z T) (.seq (.wm (WM.clear Y)) (.wm (WM.move Z Y)))

theorem mulStep_spec {X Y Z A2 T : Fin nr} (hR : [Y, A2, X, Z, T].Nodup) (σ : WState ns nr)
    (hZ : σ.val Z = 0) (hA2 : σ.val A2 = 0) (hT : σ.val T = 0) (hcap : σ.val Y * σ.val X + σ.val Y ≤ cap)
    (hcapY : 2 * σ.val Y ≤ cap) :
    WXExec cap (mulStep X Y Z A2 T) σ (σ.setv Y (σ.val Y * σ.val X))
      (σ.val Y * (18 * σ.val X + 3 + 8) + 7 * σ.val Y + 3 + 1 + (3 * σ.val Y + 1) + 1 + (7 * (σ.val Y * σ.val X) + 1)) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR'
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hR'
  have e1 := mulR_spec cap (A := Y) (A2 := A2) (B := X) (C := Z) (T := T) hR σ hA2 hT (by rw [hZ]; nlinarith)
    (by omega)
  rw [hZ, Nat.zero_add] at e1
  have hYZ : (σ.setv Z (σ.val Y * σ.val X)).val Y = σ.val Y := by
    simp only [WState.setv_val]; exact Function.update_of_ne h3 _ _
  have e2 := wclear_spec (cap := cap) Y (σ.val Y) (σ.setv Z (σ.val Y * σ.val X)) hYZ (by rw [hYZ]; omega)
  have e3 := wmove_spec (cap := cap) Z Y (Ne.symm h3) (σ.val Y * σ.val X)
    ((σ.setv Z (σ.val Y * σ.val X)).setv Y 0) (by simp [Function.update_of_ne (Ne.symm h3)])
    (by simp [Function.update_of_ne (Ne.symm h3)]; nlinarith) (by simp [Function.update_of_ne (Ne.symm h3)]; nlinarith)
  refine (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.wm e3))).cast cap ?_ (by omega)
  apply WState.eq <;> try rfl
  funext r
  simp only [WState.setv_val, Function.update_apply]
  split_ifs <;> simp_all

/-- `Y := Y·X^k`. -/
def powW (X Y Z A2 T : Fin nr) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | k + 1 => .seq (mulStep X Y Z A2 T) (powW X Y Z A2 T k)

/-- A crude cost bound of `powW` when every intermediate value is at most `W`. -/
def powCost (W k : ℕ) : ℕ := k * (40 * W * W + 40 * W + 20)

theorem powW_spec {X Y Z A2 T : Fin nr} (hR : [Y, A2, X, Z, T].Nodup) (W : ℕ) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val Z = 0 → σ.val A2 = 0 → σ.val T = 0 →
      σ.val Y * σ.val X ^ k ≤ W → 1 ≤ σ.val X → 2 * W + W * W ≤ cap →
      WXExec cap (powW X Y Z A2 T k) σ (σ.setv Y (σ.val Y * σ.val X ^ k)) (powCost W k)
  | 0, σ, _, _, _, _, _, _ => by
    simp only [powW, pow_zero, Nat.mul_one, wsetv_same, powCost, Nat.zero_mul]
    exact WXExec.skip cap σ
  | k + 1, σ, hZ, hA2, hT, hW, hX, hcap => by
    have hR' := hR
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
      and_true] at hR'
    obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hR'
    have hpk : 1 ≤ σ.val X ^ k := Nat.one_le_pow _ _ hX
    have hYX : σ.val Y * σ.val X ≤ W := by
      calc σ.val Y * σ.val X ≤ σ.val Y * σ.val X * σ.val X ^ k := Nat.le_mul_of_pos_right _ hpk
        _ = σ.val Y * σ.val X ^ (k + 1) := by ring
        _ ≤ W := hW
    have hY : σ.val Y ≤ W := le_trans (Nat.le_mul_of_pos_right _ hX) hYX
    have hXW : σ.val X ≤ W ∨ σ.val Y = 0 := by
      rcases Nat.eq_zero_or_pos (σ.val Y) with h | h
      · exact Or.inr h
      · exact Or.inl (le_trans (Nat.le_mul_of_pos_left _ h) hYX)
    have e1 := mulStep_spec cap hR σ hZ hA2 hT (by nlinarith) (by nlinarith)
    have ih := powW_spec hR W k (σ.setv Y (σ.val Y * σ.val X))
      (by simp [Function.update_of_ne (Ne.symm h3), hZ]) (by simp [Function.update_of_ne (Ne.symm h1), hA2])
      (by simp [Function.update_of_ne (Ne.symm h4), hT])
      (by
        simp only [WState.setv_val, Function.update_self, Function.update_of_ne (Ne.symm h2)]
        calc σ.val Y * σ.val X * σ.val X ^ k = σ.val Y * σ.val X ^ (k + 1) := by ring
            _ ≤ W := hW)
      (by simp only [WState.setv_val, Function.update_of_ne (Ne.symm h2)]; exact hX) hcap
    refine (WXExec.seq e1 ih).cast cap ?_ ?_
    · rw [wsetv_setv]
      simp only [WState.setv_val, Function.update_self, Function.update_of_ne (Ne.symm h2)]
      ring_nf
    · unfold powCost
      rcases hXW with hXW | hY0
      · have : σ.val Y * (18 * σ.val X + 3 + 8) ≤ 18 * W * W + 11 * W := by nlinarith
        nlinarith
      · rw [hY0]; simp; nlinarith

def boundW (Q X Y Z A2 T BR : Fin nr) (Cb eb : ℕ) : WMX ns nr :=
  .seq (addR Q X T) (.seq (WMX.inc X) (.seq (.wm (NodeEmit.incN Y Cb)) (.seq (powW X Y Z A2 T eb)
    (.seq (.wm (WM.move Y BR)) (.wm (WM.clear X))))))

theorem boundW_spec {Q X Y Z A2 T BR : Fin nr} (hR : [Q, X, Y, Z, A2, T, BR].Nodup) (Cb eb W : ℕ) (σ : WState ns nr)
    (hX : σ.val X = 0) (hY : σ.val Y = 0) (hZ : σ.val Z = 0) (hA2 : σ.val A2 = 0) (hT : σ.val T = 0)
    (hBR : σ.val BR = 0) (hW : Cb * (σ.val Q + 1) ^ eb ≤ W) (hcap : 2 * W + W * W + σ.val Q + 2 ≤ cap) :
    WXExec cap (boundW Q X Y Z A2 T BR Cb eb) σ (σ.setv BR (Cb * (σ.val Q + 1) ^ eb))
      (18 * σ.val Q + 3 + 1 + 3 + 1 + 4 * Cb + 1 + powCost W eb + 1 + (7 * (Cb * (σ.val Q + 1) ^ eb) + 1) + 1 +
        (3 * (σ.val Q + 1) + 1)) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR'
  obtain ⟨⟨q1, q2, q3, q4, q5, q6⟩, ⟨x1, x2, x3, x4, x5⟩, ⟨y1, y2, y3, y4⟩, ⟨z1, z2, z3⟩, ⟨a1, a2⟩, t1⟩ := hR'
  set q := σ.val Q
  have hp : 1 ≤ (q + 1) ^ eb := Nat.one_le_pow _ _ (by omega)
  have hCbW : Cb ≤ W := le_trans (Nat.le_mul_of_pos_right _ hp) hW
  have e1 := addR_spec cap (A := Q) (B := X) (T := T) q1 q5 x4 σ hT (by rw [hX]; nlinarith)
  rw [hX, Nat.zero_add] at e1
  set σ1 := σ.setv X q with hσ1
  have e2 := WXExec.inc cap X σ1 (by simp [hσ1]; nlinarith)
  set σ2 := σ1.setv X (σ1.val X + 1) with hσ2
  have e3 := NodeEmit.incN_spec cap Y Cb σ2 (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm x1), hY]; omega)
  set σ3 := σ2.setv Y (σ2.val Y + Cb) with hσ3
  have hσ3Y : σ3.val Y = Cb := by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm x1), hY]
  have hσ3X : σ3.val X = q + 1 := by simp [hσ3, hσ2, hσ1, Function.update_of_ne x1]
  have e4 := powW_spec cap (X := X) (Y := Y) (Z := Z) (A2 := A2) (T := T) (by simp [*, Ne.symm y3, Ne.symm x1,
      Ne.symm x3, Ne.symm y4, Ne.symm z1, Ne.symm z3, Ne.symm z2, Ne.symm a1, Ne.symm x4])
    W eb σ3 (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm y1), Function.update_of_ne (Ne.symm x2), hZ])
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm y2), Function.update_of_ne (Ne.symm x3), hA2])
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm y3), Function.update_of_ne (Ne.symm x4), hT])
    (by rw [hσ3Y, hσ3X]; exact hW) (by rw [hσ3X]; omega) (by omega)
  rw [hσ3Y, hσ3X] at e4
  set σ4 := σ3.setv Y (Cb * (q + 1) ^ eb) with hσ4
  have e5 := wmove_spec (cap := cap) Y BR y4 (Cb * (q + 1) ^ eb) σ4 (by simp [hσ4]) (by simp [hσ4]; omega)
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm y4), Function.update_of_ne (Ne.symm x5), hBR]; omega)
  have hX6 : ((σ4.setv Y 0).setv BR (σ4.val BR + σ4.val Y)).val X = q + 1 := by
    simp [hσ4, hσ3, Function.update_of_ne x5, Function.update_of_ne x1, hσ3X]; simp [hσ2, hσ1]
  have e6 := wclear_spec (cap := cap) X (q + 1) ((σ4.setv Y 0).setv BR (σ4.val BR + σ4.val Y)) hX6
    (by rw [hX6]; omega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.wm e3) (WXExec.seq e4 (WXExec.seq (WXExec.wm e5)
    (WXExec.wm e6)))))).cast cap ?_ (le_of_eq (by ring))
  apply WState.eq <;> try rfl
  funext r
  simp only [hσ4, hσ3, hσ2, hσ1, WState.setv_val, Function.update_apply]
  split_ifs <;> simp_all

def fillW (TT LG : Fin (ns + 1)) (BR C2 CNT T : Fin nr) : WMX ns nr :=
  .seq (repK BR C2 (.seq (WMX.wr TT true) (.seq (WMX.fwd TT) (.seq (WMX.wr LG false) (WMX.fwd LG)))))
    (.seq (addR BR CNT T) (.seq (.wm (WM.rewind TT CNT)) (.seq (addR BR CNT T) (.wm (WM.rewind LG CNT)))))

theorem fillW_spec {TT LG : Fin (ns + 1)} (hTL : TT ≠ LG) {BR C2 CNT T : Fin nr} (hR : [BR, C2, CNT, T].Nodup)
    (B : ℕ) (σ : WState ns nr) (hTT : σ.st TT = []) (hTTh : σ.sh TT = 0) (hLG : σ.st LG = []) (hLGh : σ.sh LG = 0)
    (hB : σ.val BR = B) (hC2 : σ.val C2 = 0) (hCNT : σ.val CNT = 0) (hT : σ.val T = 0) (hcap : 2 * B + 1 ≤ cap) :
    WXExec cap (fillW TT LG BR C2 CNT T) σ ((σ.sets TT (List.replicate B true)).sets LG (List.replicate B false))
      (B * (7 + 8) + 7 * B + 3 + 1 + (18 * B + 3 + 1 + (5 * B + 1 + 1 + (18 * B + 3 + 1 + (5 * B + 1))))) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR'
  obtain ⟨⟨b1, b2, b3⟩, ⟨c1, c2⟩, n1⟩ := hR'
  let st : ℕ → WState ns nr := fun k =>
    (((σ.sets TT (List.replicate k true)).seth TT k).sets LG (List.replicate k false)).seth LG k
  have e1 := Runs.repE (cap := cap) (K := BR) (K2 := C2)
    (body := .seq (WMX.wr TT true) (.seq (WMX.fwd TT) (.seq (WMX.wr LG false) (WMX.fwd LG)))) b1 7 B st
    (by omega) (fun k => rfl) (fun k => rfl)
    (fun k _ v1 v2 => by
      set σa := ((st k).setv BR v1).setv C2 v2 with hσa
      have w1 := WXExec.wr cap TT true σa
      set σb := σa.sets TT (writeTapeBit (σa.st TT) (σa.sh TT) true) with hσb
      have w2 := WXExec.fwd cap TT σb
      set σc := σb.seth TT (σb.sh TT + 1) with hσc
      have w3 := WXExec.wr cap LG false σc
      set σd := σc.sets LG (writeTapeBit (σc.st LG) (σc.sh LG) false) with hσd
      have w4 := WXExec.fwd cap LG σd
      refine (WXExec.seq w1 (WXExec.seq w2 (WXExec.seq w3 w4))).cast cap ?_ (by omega)
      have hk1 : writeTapeBit (List.replicate k true) k true = List.replicate (k + 1) true := by
        have := writeTapeBit_end' (List.replicate k true) true
        rw [List.length_replicate] at this; rw [this, List.replicate_succ']
      have hk2 : writeTapeBit (List.replicate k false) k false = List.replicate (k + 1) false := by
        have := writeTapeBit_end' (List.replicate k false) false
        rw [List.length_replicate] at this; rw [this, List.replicate_succ']
      apply WState.eq
      · funext x; by_cases hx : x = TT
        · subst hx; simp [hσd, hσc, hσb, hσa, st, Function.update_of_ne hTL]
        · by_cases hl : x = LG
          · subst hl; simp [hσd, hσc, hσb, hσa, st, Function.update_of_ne hx]
          · simp [hσd, hσc, hσb, hσa, st, Function.update_of_ne hx, Function.update_of_ne hl]
      · funext x; by_cases hx : x = TT
        · subst hx; simp [hσd, hσc, hσb, hσa, st, Function.update_of_ne hTL, hk1]
        · by_cases hl : x = LG
          · subst hl; simp [hσd, hσc, hσb, hσa, st, Function.update_of_ne hx, Function.update_of_ne (Ne.symm hTL), hk2]
          · simp [hσd, hσc, hσb, hσa, st, Function.update_of_ne hx, Function.update_of_ne hl]
      · rfl
      · rfl)
    (by simp [st, hB]) (by simp [st, hC2])
  have hst0 : st 0 = σ := by
    apply WState.eq
    · funext x; by_cases hx : x = TT
      · subst hx; simp [st, Function.update_of_ne hTL, hTTh]
      · by_cases hl : x = LG
        · subst hl; simp [st, hLGh]
        · simp [st, Function.update_of_ne hx, Function.update_of_ne hl]
    · funext x; by_cases hx : x = TT
      · subst hx; simp [st, Function.update_of_ne hTL, hTT]
      · by_cases hl : x = LG
        · subst hl; simp [st, hLG]
        · simp [st, Function.update_of_ne hx, Function.update_of_ne hl]
    · rfl
    · rfl
  rw [hst0] at e1
  have hBst : (st B).val BR = B := by simp [st, hB]
  have e2 := addR_spec cap (A := BR) (B := CNT) (T := T) b2 b3 n1 (st B) (by simp [st, hT])
    (by simp [st, hCNT, hB]; omega)
  have hc : (st B).val CNT + (st B).val BR = B := by simp [st, hCNT, hB]
  rw [hc] at e2
  have e3 := wrewind_spec (cap := cap) TT CNT B ((st B).setv CNT B) (by simp) (by simp; omega)
  set σ3 := (((st B).setv CNT B).setv CNT 0).seth TT (((st B).setv CNT B).sh TT - B) with hσ3
  have h3T : σ3.val T = 0 := by simp [hσ3, st, Function.update_of_ne (Ne.symm n1), hT]
  have h3C : σ3.val CNT = 0 := by simp [hσ3]
  have h3B : σ3.val BR = B := by simp [hσ3, st, Function.update_of_ne b2, hB]
  have e4 := addR_spec cap (A := BR) (B := CNT) (T := T) b2 b3 n1 σ3 h3T (by rw [h3C, h3B]; omega)
  rw [h3C, h3B, Nat.zero_add] at e4
  have e5 := wrewind_spec (cap := cap) LG CNT B (σ3.setv CNT B) (by simp) (by simp; omega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.wm e3) (WXExec.seq e4 (WXExec.wm e5))))).cast cap ?_
    (by rw [hBst])
  apply WState.eq
  · funext x; by_cases hx : x = TT
    · subst hx; simp [hσ3, st, Function.update_of_ne hTL, hTTh]
    · by_cases hl : x = LG
      · subst hl; simp [hσ3, st, Function.update_of_ne hx, hLGh]
      · simp [hσ3, st, Function.update_of_ne hx, Function.update_of_ne hl]
  · funext x; by_cases hx : x = TT
    · subst hx; simp [hσ3, st, Function.update_of_ne hTL]
    · by_cases hl : x = LG
      · subst hl; simp [hσ3, st, Function.update_of_ne hx]
      · simp [hσ3, st, Function.update_of_ne hx, Function.update_of_ne hl]
  · funext r; by_cases hr : r = CNT
    · subst hr; simp [hσ3, st, hCNT]
    · simp [hσ3, st, Function.update_of_ne hr]
  · simp [hσ3, st]

end NearCubicGates.Close.CheckedPCPP.EncSetup
