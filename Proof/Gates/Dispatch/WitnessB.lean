import Proof.Gates.Dispatch.WitnessA

/-!
# Fragment (W), part B: the variables and the bit gadgets

Variables (all in `WitVar`): `61` the flag `vWF`, `62` the coordinate bitmask `vBM`, `63` the packed coefficient bits
`vPK` (these three are what `print` reads back), scratch `98–120`.
* `rdBits M X`: read `env M` witness bits little-endian into `X`;
* `extractW`: take `env xW` bits off `xRem` (little-endian) into `xV`;
* `widthW`: `xW := ⌈lg(2·xA + 1)⌉`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

def vBM : Fin VV := ⟨62, by decide⟩
def vPK : Fin VV := ⟨63, by decide⟩
def xI : Fin VV := ⟨98, by decide⟩
def xX : Fin VV := ⟨99, by decide⟩
def xP : Fin VV := ⟨100, by decide⟩
def xC : Fin VV := ⟨101, by decide⟩
def xB : Fin VV := ⟨102, by decide⟩
def xT : Fin VV := ⟨103, by decide⟩
def xQ : Fin VV := ⟨104, by decide⟩
def xR : Fin VV := ⟨105, by decide⟩
def xSum : Fin VV := ⟨106, by decide⟩
def xS : Fin VV := ⟨107, by decide⟩
def xRo : Fin VV := ⟨108, by decide⟩
def xNR : Fin VV := ⟨109, by decide⟩
def xM : Fin VV := ⟨110, by decide⟩
def xIc : Fin VV := ⟨111, by decide⟩
def xA : Fin VV := ⟨112, by decide⟩
def xW : Fin VV := ⟨113, by decide⟩
def xV : Fin VV := ⟨114, by decide⟩
def xRem : Fin VV := ⟨115, by decide⟩
def xT2 : Fin VV := ⟨116, by decide⟩
def xLC : Fin VV := ⟨118, by decide⟩
def xT3 : Fin VV := ⟨119, by decide⟩
def xP2 : Fin VV := ⟨120, by decide⟩

variable {C : Ctx}

/-! ## Reading witness bits -/

/-- Read `env M` witness bits, little-endian, into `X`. -/
def rdBits (M X : Fin VV) : St VV :=
  .seq (.op (.zero X)) (.seq (.op (.copy xP v1)) (.seq (.op (.zero xC))
    (.loop (.lt xC M) (.seq (.op (.rdW xB)) (.seq (.ite (.eq xB v1) (.op (.add X xP)) skipS)
      (.seq (.op (.shl xP)) (.op (.inc xC))))))))

theorem bitOf_min (w : List Bool) (q : ℕ) : bitOf w (min q w.length) = (w.getD q false).toNat := by
  unfold bitOf
  by_cases h : q < w.length
  · rw [Nat.min_eq_left h.le]
  · rw [Nat.min_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
      List.getElem?_eq_none (by omega)]

theorem wq_step (w : List Bool) (q : ℕ) :
    (if min q w.length < w.length then min q w.length + 1 else min q w.length) = min (q + 1) w.length := by
  split_ifs with h <;> omega

theorem rdBits_spec (M X : Fin VV) (hMX : (M = pLAM ∧ X = xX) ∨ (M = xLC ∧ X = vPK))
    (a : DS VV) (hc : Cst a) (pos m : ℕ) (hq : a.wq = min pos C.wit.length)
    (hm : a.env M = m) (hW : m + 1 < C.Wd) :
    Hs C (rdBits M X) a (10 * m + 10) (fun b => b.env X = bitsValue ((C.wit.drop pos).take m) ∧
      b.wq = min (pos + m) C.wit.length ∧ b.cp = a.cp ∧ b.out = a.out ∧ Cst b ∧ Fr a b [X, xP, xC, xB, vJ]) := by
  have hv1 := hc.one
  have hpw : ∀ j, j ≤ m → 2 ^ (j + 1) ≤ 2 ^ C.Wd := fun j hj => Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF : M ∉ [X, xP, xC, xB, vJ] ∧ vZ ∉ [X, xP, xC, xB, vJ] ∧ v1 ∉ [X, xP, xC, xB, vJ] ∧
      v2 ∉ [X, xP, xC, xB, vJ] ∧ vPOS ∉ [X, xP, xC, xB, vJ] ∧ X ∈ [X, xP, xC, xB, vJ] ∧ xC ≠ M ∧
      xP ≠ X ∧ xC ≠ X ∧ xB ≠ X ∧ vJ ≠ X ∧ v1 ≠ X ∧ X ≠ xP ∧ M ≠ xB ∧ X ≠ xC ∧ X ≠ xB ∧ X ≠ vJ ∧ X ≠ v1 := by
    rcases hMX with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨hFM, hFZ, hF1, hF2, hFP, hFX, hCM, hPX, hCX, hBX, hJX, h1X, hXP, hMB, hXC, hXB, hXJ, hX1⟩ := hF
  · let I : ℕ → DS VV → Prop := fun j b => b.env X = bitsValue ((C.wit.drop pos).take j) ∧ b.env xP = 2 ^ j ∧
      b.env xC = j ∧ b.wq = min (pos + j) C.wit.length ∧ b.cp = a.cp ∧ b.out = a.out ∧ Fr a b [X, xP, xC, xB, vJ]
    have hM' : ∀ b, Fr a b [X, xP, xC, xB, vJ] → b.env M = m := fun b hb => by
      rw [hb M hFM, hm]
    have l := Hs.loopN (C := C) (c := .lt xC M) (s := .seq (.op (.rdW xB))
        (.seq (.ite (.eq xB v1) (.op (.add X xP)) skipS) (.seq (.op (.shl xP)) (.op (.inc xC)))))
        hCM I m 8 ?_ ?_
    · refine Hs.mono (Hs.seq (hs_zero C X a) (fun b hb => Hs.seq (hs_copy C xP v1 b (by decide)) (fun d hd =>
        Hs.seq (hs_zero C xC d) (fun e he => l e ?_)))) (by omega) ?_
      · subst hb hd he
        refine ⟨by vsimp [Function.update_apply, hPX, hCX, hBX, hJX, h1X, hXP, hXC, hXB, hXJ, hX1, hCX, hPX, bitsValue], by vsimp [Function.update_apply, hPX, hCX, hBX, hJX, h1X, hXP, hXC, hXB, hXJ, hX1, hv1, hCX, hPX],
          by vsimp [], by simp [hq], rfl, rfl, ?_⟩
        exact Fr.trans (Fr.set a _ hFX) (Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp)))
      · rintro b ⟨b1, -, -, b4, b5, b6, b7⟩
        exact ⟨b1, b4, b5, b6, Cst.of_fr hc b7 ⟨hFZ, hF1, hF2⟩ (by rw [b7 vPOS hFP, hc.pos, b5]), b7⟩
    · intro j hj b ⟨b1, b2, b3, b4, b5, b6, b7⟩
      have bv1 : b.env v1 = 1 := by rw [b7 v1 hF1]; exact hv1
      refine ⟨by simp [Cnd.eval, b3, hM' b b7, hj], ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 6) (hs_rdW C xB b) (fun d hd => ?_)
      subst hd
      set bit := (C.wit.getD (pos + j) false).toNat with hbit
      have hbitv : bitOf C.wit b.wq = bit := by rw [b4, bitOf_min]
      have hX2 : bitsValue ((C.wit.drop pos).take j) < 2 ^ j :=
        lt_of_lt_of_le (bitsValue_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))
      have hwq : (if b.wq < C.wit.length then b.wq + 1 else b.wq) = min (pos + (j + 1)) C.wit.length := by
        rw [b4, wq_step]; congr 1
      have bt : bitsValue ((C.wit.drop pos).take (j + 1)) = bitsValue ((C.wit.drop pos).take j) + bit * 2 ^ j := by
        rw [bitsValue_take_succ, getD_drop]
      have step2 : Hs C (.ite (.eq xB v1) (.op (.add X xP)) skipS)
          { b.set xB (bitOf C.wit b.wq) with wq := if b.wq < C.wit.length then b.wq + 1 else b.wq } 2
          (fun e => e.env X = bitsValue ((C.wit.drop pos).take (j + 1)) ∧ e.env xP = 2 ^ j ∧ e.env xC = j ∧
            e.wq = min (pos + (j + 1)) C.wit.length ∧ e.cp = a.cp ∧ e.out = a.out ∧ Fr a e [X, xP, xC, xB, vJ]) := by
        have hfr0 : Fr a ({ b.set xB (bitOf C.wit b.wq) with wq := if b.wq < C.wit.length then b.wq + 1 else b.wq })
            [X, xP, xC, xB, vJ] := Fr.trans b7 (Fr.set b _ (by simp))
        refine Hs.ite (c := .eq xB v1) (show xB ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
        · have hb1 : bit = 1 := by
            simp only [Cnd.eval, decide_eq_true_eq] at he; vsimp [bv1] at he; rw [← hbitv]; exact he
          refine Hs.mono (hs_add C X xP _ hXP ?_) le_rfl ?_
          · vsimp [Function.update_apply, hPX, hCX, hBX, hJX, h1X, hXP, hXC, hXB, hXJ, hX1, hBX, b1, b2]
            have := hpw j hj.le; rw [pow_succ] at this; omega
          · rintro e rfl
            refine ⟨?_, by vsimp [Function.update_apply, hPX, hCX, hBX, hJX, h1X, hXP, hXC, hXB, hXJ, hX1, hPX, b2], by vsimp [Function.update_apply, hPX, hCX, hBX, hJX, h1X, hXP, hXC, hXB, hXJ, hX1, hCX, b3], by simp [hwq],
              b5, b6, Fr.trans hfr0 (Fr.set _ _ hFX)⟩
            vsimp [Function.update_apply, hPX, hCX, hBX, hJX, h1X, hXP, hXC, hXB, hXJ, hX1, hBX, b1, b2, bt, hb1]
        · have hb0 : bit = 0 := by
            simp only [Cnd.eval, decide_eq_false_iff_not] at he; vsimp [bv1] at he
            have := bitOf_le C.wit b.wq; rw [← hbitv]; omega
          refine Hs.mono (skip_spec _) (by omega) ?_
          rintro e rfl
          refine ⟨?_, by vsimp [b2], by vsimp [b3], by simp [hwq], b5, b6, Fr.trans hfr0 (Fr.set _ _ (by simp))⟩
          rw [bt, hb0]
          vsimp [Function.update_apply, hPX, hCX, hBX, hJX, h1X, hXP, hXC, hXB, hXJ, hX1, hJX.symm, hBX.symm, b1]
      refine Hs.seq (t2 := 3) step2 (fun e ⟨e1, e2, e3, e4, e5, e6, e7⟩ => ?_)
      refine Hs.seq (t2 := 1) (hs_shl C xP e (by
        rw [e2]; have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show j + 2 ≤ C.Wd by omega)
        rw [pow_succ, pow_succ] at h; have := Nat.one_le_two_pow (n := j); nlinarith)) (fun f hf => ?_)
      subst hf
      refine Hs.mono (hs_inc C xC _ (by vsimp [e3]; have := Nat.lt_two_pow_self (n := C.Wd); omega)) le_rfl ?_
      rintro g rfl
      refine ⟨by vsimp [Function.update_apply, hPX, hCX, hBX, hJX, h1X, hXP, hXC, hXB, hXJ, hX1, hCX.symm, hPX.symm, e1], by vsimp [e2, pow_succ]; ring, by vsimp [e3],
        e4, e5, e6, ?_⟩
      exact Fr.trans e7 (Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp)))
    · intro b ⟨_, _, b3, _, _, _, b7⟩
      simp [Cnd.eval, b3, hM' b b7]

/-! ## Taking bits off a packed number -/

/-- Move `env xW` low bits of `xRem` (little-endian) into `xV`. -/
def extractW : St VV :=
  .seq (.op (.zero xV)) (.seq (.op (.copy xP v1)) (.seq (.op (.zero xC))
    (.loop (.lt xC xW) (.seq (.op (.dm xRem v2 xQ xR)) (.seq (.ite (.eq xR v1) (.op (.add xV xP)) skipS)
      (.seq (.op (.copy xRem xQ)) (.seq (.op (.shl xP)) (.op (.inc xC)))))))))

def extractT : List (Fin VV) := [xV, xP, xC, xQ, xR, xRem, vJ]

theorem extractW_spec (a : DS VV) (hc : Cst a) (l : List Bool) (w : ℕ) (hrem : a.env xRem = bitsValue l)
    (hw : a.env xW = w) (hW : w + 2 ≤ C.Wd) :
    Hs C extractW a (12 * w + 10) (fun b => b.env xV = bitsValue (l.take w) ∧ b.env xRem = bitsValue (l.drop w) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b extractT) := by
  have hv1 := hc.one
  have hv2 := hc.two
  let I : ℕ → DS VV → Prop := fun j b => b.env xV = bitsValue (l.take j) ∧ b.env xRem = bitsValue (l.drop j) ∧
    b.env xP = 2 ^ j ∧ b.env xC = j ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b extractT
  have hW' : ∀ b, Fr a b extractT → b.env xW = w := fun b hb => by rw [hb xW (by decide), hw]
  have l1 := Hs.loopN (C := C) (c := .lt xC xW) (s := .seq (.op (.dm xRem v2 xQ xR))
      (.seq (.ite (.eq xR v1) (.op (.add xV xP)) skipS) (.seq (.op (.copy xRem xQ)) (.seq (.op (.shl xP))
        (.op (.inc xC)))))) (show xC ≠ xW by decide) I w 10 ?_ ?_
  · refine Hs.mono (Hs.seq (hs_zero C xV a) (fun b hb => Hs.seq (hs_copy C xP v1 b (by decide)) (fun d hd =>
      Hs.seq (hs_zero C xC d) (fun e he => l1 e ?_)))) (by omega) ?_
    · subst hb hd he
      refine ⟨by vsimp [bitsValue], by vsimp [hrem], by vsimp [hv1], by vsimp [], rfl, rfl, rfl, ?_⟩
      exact Fr.trans (Fr.set a _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
    · rintro b ⟨b1, b2, -, -, b5, b6, b7, b8⟩
      exact ⟨b1, b2, b5, b6, b7, Cst.of_fr hc b8 (by decide) (by rw [b8 vPOS (by decide), hc.pos, b5]), b8⟩
  · intro j hj b ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
    have bv1 : b.env v1 = 1 := by rw [b8 v1 (by decide)]; exact hv1
    have bv2 : b.env v2 = 2 := by rw [b8 v2 (by decide)]; exact hv2
    refine ⟨by simp [Cnd.eval, b4, hW' b b8, hj], ?_⟩
    have hpw : 2 ^ (j + 2) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 4 ≤ 2 ^ C.Wd := le_trans (by rw [pow_succ, pow_succ]; have := Nat.one_le_two_pow (n := j); omega) hpw
    obtain ⟨bit, hbit⟩ : ∃ bt, bt = (l.getD j false).toNat := ⟨_, rfl⟩
    have hbit1 : bit ≤ 1 := by rw [hbit]; cases l.getD j false <;> simp
    have hsplit := bitsValue_drop_succ l j
    rw [← hbit] at hsplit
    refine Hs.seq (t1 := 1) (t2 := 8) (hs_dm C xRem v2 xQ xR b (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [bv2]; norm_num) (by rw [bv2]; omega)) (fun d hd => ?_)
    subst hd
    have dR : ((b.set xQ (b.env xRem / b.env v2)).set xR (b.env xRem % b.env v2)).env xR = bit := by
      vsimp [b2, bv2, hsplit]; omega
    have dQ : ((b.set xQ (b.env xRem / b.env v2)).set xR (b.env xRem % b.env v2)).env xQ =
        bitsValue (l.drop (j + 1)) := by
      vsimp [b2, bv2, hsplit]; omega
    have hlt : bitsValue (l.take j) < 2 ^ j :=
      lt_of_lt_of_le (bitsValue_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))
    have hts := bitsValue_take_succ l j
    rw [← hbit] at hts
    have dv1 : ((b.set xQ (b.env xRem / b.env v2)).set xR (b.env xRem % b.env v2)).env v1 = 1 := by vsimp [bv1]
    refine Hs.seq (t1 := 2) (t2 := 5) (Hs.ite (c := .eq xR v1) (show xR ≠ v1 by decide)
      (R := fun e => e.env xV = bitsValue (l.take (j + 1)) ∧ e.env xQ = bitsValue (l.drop (j + 1)) ∧
        e.env xP = 2 ^ j ∧ e.env xC = j ∧ e.cp = a.cp ∧ e.wq = a.wq ∧ e.out = a.out ∧ Fr a e extractT)
      (fun he => ?_) (fun he => ?_)) (fun e ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ => ?_)
    · have hb : bit = 1 := by
        have h := he; simp only [Cnd.eval, decide_eq_true_eq] at h; rw [dR, dv1] at h; exact h
      refine Hs.mono (hs_add C xV xP _ (by decide) ?_) (by omega) ?_
      · vsimp [b1, b3]; have := hpw; rw [pow_succ, pow_succ] at this; omega
      · rintro e rfl
        refine ⟨by vsimp [b1, b3, hts, hb], by vsimp [dQ]; exact dQ, by vsimp [b3], by vsimp [b4], b5, b6, b7, ?_⟩
        exact Fr.trans b8 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
    · have hb : bit = 0 := by
        have h := he; simp only [Cnd.eval, decide_eq_false_iff_not] at h; rw [dR, dv1] at h; omega
      refine Hs.mono (skip_spec _) (by omega) ?_
      rintro e rfl
      refine ⟨by vsimp [b1, hts, hb], by vsimp []; exact dQ, by vsimp [b3], by vsimp [b4], b5, b6, b7, ?_⟩
      exact Fr.trans b8 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
    · refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C xRem xQ e (by decide)) (fun f hf => ?_)
      subst hf
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_shl C xP _ (by
        vsimp [e3]; rw [pow_succ, pow_succ] at hpw; have := Nat.one_le_two_pow (n := j); nlinarith)) (fun g hg => ?_)
      subst hg
      refine Hs.mono (hs_inc C xC _ (by vsimp [e4]; have := Nat.lt_two_pow_self (n := C.Wd); omega)) le_rfl ?_
      rintro h rfl
      refine ⟨by vsimp [e1], by vsimp [e2], by vsimp [e3, pow_succ]; ring, by vsimp [e4], e5, e6, e7, ?_⟩
      exact Fr.trans e8 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
  · intro b ⟨_, _, _, b4, _, _, _, b8⟩
    simp [Cnd.eval, b4, hW' b b8]

/-! ## The field width `⌈lg(2|a|+1)⌉` -/

def widthW : St VV :=
  .seq (.op (.copy xT2 xA)) (.seq (.op (.add xT2 xA)) (.seq (.op (.inc xT2)) (.seq (.op (.zero xW))
    (.seq (.op (.copy xP v1)) (.loop (.lt xP xT2) (.seq (.op (.shl xP)) (.op (.inc xW))))))))

def widthT : List (Fin VV) := [xT2, xW, xP, vJ]

theorem widthW_spec (a : DS VV) (hc : Cst a) (A : ℕ) (hA : a.env xA = A) (hW : coefWidth (A : ℤ) + 2 ≤ C.Wd)
    (hAW : 2 * A + 2 < 2 ^ C.Wd) :
    Hs C widthW a (5 * coefWidth (A : ℤ) + 12) (fun b => b.env xW = coefWidth (A : ℤ) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ Fr a b widthT) := by
  have hv1 := hc.one
  set m := coefWidth (A : ℤ) with hm
  have hmc : m = Nat.clog 2 (2 * A + 1) := by simp [hm, coefWidth]
  let I : ℕ → DS VV → Prop := fun j b => b.env xW = j ∧ b.env xP = 2 ^ j ∧ b.env xT2 = 2 * A + 1 ∧ b.cp = a.cp ∧
    b.wq = a.wq ∧ b.out = a.out ∧ Fr a b widthT
  have l1 := Hs.loopN (C := C) (c := .lt xP xT2) (s := .seq (.op (.shl xP)) (.op (.inc xW))) (show xP ≠ xT2 by decide) I m 3 ?_ ?_
  · refine Hs.mono (Hs.seq (hs_copy C xT2 xA a (by decide)) (fun b hb => Hs.seq (hs_add C xT2 xA b (by decide)
      (by subst hb; vsimp [hA]; omega)) (fun d hd => Hs.seq (hs_inc C xT2 d (by subst hb hd; vsimp [hA]; omega))
      (fun e he => Hs.seq (hs_zero C xW e) (fun f hf => Hs.seq (hs_copy C xP v1 f (by decide))
        (fun g hg => l1 g ?_)))))) (by omega) ?_
    · subst hb hd he hf hg
      refine ⟨by vsimp [], by vsimp [hv1], by vsimp [hA]; ring, rfl, rfl, rfl, ?_⟩
      exact Fr.trans (Fr.set a _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))))
    · rintro b ⟨b1, -, -, b4, b5, b6, b7⟩
      exact ⟨b1, b4, b5, b6, Cst.of_fr hc b7 (by decide) (by rw [b7 vPOS (by decide), hc.pos, b4]), b7⟩
  · intro j hj b ⟨b1, b2, b3, b4, b5, b6, b7⟩
    have hlt : 2 ^ j < 2 * A + 1 := (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by rw [← hmc]; exact hj)
    refine ⟨by simp [Cnd.eval, b2, b3, hlt], ?_⟩
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_shl C xP b (by
      rw [b2]; have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show j + 2 ≤ C.Wd by omega)
      rw [pow_succ, pow_succ] at h; have := Nat.one_le_two_pow (n := j); nlinarith)) (fun d hd => ?_)
    subst hd
    refine Hs.mono (hs_inc C xW _ (by vsimp [b1]; have := Nat.lt_two_pow_self (n := C.Wd); omega)) le_rfl ?_
    rintro e rfl
    exact ⟨by vsimp [b1], by vsimp [b2, pow_succ]; ring, by vsimp [b3], b4, b5, b6,
      Fr.trans b7 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩
  · intro b ⟨_, b2, b3, _, _, _, _⟩
    have : ¬ 2 ^ m < 2 * A + 1 := fun h => by
      have := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr h; rw [← hmc] at this; omega
    simp [Cnd.eval, b2, b3, this]

/-! ## Positioning the call-word cursor -/

def seekW (co : Fin VV) : St VV := .seq (.op .rstC) (.seq (.op (.zero vPOS)) (.loop (.lt vPOS co) rdc))

theorem seekW_spec (co : Fin VV) (hco : co ∉ [t0, vPOS, vJ]) (hcov : co ≠ vPOS) (a : DS VV) (hc : Cst a) (q : ℕ)
    (hq : a.env co = q) (hql : q ≤ C.cw.length) (hW : C.cw.length < 2 ^ C.Wd) :
    Hs C (seekW co) a (5 * q + 6) (fun b => b.cp = q ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b [t0, vPOS, vJ]) := by
  let I : ℕ → DS VV → Prop := fun j b => b.cp = j ∧ b.env vPOS = j ∧ b.wq = a.wq ∧ b.out = a.out ∧
    Fr a b [t0, vPOS, vJ]
  have hq' : ∀ b, Fr a b [t0, vPOS, vJ] → b.env co = q := fun b hb => by rw [hb co hco, hq]
  have l1 := Hs.loopN (C := C) (c := .lt vPOS co) (s := rdc) (Ne.symm hcov) I q 3 ?_ ?_
  · refine Hs.mono (Hs.seq (hs_rstC C a) (fun b hb => Hs.seq (hs_zero C vPOS b) (fun d hd => l1 d ?_))) (by omega) ?_
    · subst hb hd
      exact ⟨rfl, by vsimp [], rfl, rfl, Fr.set _ _ (by decide)⟩
    · rintro b ⟨b1, b2, b3, b4, b5⟩
      exact ⟨b1, b3, b4, Cst.of_fr hc b5 (by decide) (by rw [b2, b1]), b5⟩
  · intro j hj b ⟨b1, b2, b3, b4, b5⟩
    refine ⟨by simp [Cnd.eval, b2, hq' b b5, hj], ?_⟩
    refine Hs.mono (rdc_spec b (by rw [b2, b1]) (by rw [b1]; omega) hW) le_rfl ?_
    rintro d ⟨d1, d2, d3, d4, d5, d6⟩
    exact ⟨by rw [d3, b1], by rw [d2, b1], by rw [d4, b3], by rw [d5, b4], Fr.trans b5 (Fr.weaken d6 (by decide))⟩
  · intro b ⟨_, b2, _, _, b5⟩
    simp [Cnd.eval, b2, hq' b b5]

end NearCubicGates.Close.Dispatch
