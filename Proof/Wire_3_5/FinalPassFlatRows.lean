import Proof.Wire_3_5.FinalPassFlatEmit
import Proof.Wire_3_5.FinalPassFiltTabZero

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Flat
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Filt

variable (cap : ℕ)

theorem w_a (x : TSt) (n : ℕ) : x.w.setv gA n = { x with a := n }.w := by tst_eq

/-! ## One row bit -/

/-- Emit `[true, !NS]` and clear `NS`. -/
def rowOut : TProg :=
  .seq (emitC qO gOP true) (.seq (.ifr gNS (emitC qO gOP false) (emitC qO gOP true)) (WM.clear gNS))

theorem rowOut_spec (x : TSt) (nb : Bool) (hns : x.ns = nb.toNat) (hO : x.ow.length + 2 < cap) :
    WExec cap rowOut x.w { x with ow := x.ow ++ [true, !nb], ns := 0 }.w 22 := by
  have s1 := emitC_spec cap qO gOP true x.w (by show x.ow.length = x.ow.length; rfl) (by show x.ow.length < cap; omega)
  rw [w_o_emit] at s1
  obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { x with ow := x.ow ++ [true] } := ⟨_, rfl⟩
  rw [← hx1] at s1
  have hO1 : x1.w.sh qO = (x1.w.st qO).length := by rw [hx1]; rfl
  have hc1 : x1.w.val gOP < cap := by rw [hx1]; show (x.ow ++ [true]).length < cap; simp; omega
  obtain ⟨x2, hx2⟩ : ∃ y : TSt, y = { x1 with ow := x1.ow ++ [!nb] } := ⟨_, rfl⟩
  have s2 : WExec cap (.ifr gNS (emitC qO gOP false) (emitC qO gOP true)) x1.w x2.w 8 := by
    have hns1 : x1.w.val gNS = nb.toNat := by rw [hx1]; exact hns
    cases nb
    · have h := emitC_spec cap qO gOP true x1.w hO1 hc1
      rw [w_o_emit] at h
      exact WExec.ifrF hns1 (by rw [hx2]; exact h)
    · have h := emitC_spec cap qO gOP false x1.w hO1 hc1
      rw [w_o_emit] at h
      exact WExec.ifrT (by rw [hns1]; decide) (by rw [hx2]; exact h)
  have hnb1 := Bool.toNat_le nb
  have s3 := wclear_spec cap gNS nb.toNat x2.w (by rw [hx2, hx1]; exact hns)
    (by rw [hx2, hx1]; show x.ns ≤ cap; rw [hns]; omega)
  rw [w_ns] at s3
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by omega)
  rw [hx2, hx1]
  simp

/-! ## One label -/

/-- A row bit: label `k` lies in level `a` (no prefix hash bit is one). -/
def rowBit (epb bwb : List Bool) (lb a k : ℕ) : Bool := !mism (binary lb k) epb bwb lb 0 a

/-- One label: the prefix test, the bit, the next label. -/
def rowStep : TProg := .seq selT (.seq rowOut kInc)

def rowStepCost (lb a : ℕ) : ℕ := selTCost lb a + 1 + (22 + 1 + (lb * 41 + 3 * 1 + 12))

theorem rowStep_spec (x : TSt) (k : ℕ) (epb bwb : List Bool) (hlb : x.lb = epb.length / 2 + 1)
    (hepl : 1 ≤ epb.length ∧ epb.length % 2 = 1) (hbwl : bwb.length = x.lb)
    (hk : x.kw = frame (binary x.lb k)) (hep : x.ep = frameP epb ++ [false]) (hbw : x.bw = frameP bwb ++ [false])
    (ha : x.a ≤ x.lb) (hs : x.s = 0) (hj : x.j = 0) (heph : x.eph = 0) (hbwh : x.bwh = 0) (hf : x.f = 0)
    (hns : x.ns = 0) (hcap : 4 * x.lb + 4 ≤ cap) (hO : x.ow.length + 2 < cap) :
    WExec cap rowStep x.w
      { x with kw := frame (binary x.lb (k + 1)), ow := x.ow ++ [true, rowBit epb bwb x.lb x.a k] }.w
      (rowStepCost x.lb x.a) := by
  have s1 := selT_spec cap x (binary x.lb k) epb bwb hlb (by simp only [binary_length]; omega) hepl (by omega)
    (by rw [hk, frame_bin]) hep hbw ha hs hj heph hbwh hf hns hcap
  obtain ⟨y1, hy1⟩ : ∃ y : TSt, y = { x with ns := (mism (binary x.lb k) epb bwb x.lb 0 x.a).toNat } := ⟨_, rfl⟩
  rw [← hy1] at s1
  have s2 := rowOut_spec cap y1 (mism (binary x.lb k) epb bwb x.lb 0 x.a) (by rw [hy1])
    (by rw [hy1]; exact hO)
  obtain ⟨y2, hy2⟩ : ∃ y : TSt, y = { y1 with ow := y1.ow ++ [true, !mism (binary x.lb k) epb bwb x.lb 0 x.a],
                                                ns := 0 } := ⟨_, rfl⟩
  rw [← hy2] at s2
  have s3 := kInc_spec cap y2 k bwb (by rw [hy2, hy1]; exact hk) (by rw [hy2, hy1, frame_eq_frameP]; exact hbw)
    (by rw [hy2, hy1]; exact hbwl) (by rw [hy2, hy1]; exact hf) (by rw [hy2, hy1]; exact hbwh)
    (by rw [hy2, hy1]; show 2 * x.lb + 2 ≤ cap; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ ?_
  · rw [hy2, hy1]
    cases x
    simp only at hns ⊢
    subst hns
    rfl
  · rw [hy2, hy1]; dsimp only; unfold rowStepCost; omega

/-! ## One level -/

/-- The row bits of labels `k, …, k+n−1`. -/
def rowBits (epb bwb : List Bool) (lb a k n : ℕ) : List Bool := (List.range' k n).map (rowBit epb bwb lb a)

/-- The labels, counted down in `CK`. -/
def rowLoop : TProg := .whr gCK (.seq rowStep (.dec gCK))

theorem rowLoop_spec (epb bwb : List Bool) (hepl : 1 ≤ epb.length ∧ epb.length % 2 = 1) :
    ∀ (n k : ℕ) (x : TSt), x.lb = epb.length / 2 + 1 → bwb.length = x.lb → x.kw = frame (binary x.lb k) →
      x.ep = frameP epb ++ [false] → x.bw = frameP bwb ++ [false] → x.a ≤ x.lb → x.s = 0 → x.j = 0 → x.eph = 0 →
      x.bwh = 0 → x.f = 0 → x.ns = 0 → x.ck = n → 4 * x.lb + 4 ≤ cap → x.ow.length + 2 * n + 2 < cap → n ≤ cap →
      WExec cap rowLoop x.w
        { x with kw := frame (binary x.lb (k + n)), ow := x.ow ++ frameP (rowBits epb bwb x.lb x.a k n), ck := 0 }.w
        (n * (rowStepCost x.lb x.a + 4) + 1)
  | 0, k, x, _, _, hk, _, _, _, _, _, _, _, _, _, hck, _, _, _ => by
    refine WExec.cast cap (WExec.whrF hck) ?_ (by omega)
    have e : ({ x with kw := frame (binary x.lb (k + 0)), ow := x.ow ++ frameP (rowBits epb bwb x.lb x.a k 0), ck := 0 } : TSt) = x := by
      cases x
      simp only at hck hk ⊢
      subst hck hk
      simp [rowBits, frameP]
    rw [e]
  | n + 1, k, x, hlb, hbwl, hk, hep, hbw, ha, hs, hj, heph, hbwh, hf, hns, hck, hcap, hO, hn => by
    have s1 := rowStep_spec cap x k epb bwb hlb hepl hbwl hk hep hbw ha hs hj heph hbwh hf hns hcap (by omega)
    obtain ⟨y1, hy1⟩ : ∃ y : TSt,
        y = { x with kw := frame (binary x.lb (k + 1)), ow := x.ow ++ [true, rowBit epb bwb x.lb x.a k] } := ⟨_, rfl⟩
    rw [← hy1] at s1
    have s2 := WExec.dec (cap := cap) gCK y1.w (by rw [hy1]; show x.ck ≤ cap; omega)
    rw [w_ck] at s2
    obtain ⟨y2, hy2⟩ : ∃ y : TSt, y = { y1 with ck := y1.w.val gCK - 1 } := ⟨_, rfl⟩
    rw [← hy2] at s2
    have hl2 : y2.ow.length = x.ow.length + 2 := by rw [hy2, hy1]; simp
    have ih := rowLoop_spec epb bwb hepl n (k + 1) y2
      (by rw [hy2, hy1]; exact hlb) (by rw [hy2, hy1]; exact hbwl) (by rw [hy2, hy1])
      (by rw [hy2, hy1]; exact hep) (by rw [hy2, hy1]; exact hbw) (by rw [hy2, hy1]; exact ha)
      (by rw [hy2, hy1]; exact hs) (by rw [hy2, hy1]; exact hj) (by rw [hy2, hy1]; exact heph)
      (by rw [hy2, hy1]; exact hbwh) (by rw [hy2, hy1]; exact hf) (by rw [hy2, hy1]; exact hns)
      (by rw [hy2, hy1]; show x.ck - 1 = n; omega) (by rw [hy2, hy1]; exact hcap) (by omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by show x.ck ≠ 0; omega) (WExec.seq s1 s2) ih) ?_ ?_
    · rw [hy2, hy1]
      have hr : rowBits epb bwb x.lb x.a k (n + 1) = rowBit epb bwb x.lb x.a k :: rowBits epb bwb x.lb x.a (k + 1) n := by
        simp [rowBits, List.range'_succ]
      rw [hr, show k + 1 + n = k + (n + 1) by omega]
      congr 1
      cases x
      simp_all [frameP]
    · have e : y2.lb = x.lb ∧ y2.a = x.a := by rw [hy2, hy1]; exact ⟨rfl, rfl⟩
      rw [e.1, e.2]; nlinarith

/-- The row of level `a`. -/
def rowOf (epb bwb : List Bool) (lb a L : ℕ) : List Bool := rowBits epb bwb lb a 0 L

/-- One level: `CK := L`, the labels, the row closed, the label word zeroed. -/
def levelBody : TProg :=
  .seq (Hash4.wcopyR gL gCK gT) (.seq rowLoop (.seq (emitC qO gOP false) (mapPass zeroOut keepS qK qBW gF gR)))

def levelCost (lb a L : ℕ) : ℕ :=
  18 * L + 3 + 1 + (L * (rowStepCost lb a + 4) + 1 + 1 + (7 + 1 + (lb * 41 + 3)))

theorem levelCost_mono (lb a b L : ℕ) (h : a ≤ b) : levelCost lb a L ≤ levelCost lb b L := by
  unfold levelCost rowStepCost selTCost
  have h1 : a * (selStepCost lb + 4) ≤ b * (selStepCost lb + 4) := Nat.mul_le_mul_right _ h
  have h2 : L * (18 * lb + 18 * a + a * (selStepCost lb + 4) + 3 * lb + 5 * (2 * a) + 16 + 1 +
      (22 + 1 + (lb * 41 + 3 * 1 + 12)) + 4) ≤ L * (18 * lb + 18 * b + b * (selStepCost lb + 4) + 3 * lb +
      5 * (2 * b) + 16 + 1 + (22 + 1 + (lb * 41 + 3 * 1 + 12)) + 4) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem levelBody_spec (x : TSt) (epb bwb : List Bool) (hepl : 1 ≤ epb.length ∧ epb.length % 2 = 1)
    (hlb : x.lb = epb.length / 2 + 1) (hbwl : bwb.length = x.lb) (hk : x.kw = frame (binary x.lb 0))
    (hep : x.ep = frameP epb ++ [false]) (hbw : x.bw = frameP bwb ++ [false]) (ha : x.a ≤ x.lb) (hs : x.s = 0)
    (hj : x.j = 0) (heph : x.eph = 0) (hbwh : x.bwh = 0) (hf : x.f = 0) (hns : x.ns = 0) (hck : x.ck = 0)
    (hcap : 4 * x.lb + 4 ≤ cap) (hO : x.ow.length + 2 * x.L + 4 < cap) :
    WExec cap levelBody x.w { x with ow := x.ow ++ frameP (rowOf epb bwb x.lb x.a x.L) ++ [false] }.w
      (levelCost x.lb x.a x.L) := by
  have s1 := Hash4.wcopyR_spec cap gL gCK gT (by decide) (by decide) (by decide) x.w (by exact hck) rfl
    (by show x.L ≤ cap; omega)
  rw [w_ck] at s1
  obtain ⟨y1, hy1⟩ : ∃ y : TSt, y = { x with ck := x.L } := ⟨_, rfl⟩
  have e1 : ({ x with ck := x.w.val gL } : TSt) = y1 := by rw [hy1]; rfl
  rw [e1] at s1
  have s2 := rowLoop_spec cap epb bwb hepl x.L 0 y1 (by rw [hy1]; exact hlb) (by rw [hy1]; exact hbwl)
    (by rw [hy1]; exact hk) (by rw [hy1]; exact hep) (by rw [hy1]; exact hbw) (by rw [hy1]; exact ha)
    (by rw [hy1]; exact hs) (by rw [hy1]; exact hj) (by rw [hy1]; exact heph) (by rw [hy1]; exact hbwh)
    (by rw [hy1]; exact hf) (by rw [hy1]; exact hns) (by rw [hy1]) (by rw [hy1]; exact hcap)
    (by rw [hy1]; show x.ow.length + 2 * x.L + 2 < cap; omega) (by omega)
  obtain ⟨y2, hy2⟩ : ∃ y : TSt, y = { x with kw := frame (binary x.lb x.L), ow := x.ow ++ frameP (rowOf epb bwb x.lb x.a x.L), ck := 0 } :=
    ⟨_, rfl⟩
  have e2 : ({ y1 with kw := frame (binary y1.lb (0 + x.L)), ow := y1.ow ++ frameP (rowBits epb bwb y1.lb y1.a 0 x.L), ck := 0 } : TSt) = y2 := by
    rw [hy2, hy1]; simp only [Nat.zero_add]; rfl
  rw [e2] at s2
  have hl2 : y2.ow.length = x.ow.length + 2 * x.L := by
    rw [hy2]; simp [rowOf, rowBits, frameP_length]
  have s3 := emitC_spec cap qO gOP false y2.w rfl (by show y2.ow.length < cap; omega)
  rw [w_o_emit] at s3
  obtain ⟨y3, hy3⟩ : ∃ y : TSt, y = { y2 with ow := y2.ow ++ [false] } := ⟨_, rfl⟩
  rw [← hy3] at s3
  have s4 := zeroT_spec cap qK qBW (by decide) y3 x.lb (binary x.lb x.L) bwb [false]
    (by rw [hy3, hy2]; show frame (binary x.lb x.L) = _; rw [frame_bin])
    rfl (by rw [hy3, hy2]; exact hbw) (by rw [hy3, hy2]; exact hbwh) (by simp [binary_length, hbwl])
    (by simp [binary_length]) (by rw [hy3, hy2]; exact hf) (by omega)
  rw [w_kw, frame_zero] at s4
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · rw [hy3, hy2]
    cases x
    simp only at hk hck ⊢
    subst hk hck
    simp
  · have e : y1.lb = x.lb ∧ y1.a = x.a := by rw [hy1]; exact ⟨rfl, rfl⟩
    rw [e.1, e.2]
    show 18 * x.L + 3 + 1 + (x.L * (rowStepCost x.lb x.a + 4) + 1 + 1 + (7 + 1 + (x.lb * 41 + 3))) ≤
      levelCost x.lb x.a x.L
    unfold levelCost; omega

/-! ## All levels -/

/-- The rows of levels `n−1, …, 0`, each framed and closed by `false`. -/
def levelRows (epb bwb : List Bool) (lb L n : ℕ) : List Bool :=
  (List.range n).reverse.flatMap fun j => frameP (rowOf epb bwb lb j L) ++ [false]

theorem levelRows_succ (epb bwb : List Bool) (lb L n : ℕ) :
    levelRows epb bwb lb L (n + 1) = frameP (rowOf epb bwb lb n L) ++ [false] ++ levelRows epb bwb lb L n := by
  simp [levelRows, List.range_succ]

theorem levelRows_length (epb bwb : List Bool) (lb L n : ℕ) : (levelRows epb bwb lb L n).length = n * (2 * L + 1) := by
  induction n with
  | zero => simp [levelRows]
  | succ n ih =>
    rw [levelRows_succ, List.length_append, List.length_append, ih]
    simp [rowOf, rowBits, frameP_length]; ring

/-- The levels, counted down in `A`. -/
def levelLoop : TProg := .whr gA (.seq (.dec gA) levelBody)

theorem levelLoop_spec (epb bwb : List Bool) (hepl : 1 ≤ epb.length ∧ epb.length % 2 = 1) :
    ∀ (n : ℕ) (x : TSt), x.lb = epb.length / 2 + 1 → bwb.length = x.lb → x.kw = frame (binary x.lb 0) →
      x.ep = frameP epb ++ [false] → x.bw = frameP bwb ++ [false] → x.a = n → n ≤ x.lb + 1 → x.s = 0 → x.j = 0 →
      x.eph = 0 → x.bwh = 0 → x.f = 0 → x.ns = 0 → x.ck = 0 → 4 * x.lb + 4 ≤ cap →
      x.ow.length + n * (2 * x.L + 1) + 4 < cap → n ≤ cap →
      WExec cap levelLoop x.w { x with a := 0, ow := x.ow ++ levelRows epb bwb x.lb x.L n }.w
        (n * (levelCost x.lb x.lb x.L + 4) + 1)
  | 0, x, _, _, _, _, _, ha, _, _, _, _, _, _, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF ha) ?_ (by omega)
    cases x
    simp only at ha ⊢
    subst ha
    simp [levelRows]
  | n + 1, x, hlb, hbwl, hk, hep, hbw, ha, han, hs, hj, heph, hbwh, hf, hns, hck, hcap, hO, hn => by
    have s1 := WExec.dec (cap := cap) gA x.w (by show x.a ≤ cap; omega)
    rw [w_a] at s1
    obtain ⟨y1, hy1⟩ : ∃ y : TSt, y = { x with a := n } := ⟨_, rfl⟩
    have e1 : ({ x with a := x.w.val gA - 1 } : TSt) = y1 := by rw [hy1]; show { x with a := x.a - 1 } = _; rw [ha]; rfl
    rw [e1] at s1
    have hsq : (n + 1) * (2 * x.L + 1) = n * (2 * x.L + 1) + (2 * x.L + 1) := by ring
    have hL1 : y1.ow.length + 2 * y1.L + 4 < cap := by
      rw [hy1]; show x.ow.length + 2 * x.L + 4 < cap; omega
    have s2 := levelBody_spec cap y1 epb bwb hepl (by rw [hy1]; exact hlb) (by rw [hy1]; exact hbwl)
      (by rw [hy1]; exact hk) (by rw [hy1]; exact hep) (by rw [hy1]; exact hbw) (by rw [hy1]; show n ≤ x.lb; omega)
      (by rw [hy1]; exact hs) (by rw [hy1]; exact hj) (by rw [hy1]; exact heph) (by rw [hy1]; exact hbwh)
      (by rw [hy1]; exact hf) (by rw [hy1]; exact hns) (by rw [hy1]; exact hck) (by rw [hy1]; exact hcap) hL1
    obtain ⟨y2, hy2⟩ : ∃ y : TSt, y = { x with a := n, ow := x.ow ++ frameP (rowOf epb bwb x.lb n x.L) ++ [false] } :=
      ⟨_, rfl⟩
    have e2 : ({ y1 with ow := y1.ow ++ frameP (rowOf epb bwb y1.lb y1.a y1.L) ++ [false] } : TSt) = y2 := by
      rw [hy2, hy1]
    rw [e2] at s2
    have hl2 : y2.ow.length = x.ow.length + (2 * x.L + 1) ∧ y2.L = x.L := by
      rw [hy2]; refine ⟨?_, rfl⟩; simp [rowOf, rowBits, frameP_length]
    have ih := levelLoop_spec epb bwb hepl n y2 (by rw [hy2]; exact hlb) (by rw [hy2]; exact hbwl)
      (by rw [hy2]; exact hk) (by rw [hy2]; exact hep) (by rw [hy2]; exact hbw) (by rw [hy2])
      (by rw [hy2]; show n ≤ x.lb + 1; omega) (by rw [hy2]; exact hs) (by rw [hy2]; exact hj) (by rw [hy2]; exact heph) (by rw [hy2]; exact hbwh)
      (by rw [hy2]; exact hf) (by rw [hy2]; exact hns) (by rw [hy2]; exact hck) (by rw [hy2]; exact hcap)
      (by rw [hl2.1, hl2.2]; omega) (by omega)
    have hm := levelCost_mono x.lb n x.lb x.L (by omega)
    refine WExec.cast cap (WExec.whrT (by show x.a ≠ 0; omega) (WExec.seq s1 s2) ih) ?_ ?_
    · rw [hy2, levelRows_succ]
      simp only [List.append_assoc]
    · have e : y1.lb = x.lb ∧ y1.a = n ∧ y1.L = x.L ∧ y2.lb = x.lb ∧ y2.L = x.L := by
        rw [hy1, hy2]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      rw [e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2]
      have hsq2 : (n + 1) * (levelCost x.lb x.lb x.L + 4) = n * (levelCost x.lb x.lb x.L + 4) +
          (levelCost x.lb x.lb x.L + 4) := by ring
      omega

end NearCubicWires.WireExponent3_5.FinalPass.Flat
