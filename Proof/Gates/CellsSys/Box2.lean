import Proof.Gates.CellsSys.Box

set_option autoImplicit false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

/-! ## Value level -/

/-- The lower end, clamped at `−W`. -/
def loP (cp cn xp xn A Λ W : ℕ) : ℕ × ℕ :=
  if xn + (fdivP (cp + A) (cn + Λ) A).2 < xp + (fdivP (cp + A) (cn + Λ) A).1 + W then
    (xp + (fdivP (cp + A) (cn + Λ) A).1, xn + (fdivP (cp + A) (cn + Λ) A).2) else (0, W)

/-- The upper end, clamped at `W`. -/
def hiP (cp cn xp xn A Λ W : ℕ) : ℕ × ℕ :=
  if xn + (fdivP (cp + Λ) (cn + 1) A).2 + W < xp + (fdivP (cp + Λ) (cn + 1) A).1 then (W, 0) else
    (xp + (fdivP (cp + Λ) (cn + 1) A).1, xn + (fdivP (cp + Λ) (cn + 1) A).2)

/-- The side length `(hi − lo + 1).toNat`. -/
def lenP (lo hi : ℕ × ℕ) : ℕ := (hi.1 + lo.2 + 1) - (hi.2 + lo.1)

theorem loP_eq (cp cn xp xn A Λ W : ℕ) (hA : 0 < A) :
    zOf (loP cp cn xp xn A Λ W).1 (loP cp cn xp xn A Λ W).2 =
      (if ScoreBox.lower (zOf cp cn) A (zOf xp xn) Λ ≤ -(W : ℤ) then -(W : ℤ)
        else ScoreBox.lower (zOf cp cn) A (zOf xp xn) Λ) := by
  have hf := fdivP_eq (cp + A) (cn + Λ) A hA
  have hlow : ScoreBox.lower (zOf cp cn) A (zOf xp xn) Λ =
      zOf (xp + (fdivP (cp + A) (cn + Λ) A).1) (xn + (fdivP (cp + A) (cn + Λ) A).2) := by
    unfold ScoreBox.lower ScoreBox.ceilDiv
    have : zOf cp cn - (Λ : ℤ) + 1 + A - 1 = zOf (cp + A) (cn + Λ) := by unfold zOf; push_cast; ring
    rw [this, ← hf]; unfold zOf; push_cast; ring
  rw [hlow]
  unfold loP zOf
  split_ifs with h1 h2 h2 <;> push_cast <;> omega

theorem hiP_eq (cp cn xp xn A Λ W : ℕ) (hA : 0 < A) :
    zOf (hiP cp cn xp xn A Λ W).1 (hiP cp cn xp xn A Λ W).2 =
      (if ScoreBox.upper (zOf cp cn) A (zOf xp xn) Λ ≤ (W : ℤ) then ScoreBox.upper (zOf cp cn) A (zOf xp xn) Λ
        else (W : ℤ)) := by
  have hf := fdivP_eq (cp + Λ) (cn + 1) A hA
  have hup : ScoreBox.upper (zOf cp cn) A (zOf xp xn) Λ =
      zOf (xp + (fdivP (cp + Λ) (cn + 1) A).1) (xn + (fdivP (cp + Λ) (cn + 1) A).2) := by
    unfold ScoreBox.upper
    have : zOf cp cn + (Λ : ℤ) - 1 = zOf (cp + Λ) (cn + 1) := by unfold zOf; push_cast; ring
    rw [this, ← hf]; unfold zOf; push_cast; ring
  rw [hup]
  unfold hiP zOf
  split_ifs with h1 h2 h2 <;> push_cast <;> omega

theorem lenP_eq (lo hi : ℕ × ℕ) : lenP lo hi = (zOf hi.1 hi.2 - zOf lo.1 lo.2 + 1).toNat := by
  unfold lenP zOf; omega

/-! ## Floor division of a pair -/

def fdivB (np nn : Fin VV) : St VV MM :=
  .ite (.lt np nn)
    (.seq (.op (.zero q3)) (.seq (.op (.copy q4 nn)) (.seq (.op (.sub q4 np)) (.seq (.op (.add q4 vA))
      (.seq (.op (.sub q4 v1)) (.seq (.op (.dm q4 vA q1 q2)) (.op (.copy q4 q1))))))))
    (.seq (.op (.zero q4)) (.seq (.op (.copy q3 np)) (.seq (.op (.sub q3 nn)) (.seq (.op (.dm q3 vA q1 q2))
      (.op (.copy q3 q1))))))

theorem fdivB_spec (np nn : Fin VV) (hnp : np ∉ [q1, q2, q3, q4, vA, v1]) (hnn : nn ∉ [q1, q2, q3, q4, vA, v1])
    (hnpn : np ≠ nn) (a : DS VV MM) (hc : Cst a) (Np Nn A : ℕ) (h1 : a.env np = Np) (h2 : a.env nn = Nn)
    (h3 : a.env vA = A) (hA : 1 ≤ A) (hW : Np + Nn + 2 * A < 2 ^ C.Wd) :
    Hs C (fdivB np nn) a 20 (fun b => b.env q3 = (fdivP Np Nn A).1 ∧ b.env q4 = (fdivP Np Nn A).2 ∧
      Fr a b [q1, q2, q3, q4] ∧ Same a b) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnp hnn
  refine Hs.mono (Hs.ite (show np ≠ nn from hnpn) (fun he => ?_) (fun he => ?_)) (le_refl 20) (fun _ h => h)
  · have hlt : Np < Nn := by simpa [Cnd.eval, h1, h2] using he
    refine Hx.hs (Hs.then (o_zero q3 a) (fun e1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
    refine Hs.then (o_copy q4 nn e1 (Ne.symm hnn.2.2.2.1)) (fun e2 ⟨r1, r2, r3⟩ k2 hk2 => ?_)
    have e1n : e1.env nn = Nn := by rw [p2 nn (by simp; exact hnn.2.2.1)]; exact h2
    rw [e1n] at r1
    have e2p : e2.env np = Np := by
      rw [r2 np (by simp; exact hnp.2.2.2.1), p2 np (by simp; exact hnp.2.2.1)]; exact h1
    refine Hs.then (o_sub q4 np e2 (Ne.symm hnp.2.2.2.1) (by rw [r1, e2p]; omega)) (fun e3 ⟨s1, s2, s3⟩ k3 hk3 => ?_)
    rw [r1, e2p] at s1
    have e3A : e3.env vA = A := by simp (disch := decide) only [s2.ev, r2.ev, p2.ev]; exact h3
    refine Hs.then (o_add q4 vA e3 (by decide) (by rw [s1, e3A]; omega)) (fun e4 ⟨u1, u2, u3⟩ k4 hk4 => ?_)
    rw [s1, e3A] at u1
    have c4 : Cst e4 := cst_of (cst_of (cst_of (cst_of hc p2 (by decide)) r2 (by decide)) s2 (by decide)) u2
      (by decide)
    refine Hs.then (o_sub q4 v1 e4 (by decide) (by rw [u1, c4.one]; omega)) (fun e5 ⟨v1', v2', v3'⟩ k5 hk5 => ?_)
    rw [u1, c4.one] at v1'
    have e5A : e5.env vA = A := by simp (disch := decide) only [v2'.ev, u2.ev]; exact e3A
    refine Hs.then (o_dm q4 vA q1 q2 e5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [e5A]; omega) (by rw [e5A]; omega)) (fun e6 ⟨w1, w2, w3, w4⟩ k6 hk6 => ?_)
    rw [v1', e5A] at w1
    refine Hs.last (o_copy q4 q1 e6 (by decide)) (fun g ⟨x1, x2, x3⟩ k7 hk7 => ?_)
    rw [w1] at x1
    refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega⟩
    · simp (disch := decide) only [x2.ev, w3.ev, v2'.ev, u2.ev, s2.ev, r2.ev]; rw [p1]
      unfold fdivP; rw [if_neg (by omega)]
    · rw [x1]; unfold fdivP; rw [if_neg (by omega)]
    · exact Fr.trans (p2.weaken (by decide)) (Fr.trans (r2.weaken (by decide)) (Fr.trans (s2.weaken (by decide))
        (Fr.trans (u2.weaken (by decide)) (Fr.trans (v2'.weaken (by decide)) (Fr.trans (w3.weaken (by decide))
        (x2.weaken (by decide)))))))
    · exact Same.trans p3 (Same.trans r3 (Same.trans s3 (Same.trans u3 (Same.trans v3' (Same.trans w4 x3)))))
  · have hle : Nn ≤ Np := by simpa [Cnd.eval, h1, h2] using he
    refine Hx.hs (Hs.then (o_zero q4 a) (fun e1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
    refine Hs.then (o_copy q3 np e1 (Ne.symm hnp.2.2.1)) (fun e2 ⟨r1, r2, r3⟩ k2 hk2 => ?_)
    have e1p : e1.env np = Np := by rw [p2 np (by simp; exact hnp.2.2.2.1)]; exact h1
    rw [e1p] at r1
    have e2n : e2.env nn = Nn := by
      rw [r2 nn (by simp; exact hnn.2.2.1), p2 nn (by simp; exact hnn.2.2.2.1)]; exact h2
    refine Hs.then (o_sub q3 nn e2 (Ne.symm hnn.2.2.1) (by rw [r1, e2n]; omega)) (fun e3 ⟨s1, s2, s3⟩ k3 hk3 => ?_)
    rw [r1, e2n] at s1
    have e3A : e3.env vA = A := by simp (disch := decide) only [s2.ev, r2.ev, p2.ev]; exact h3
    refine Hs.then (o_dm q3 vA q1 q2 e3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [e3A]; omega) (by rw [e3A]; omega)) (fun e4 ⟨w1, w2, w3, w4⟩ k4 hk4 => ?_)
    rw [s1, e3A] at w1
    refine Hs.last (o_copy q3 q1 e4 (by decide)) (fun g ⟨x1, x2, x3⟩ k5 hk5 => ?_)
    rw [w1] at x1
    refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega⟩
    · rw [x1]; unfold fdivP; rw [if_pos hle]
    · simp (disch := decide) only [x2.ev, w3.ev, s2.ev, r2.ev]; rw [p1]
      unfold fdivP; rw [if_pos hle]
    · exact Fr.trans (p2.weaken (by decide)) (Fr.trans (r2.weaken (by decide)) (Fr.trans (s2.weaken (by decide))
        (Fr.trans (w3.weaken (by decide)) (x2.weaken (by decide)))))
    · exact Same.trans p3 (Same.trans r3 (Same.trans s3 (Same.trans w4 x3)))

theorem fdivP_le (Np Nn A : ℕ) (hA : 1 ≤ A) : (fdivP Np Nn A).1 ≤ Np ∧ (fdivP Np Nn A).2 ≤ Nn := by
  unfold fdivP
  split_ifs with h
  · exact ⟨le_trans (Nat.div_le_self _ _) (by omega), by simp⟩
  · refine ⟨by simp, ?_⟩
    have : (Nn - Np + A - 1) / A ≤ Nn - Np := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      have : Nn - Np ≤ A * (Nn - Np) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega

/-! ## `K`, `X` of the role -/

def kxB : St VV MM :=
  .seq (.op (.copy ix rI)) (.seq (.op (.shl ix)) (.seq (.op (.shl ix)) (.seq (fetch sX ix kP) (.seq (.op (.inc ix))
  (.seq (fetch sX ix kN) (.seq (.op (.inc ix)) (.seq (fetch sX ix xP) (.seq (.op (.inc ix)) (fetch sX ix xN)))))))))

def kxT : List (Fin VV) := [ix, kP, kN, xP, xN, c0, vJ]

theorem kxB_spec (a : DS VV MM) (hc : Cst a) (hrc : RcOK a) (r : ℕ) (XL : List ℕ) (hr : a.env rI = r)
    (hX : a.ram sX = XL) (hlen : 4 * r + 3 < XL.length) (hW : 2 * XL.length < 2 ^ C.Wd) :
    Hs C kxB a (24 * XL.length + 60) (fun b => b.env kP = XL.getD (4 * r) 0 ∧ b.env kN = XL.getD (4 * r + 1) 0 ∧
      b.env xP = XL.getD (4 * r + 2) 0 ∧ b.env xN = XL.getD (4 * r + 3) 0 ∧ Fr a b kxT ∧ Kp a b ∧ RcOK b ∧
      Cst b) := by
  refine Hx.hs (Hs.then (o_copy ix rI a (by decide)) (fun e1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  rw [hr] at p1
  refine Hs.then (o_shl ix e1 (by rw [p1]; omega)) (fun e2 ⟨q1, q2, q3⟩ k2 hk2 => ?_)
  rw [p1] at q1
  refine Hs.then (o_shl ix e2 (by rw [q1]; omega)) (fun e3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  rw [q1] at r1
  have S3 : Same a e3 := Same.trans p3 (Same.trans q3 r3)
  have rc3 : RcOK e3 := RcOK.same hrc S3
  have hX3 : e3.ram sX = XL := by rw [S3.ram, hX]
  have hi : 2 * (2 * r) = 4 * r := by ring
  rw [hi] at r1
  refine Hs.then (o_fetch sX ix kP (by decide) (by decide) (by decide) e3 (by rw [r1, hX3]; omega) (by rw [r1]; omega))
    (fun e4 ⟨s1, s2, s3, s4⟩ k4 hk4 => ?_)
  have rc4 : RcOK e4 := RcOK.fetch rc3 s3 s4 (by rw [r1, hX3]; omega)
  rw [r1, hX3] at s1
  have e4x : e4.env ix = 4 * r := by simp (disch := decide) only [s2.ev]; exact r1
  refine Hs.then (o_inc ix e4 (by rw [e4x]; omega)) (fun e5 ⟨u1, u2, u3⟩ k5 hk5 => ?_)
  rw [e4x] at u1
  have PolyTab : Kp a e5 := Kp.trans (Kp.of_same S3) (Kp.trans s3 (Kp.of_same u3))
  refine Hs.then (o_fetch sX ix kN (by decide) (by decide) (by decide) e5 (by rw [u1, PolyTab.ram, hX]; omega) (by rw [u1]; omega))
    (fun e6 ⟨v1', v2', v3', v4'⟩ k6 hk6 => ?_)
  have rc6 : RcOK e6 := RcOK.fetch (RcOK.same rc4 u3) v3' v4' (by rw [u1, PolyTab.ram, hX]; omega)
  rw [u1, PolyTab.ram, hX] at v1'
  have e6x : e6.env ix = 4 * r + 1 := by simp (disch := decide) only [v2'.ev]; exact u1
  refine Hs.then (o_inc ix e6 (by rw [e6x]; omega)) (fun e7 ⟨w1, w2, w3⟩ k7 hk7 => ?_)
  rw [e6x] at w1
  have K7 : Kp a e7 := Kp.trans PolyTab (Kp.trans v3' (Kp.of_same w3))
  refine Hs.then (o_fetch sX ix xP (by decide) (by decide) (by decide) e7 (by rw [w1, K7.ram, hX]; omega) (by rw [w1]; omega))
    (fun e8 ⟨x1, x2, x3, x4⟩ k8 hk8 => ?_)
  have rc8 : RcOK e8 := RcOK.fetch (RcOK.same rc6 w3) x3 x4 (by rw [w1, K7.ram, hX]; omega)
  rw [w1, K7.ram, hX] at x1
  have e8x : e8.env ix = 4 * r + 1 + 1 := by simp (disch := decide) only [x2.ev]; exact w1
  refine Hs.then (o_inc ix e8 (by rw [e8x]; omega)) (fun e9 ⟨y1, y2, y3⟩ k9 hk9 => ?_)
  rw [e8x] at y1
  have K9 : Kp a e9 := Kp.trans K7 (Kp.trans x3 (Kp.of_same y3))
  refine Hs.last (o_fetch sX ix xN (by decide) (by decide) (by decide) e9 (by rw [y1, K9.ram, hX]; omega) (by rw [y1]; omega))
    (fun g ⟨z1, z2, z3, z4⟩ k10 hk10 => ?_)
  have rcg : RcOK g := RcOK.fetch (RcOK.same rc8 y3) z3 z4 (by rw [y1, K9.ram, hX]; omega)
  rw [y1, K9.ram, hX] at z1
  have FR : Fr a g kxT := Fr.trans (p2.weaken (by decide)) (Fr.trans (q2.weaken (by decide)) (Fr.trans
    (r2.weaken (by decide)) (Fr.trans (s2.weaken (by decide)) (Fr.trans (u2.weaken (by decide)) (Fr.trans
    (v2'.weaken (by decide)) (Fr.trans (w2.weaken (by decide)) (Fr.trans (x2.weaken (by decide)) (Fr.trans
    (y2.weaken (by decide)) (z2.weaken (by decide))))))))))
  have r3' : e3.rc sX ≤ XL.length := by have := rc3 sX; rwa [hX3] at this
  have r5' : e5.rc sX ≤ XL.length := by have := RcOK.same rc4 u3 sX; rwa [PolyTab.ram, hX] at this
  have r7' : e7.rc sX ≤ XL.length := by have := RcOK.same rc6 w3 sX; rwa [K7.ram, hX] at this
  have r9' : e9.rc sX ≤ XL.length := by have := RcOK.same rc8 y3 sX; rwa [K9.ram, hX] at this
  rw [r1] at hk4; rw [u1] at hk6; rw [w1] at hk8; rw [y1] at hk10
  refine ⟨⟨by simp (disch := decide) only [z2.ev, y2.ev, x2.ev, w2.ev, v2'.ev, u2.ev]; exact s1,
    by simp (disch := decide) only [z2.ev, y2.ev, x2.ev, w2.ev]; exact v1',
    by simp (disch := decide) only [z2.ev, y2.ev]; exact x1, by rw [z1],
    FR, Kp.trans K9 z3, rcg, cst_of hc FR (by decide)⟩, by omega⟩

/-! ## The centre -/

def ctrB : St VV MM :=
  .seq (.op (.copy q1 accP)) (.seq (.op (.add q1 kN)) (.seq (.op (.mul vM1 q1 Cp)) (.seq (.op (.copy q1 accN))
    (.seq (.op (.add q1 kP)) (.op (.mul vM1 q1 Cn))))))

theorem ctrB_spec (a : DS VV MM) (aP aN kp kn M : ℕ) (h1 : a.env accP = aP) (h2 : a.env accN = aN)
    (h3 : a.env kP = kp) (h4 : a.env kN = kn) (h5 : a.env vM1 = M) (hM : 1 ≤ M)
    (hW1 : M * (aP + kn) < 2 ^ C.Wd) (hW2 : M * (aN + kp) < 2 ^ C.Wd) :
    Hs C ctrB a 11 (fun b => b.env Cp = M * (aP + kn) ∧ b.env Cn = M * (aN + kp) ∧ Fr a b [q1, Cp, Cn] ∧
      Same a b) := by
  have l1 : aP + kn ≤ M * (aP + kn) := Nat.le_mul_of_pos_left _ (by omega)
  have l2 : aN + kp ≤ M * (aN + kp) := Nat.le_mul_of_pos_left _ (by omega)
  refine Hx.hs (Hs.then (o_copy q1 accP a (by decide)) (fun e1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  rw [h1] at p1
  have e1k : e1.env kN = kn := by simp (disch := decide) only [p2.ev]; exact h4
  refine Hs.then (o_add q1 kN e1 (by decide) (by rw [p1, e1k]; omega)) (fun e2 ⟨q1', q2', q3'⟩ k2 hk2 => ?_)
  rw [p1, e1k] at q1'
  have e2M : e2.env vM1 = M := by simp (disch := decide) only [q2'.ev, p2.ev]; exact h5
  refine Hs.then (o_mul vM1 q1 Cp e2 (by decide) (by decide) (by decide) (by rw [e2M, q1']; exact hW1))
    (fun e3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  rw [e2M, q1'] at r1
  have e3a : e3.env accN = aN := by simp (disch := decide) only [r2.ev, q2'.ev, p2.ev]; exact h2
  refine Hs.then (o_copy q1 accN e3 (by decide)) (fun e4 ⟨s1, s2, s3⟩ k4 hk4 => ?_)
  rw [e3a] at s1
  have e4k : e4.env kP = kp := by simp (disch := decide) only [s2.ev, r2.ev, q2'.ev, p2.ev]; exact h3
  refine Hs.then (o_add q1 kP e4 (by decide) (by rw [s1, e4k]; omega)) (fun e5 ⟨u1, u2, u3⟩ k5 hk5 => ?_)
  rw [s1, e4k] at u1
  have e5M : e5.env vM1 = M := by simp (disch := decide) only [u2.ev, s2.ev, r2.ev]; exact e2M
  refine Hs.last (o_mul vM1 q1 Cn e5 (by decide) (by decide) (by decide) (by rw [e5M, u1]; exact hW2))
    (fun g ⟨v1', v2', v3'⟩ k6 hk6 => ?_)
  rw [e5M, u1] at v1'
  refine ⟨⟨by simp (disch := decide) only [v2'.ev, u2.ev, s2.ev]; exact r1, v1',
    Fr.trans (p2.weaken (by decide)) (Fr.trans (q2'.weaken (by decide)) (Fr.trans (r2.weaken (by decide))
      (Fr.trans (s2.weaken (by decide)) (Fr.trans (u2.weaken (by decide)) (v2'.weaken (by decide)))))),
    Same.trans p3 (Same.trans q3' (Same.trans r3 (Same.trans s3 (Same.trans u3 v3'))))⟩, by omega⟩

/-! ## The ends and the length -/

def loB : St VV MM :=
  .seq (.op (.copy f2 Cp)) (.seq (.op (.add f2 vA)) (.seq (.op (.copy f3 Cn)) (.seq (.op (.add f3 vLam)) (.seq (fdivB f2 f3) (.seq (.op (.copy lP xP)) (.seq (.op (.add lP q3)) (.seq (.op (.copy lN xN)) (.seq (.op (.add lN q4)) (.seq (.op (.copy f2 lP)) (.seq (.op (.add f2 Wv)) (.ite (.lt lN f2) skipS (.seq (.op (.zero lP)) (.op (.copy lN Wv))))))))))))))

def loT : List (Fin VV) := [f2, f3, q1, q2, q3, q4, lP, lN, vJ]

theorem loB_spec (a : DS VV MM) (hc : Cst a) (cp cn xp xn A Λ W U : ℕ) (h1 : a.env Cp = cp) (h2 : a.env Cn = cn)
    (h3 : a.env xP = xp) (h4 : a.env xN = xn) (h5 : a.env vA = A) (h6 : a.env vLam = Λ) (h7 : a.env Wv = W)
    (hA : 1 ≤ A) (hU : cp + cn + xp + xn + A + Λ + W ≤ U) (hW : 8 * U + 8 < 2 ^ C.Wd) :
    Hs C loB a 60 (fun b => b.env lP = (loP cp cn xp xn A Λ W).1 ∧ b.env lN = (loP cp cn xp xn A Λ W).2 ∧
      Fr a b loT ∧ Same a b) := by
  have hf := fdivP_le (cp + A) (cn + Λ) A hA
  refine Hx.hs (Hs.then (o_copy f2 Cp a (by decide)) (fun e1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  rw [h1] at p1
  have e1A : e1.env vA = A := by simp (disch := decide) only [p2.ev]; exact h5
  refine Hs.then (o_add f2 vA e1 (by decide) (by rw [p1, e1A]; omega)) (fun e2 ⟨q1', q2', q3'⟩ k2 hk2 => ?_)
  rw [p1, e1A] at q1'
  refine Hs.then (o_copy f3 Cn e2 (by decide)) (fun e3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  have e2c : e2.env Cn = cn := by simp (disch := decide) only [q2'.ev, p2.ev]; exact h2
  rw [e2c] at r1
  have e3L : e3.env vLam = Λ := by simp (disch := decide) only [r2.ev, q2'.ev, p2.ev]; exact h6
  refine Hs.then (o_add f3 vLam e3 (by decide) (by rw [r1, e3L]; omega)) (fun e4 ⟨s1, s2, s3⟩ k4 hk4 => ?_)
  rw [r1, e3L] at s1
  have c4 : Cst e4 := cst_of (cst_of (cst_of (cst_of hc p2 (by decide)) q2' (by decide)) r2 (by decide)) s2
    (by decide)
  have e4f2 : e4.env f2 = cp + A := by simp (disch := decide) only [s2.ev, r2.ev]; exact q1'
  have e4A : e4.env vA = A := by simp (disch := decide) only [s2.ev, r2.ev, q2'.ev]; exact e1A
  refine Hs.then (fdivB_spec f2 f3 (by decide) (by decide) (by decide) e4 c4 _ _ A e4f2 s1 e4A hA (by omega))
    (fun e5 ⟨u1, u2, u3, u4⟩ k5 hk5 => ?_)
  refine Hs.then (o_copy lP xP e5 (by decide)) (fun e6 ⟨v1', v2', v3'⟩ k6 hk6 => ?_)
  have e5x : e5.env xP = xp := by simp (disch := decide) only [u3.ev, s2.ev, r2.ev, q2'.ev, p2.ev]; exact h3
  rw [e5x] at v1'
  have e6q : e6.env q3 = (fdivP (cp + A) (cn + Λ) A).1 := by simp (disch := decide) only [v2'.ev]; exact u1
  refine Hs.then (o_add lP q3 e6 (by decide) (by rw [v1', e6q]; omega)) (fun e7 ⟨w1, w2, w3⟩ k7 hk7 => ?_)
  rw [v1', e6q] at w1
  refine Hs.then (o_copy lN xN e7 (by decide)) (fun e8 ⟨x1, x2, x3⟩ k8 hk8 => ?_)
  have e7x : e7.env xN = xn := by
    simp (disch := decide) only [w2.ev, v2'.ev, u3.ev, s2.ev, r2.ev, q2'.ev, p2.ev]; exact h4
  rw [e7x] at x1
  have e8q : e8.env q4 = (fdivP (cp + A) (cn + Λ) A).2 := by simp (disch := decide) only [x2.ev, w2.ev, v2'.ev]; exact u2
  refine Hs.then (o_add lN q4 e8 (by decide) (by rw [x1, e8q]; omega)) (fun e9 ⟨y1, y2, y3⟩ k9 hk9 => ?_)
  rw [x1, e8q] at y1
  refine Hs.then (o_copy f2 lP e9 (by decide)) (fun e10 ⟨z1, z2, z3⟩ k10 hk10 => ?_)
  have e9l : e9.env lP = xp + (fdivP (cp + A) (cn + Λ) A).1 := by simp (disch := decide) only [y2.ev, x2.ev]; exact w1
  rw [e9l] at z1
  have e10W : e10.env Wv = W := by
    simp (disch := decide) only [z2.ev, y2.ev, x2.ev, w2.ev, v2'.ev, u3.ev, s2.ev, r2.ev, q2'.ev, p2.ev]; exact h7
  refine Hs.then (o_add f2 Wv e10 (by decide) (by rw [z1, e10W]; omega)) (fun e11 ⟨a1', a2', a3'⟩ k11 hk11 => ?_)
  rw [z1, e10W] at a1'
  have e11N : e11.env lN = xn + (fdivP (cp + A) (cn + Λ) A).2 := by simp (disch := decide) only [a2'.ev, z2.ev]; exact y1
  have e11P : e11.env lP = xp + (fdivP (cp + A) (cn + Λ) A).1 := by simp (disch := decide) only [a2'.ev, z2.ev]; exact e9l
  have e11W : e11.env Wv = W := by simp (disch := decide) only [a2'.ev]; exact e10W
  have FR11 : Fr a e11 loT := Fr.trans (p2.weaken (by decide)) (Fr.trans (q2'.weaken (by decide)) (Fr.trans
    (r2.weaken (by decide)) (Fr.trans (s2.weaken (by decide)) (Fr.trans (u3.weaken (by decide)) (Fr.trans
    (v2'.weaken (by decide)) (Fr.trans (w2.weaken (by decide)) (Fr.trans (x2.weaken (by decide)) (Fr.trans
    (y2.weaken (by decide)) (Fr.trans (z2.weaken (by decide)) (a2'.weaken (by decide)))))))))))
  have SM11 : Same a e11 := Same.trans p3 (Same.trans q3' (Same.trans r3 (Same.trans s3 (Same.trans u4 (Same.trans
    v3' (Same.trans w3 (Same.trans x3 (Same.trans y3 (Same.trans z3 a3')))))))))
  refine Hs.last (t := 4) (Hs.ite (show lN ≠ f2 by decide) (fun he => ?_) (fun he => ?_))
    (fun g ⟨g1, g2, g3, g4⟩ k12 hk12 => ⟨⟨g1, g2, Fr.trans FR11 g3, Same.trans SM11 g4⟩, by omega⟩)
    (R1 := fun g => g.env lP = (loP cp cn xp xn A Λ W).1 ∧ g.env lN = (loP cp cn xp xn A Λ W).2 ∧
      Fr e11 g loT ∧ Same e11 g)
  · have hlt : xn + (fdivP (cp + A) (cn + Λ) A).2 < xp + (fdivP (cp + A) (cn + Λ) A).1 + W := by
      simpa [Cnd.eval, e11N, a1'] using he
    refine Hs.mono (skip_spec e11) (by norm_num) ?_
    rintro g rfl
    refine ⟨by rw [DS.set_env_ne _ _ (by decide), e11P]; unfold loP; rw [if_pos hlt],
      by rw [DS.set_env_ne _ _ (by decide), e11N]; unfold loP; rw [if_pos hlt], Fr.set _ _ (by decide),
      Same.set _ _ _⟩
  · have hlt : ¬ xn + (fdivP (cp + A) (cn + Λ) A).2 < xp + (fdivP (cp + A) (cn + Λ) A).1 + W := by
      simpa [Cnd.eval, e11N, a1'] using he
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1) (o_zero lP e11) (fun f ⟨f1', f2', f3'⟩ => ?_)) (by norm_num)
      (fun _ h => h)
    refine Hs.mono (o_copy lN Wv f (by decide)) le_rfl ?_
    rintro g ⟨g1, g2, g3⟩
    refine ⟨by simp (disch := decide) only [g2.ev]; rw [f1']; unfold loP; rw [if_neg hlt],
      by rw [g1]; simp (disch := decide) only [f2'.ev]; rw [e11W]; unfold loP; rw [if_neg hlt],
      Fr.trans (f2'.weaken (by decide)) (g2.weaken (by decide)), Same.trans f3' g3⟩

def hiB : St VV MM :=
  .seq (.op (.copy f2 Cp)) (.seq (.op (.add f2 vLam)) (.seq (.op (.copy f3 Cn)) (.seq (.op (.inc f3)) (.seq (fdivB f2 f3) (.seq (.op (.copy hP xP)) (.seq (.op (.add hP q3)) (.seq (.op (.copy hN xN)) (.seq (.op (.add hN q4)) (.seq (.op (.copy f2 hN)) (.seq (.op (.add f2 Wv)) (.ite (.lt f2 hP) (.seq (.op (.copy hP Wv)) (.op (.zero hN))) skipS)))))))))))

def hiT : List (Fin VV) := [f2, f3, q1, q2, q3, q4, hP, hN, vJ]

theorem hiB_spec (a : DS VV MM) (hc : Cst a) (cp cn xp xn A Λ W U : ℕ) (h1 : a.env Cp = cp) (h2 : a.env Cn = cn)
    (h3 : a.env xP = xp) (h4 : a.env xN = xn) (h5 : a.env vA = A) (h6 : a.env vLam = Λ) (h7 : a.env Wv = W)
    (hA : 1 ≤ A) (hU : cp + cn + xp + xn + A + Λ + W ≤ U) (hW : 8 * U + 8 < 2 ^ C.Wd) :
    Hs C hiB a 60 (fun b => b.env hP = (hiP cp cn xp xn A Λ W).1 ∧ b.env hN = (hiP cp cn xp xn A Λ W).2 ∧
      Fr a b hiT ∧ Same a b) := by
  have hf := fdivP_le (cp + Λ) (cn + 1) A hA
  refine Hx.hs (Hs.then (o_copy f2 Cp a (by decide)) (fun e1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  rw [h1] at p1
  have e1L : e1.env vLam = Λ := by simp (disch := decide) only [p2.ev]; exact h6
  refine Hs.then (o_add f2 vLam e1 (by decide) (by rw [p1, e1L]; omega)) (fun e2 ⟨q1', q2', q3'⟩ k2 hk2 => ?_)
  rw [p1, e1L] at q1'
  refine Hs.then (o_copy f3 Cn e2 (by decide)) (fun e3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  have e2c : e2.env Cn = cn := by simp (disch := decide) only [q2'.ev, p2.ev]; exact h2
  rw [e2c] at r1
  refine Hs.then (o_inc f3 e3 (by rw [r1]; omega)) (fun e4 ⟨s1, s2, s3⟩ k4 hk4 => ?_)
  rw [r1] at s1
  have c4 : Cst e4 := cst_of (cst_of (cst_of (cst_of hc p2 (by decide)) q2' (by decide)) r2 (by decide)) s2
    (by decide)
  have e4f2 : e4.env f2 = cp + Λ := by simp (disch := decide) only [s2.ev, r2.ev]; exact q1'
  have e4A : e4.env vA = A := by simp (disch := decide) only [s2.ev, r2.ev, q2'.ev, p2.ev]; exact h5
  refine Hs.then (fdivB_spec f2 f3 (by decide) (by decide) (by decide) e4 c4 _ _ A e4f2 s1 e4A hA (by omega))
    (fun e5 ⟨u1, u2, u3, u4⟩ k5 hk5 => ?_)
  refine Hs.then (o_copy hP xP e5 (by decide)) (fun e6 ⟨v1', v2', v3'⟩ k6 hk6 => ?_)
  have e5x : e5.env xP = xp := by simp (disch := decide) only [u3.ev, s2.ev, r2.ev, q2'.ev, p2.ev]; exact h3
  rw [e5x] at v1'
  have e6q : e6.env q3 = (fdivP (cp + Λ) (cn + 1) A).1 := by simp (disch := decide) only [v2'.ev]; exact u1
  refine Hs.then (o_add hP q3 e6 (by decide) (by rw [v1', e6q]; omega)) (fun e7 ⟨w1, w2, w3⟩ k7 hk7 => ?_)
  rw [v1', e6q] at w1
  refine Hs.then (o_copy hN xN e7 (by decide)) (fun e8 ⟨x1, x2, x3⟩ k8 hk8 => ?_)
  have e7x : e7.env xN = xn := by
    simp (disch := decide) only [w2.ev, v2'.ev, u3.ev, s2.ev, r2.ev, q2'.ev, p2.ev]; exact h4
  rw [e7x] at x1
  have e8q : e8.env q4 = (fdivP (cp + Λ) (cn + 1) A).2 := by simp (disch := decide) only [x2.ev, w2.ev, v2'.ev]; exact u2
  refine Hs.then (o_add hN q4 e8 (by decide) (by rw [x1, e8q]; omega)) (fun e9 ⟨y1, y2, y3⟩ k9 hk9 => ?_)
  rw [x1, e8q] at y1
  refine Hs.then (o_copy f2 hN e9 (by decide)) (fun e10 ⟨z1, z2, z3⟩ k10 hk10 => ?_)
  rw [y1] at z1
  have e10W : e10.env Wv = W := by
    simp (disch := decide) only [z2.ev, y2.ev, x2.ev, w2.ev, v2'.ev, u3.ev, s2.ev, r2.ev, q2'.ev, p2.ev]; exact h7
  refine Hs.then (o_add f2 Wv e10 (by decide) (by rw [z1, e10W]; omega)) (fun e11 ⟨a1', a2', a3'⟩ k11 hk11 => ?_)
  rw [z1, e10W] at a1'
  have e11N : e11.env hN = xn + (fdivP (cp + Λ) (cn + 1) A).2 := by simp (disch := decide) only [a2'.ev, z2.ev]; exact y1
  have e11P : e11.env hP = xp + (fdivP (cp + Λ) (cn + 1) A).1 := by
    simp (disch := decide) only [a2'.ev, z2.ev, y2.ev, x2.ev]; exact w1
  have e11W : e11.env Wv = W := by simp (disch := decide) only [a2'.ev]; exact e10W
  have FR11 : Fr a e11 hiT := Fr.trans (p2.weaken (by decide)) (Fr.trans (q2'.weaken (by decide)) (Fr.trans
    (r2.weaken (by decide)) (Fr.trans (s2.weaken (by decide)) (Fr.trans (u3.weaken (by decide)) (Fr.trans
    (v2'.weaken (by decide)) (Fr.trans (w2.weaken (by decide)) (Fr.trans (x2.weaken (by decide)) (Fr.trans
    (y2.weaken (by decide)) (Fr.trans (z2.weaken (by decide)) (a2'.weaken (by decide)))))))))))
  have SM11 : Same a e11 := Same.trans p3 (Same.trans q3' (Same.trans r3 (Same.trans s3 (Same.trans u4 (Same.trans
    v3' (Same.trans w3 (Same.trans x3 (Same.trans y3 (Same.trans z3 a3')))))))))
  refine Hs.last (t := 4) (Hs.ite (show f2 ≠ hP by decide) (fun he => ?_) (fun he => ?_))
    (fun g ⟨g1, g2, g3, g4⟩ k12 hk12 => ⟨⟨g1, g2, Fr.trans FR11 g3, Same.trans SM11 g4⟩, by omega⟩)
    (R1 := fun g => g.env hP = (hiP cp cn xp xn A Λ W).1 ∧ g.env hN = (hiP cp cn xp xn A Λ W).2 ∧
      Fr e11 g hiT ∧ Same e11 g)
  · have hlt : xn + (fdivP (cp + Λ) (cn + 1) A).2 + W < xp + (fdivP (cp + Λ) (cn + 1) A).1 := by
      have := he; simp only [Cnd.eval, decide_eq_true_eq] at this
      rw [a1', e11P] at this; exact this
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1) (o_copy hP Wv e11 (by decide)) (fun f ⟨f1', f2', f3'⟩ => ?_))
      (by norm_num) (fun _ h => h)
    refine Hs.mono (o_zero hN f) le_rfl ?_
    rintro g ⟨g1, g2, g3⟩
    refine ⟨by simp (disch := decide) only [g2.ev]; rw [f1', e11W]; unfold hiP; rw [if_pos hlt],
      by rw [g1]; unfold hiP; rw [if_pos hlt], Fr.trans (f2'.weaken (by decide)) (g2.weaken (by decide)),
      Same.trans f3' g3⟩
  · have hlt : ¬ xn + (fdivP (cp + Λ) (cn + 1) A).2 + W < xp + (fdivP (cp + Λ) (cn + 1) A).1 := by
      have := he; simp only [Cnd.eval, decide_eq_false_iff_not] at this
      rw [a1', e11P] at this; exact this
    refine Hs.mono (skip_spec e11) (by norm_num) ?_
    rintro g rfl
    refine ⟨by rw [DS.set_env_ne _ _ (by decide), e11P]; unfold hiP; rw [if_neg hlt],
      by rw [DS.set_env_ne _ _ (by decide), e11N]; unfold hiP; rw [if_neg hlt], Fr.set _ _ (by decide),
      Same.set _ _ _⟩

def lenB : St VV MM :=
  .seq (.op (.copy f2 hP)) (.seq (.op (.add f2 lN)) (.seq (.op (.inc f2)) (.seq (.op (.copy f3 hN))
  (.seq (.op (.add f3 lP)) (.ite (.lt f2 f3) (.op (.zero nL)) (.seq (.op (.copy nL f2)) (.op (.sub nL f3))))))))

theorem lenB_spec (a : DS VV MM) (lp ln hp hn : ℕ) (h1 : a.env lP = lp) (h2 : a.env lN = ln) (h3 : a.env hP = hp)
    (h4 : a.env hN = hn) (hW : hp + ln + hn + lp + 1 < 2 ^ C.Wd) :
    Hs C lenB a 16 (fun b => b.env nL = lenP (lp, ln) (hp, hn) ∧ Fr a b [f2, f3, nL] ∧ Same a b) := by
  refine Hx.hs (Hs.then (o_copy f2 hP a (by decide)) (fun e1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  rw [h3] at p1
  have e1l : e1.env lN = ln := by simp (disch := decide) only [p2.ev]; exact h2
  refine Hs.then (o_add f2 lN e1 (by decide) (by rw [p1, e1l]; omega)) (fun e2 ⟨q1', q2', q3'⟩ k2 hk2 => ?_)
  rw [p1, e1l] at q1'
  refine Hs.then (o_inc f2 e2 (by rw [q1']; omega)) (fun e3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  rw [q1'] at r1
  refine Hs.then (o_copy f3 hN e3 (by decide)) (fun e4 ⟨s1, s2, s3⟩ k4 hk4 => ?_)
  have e3h : e3.env hN = hn := by simp (disch := decide) only [r2.ev, q2'.ev, p2.ev]; exact h4
  rw [e3h] at s1
  have e4l : e4.env lP = lp := by simp (disch := decide) only [s2.ev, r2.ev, q2'.ev, p2.ev]; exact h1
  refine Hs.then (o_add f3 lP e4 (by decide) (by rw [s1, e4l]; omega)) (fun e5 ⟨u1, u2, u3⟩ k5 hk5 => ?_)
  rw [s1, e4l] at u1
  have e5f2 : e5.env f2 = hp + ln + 1 := by simp (disch := decide) only [u2.ev, s2.ev]; exact r1
  have FR5 : Fr a e5 [f2, f3, nL] := Fr.trans (p2.weaken (by decide)) (Fr.trans (q2'.weaken (by decide))
    (Fr.trans (r2.weaken (by decide)) (Fr.trans (s2.weaken (by decide)) (u2.weaken (by decide)))))
  have SM5 : Same a e5 := Same.trans p3 (Same.trans q3' (Same.trans r3 (Same.trans s3 u3)))
  refine Hs.last (t := 4) (Hs.ite (show f2 ≠ f3 by decide) (fun he => ?_) (fun he => ?_))
    (fun g ⟨g1, g2, g3⟩ k6 hk6 => ⟨⟨g1, Fr.trans FR5 g2, Same.trans SM5 g3⟩, by omega⟩)
    (R1 := fun g => g.env nL = lenP (lp, ln) (hp, hn) ∧ Fr e5 g [f2, f3, nL] ∧ Same e5 g)
  · have hlt : hp + ln + 1 < hn + lp := by simpa [Cnd.eval, e5f2, u1] using he
    refine Hs.mono (o_zero nL e5) (by norm_num) ?_
    rintro g ⟨g1, g2, g3⟩
    exact ⟨by rw [g1]; unfold lenP; simp only; omega, g2.weaken (by decide), g3⟩
  · have hle : ¬ hp + ln + 1 < hn + lp := by simpa [Cnd.eval, e5f2, u1] using he
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1) (o_copy nL f2 e5 (by decide)) (fun f ⟨f1', f2', f3'⟩ => ?_))
      (by norm_num) (fun _ h => h)
    have ff3 : f.env f3 = hn + lp := by simp (disch := decide) only [f2'.ev]; exact u1
    refine Hs.mono (o_sub nL f3 f (by decide) (by rw [f1', e5f2, ff3]; omega)) le_rfl ?_
    rintro g ⟨g1, g2, g3⟩
    exact ⟨by rw [g1, f1', e5f2, ff3]; unfold lenP; simp only, Fr.trans (f2'.weaken (by decide))
      (g2.weaken (by decide)), Same.trans f3' g3⟩

end NearCubicGates.Close.Cells.SystemsPhase
