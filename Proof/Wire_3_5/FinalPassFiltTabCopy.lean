import Proof.Wire_3_5.FinalPassFiltTabStep

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.GF2

variable (cap : ℕ)

/-- All coordinates. -/
def kLoop : TProg := .whr gCK (.seq kStep (.dec gCK))

/-- The coefficient of coordinate `k` of a copy with fields `v`, `u`, diagonals `epb`, translation `bwb`. -/
def cbit (p m lb a v u tv : ℕ) (epb bwb : List Bool) (k : ℕ) : Bool :=
  coefBit (binary lb k) epb bwb lb a (binary m (fmulShift p m u (powN p m v (k + 1)))) (binary m tv)

/-- The marked coefficients of the coordinates `k, …, k+n−1`. -/
def pairs (p m lb a v u tv : ℕ) (epb bwb : List Bool) (k n : ℕ) : List Bool :=
  (List.range' k n).flatMap fun k' => [true, cbit p m lb a v u tv epb bwb k']

theorem pairs_succ (p m lb a v u tv : ℕ) (epb bwb : List Bool) (k n : ℕ) :
    pairs p m lb a v u tv epb bwb k (n + 1) =
      [true, cbit p m lb a v u tv epb bwb k] ++ pairs p m lb a v u tv epb bwb (k + 1) n := by
  simp [pairs, List.range'_succ]

theorem pairs_length (p m lb a v u tv : ℕ) (epb bwb : List Bool) (k n : ℕ) :
    (pairs p m lb a v u tv epb bwb k n).length = 2 * n := by
  induction n generalizing k with
  | zero => simp [pairs]
  | succ n ih => rw [pairs_succ, List.length_append, ih]; simp; omega

theorem kLoop_spec (p v u tv : ℕ) (epb bwb : List Bool) :
    ∀ (n k a0 s0 : ℕ) (x : TSt), x.ck = n →
      1 ≤ x.m → x.lb = epb.length / 2 + 1 → (1 ≤ epb.length ∧ epb.length % 2 = 1) → bwb.length = x.lb →
      x.a ≤ x.lb → x.fv = frame (binary x.m v) → x.fu = frame (binary x.m u) →
      x.pw = frame (binary x.m (powN p x.m v k)) → x.acc = frame (binary x.m a0) → x.st = frame (binary x.m s0) →
      x.tauw = frame (binary x.m tv) → x.pmw = frame (binary x.m p) → x.kw = frame (binary x.lb k) →
      x.bw = frame bwb → x.ep = frame epb → x.f = 0 → x.ns = 0 → x.tf = 0 → x.s = 0 → x.j = 0 → x.eph = 0 →
      x.bwh = 0 → 4 * x.lb + 2 * x.m + 8 ≤ cap → x.ow.length + 2 * n + 2 < cap → n ≤ cap →
      ∃ a1 s1 : ℕ, WExec cap kLoop x.w
        { x with ck := 0, pw := frame (binary x.m (powN p x.m v (k + n))), acc := frame (binary x.m a1),
                 st := frame (binary x.m s1), kw := frame (binary x.lb (k + n)),
                 ow := x.ow ++ pairs p x.m x.lb x.a v u tv epb bwb k n }.w
        (n * (kStepCost x.m x.lb x.a + 4) + 1)
  | 0, k, a0, s0, x, hck, _, _, _, _, _, _, _, hpw, hacc, hst, _, _, hkw, _, _, _, _, _, _, _, _, _, _, _, _ => by
    refine ⟨a0, s0, WExec.cast cap (WExec.whrF hck) ?_ (by omega)⟩
    have e : ({ x with ck := 0, pw := frame (binary x.m (powN p x.m v (k + 0))), acc := frame (binary x.m a0),
                       st := frame (binary x.m s0), kw := frame (binary x.lb (k + 0)),
                       ow := x.ow ++ pairs p x.m x.lb x.a v u tv epb bwb k 0 } : TSt) = x := by
      cases x
      simp only at hck hpw hacc hst hkw ⊢
      subst hck hpw hacc hst hkw
      simp [pairs]
    rw [e]
  | n + 1, k, a0, s0, x, hck, hm, hlbE, hepl, hbwl, ha, hfv, hfu, hpw, hacc, hst, htau, hpm, hkw, hbw, hep, hf, hns,
      htf, hs, hj, heph, hbwh, hcap, hO, hn => by
    obtain ⟨a1, s1, h1⟩ := kStep_spec cap x p v u tv a0 s0 k epb bwb hm hlbE hepl hbwl ha hfv hfu hpw hacc hst htau hpm
      hkw hbw hep hf hns htf hs hj heph hbwh hcap (by omega)
    obtain ⟨c1, hc1⟩ : ∃ b : Bool, b = coefBit (binary x.lb k) epb bwb x.lb x.a
        (binary x.m (fmulShift p x.m u (powN p x.m v (k + 1)))) (binary x.m tv) := ⟨_, rfl⟩
    rw [← hc1] at h1
    obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { x with pw := frame (binary x.m (powN p x.m v (k + 1))),
                                               acc := frame (binary x.m a1), st := frame (binary x.m s1),
                                               kw := frame (binary x.lb (k + 1)), ow := x.ow ++ [true, c1] } :=
      ⟨_, rfl⟩
    rw [← hx1] at h1
    have h2 := WExec.dec (cap := cap) gCK x1.w (by rw [hx1]; show x.ck ≤ cap; omega)
    rw [w_ck] at h2
    obtain ⟨x2, hx2⟩ : ∃ y : TSt, y = { x1 with ck := x1.w.val gCK - 1 } := ⟨_, rfl⟩
    rw [← hx2] at h2
    have hm2 : x2.m = x.m := by rw [hx2, hx1]
    have hlb2 : x2.lb = x.lb := by rw [hx2, hx1]
    have ha2 : x2.a = x.a := by rw [hx2, hx1]
    obtain ⟨a2, s2, ih⟩ := kLoop_spec p v u tv epb bwb n (k + 1) a1 s1 x2 (by rw [hx2, hx1]; show x.ck - 1 = n; omega)
      (by rw [hm2]; exact hm) (by rw [hlb2]; exact hlbE) hepl (by rw [hlb2]; exact hbwl) (by rw [hlb2, ha2]; exact ha)
      (by rw [hm2, hx2, hx1]; exact hfv) (by rw [hm2, hx2, hx1]; exact hfu) (by rw [hm2, hx2, hx1])
      (by rw [hm2, hx2, hx1]) (by rw [hm2, hx2, hx1]) (by rw [hm2, hx2, hx1]; exact htau)
      (by rw [hm2, hx2, hx1]; exact hpm) (by rw [hlb2, hx2, hx1]) (by rw [hx2, hx1]; exact hbw)
      (by rw [hx2, hx1]; exact hep) (by rw [hx2, hx1]; exact hf) (by rw [hx2, hx1]; exact hns)
      (by rw [hx2, hx1]; exact htf) (by rw [hx2, hx1]; exact hs) (by rw [hx2, hx1]; exact hj)
      (by rw [hx2, hx1]; exact heph) (by rw [hx2, hx1]; exact hbwh) (by rw [hlb2, hm2]; exact hcap)
      (by rw [hx2, hx1]; show (x.ow ++ [true, c1]).length + 2 * n + 2 < cap; simp; omega) (by omega)
    refine ⟨a2, s2, WExec.cast cap (WExec.whrT (by show x.ck ≠ 0; omega) (WExec.seq h1 h2) ih) ?_ ?_⟩
    · have e : ({ x2 with ck := 0, pw := frame (binary x2.m (powN p x2.m v (k + 1 + n))),
                          acc := frame (binary x2.m a2), st := frame (binary x2.m s2),
                          kw := frame (binary x2.lb (k + 1 + n)),
                          ow := x2.ow ++ pairs p x2.m x2.lb x2.a v u tv epb bwb (k + 1) n } : TSt) =
          { x with ck := 0, pw := frame (binary x.m (powN p x.m v (k + (n + 1)))), acc := frame (binary x.m a2),
                   st := frame (binary x.m s2), kw := frame (binary x.lb (k + (n + 1))),
                   ow := x.ow ++ pairs p x.m x.lb x.a v u tv epb bwb k (n + 1) } := by
        rw [hm2, hlb2, ha2, hx2, hx1, pairs_succ, hc1, show k + 1 + n = k + (n + 1) by omega]
        simp only [cbit, List.append_assoc]
      rw [e]
    · rw [hm2, hlb2, ha2]
      generalize kStepCost x.m x.lb x.a = K
      ring_nf
      omega

/-! ## The fields of a copy -/

theorem frameP_binary_split (r s n X : ℕ) (h : s + n ≤ r) :
    frameP (binary r X) = frameP (binary s X) ++ frameP (binary n (X / 2 ^ s)) ++
      frameP (binary (r - s - n) (X / 2 ^ (s + n))) := by
  have e1 := binary_add s (r - s) X
  have e2 := binary_add n (r - s - n) (X / 2 ^ s)
  rw [show s + (r - s) = r by omega] at e1
  rw [show n + (r - s - n) = r - s by omega, Nat.div_div_eq_div_mul, ← pow_add] at e2
  rw [e1, e2, frameP_append, frameP_append, List.append_assoc]

theorem binary_mod (n y : ℕ) : binary n (y % 2 ^ n) = binary n y :=
  binary_congr n _ _ (fun i hi => by rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and])

/-- Copy `n` bits of `V` (at its head) into the framed word on stream `A`. -/
theorem copyV_spec (A : Fin 12) (hA : A ≠ qV) (y : TSt) (r X s n : ℕ) (old restV restA : List Bool)
    (hV : y.vw = frameP (binary r X) ++ restV) (hvh : y.vh = 2 * s) (hsn : s + n ≤ r)
    (hAw : y.w.st A = frameP old ++ false :: restA) (hAh : y.w.sh A = 0) (hol : old.length = n)
    (hf : y.f = 0) (hcap : 1 ≤ cap) (hc2 : 2 * n ≤ cap) :
    WExec cap (mapPass copyOut keepS A qV gF gR) y.w
      ((y.w.sets A (frameP (binary n (X / 2 ^ s)) ++ false :: restA)).setv gF 0) (n * 41 + 3) := by
  have hsplit := frameP_binary_split r s n X hsn
  have h := mapPassAt_spec cap copyOut keepS A qV gF gR hA (by decide) hcap old (binary n (X / 2 ^ s)) []
    (frameP (binary s X)) restA (frameP (binary (r - s - n) (X / 2 ^ (s + n))) ++ restV) false y.w (by simp [hol])
    (by simpa using hAw) (by simpa using hAh) (by show y.vw = _; rw [hV, hsplit]; simp only [List.append_assoc])
    (by show y.vh = _; rw [hvh]; simp) (by show y.f = _; simp [hf]) rfl (by rw [hol]; exact hc2)
  rw [mapS_copy _ _ _ (by simp [hol]), hol] at h
  simpa using h

/-- Copy `n` bits of `V` (at its head) into a framed word on stream `A` after a prefix. -/
theorem copyVAt_spec (A : Fin 12) (hA : A ≠ qV) (y : TSt) (r X s n : ℕ) (preA old restV restA : List Bool)
    (hV : y.vw = frameP (binary r X) ++ restV) (hvh : y.vh = 2 * s) (hsn : s + n ≤ r)
    (hAw : y.w.st A = preA ++ frameP old ++ false :: restA) (hAh : y.w.sh A = preA.length) (hol : old.length = n)
    (hf : y.f = 0) (hcap : 1 ≤ cap) (hc2 : 2 * n ≤ cap) :
    WExec cap (mapPass copyOut keepS A qV gF gR) y.w
      ((y.w.sets A (preA ++ frameP (binary n (X / 2 ^ s)) ++ false :: restA)).setv gF 0) (n * 41 + 3) := by
  have hsplit := frameP_binary_split r s n X hsn
  have h := mapPassAt_spec cap copyOut keepS A qV gF gR hA (by decide) hcap old (binary n (X / 2 ^ s)) preA
    (frameP (binary s X)) restA (frameP (binary (r - s - n) (X / 2 ^ (s + n))) ++ restV) false y.w (by simp [hol])
    hAw hAh (by show y.vw = _; rw [hV, hsplit]; simp only [List.append_assoc])
    (by show y.vh = _; rw [hvh]; simp) (by show y.f = _; simp [hf]) rfl (by rw [hol]; exact hc2)
  rw [mapS_copy _ _ _ (by simp [hol]), hol] at h
  simpa using h

/-- `v` and `u`. -/
def cVU : TProg :=
  .seq (mapPass copyOut keepS qFV qV gF gR) (.seq (advC qV gM gT gVP)
    (.seq (mapPass copyOut keepS qFU qV gF gR) (advC qV gM gT gVP)))

theorem cVU_spec (y : TSt) (r X d : ℕ) (fv0 fu0 : ℕ) (restV : List Bool)
    (hV : y.vw = frameP (binary r X) ++ restV) (hvh : y.vh = 2 * d) (hdr : d + 2 * y.m ≤ r)
    (hfv : y.fv = frame (binary y.m fv0)) (hfu : y.fu = frame (binary y.m fu0)) (hf : y.f = 0)
    (hcap : 2 * r + 2 * y.m + 2 ≤ cap) :
    WExec cap cVU y.w { y with fv := frame (binary y.m (X / 2 ^ d % 2 ^ y.m)),
                               fu := frame (binary y.m (X / 2 ^ (d + y.m) % 2 ^ y.m)),
                               vh := 2 * d + 2 * y.m + 2 * y.m }.w
      (2 * (y.m * 41 + 3) + 2 * (26 * y.m + 3) + 3) := by
  have s1 := copyV_spec cap qFV (by decide) y r X d y.m (binary y.m fv0) restV [] hV hvh (by omega)
    (by show y.fv = _; rw [hfv, frame_bin]) rfl (by simp) hf (by omega) (by omega)
  rw [w_fv, w_f] at s1
  obtain ⟨x1, hx1⟩ : ∃ z : TSt, z = { { y with fv := frameP (binary y.m (X / 2 ^ d)) ++ false :: [] } with f := 0 } :=
    ⟨_, rfl⟩
  rw [← hx1] at s1
  have s2 := advC_spec cap qV gM gT gVP (by decide) (by decide) (by decide) y.m x1.w (by rw [hx1]; rfl)
    (by rw [hx1]; rfl) (by omega) (by rw [hx1]; show y.vh + 2 * y.m ≤ cap; omega)
  rw [w_v_adv] at s2
  obtain ⟨x2, hx2⟩ : ∃ z : TSt, z = { x1 with vh := x1.vh + 2 * y.m } := ⟨_, rfl⟩
  rw [← hx2] at s2
  have s3 := copyV_spec cap qFU (by decide) x2 r X (d + y.m) y.m (binary y.m fu0) restV []
    (by rw [hx2, hx1]; exact hV) (by rw [hx2, hx1]; show y.vh + 2 * y.m = _; omega) (by omega)
    (by rw [hx2, hx1]; show y.fu = _; rw [hfu, frame_bin]) (by rw [hx2]; rfl) (by simp) (by rw [hx2, hx1]) (by omega)
    (by omega)
  rw [w_fu, w_f] at s3
  obtain ⟨x3, hx3⟩ : ∃ z : TSt, z = { { x2 with fu := frameP (binary y.m (X / 2 ^ (d + y.m))) ++ false :: [] } with
                                                f := 0 } := ⟨_, rfl⟩
  rw [← hx3] at s3
  have s4 := advC_spec cap qV gM gT gVP (by decide) (by decide) (by decide) y.m x3.w (by rw [hx3, hx2, hx1]; rfl)
    (by rw [hx3]; rfl) (by omega) (by rw [hx3, hx2, hx1]; show y.vh + 2 * y.m + 2 * y.m ≤ cap; omega)
  rw [w_v_adv] at s4
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ (by omega)
  rw [hx3, hx2, hx1, binary_mod, binary_mod, ← frame_bin, ← frame_bin, hvh]
  cases y
  simp only at hf ⊢
  subst hf
  rfl

/-- The Toeplitz translation. -/
def cBW : TProg := .seq (mapPass copyOut keepS qBW qV gF gR) (advC qV gLB gT gVP)

theorem cBW_spec (y : TSt) (r X d bw0 : ℕ) (restV : List Bool)
    (hV : y.vw = frameP (binary r X) ++ restV) (hvh : y.vh = 2 * d) (hdr : d + y.lb ≤ r)
    (hbw : y.bw = frame (binary y.lb bw0)) (hbwh : y.bwh = 0) (hf : y.f = 0) (hcap : 2 * r + 2 * y.lb + 2 ≤ cap) :
    WExec cap cBW y.w { y with bw := frame (binary y.lb (X / 2 ^ d)), vh := 2 * d + 2 * y.lb }.w
      (y.lb * 41 + 3 + 26 * y.lb + 4) := by
  have s1 := copyV_spec cap qBW (by decide) y r X d y.lb (binary y.lb bw0) restV [] hV hvh hdr
    (by show y.bw = _; rw [hbw, frame_bin]) hbwh (by simp) hf (by omega) (by omega)
  rw [w_bw, w_f] at s1
  obtain ⟨x1, hx1⟩ : ∃ z : TSt, z = { { y with bw := frameP (binary y.lb (X / 2 ^ d)) ++ false :: [] } with f := 0 } :=
    ⟨_, rfl⟩
  rw [← hx1] at s1
  have s2 := advC_spec cap qV gLB gT gVP (by decide) (by decide) (by decide) y.lb x1.w (by rw [hx1]; rfl)
    (by rw [hx1]; rfl) (by omega) (by rw [hx1]; show y.vh + 2 * y.lb ≤ cap; omega)
  rw [w_v_adv] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by omega)
  rw [hx1, ← frame_bin, hvh]
  cases y
  simp only at hf ⊢
  subst hf
  rfl

theorem w_rev (x : TSt) (E : List Bool) (n : ℕ) :
    ((((((x.w.sets qEP E).seth qEP 0).seth qV n).setv gJ 0).setv gVP n).setv gEP 0) =
      { x with ep := E, eph := 0, vh := n, j := 0 }.w := by
  tst_eq

/-- The diagonals: the strict upper ones in place, the main and lower ones reversed in front. -/
def cEP : TProg :=
  .seq (advC qEP gLB gT gEP) (.seq (mapPass copyOut keepS qEP qV gF gR) (.seq (retC qEP gLB gT gEP)
    (.seq (advC qV gLB1 gT gVP) (.seq (advC qEP gLB1 gT gEP) (.seq (Hash4.wcopyR gLB gJ gT)
    (.seq (revLoop qEP qV gJ gVP) (WM.clear gEP)))))))

/-- The diagonal word of a copy whose strict upper diagonals start at bit `d`. -/
def epOf (lb X d : ℕ) : List Bool := (binary lb (X / 2 ^ (d + (lb - 1)))).reverse ++ binary (lb - 1) (X / 2 ^ d)

theorem epOf_length (lb X d : ℕ) : (epOf lb X d).length = lb + (lb - 1) := by simp [epOf]

theorem cEP_spec (y : TSt) (r X d : ℕ) (epOld restV : List Bool)
    (hV : y.vw = frameP (binary r X) ++ restV) (hvh : y.vh = 2 * d) (hdr : d + (y.lb - 1) + y.lb ≤ r)
    (hep : y.ep = frame epOld) (hepl : epOld.length = y.lb + (y.lb - 1)) (hlb : 1 ≤ y.lb)
    (heph : y.eph = 0) (hj : y.j = 0) (hf : y.f = 0) (hcap : 2 * r + 4 * y.lb + 4 ≤ cap) :
    WExec cap cEP y.w { y with ep := frame (epOf y.lb X d), vh := 2 * d + 2 * (y.lb - 1) + 2 * y.lb }.w
      (200 * y.lb + 60) := by
  -- 1: EP to the upper diagonals
  have s1 := advC_spec cap qEP gLB gT gEP (by decide) (by decide) (by decide) y.lb y.w rfl rfl (by omega)
    (by show y.eph + 2 * y.lb ≤ cap; omega)
  rw [w_ep_adv] at s1
  obtain ⟨x1, hx1⟩ : ∃ z : TSt, z = { y with eph := y.eph + 2 * y.lb } := ⟨_, rfl⟩
  rw [← hx1] at s1
  -- 2: copy the upper diagonals
  have hsplitE : frameP epOld = frameP (epOld.take y.lb) ++ frameP (epOld.drop y.lb) := frameP_split epOld y.lb
  have s2 := copyVAt_spec cap qEP (by decide) x1 r X d (y.lb - 1) (frameP (epOld.take y.lb)) (epOld.drop y.lb)
    restV [] (by rw [hx1]; exact hV) (by rw [hx1]; exact hvh) (by omega)
    (by rw [hx1]; show y.ep = _; rw [hep, frame_eq_frameP, hsplitE])
    (by rw [hx1]; show y.eph + 2 * y.lb = _; simp [frameP_length]; omega) (by simp [hepl])
    (by rw [hx1]; exact hf) (by omega) (by omega)
  rw [w_ep, w_f] at s2
  obtain ⟨x2, hx2⟩ : ∃ z : TSt, z = { { x1 with ep := frameP (epOld.take y.lb) ++
                                                frameP (binary (y.lb - 1) (X / 2 ^ d)) ++ false :: [] } with
                                                f := 0 } := ⟨_, rfl⟩
  rw [← hx2] at s2
  -- 3: EP back
  have s3 := retC_spec cap qEP gLB gT gEP (by decide) (by decide) (by decide) y.lb x2.w (by rw [hx2, hx1]; rfl)
    (by rw [hx2]; rfl) (by omega) (by rw [hx2, hx1]; show y.eph + 2 * y.lb ≤ cap; omega)
  rw [w_ep_ret] at s3
  obtain ⟨x3, hx3⟩ : ∃ z : TSt, z = { x2 with eph := x2.eph - 2 * y.lb } := ⟨_, rfl⟩
  rw [← hx3] at s3
  -- 4: V to the main and lower diagonals
  have s4 := advC_spec cap qV gLB1 gT gVP (by decide) (by decide) (by decide) (y.lb - 1) x3.w
    (by rw [hx3, hx2, hx1]; rfl) (by rw [hx3]; rfl) (by omega) (by rw [hx3, hx2, hx1]; show y.vh + 2 * (y.lb - 1) ≤ cap; omega)
  rw [w_v_adv] at s4
  obtain ⟨x4, hx4⟩ : ∃ z : TSt, z = { x3 with vh := x3.vh + 2 * (y.lb - 1) } := ⟨_, rfl⟩
  rw [← hx4] at s4
  -- 5: EP to its bit ℓ − 1
  have s5 := advC_spec cap qEP gLB1 gT gEP (by decide) (by decide) (by decide) (y.lb - 1) x4.w
    (by rw [hx4, hx3, hx2, hx1]; rfl) (by rw [hx4]; rfl) (by omega)
    (by rw [hx4, hx3, hx2, hx1]; show y.eph + 2 * y.lb - 2 * y.lb + 2 * (y.lb - 1) ≤ cap; omega)
  rw [w_ep_adv] at s5
  obtain ⟨x5, hx5⟩ : ∃ z : TSt, z = { x4 with eph := x4.eph + 2 * (y.lb - 1) } := ⟨_, rfl⟩
  rw [← hx5] at s5
  -- 6: J := ℓ
  have s6 := Hash4.wcopyR_spec cap gLB gJ gT (by decide) (by decide) (by decide) x5.w
    (by rw [hx5, hx4, hx3, hx2, hx1]; exact hj) (by rw [hx5]; rfl) (by rw [hx5, hx4, hx3, hx2, hx1]; show y.lb ≤ cap; omega)
  rw [w_j] at s6
  obtain ⟨x6, hx6⟩ : ∃ z : TSt, z = { x5 with j := x5.w.val gLB } := ⟨_, rfl⟩
  rw [← hx6] at s6
  -- 7: the reversal
  have hEP6 : x6.w.st qEP = frameP (epOld.take y.lb ++ binary (y.lb - 1) (X / 2 ^ d)) ++ [false] := by
    rw [hx6, hx5, hx4, hx3, hx2]; show _ ++ _ ++ _ = _; rw [frameP_append]
  have hsplitV := frameP_binary_split r (d + (y.lb - 1)) y.lb X (by omega)
  obtain ⟨τ, hτ, h1, h2, h3, h4, h5, h6, hfr⟩ := revLoop_spec cap qEP qV gJ gVP (by decide) (by decide) y.lb
    (epOld.take y.lb ++ binary (y.lb - 1) (X / 2 ^ d)) (binary y.lb (X / 2 ^ (d + (y.lb - 1))))
    (frameP (binary (d + (y.lb - 1)) X)) [false]
    (frameP (binary (r - (d + (y.lb - 1)) - y.lb) (X / 2 ^ (d + (y.lb - 1) + y.lb))) ++ restV) x6.w
    (by rw [hx6, hx5, hx4, hx3, hx2, hx1]; rfl) (by simp [hepl]) (by simp) hEP6
    (by rw [hx6, hx5, hx4, hx3, hx2, hx1]; show y.eph + 2 * y.lb - 2 * y.lb + 2 * (y.lb - 1) = _; omega)
    (by rw [hx6, hx5, hx4, hx3, hx2, hx1]; show y.vw = _; rw [hV, hsplitV]; simp only [List.append_assoc])
    (by rw [hx6, hx5, hx4, hx3, hx2, hx1]; show y.vh + 2 * (y.lb - 1) = _; simp [frameP_length]; omega)
    (by rw [hx6, hx5, hx4, hx3, hx2, hx1]; show y.vh + 2 * (y.lb - 1) + 2 * y.lb ≤ cap; omega) (by omega)
  -- 8: clear the EP counter
  have hEPv : τ.val gEP = 2 * (y.lb - 1) := by
    rw [hfr.2.1 gEP (by decide)]
    rw [hx6, hx5, hx4, hx3, hx2, hx1]; show y.eph + 2 * y.lb - 2 * y.lb + 2 * (y.lb - 1) = _; omega
  have s8 := wclear_spec cap gEP (2 * (y.lb - 1)) τ hEPv (by omega)
  have hL5 : x5.w.val gLB = y.lb := by rw [hx5, hx4, hx3, hx2, hx1]; rfl
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq hτ s8))))))) ?_ (by omega)
  -- the final state
  have hrev : (binary y.lb (X / 2 ^ (d + (y.lb - 1)))).take y.lb = binary y.lb (X / 2 ^ (d + (y.lb - 1))) := by
    simp
  have hdrop : (epOld.take y.lb ++ binary (y.lb - 1) (X / 2 ^ d)).drop y.lb = binary (y.lb - 1) (X / 2 ^ d) := by
    rw [List.drop_append_of_le_length (by simp [hepl]), List.drop_eq_nil_of_le (by simp [hepl])]
    simp
  rw [hrev, hdrop] at h1
  have hvh6 : x6.vh = 2 * d + 2 * (y.lb - 1) := by rw [hx6, hx5, hx4, hx3, hx2, hx1]; show y.vh + _ = _; rw [hvh]
  have hτ_eq : τ = (((((x6.w.sets qEP (frame (epOf y.lb X d))).seth qEP 0).seth qV (x6.vh + 2 * y.lb)).setv gJ 0).setv
      gVP (x6.vh + 2 * y.lb)) := by
    refine WState.eq ?_ ?_ ?_ ?_
    · funext i
      simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      by_cases hiV : i = qV
      · subst hiV; rw [if_pos rfl, h4]; simp [frameP_length]; omega
      · rw [if_neg hiV]
        by_cases hiE : i = qEP
        · subst hiE; rw [if_pos rfl, h2]
        · rw [if_neg hiE, (hfr.1 i (by rintro (h | h) <;> contradiction)).2]
    · funext i
      simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      by_cases hiE : i = qEP
      · subst hiE; rw [if_pos rfl, h1, frame_eq_frameP]; rfl
      · rw [if_neg hiE]
        by_cases hiV : i = qV
        · subst hiV; exact h3
        · exact (hfr.1 i (by rintro (h | h) <;> contradiction)).1
    · funext q
      simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      by_cases hqP : q = gVP
      · subst hqP; rw [if_pos rfl, h5]; rfl
      · rw [if_neg hqP]
        by_cases hqJ : q = gJ
        · subst hqJ; rw [if_pos rfl, h6]
        · rw [if_neg hqJ, hfr.2.1 q (by rintro (h | h) <;> contradiction)]
    · exact hfr.2.2
  rw [hτ_eq, w_rev]
  have e : ({ x6 with ep := frame (epOf y.lb X d), eph := 0, vh := x6.vh + 2 * y.lb, j := 0 } : TSt) =
      { y with ep := frame (epOf y.lb X d), vh := 2 * d + 2 * (y.lb - 1) + 2 * y.lb } := by
    rw [hvh6, hx6, hx5, hx4, hx3, hx2, hx1]
    cases y
    simp only at heph hj hf ⊢
    subst heph hj hf
    rfl
  rw [e]

theorem mapS_one_state (as bs : List Bool) (h : as.length = bs.length) (h1 : 1 ≤ as.length) :
    (mapS oneOut oneNxt as bs true).2 = false := by
  obtain ⟨a, as', rfl⟩ : ∃ a as', as = a :: as' := by
    cases as with
    | nil => simp at h1
    | cons a as' => exact ⟨a, as', rfl⟩
  obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
    cases bs with
    | nil => simp at h
    | cons b bs' => exact ⟨b, bs', rfl⟩
  simp only [mapS, oneNxt, mapS_zero_state as' bs' (by simpa using h)]

theorem w_o_emit' (x : TSt) (b : Bool) :
    ((x.w.sets qO (x.w.st qO ++ [b])).seth qO (x.w.sh qO + 1)).setv gOP (x.w.val gOP + 1) =
      { x with ow := x.ow ++ [b] }.w := w_o_emit x b

/-- Start a copy: the marker, `K := 0`, `PW := 1`, `CK := L`. -/
def cInit : TProg :=
  .seq (emitC qO gOP true) (.seq (mapPass zeroOut keepS qK qBW gF gR) (.seq (setFlag gF true)
    (.seq (mapPass oneOut oneNxt qPW qFV gF gR) (Hash4.wcopyR gL gCK gT))))

theorem cInit_spec (y : TSt) (kw0 bw0 pw0 fv0 : ℕ) (hm : 1 ≤ y.m)
    (hkw : y.kw = frame (binary y.lb kw0)) (hbw : y.bw = frame (binary y.lb bw0)) (hpw : y.pw = frame (binary y.m pw0))
    (hfv : y.fv = frame (binary y.m fv0)) (hf : y.f = 0) (hck : y.ck = 0) (hbwh : y.bwh = 0)
    (hcap : 2 * y.lb + 2 * y.m + y.L + 2 ≤ cap) (hO : y.ow.length + 1 < cap) :
    WExec cap cInit y.w { y with ow := y.ow ++ [true], kw := frame (binary y.lb 0), pw := frame (binary y.m 1),
                                 ck := y.L }.w (y.lb * 41 + y.m * 41 + 18 * y.L + 26) := by
  have s1 := emitC_spec cap qO gOP true y.w rfl (by show y.ow.length < cap; omega)
  rw [w_o_emit] at s1
  obtain ⟨x1, hx1⟩ : ∃ z : TSt, z = { y with ow := y.ow ++ [true] } := ⟨_, rfl⟩
  rw [← hx1] at s1
  have s2 := mapPass_spec cap zeroOut keepS qK qBW gF gR (by decide) (by decide) (by omega)
    (binary y.lb kw0) (binary y.lb bw0) [] [false] false x1.w (by simp)
    (by rw [hx1]; show y.kw = _; rw [hkw, frame_bin]) rfl (by rw [hx1]; show y.bw = _; rw [hbw, frame_bin])
    (by rw [hx1]; exact hbwh) (by rw [hx1]; show y.f = _; simp [hf]) rfl (by simp; omega)
  rw [mapS_zero _ _ _ (by simp), binary_length, ← binary_zero', w_kw, w_f] at s2
  obtain ⟨x2, hx2⟩ : ∃ z : TSt, z = { { x1 with kw := frameP (binary y.lb 0) ++ false :: [] } with
                                                f := (false).toNat } := ⟨_, rfl⟩
  rw [← hx2] at s2
  have s3 := setFlag_spec cap gF true false x2.w (by rw [hx2]; rfl) (by omega)
  rw [w_f] at s3
  obtain ⟨x3, hx3⟩ : ∃ z : TSt, z = { x2 with f := (true).toNat } := ⟨_, rfl⟩
  rw [← hx3] at s3
  have s4 := mapPass_spec cap oneOut oneNxt qPW qFV gF gR (by decide) (by decide) (by omega)
    (binary y.m pw0) (binary y.m fv0) [] [false] true x3.w (by simp)
    (by rw [hx3, hx2, hx1]; show y.pw = _; rw [hpw, frame_bin]) rfl
    (by rw [hx3, hx2, hx1]; show y.fv = _; rw [hfv, frame_bin]) rfl (by rw [hx3]; rfl) rfl (by simp; omega)
  rw [mapS_one _ _ (by simp) (by simp; omega), mapS_one_state _ _ (by simp) (by simp; omega), binary_length,
    w_pw, w_f] at s4
  obtain ⟨x4, hx4⟩ : ∃ z : TSt, z = { { x3 with pw := frameP (binary y.m 1) ++ false :: [] } with
                                                f := (false).toNat } := ⟨_, rfl⟩
  rw [← hx4] at s4
  have s5 := Hash4.wcopyR_spec cap gL gCK gT (by decide) (by decide) (by decide) x4.w
    (by rw [hx4, hx3, hx2, hx1]; exact hck) (by rw [hx4]; rfl) (by rw [hx4, hx3, hx2, hx1]; show y.L ≤ cap; omega)
  rw [w_ck] at s5
  have hL4 : x4.w.val gL = y.L := by rw [hx4, hx3, hx2, hx1]; rfl
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (by omega)
  have e : ({ x4 with ck := y.L } : TSt) = { y with ow := y.ow ++ [true], kw := frame (binary y.lb 0),
                                                    pw := frame (binary y.m 1), ck := y.L } := by
    rw [frame_bin y.lb 0, frame_bin y.m 1, hx4, hx3, hx2, hx1]
    cases y
    simp only at hf ⊢
    subst hf
    rfl
  rw [hL4, e]

theorem pairs_zero_eq (p m lb a v u tv : ℕ) (epb bwb : List Bool) (L : ℕ) :
    pairs p m lb a v u tv epb bwb 0 L = frameP ((List.range L).map (cbit p m lb a v u tv epb bwb)) := by
  simp [pairs, frameP, List.range'_eq_map_range, List.flatMap_map]

/-- **One copy**: the fields, the start, all coordinates, the end marker. -/
def copyT : TProg := .seq cVU (.seq cBW (.seq cEP (.seq cInit (.seq kLoop (emitC qO gOP false)))))

/-- The width of one copy seed in the builder's registers. -/
def wOf (m lb : ℕ) : ℕ := 2 * m + lb + (lb - 1) + lb

/-- The cost of one copy. -/
def copyCost (m lb a L : ℕ) : ℕ :=
  (2 * (m * 41 + 3) + 2 * (26 * m + 3) + 3) + 1 + ((lb * 41 + 3 + 26 * lb + 4) + 1 + ((200 * lb + 60) + 1 +
    ((lb * 41 + m * 41 + 18 * L + 26) + 1 + ((L * (kStepCost m lb a + 4) + 1) + 1 + 7))))

/-- The coefficient word of the copy whose seed starts at bit `d` of the vertex word. -/
def coefOf (p m lb a tv X d L : ℕ) : List Bool :=
  (List.range L).map (cbit p m lb a (X / 2 ^ d % 2 ^ m) (X / 2 ^ (d + m) % 2 ^ m) tv (epOf lb X (d + 2 * m + lb))
    (binary lb (X / 2 ^ (d + 2 * m))))

theorem copyT_spec (y : TSt) (r X d p tv fv0 fu0 pw0 a0 s0 kw0 bw0 : ℕ) (epOld restV : List Bool)
    (hV : y.vw = frameP (binary r X) ++ restV) (hvh : y.vh = 2 * d) (hdr : d + wOf y.m y.lb ≤ r)
    (hm : 1 ≤ y.m) (hlb : 1 ≤ y.lb) (ha : y.a ≤ y.lb)
    (hfv : y.fv = frame (binary y.m fv0)) (hfu : y.fu = frame (binary y.m fu0)) (hpw : y.pw = frame (binary y.m pw0))
    (hacc : y.acc = frame (binary y.m a0)) (hst : y.st = frame (binary y.m s0))
    (hkw : y.kw = frame (binary y.lb kw0)) (hbw : y.bw = frame (binary y.lb bw0))
    (hep : y.ep = frame epOld) (hepl : epOld.length = y.lb + (y.lb - 1))
    (htau : y.tauw = frame (binary y.m tv)) (hpm : y.pmw = frame (binary y.m p))
    (hf : y.f = 0) (hns : y.ns = 0) (htf : y.tf = 0) (hs : y.s = 0) (hj : y.j = 0) (heph : y.eph = 0)
    (hbwh : y.bwh = 0) (hck : y.ck = 0)
    (hcap : 2 * r + 4 * y.lb + 2 * y.m + y.L + 10 ≤ cap) (hO : y.ow.length + 2 * y.L + 4 < cap) :
    ∃ a1 s1 : ℕ, WExec cap copyT y.w
      { y with vh := 2 * (d + wOf y.m y.lb), ow := y.ow ++ copyWord (coefOf p y.m y.lb y.a tv X d y.L),
               fv := frame (binary y.m (X / 2 ^ d % 2 ^ y.m)), fu := frame (binary y.m (X / 2 ^ (d + y.m) % 2 ^ y.m)),
               pw := frame (binary y.m (powN p y.m (X / 2 ^ d % 2 ^ y.m) y.L)), acc := frame (binary y.m a1),
               st := frame (binary y.m s1), kw := frame (binary y.lb y.L),
               bw := frame (binary y.lb (X / 2 ^ (d + 2 * y.m))), ep := frame (epOf y.lb X (d + 2 * y.m + y.lb)) }.w
      (copyCost y.m y.lb y.a y.L) := by
  unfold wOf at hdr
  -- the fields
  have h1 := cVU_spec cap y r X d fv0 fu0 restV hV hvh (by omega) hfv hfu hf (by omega)
  obtain ⟨FV, hFV⟩ : ∃ l : List Bool, l = frame (binary y.m (X / 2 ^ d % 2 ^ y.m)) := ⟨_, rfl⟩
  obtain ⟨FU, hFU⟩ : ∃ l : List Bool, l = frame (binary y.m (X / 2 ^ (d + y.m) % 2 ^ y.m)) := ⟨_, rfl⟩
  rw [← hFV, ← hFU] at h1
  obtain ⟨x1, hx1⟩ : ∃ z : TSt, z = { y with fv := FV, fu := FU, vh := 2 * d + 2 * y.m + 2 * y.m } := ⟨_, rfl⟩
  rw [← hx1] at h1
  have hlb1 : x1.lb = y.lb := by rw [hx1]
  have h2 := cBW_spec cap x1 r X (d + 2 * y.m) bw0 restV (by rw [hx1]; exact hV)
    (by rw [hx1]; show 2 * d + 2 * y.m + 2 * y.m = _; omega) (by rw [hlb1]; omega)
    (by rw [hlb1, hx1]; exact hbw) (by rw [hx1]; exact hbwh) (by rw [hx1]; exact hf) (by rw [hlb1]; omega)
  obtain ⟨BW, hBW⟩ : ∃ l : List Bool, l = frame (binary x1.lb (X / 2 ^ (d + 2 * y.m))) := ⟨_, rfl⟩
  rw [← hBW] at h2
  rw [hlb1] at hBW
  obtain ⟨x2, hx2⟩ : ∃ z : TSt, z = { x1 with bw := BW, vh := 2 * (d + 2 * y.m) + 2 * x1.lb } := ⟨_, rfl⟩
  rw [← hx2] at h2
  have hlb2 : x2.lb = y.lb := by rw [hx2]; exact hlb1
  have h3 := cEP_spec cap x2 r X (d + 2 * y.m + y.lb) epOld restV (by rw [hx2, hx1]; exact hV)
    (by rw [hx2]; show 2 * (d + 2 * y.m) + 2 * x1.lb = _; rw [hlb1]; omega) (by rw [hlb2]; omega) (by rw [hx2, hx1]; exact hep) (by rw [hlb2]; exact hepl)
    (by rw [hlb2]; exact hlb) (by rw [hx2, hx1]; exact heph) (by rw [hx2, hx1]; exact hj) (by rw [hx2, hx1]; exact hf)
    (by rw [hlb2]; omega)
  obtain ⟨EP, hEP⟩ : ∃ l : List Bool, l = frame (epOf x2.lb X (d + 2 * y.m + y.lb)) := ⟨_, rfl⟩
  rw [← hEP] at h3
  rw [hlb2] at hEP
  obtain ⟨x3, hx3⟩ : ∃ z : TSt, z = { x2 with ep := EP,
                                              vh := 2 * (d + 2 * y.m + y.lb) + 2 * (x2.lb - 1) + 2 * x2.lb } := ⟨_, rfl⟩
  rw [← hx3] at h3
  have hlb3 : x3.lb = y.lb := by rw [hx3]; exact hlb2
  have hm3 : x3.m = y.m := by rw [hx3, hx2, hx1]
  have hL3 : x3.L = y.L := by rw [hx3, hx2, hx1]
  -- the start
  have h4 := cInit_spec cap x3 kw0 (X / 2 ^ (d + 2 * y.m)) pw0 (X / 2 ^ d % 2 ^ y.m) (by rw [hm3]; exact hm)
    (by rw [hlb3, hx3, hx2, hx1]; exact hkw) (by rw [hlb3, hx3, hx2, hBW]) (by rw [hm3, hx3, hx2, hx1]; exact hpw)
    (by rw [hm3, hx3, hx2, hx1, hFV]) (by rw [hx3, hx2, hx1]; exact hf) (by rw [hx3, hx2, hx1]; exact hck)
    (by rw [hx3, hx2, hx1]; exact hbwh) (by rw [hlb3, hm3, hL3]; omega)
    (by rw [hx3, hx2, hx1]; show y.ow.length + 1 < cap; omega)
  obtain ⟨K0, hK0⟩ : ∃ l : List Bool, l = frame (binary x3.lb 0) := ⟨_, rfl⟩
  obtain ⟨P0, hP0⟩ : ∃ l : List Bool, l = frame (binary x3.m 1) := ⟨_, rfl⟩
  rw [← hK0, ← hP0] at h4
  rw [hlb3] at hK0
  rw [hm3] at hP0
  obtain ⟨x4, hx4⟩ : ∃ z : TSt, z = { x3 with ow := x3.ow ++ [true], kw := K0, pw := P0, ck := x3.L } := ⟨_, rfl⟩
  rw [← hx4] at h4
  have hm4 : x4.m = y.m := by rw [hx4]; exact hm3
  have hlb4 : x4.lb = y.lb := by rw [hx4]; exact hlb3
  have ha4 : x4.a = y.a := by rw [hx4, hx3, hx2, hx1]
  have hL4 : x4.L = y.L := by rw [hx4]; exact hL3
  have how4 : x4.ow = y.ow ++ [true] := by rw [hx4, hx3, hx2, hx1]
  -- all coordinates
  have hepE : (epOf y.lb X (d + 2 * y.m + y.lb)).length = y.lb + (y.lb - 1) := epOf_length _ _ _
  obtain ⟨a1, s1, h5⟩ := kLoop_spec cap p (X / 2 ^ d % 2 ^ y.m) (X / 2 ^ (d + y.m) % 2 ^ y.m) tv
    (epOf y.lb X (d + 2 * y.m + y.lb)) (binary y.lb (X / 2 ^ (d + 2 * y.m))) y.L 0 a0 s0 x4
    (by rw [hx4, hL3]) (by rw [hm4]; exact hm) (by rw [hlb4, hepE]; omega) (by rw [hepE]; omega)
    (by rw [hlb4]; simp) (by rw [hlb4, ha4]; exact ha) (by rw [hm4, hx4, hx3, hx2, hx1, hFV])
    (by rw [hm4, hx4, hx3, hx2, hx1, hFU]) (by rw [hm4, hx4, hP0]; rfl) (by rw [hm4, hx4, hx3, hx2, hx1]; exact hacc)
    (by rw [hm4, hx4, hx3, hx2, hx1]; exact hst) (by rw [hm4, hx4, hx3, hx2, hx1]; exact htau)
    (by rw [hm4, hx4, hx3, hx2, hx1]; exact hpm) (by rw [hlb4, hx4, hK0]) (by rw [hx4, hx3, hx2, hBW])
    (by rw [hx4, hx3, hEP]) (by rw [hx4, hx3, hx2, hx1]; exact hf) (by rw [hx4, hx3, hx2, hx1]; exact hns)
    (by rw [hx4, hx3, hx2, hx1]; exact htf) (by rw [hx4, hx3, hx2, hx1]; exact hs) (by rw [hx4, hx3, hx2, hx1]; exact hj)
    (by rw [hx4, hx3, hx2, hx1]; exact heph) (by rw [hx4, hx3, hx2, hx1]; exact hbwh) (by rw [hlb4, hm4]; omega)
    (by rw [how4]; simp; omega) (by omega)
  obtain ⟨PW5, hPW5⟩ : ∃ l : List Bool, l = frame (binary x4.m (powN p x4.m (X / 2 ^ d % 2 ^ y.m) (0 + y.L))) :=
    ⟨_, rfl⟩
  obtain ⟨A5, hA5⟩ : ∃ l : List Bool, l = frame (binary x4.m a1) := ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ l : List Bool, l = frame (binary x4.m s1) := ⟨_, rfl⟩
  obtain ⟨K5, hK5⟩ : ∃ l : List Bool, l = frame (binary x4.lb (0 + y.L)) := ⟨_, rfl⟩
  obtain ⟨PR, hPR⟩ : ∃ l : List Bool, l = pairs p x4.m x4.lb x4.a (X / 2 ^ d % 2 ^ y.m) (X / 2 ^ (d + y.m) % 2 ^ y.m)
      tv (epOf y.lb X (d + 2 * y.m + y.lb)) (binary y.lb (X / 2 ^ (d + 2 * y.m))) 0 y.L := ⟨_, rfl⟩
  rw [← hPW5, ← hA5, ← hS5, ← hK5, ← hPR] at h5
  rw [hm4] at hPW5 hA5 hS5
  rw [hlb4] at hK5
  rw [hm4, hlb4, ha4, pairs_zero_eq] at hPR
  obtain ⟨x5, hx5⟩ : ∃ z : TSt, z = { x4 with ck := 0, pw := PW5, acc := A5, st := S5, kw := K5, ow := x4.ow ++ PR } :=
    ⟨_, rfl⟩
  rw [← hx5] at h5
  -- the end marker
  have h6 := emitC_spec cap qO gOP false x5.w rfl
    (by rw [hx5, how4, hPR]; show (y.ow ++ [true] ++ _).length < cap; simp [frameP_length]; omega)
  rw [w_o_emit] at h6
  refine ⟨a1, s1, WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 h6)))))
    ?_ ?_⟩
  · have e : ({ x5 with ow := x5.ow ++ [false] } : TSt) =
        { y with vh := 2 * (d + wOf y.m y.lb), ow := y.ow ++ copyWord (coefOf p y.m y.lb y.a tv X d y.L),
                 fv := FV, fu := FU, pw := PW5, acc := A5, st := S5, kw := K5, bw := BW, ep := EP } := by
      rw [hx5, hx4, hx3, hx2, hx1]
      cases y
      simp only at hck hlb ⊢
      subst hck
      simp only [TSt.mk.injEq, and_true, true_and, hPR, copyWord, coefOf, frame_eq_frameP, wOf, List.append_assoc,
        List.cons_append, List.nil_append]
      omega
    rw [e, hFV, hFU, hPW5, hA5, hS5, hK5, hBW, hEP, Nat.zero_add]
  · rw [hm4, hlb4, ha4, hlb3, hm3, hL3, hlb1] at *
    unfold copyCost
    omega

end NearCubicWires.WireExponent3_5.FinalPass.Filt
