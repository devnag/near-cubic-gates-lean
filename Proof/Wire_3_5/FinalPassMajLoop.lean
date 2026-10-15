import Proof.Wire_3_5.FinalPassMajVisit

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Maj
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.ListEval NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.SupplierWalk

variable (cap : ℕ)

/-! ## The compared state on stream 2 -/

def fwdSS : MProg := WM.fwdC sSS mSP

theorem fwdSS_spec (x : MSt) (h : x.ssh < cap) : WExec cap fwdSS x.w { x with ssh := x.ssh + 1 }.w 5 := by
  have s := wfwdC_spec cap sSS mSP x.w h
  rwa [m_ss_fwd] at s

theorem read_ss (s k p : ℕ) :
    readTapeBit (List.replicate s true ++ List.replicate k false) p = readTapeBit (unary s) p := by
  unfold readTapeBit unary
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate, List.length_replicate,
    List.getElem?_cons, List.getElem?_nil]
  split_ifs <;> simp_all

theorem ss_true (s k i : ℕ) (hi : i < s) : readTapeBit (List.replicate s true ++ List.replicate k false) i = true := by
  rw [read_ss]; exact readTapeBit_unary_lt s i [] hi

theorem ss_false (s k : ℕ) : readTapeBit (List.replicate s true ++ List.replicate k false) s = false := by
  rw [read_ss]; exact readTapeBit_unary_end s []

theorem ssLoop_spec (s k : ℕ) : ∀ (i : ℕ) (x : MSt), x.ss = List.replicate s true ++ List.replicate k false →
    x.ssh = s - i → i ≤ s → s < cap → WExec cap (.whs sSS fwdSS) x.w { x with ssh := s }.w (7 * i + 1)
  | 0, x, hs, hh, _, _ => by
    have hb : wbit x.w sSS = false := by rw [wbit_ss, hs, hh, Nat.sub_zero]; exact ss_false s k
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    cases x; simp only at hh ⊢; rw [hh, Nat.sub_zero]
  | i + 1, x, hs, hh, hi, hc => by
    have hb : wbit x.w sSS = true := by rw [wbit_ss, hs, hh]; exact ss_true s k _ (by omega)
    have s1 := fwdSS_spec cap x (by omega)
    have s2 := ssLoop_spec s k i { x with ssh := x.ssh + 1 } hs (by simp only; omega) (by omega) hc
    exact WExec.cast cap (WExec.whsT hb s1 s2) rfl (by omega)

/-- `unary s` one longer. -/
def extendU : MProg := .seq (.whs sSS fwdSS) (.seq (.wr sSS true) (WM.rewind sSS mSP))

theorem write_ss (s k : ℕ) :
    writeTapeBit (List.replicate s true ++ List.replicate k false) s true =
      List.replicate (s + 1) true ++ List.replicate (k - 1) false := by
  cases k with
  | zero =>
    have h := writeTapeBit_end' (List.replicate s true) true
    simp only [List.length_replicate] at h
    simp [h, List.replicate_succ']
  | succ k =>
    have h := writeTapeBit_mid'' (List.replicate s true) (List.replicate k false) false true
    simp only [List.length_replicate] at h
    rw [List.replicate_succ, h, List.replicate_succ']
    simp

theorem extendU_spec (s k : ℕ) (x : MSt) (hs : x.ss = List.replicate s true ++ List.replicate k false)
    (hh : x.ssh = 0) (hc : s + 1 < cap) :
    WExec cap extendU x.w { x with ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false }.w
      (7 * s + 1 + 1 + (1 + 1 + (5 * s + 1))) := by
  have s1 := ssLoop_spec cap s k s x hs (by rw [hh]; omega) (le_refl _) (by omega)
  have hw : writeTapeBit x.ss s true = List.replicate (s + 1) true ++ List.replicate (k - 1) false := by
    rw [hs]; exact write_ss s k
  have s2 : WExec cap (.wr sSS true) ({ x with ssh := s } : MSt).w
      ({ x with ssh := s, ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false } : MSt).w 1 := by
    have h := WExec.wr (cap := cap) sSS true ({ x with ssh := s } : MSt).w
    rw [show (({ x with ssh := s } : MSt).w).st sSS = x.ss from rfl,
      show (({ x with ssh := s } : MSt).w).sh sSS = s from rfl, hw, m_ss_wr] at h
    exact h
  have s3 := wrewind_spec cap sSS mSP
    ({ x with ssh := s, ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false } : MSt).ssh
    ({ x with ssh := s, ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false } : MSt).w rfl
    (by show s ≤ cap; omega)
  rw [m_ss_rew] at s3
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (le_refl _)
  cases x; simp only at hh ⊢; rw [hh]

/-! ## The majority check -/

/-- `T := 2A`, `A := 0`. -/
def dblM : MProg := .whr mA (.seq (.dec mA) (.seq (.inc mT) (.inc mT)))

theorem dbl_spec : ∀ (n : ℕ) (x : MSt), x.a = n → x.tt + 2 * n ≤ cap → n ≤ cap →
    WExec cap dblM x.w { x with a := 0, tt := x.tt + 2 * n }.w (11 * n + 1)
  | 0, x, ha, _, _ => by
    refine WExec.cast cap (WExec.whrF (show x.w.val mA = 0 from ha)) ?_ (le_refl _)
    cases x; simp only at ha ⊢; rw [ha]; rfl
  | n + 1, x, ha, hc, hn => by
    have s1 := WExec.dec (cap := cap) mA x.w (show x.a ≤ cap by omega)
    rw [m_a] at s1
    have s2 := WExec.inc (cap := cap) mT ({ x with a := x.w.val mA - 1 } : MSt).w (show x.tt < cap by omega)
    rw [m_tt] at s2
    have s3 := WExec.inc (cap := cap) mT ({ x with a := x.w.val mA - 1, tt := x.tt + 1 } : MSt).w
      (show x.tt + 1 < cap by omega)
    rw [m_tt] at s3
    have ih := dbl_spec n { x with a := x.w.val mA - 1, tt := x.tt + 1 + 1 } (by show x.a - 1 = n; omega)
      (by simp only; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show x.w.val mA ≠ 0 by show x.a ≠ 0; omega)
      (WExec.seq s1 (WExec.seq s2 s3)) ih) ?_ (by omega)
    cases x; simp only at ha hc hn ⊢; congr 2; omega

/-- `F := [V > T]`, `V := 0`, `T := T − V`. -/
def cmpM : MProg := .whr mV (.seq (.dec mV) (.ifr mT (.dec mT) (WM.setF mF)))

theorem cmp_spec : ∀ (n : ℕ) (x : MSt), x.v = n → x.f ≤ 1 → n ≤ cap → x.tt ≤ cap → 1 ≤ cap →
    WExec cap cmpM x.w { x with v := 0, tt := x.tt - n, f := if x.tt < n then 1 else x.f }.w (9 * n + 1)
  | 0, x, hv, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (show x.w.val mV = 0 from hv)) ?_ (le_refl _)
    cases x; simp only at hv ⊢; rw [hv]; simp
  | n + 1, x, hv, hf, hn, ht, h1 => by
    have s1 := WExec.dec (cap := cap) mV x.w (show x.v ≤ cap by omega)
    rw [m_v] at s1
    by_cases hT : x.tt = 0
    · have s2 := wsetF_spec cap mF ({ x with v := x.w.val mV - 1 } : MSt).w hf h1
      rw [m_f] at s2
      have s2' : WExec cap (.ifr mT (.dec mT) (WM.setF mF)) ({ x with v := x.w.val mV - 1 } : MSt).w
          ({ x with v := x.w.val mV - 1, f := 1 } : MSt).w 5 := WExec.ifrF (show x.tt = 0 from hT) s2
      have ih := cmp_spec n { x with v := x.w.val mV - 1, f := 1 } (by show x.v - 1 = n; omega) (by simp only; omega)
        (by omega) ht h1
      refine WExec.cast cap (WExec.whrT (show x.w.val mV ≠ 0 by show x.v ≠ 0; omega) (WExec.seq s1 s2') ih) ?_
        (by omega)
      cases x; simp only at hT ⊢; subst hT; simp
    · have s2 := WExec.dec (cap := cap) mT ({ x with v := x.w.val mV - 1 } : MSt).w (show x.tt ≤ cap from ht)
      rw [m_tt] at s2
      have s2' : WExec cap (.ifr mT (.dec mT) (WM.setF mF)) ({ x with v := x.w.val mV - 1 } : MSt).w
          ({ x with v := x.w.val mV - 1, tt := x.tt - 1 } : MSt).w 5 :=
        WExec.mono (WExec.ifrT (show x.tt ≠ 0 from hT) s2) (by omega)
      have ih := cmp_spec n { x with v := x.w.val mV - 1, tt := x.tt - 1 } (by show x.v - 1 = n; omega) hf
        (by omega) (by simp only; omega) h1
      refine WExec.cast cap (WExec.whrT (show x.w.val mV ≠ 0 by show x.v ≠ 0; omega) (WExec.seq s1 s2') ih) ?_
        (by omega)
      cases x; simp only at hT hv ⊢; congr 2
      · omega
      · split_ifs <;> omega

/-- `R := R + S`, `S` kept (through `T2`). -/
def addSM : MProg := .seq (WM.move mS mT2) (.whr mT2 (.seq (.dec mT2) (.seq (.inc mS) (.inc mR))))

theorem addLoop_spec : ∀ (n : ℕ) (x : MSt), x.t2 = n → x.s + n ≤ cap → x.r + n ≤ cap → n ≤ cap →
    WExec cap (.whr mT2 (.seq (.dec mT2) (.seq (.inc mS) (.inc mR)))) x.w
      { x with t2 := 0, s := x.s + n, r := x.r + n }.w (11 * n + 1)
  | 0, x, h0, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (show x.w.val mT2 = 0 from h0)) ?_ (le_refl _)
    cases x; simp only at h0 ⊢; rw [h0]; rfl
  | n + 1, x, hn, hs, hr, hc => by
    have s1 := WExec.dec (cap := cap) mT2 x.w (show x.t2 ≤ cap by omega)
    rw [m_t2] at s1
    have s2 := WExec.inc (cap := cap) mS ({ x with t2 := x.w.val mT2 - 1 } : MSt).w (show x.s < cap by omega)
    rw [m_s] at s2
    have s3 := WExec.inc (cap := cap) mR ({ x with t2 := x.w.val mT2 - 1, s := x.s + 1 } : MSt).w
      (show x.r < cap by omega)
    rw [m_r] at s3
    have ih := addLoop_spec n { x with t2 := x.w.val mT2 - 1, s := x.s + 1, r := x.r + 1 }
      (by show x.t2 - 1 = n; omega) (by simp only; omega) (by simp only; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show x.w.val mT2 ≠ 0 by show x.t2 ≠ 0; omega)
      (WExec.seq s1 (WExec.seq s2 s3)) ih) ?_ (by omega)
    cases x; simp only at hn hs hr ⊢; congr 2 <;> omega

theorem addS_spec (x : MSt) (h2 : x.t2 = 0) (hs : 2 * x.s ≤ cap) (hr : x.r + x.s ≤ cap) :
    WExec cap addSM x.w { x with r := x.r + x.s }.w ((7 * x.s + 1) + 1 + (11 * x.s + 1)) := by
  have s1 := wmove_spec cap mS mT2 (by decide) x.s x.w rfl (show x.s ≤ cap by omega) (show x.t2 + x.s ≤ cap by omega)
  rw [m_s, m_t2] at s1
  have s2 := addLoop_spec cap x.s { x with s := 0, t2 := x.t2 + x.s } (by show x.t2 + x.s = x.s; omega)
    (by simp only; omega) (by simp only; omega) (by omega)
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (le_refl _)
  cases x; simp only at h2 ⊢; subst h2; simp

/-- **The majority check**: `R += S` iff `V ≤ 2A`; `A`, `V` cleared. -/
def checkM : MProg := .seq dblM (.seq cmpM (.seq (WM.clear mT) (.ifr mF (WM.clear mF) addSM)))

def checkCost (a v s : ℕ) : ℕ :=
  (11 * a + 1) + 1 + ((9 * v + 1) + 1 + ((3 * (2 * a - v) + 1) + 1 + ((7 * s + 1) + 1 + (11 * s + 1) + 1 + 4)))

theorem check_spec (x : MSt) (htt : x.tt = 0) (hf : x.f = 0) (h2 : x.t2 = 0) (hA : 2 * x.a ≤ cap) (hV : x.v ≤ cap)
    (hs : 2 * x.s ≤ cap) (hr : x.r + x.s ≤ cap) (h1 : 1 ≤ cap) :
    WExec cap checkM x.w { x with a := 0, v := 0, r := x.r + if x.v ≤ 2 * x.a then x.s else 0 }.w
      (checkCost x.a x.v x.s) := by
  obtain ⟨F0, hF0⟩ : ∃ f : ℕ, f = if x.tt + 2 * x.a < x.v then 1 else x.f := ⟨_, rfl⟩
  have s1 := dbl_spec cap x.a x rfl (by omega) (by omega)
  have s2 := cmp_spec cap x.v { x with a := 0, tt := x.tt + 2 * x.a } rfl (by simp only; omega) hV
    (by simp only; omega) h1
  have s2' : WExec cap cmpM ({ x with a := 0, tt := x.tt + 2 * x.a } : MSt).w
      ({ x with a := 0, v := 0, tt := x.tt + 2 * x.a - x.v, f := F0 } : MSt).w (9 * x.v + 1) := by
    rw [hF0]; exact s2
  have s3 := wclear_spec cap mT (x.tt + 2 * x.a - x.v)
    ({ x with a := 0, v := 0, tt := x.tt + 2 * x.a - x.v, f := F0 } : MSt).w rfl
    (show x.tt + 2 * x.a - x.v ≤ cap by omega)
  rw [m_tt] at s3
  have s3' : WExec cap (WM.clear mT) ({ x with a := 0, v := 0, tt := x.tt + 2 * x.a - x.v, f := F0 } : MSt).w
      ({ x with a := 0, v := 0, tt := 0, f := F0 } : MSt).w (3 * (x.tt + 2 * x.a - x.v) + 1) := s3
  by_cases hmaj : x.v ≤ 2 * x.a
  · have hF : F0 = 0 := by rw [hF0, if_neg (by omega), hf]
    have s4 := addS_spec cap ({ x with a := 0, v := 0, tt := 0, f := F0 } : MSt) h2 hs hr
    have s4' : WExec cap (.ifr mF (WM.clear mF) addSM) ({ x with a := 0, v := 0, tt := 0, f := F0 } : MSt).w
        ({ x with a := 0, v := 0, tt := 0, f := F0, r := x.r + x.s } : MSt).w
        ((7 * x.s + 1) + 1 + (11 * x.s + 1) + 1) := WExec.ifrF (show F0 = 0 from hF) s4
    refine WExec.cast cap (WExec.seq s1 (WExec.seq s2' (WExec.seq s3' s4'))) ?_ ?_
    · cases x; simp only at htt hf ⊢; subst htt hf hF; simp [hmaj]
    · unfold checkCost; omega
  · have hF : F0 = 1 := by rw [hF0, if_pos (by omega)]
    have s4 := wclear_spec cap mF 1 ({ x with a := 0, v := 0, tt := 0, f := F0 } : MSt).w (show F0 = 1 from hF)
      (show F0 ≤ cap by omega)
    rw [m_f] at s4
    have s4' : WExec cap (.ifr mF (WM.clear mF) addSM) ({ x with a := 0, v := 0, tt := 0, f := F0 } : MSt).w
        ({ x with a := 0, v := 0, tt := 0, f := 0 } : MSt).w (3 * 1 + 1 + 1) :=
      WExec.ifrT (show F0 ≠ 0 by omega) s4
    refine WExec.cast cap (WExec.seq s1 (WExec.seq s2' (WExec.seq s3' s4'))) ?_ ?_
    · cases x; simp only at htt hf ⊢; subst htt hf; simp [hmaj]
    · unfold checkCost; omega

end NearCubicWires.WireExponent3_5.FinalPass.Maj
