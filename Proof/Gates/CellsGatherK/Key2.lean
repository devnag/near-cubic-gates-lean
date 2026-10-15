import Proof.Gates.CellsGatherK.Key1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.QueryKey

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

/-- Frame with an explicit list of written variables. -/
structure KG (T : List (Fin VV)) (a b : DS VV MM) : Prop where
  fr : Fr a b T
  ram : b.ram = a.ram
  rc : ∀ m, m ≠ sE → b.rc m = a.rc m
  rcE : b.rc sE ≤ (b.ram sE).length
  ip : b.ip = a.ip
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc

theorem KG.trans {T : List (Fin VV)} {a b d : DS VV MM} (h1 : KG T a b) (h2 : KG T b d) : KG T a d :=
  ⟨h1.fr.trans h2.fr, h2.ram.trans h1.ram, fun m hm => (h2.rc m hm).trans (h1.rc m hm), h2.rcE, h2.ip.trans h1.ip,
    h2.out.trans h1.out, h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc⟩

theorem KG.weaken {T T' : List (Fin VV)} {a b : DS VV MM} (h : KG T a b) (hT : ∀ y ∈ T, y ∈ T') : KG T' a b :=
  ⟨h.fr.weaken hT, h.ram, h.rc, h.rcE, h.ip, h.out, h.kin, h.kout, h.kc⟩

theorem KG.of_same {T : List (Fin VV)} {a b : DS VV MM} (hf : Fr a b T) (hs : Same a b)
    (hE : a.rc sE ≤ (a.ram sE).length) : KG T a b :=
  ⟨hf, hs.ram, fun m _ => by rw [hs.rc], by rw [hs.rc, hs.ram]; exact hE, hs.ip, hs.out, hs.kin, hs.kout, hs.kc⟩

theorem KG.set {T : List (Fin VV)} {a b : DS VV MM} (h : KG T a b) {x : Fin VV} (hx : x ∈ T) (v : ℕ) :
    KG T a (b.set x v) :=
  ⟨h.fr.trans (Fr.set b v hx), h.ram, h.rc, h.rcE, h.ip, h.out, h.kin, h.kout, h.kc⟩

theorem KG.toKF {T : List (Fin VV)} {a b : DS VV MM} (h : KG T a b) (hT : ∀ y ∈ T, keyScratch y) : KF a b :=
  ⟨h.ram, h.rc, h.rcE, h.ip, h.out, h.kin, h.kout, h.kc, fun x hx => h.fr x (fun h' => hx (hT x h'))⟩

/-! ## The header -/

def hdrP : St VV MM := .seq (.op (.zero kKey)) (.seq (accP vZ) (.seq (accP kPC) (accP kQ)))

theorem hdrP_spec (a : DS VV MM) (hc : Cst a) (kb pc q : ℕ) (hKB : a.env vKB = 2 ^ kb) (hpc : a.env kPC = pc)
    (hq : a.env kQ = q) (hlt : ∀ z ∈ [0, pc, q], z < 2 ^ kb) (hW : 2 ^ (kb * 3) ≤ 2 ^ C.Wd) :
    Hs C hdrP a 22 (fun b => b.env kKey = rk kb [0, pc, q] ∧ Fr a b [kKey, kTmp] ∧ Same a b) := by
  obtain ⟨s1, n1, e1, hn1, h1, f1, m1⟩ := o_zero (C := C) kKey a
  have g1 : ∀ x, x ≠ kKey → x ≠ kTmp → s1.env x = a.env x := fun x h _ => f1.ev (by simp; exact h)
  obtain ⟨s2, n2, e2, hn2, h2, f2, m2⟩ := accP_spec (C := C) vZ (by decide) (by decide) s1 (2 ^ kb)
    (by rw [g1 vKB (by decide) (by decide), hKB])
    (by
      rw [h1, g1 vZ (by decide) (by decide), hc.z]
      simp only [zero_mul, add_zero]; positivity)
  have g2 : ∀ x, x ≠ kKey → x ≠ kTmp → s2.env x = a.env x := fun x h h' => by
    rw [f2.ev (by simp; exact ⟨h, h'⟩)]; exact g1 x h h'
  have hk2 : s2.env kKey = rk kb [0] := by
    rw [h2, h1, g1 vZ (by decide) (by decide), hc.z]; simp [rk]
  obtain ⟨s3, n3, e3, hn3, h3, f3, m3⟩ := accP_spec (C := C) kPC (by decide) (by decide) s2 (2 ^ kb)
    (by rw [g2 vKB (by decide) (by decide), hKB])
    (by
      rw [hk2, g2 kPC (by decide) (by decide), hpc]
      exact acc_fit kb C.Wd [0] pc (by intro z hz; exact hlt z (by simp at hz ⊢; tauto))
        (by simp; exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hW))
  have g3 : ∀ x, x ≠ kKey → x ≠ kTmp → s3.env x = a.env x := fun x h h' => by
    rw [f3.ev (by simp; exact ⟨h, h'⟩)]; exact g2 x h h'
  have hk3 : s3.env kKey = rk kb [0, pc] := by
    rw [h3, hk2, g2 kPC (by decide) (by decide), hpc, show [0, pc] = [0] ++ [pc] from rfl, rk_snoc]
  obtain ⟨s4, n4, e4, hn4, h4, f4, m4⟩ := accP_spec (C := C) kQ (by decide) (by decide) s3 (2 ^ kb)
    (by rw [g3 vKB (by decide) (by decide), hKB])
    (by
      rw [hk3, g3 kQ (by decide) (by decide), hq]
      exact acc_fit kb C.Wd [0, pc] q (by intro z hz; exact hlt z (by simp at hz ⊢; tauto))
        (by simp; exact hW))
  refine ⟨s4, n1 + (n2 + (n3 + n4 + 1) + 1) + 1, Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4)), by omega, ?_, ?_,
    ((m1.trans m2).trans m3).trans m4⟩
  · rw [h4, hk3, g3 kQ (by decide) (by decide), hq, show [0, pc, q] = [0, pc] ++ [q] from rfl, rk_snoc]
  · exact (((f1.weaken (by decide)).trans f2).trans f3).trans f4

/-! ## The window and the number of digits -/

def setP : St VV MM :=
  .seq (.op (.copy kW vHE)) (.seq (.op (.add kW vHE)) (.seq (.op (.sub kW v1)) (.op (.mul gRC gJ kN))))

theorem setP_spec (a : DS VV MM) (hc : Cst a) (hE J rc : ℕ) (hhE : a.env vHE = hE) (hJ : a.env gJ = J)
    (hrc : a.env gRC = rc) (h1 : 1 ≤ hE) (hW : 2 * hE + rc * J < 2 ^ C.Wd) :
    Hs C setP a 7 (fun b => b.env kW = 2 * hE - 1 ∧ b.env kN = rc * J ∧ Fr a b [kW, kN] ∧ Same a b) := by
  obtain ⟨s1, n1, e1, hn1, r1, f1, m1⟩ := o_copy (C := C) kW vHE a (by decide)
  have g1 : s1.env vHE = hE := by rw [f1.ev (by decide), hhE]
  obtain ⟨s2, n2, e2, hn2, r2, f2, m2⟩ := o_add (C := C) kW vHE s1 (by decide) (by rw [r1, g1, hhE]; omega)
  have g2 : s2.env v1 = 1 := by rw [f2.ev (by decide), f1.ev (by decide)]; exact hc.one
  obtain ⟨s3, n3, e3, hn3, r3, f3, m3⟩ := o_sub (C := C) kW v1 s2 (by decide) (by rw [r2, r1, g1, hhE, g2]; omega)
  have g3 : s3.env gRC = rc ∧ s3.env gJ = J := by
    refine ⟨by rw [f3.ev (by decide), f2.ev (by decide), f1.ev (by decide), hrc],
      by rw [f3.ev (by decide), f2.ev (by decide), f1.ev (by decide), hJ]⟩
  obtain ⟨s4, n4, e4, hn4, r4, f4, m4⟩ := o_mul (C := C) gRC gJ kN s3 (by decide) (by decide) (by decide)
    (by rw [g3.1, g3.2]; omega)
  refine ⟨s4, n1 + (n2 + (n3 + n4 + 1) + 1) + 1, Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4)), by omega, ?_, ?_, ?_,
    ((m1.trans m2).trans m3).trans m4⟩
  · rw [f4.ev (by decide), r3, r2, r1, g1, hhE, g2]; omega
  · rw [r4, g3.1, g3.2]
  · exact (((f1.weaken (by decide)).trans (f2.weaken (by decide))).trans (f3.weaken (by decide))).trans
      (f4.weaken (by decide))

/-! ## Powers -/

/-- `kP := x^e` (`e` the value of variable `e`). -/
def powK (x e : Fin VV) : St VV MM :=
  .seq (.op (.copy kP v1)) (forS kI e (.seq (.op (.mul kP x kTmp)) (.op (.copy kP kTmp))))

theorem powK_spec (x e : Fin VV) (hx : x ∉ [kP, kTmp, kI]) (he : e ∉ [kP, kTmp, kI]) (a : DS VV MM) (hc : Cst a)
    (B N : ℕ) (hB : a.env x = B) (hN : a.env e = N) (h1 : 1 ≤ B) (hW : B ^ N < 2 ^ C.Wd) (hNW : N < 2 ^ C.Wd) :
    Hs C (powK x e) a (N * 7 + 6) (fun b => b.env kP = B ^ N ∧ Fr a b [kP, kTmp, kI] ∧ Same a b) := by
  have hxP : x ≠ kP := fun h => hx (by rw [h]; decide)
  have hxT : x ≠ kTmp := fun h => hx (by rw [h]; decide)
  obtain ⟨s1, n1, e1, hn1, r1, f1, m1⟩ := o_copy (C := C) kP v1 a (by decide)
  have hv1 : s1.env kP = 1 := by rw [r1]; exact hc.one
  let I : ℕ → DS VV MM → Prop := fun k b => b.env kP = B ^ k ∧ Fr a b [kP, kTmp, kI] ∧ Same a b
  have hloop := forS_spec' (C := C) kI e (fun h => he (by rw [← h]; decide))
    (.seq (.op (.mul kP x kTmp)) (.op (.copy kP kTmp))) s1 N hNW I 3
    (fun k b v ⟨h1, h2, h3⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact h1, h2.trans (Fr.set b v (by decide)),
      h3.trans (Same.set b kI v)⟩)
    ⟨by rw [hv1, pow_zero], f1.weaken (by decide), m1⟩ (by rw [f1.ev (by simp at he ⊢; exact he.1)]; exact hN) ?_
  · obtain ⟨s2, n2, e2, hn2, ⟨r2, f2, m2⟩, -, -⟩ := hloop
    exact ⟨s2, n1 + n2 + 1, Ex.seq e1 e2, by omega, r2, f2, m2⟩
  · intro k hk b ⟨hb1, hb2, hb3⟩ hbk hbN
    have hbx : b.env x = B := by rw [hb2 x hx, hB]
    have hle : B ^ (k + 1) ≤ B ^ N := Nat.pow_le_pow_right h1 hk
    obtain ⟨s2, n2, e2, hn2, r2, f2, m2⟩ := o_mul (C := C) kP x kTmp b (Ne.symm hxP) (by decide) hxT
      (by rw [hb1, hbx, ← pow_succ]; omega)
    obtain ⟨s3, n3, e3, hn3, r3, f3, m3⟩ := o_copy (C := C) kP kTmp s2 (by decide)
    refine ⟨s3, n2 + n3 + 1, Ex.seq e2 e3, by omega, ⟨?_, ?_, (hb3.trans m2).trans m3⟩, ?_, ?_⟩
    · rw [r3, r2, hb1, hbx, pow_succ]
    · exact (hb2.trans (f2.weaken (by decide))).trans (f3.weaken (by decide))
    · rw [f3.ev (by decide), f2.ev (by decide)]; exact hbk
    · rw [f3.ev (fun h => he (by simp at h ⊢; tauto)), f2.ev (fun h => he (by simp at h ⊢; tauto))]; exact hbN

/-! ## One digit of a counter -/

/-- `kP := kP / b`; `kD := (t / kP) % b` (base variable `bv`, counter variable `tv`). -/
def digP (bv tv : Fin VV) : St VV MM :=
  .seq (.op (.dm kP bv kTmp kD)) (.seq (.op (.copy kP kTmp)) (.seq (.op (.dm tv kP kTmp kD)) (.op (.dm kTmp bv t6 kD))))

def digT : List (Fin VV) := [kP, kTmp, kD, t6]

theorem digP_spec (bv tv : Fin VV) (hb : bv ∉ digT) (ht : tv ∉ digT) (a : DS VV MM) (B T m : ℕ)
    (hB : a.env bv = B) (hT : a.env tv = T) (hP : a.env kP = B ^ (m + 1)) (h1 : 1 ≤ B)
    (hW : 2 * B ^ (m + 1) ≤ 2 ^ C.Wd) :
    Hs C (digP bv tv) a 7 (fun b => b.env kP = B ^ m ∧ b.env kD = T / B ^ m % B ∧ Fr a b digT ∧ Same a b) := by
  have hBm : 0 < B ^ m := by positivity
  have hle : B ^ m ≤ B ^ (m + 1) := Nat.pow_le_pow_right h1 (by omega)
  have hb1 : bv ≠ kP := fun h => hb (by rw [h]; decide)
  have hb2 : bv ≠ kTmp := fun h => hb (by rw [h]; decide)
  have hb3 : bv ≠ kD := fun h => hb (by rw [h]; decide)
  have hb4 : bv ≠ t6 := fun h => hb (by rw [h]; decide)
  have ht1 : tv ≠ kP := fun h => ht (by rw [h]; decide)
  have ht2 : tv ≠ kTmp := fun h => ht (by rw [h]; decide)
  have ht3 : tv ≠ kD := fun h => ht (by rw [h]; decide)
  have hBB : 2 * B ≤ 2 ^ C.Wd := le_trans (by have := Nat.le_self_pow (by omega : m + 1 ≠ 0) B; omega) hW
  obtain ⟨s1, n1, e1, hn1, q1, r1, f1, m1⟩ := o_dm (C := C) kP bv kTmp kD a (Ne.symm hb1) (by decide) (by decide)
    hb2 hb3 (by decide) (by rw [hB]; omega) (by rw [hB]; exact hBB)
  have g1b : s1.env bv = B := by rw [f1.ev (by simp; exact ⟨hb2, hb3⟩), hB]
  obtain ⟨s2, n2, e2, hn2, q2, f2, m2⟩ := o_copy (C := C) kP kTmp s1 (by decide)
  have hP2 : s2.env kP = B ^ m := by
    rw [q2, q1, hP, hB, pow_succ, Nat.mul_div_cancel _ (by omega)]
  have g2t : s2.env tv = T := by
    rw [f2.ev (by simp; exact ht1), f1.ev (by simp; exact ⟨ht2, ht3⟩), hT]
  have g2b : s2.env bv = B := by rw [f2.ev (by simp; exact hb1), g1b]
  obtain ⟨s3, n3, e3, hn3, q3, r3, f3, m3⟩ := o_dm (C := C) tv kP kTmp kD s2 ht1 ht2 ht3 (by decide) (by decide)
    (by decide) (by rw [hP2]; exact hBm) (by rw [hP2]; omega)
  have g3b : s3.env bv = B := by rw [f3.ev (by simp; exact ⟨hb2, hb3⟩), g2b]
  obtain ⟨s4, n4, e4, hn4, q4, r4, f4, m4⟩ := o_dm (C := C) kTmp bv t6 kD s3 hb2.symm (by decide) (by decide)
    hb4 hb3 (by decide) (by rw [g3b]; omega) (by rw [g3b]; exact hBB)
  refine ⟨s4, n1 + (n2 + (n3 + n4 + 1) + 1) + 1, Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4)), by omega, ?_, ?_, ?_,
    ((m1.trans m2).trans m3).trans m4⟩
  · rw [f4.ev (by decide), f3.ev (by decide), hP2]
  · rw [r4, q3, g3b, g2t, hP2]
  · exact (((f1.weaken (by decide)).trans (f2.weaken (by decide))).trans (f3.weaken (by decide))).trans
      (f4.weaken (by decide))

end NearCubicGates.Close.Cells.QueryKey
