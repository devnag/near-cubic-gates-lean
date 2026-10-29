import Proof.Gates.Dispatch.ParamsA

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter

variable {C : Ctx}

def pM : Fin VV := ⟨147, by decide⟩
def pDM : Fin VV := ⟨148, by decide⟩
def pU : Fin VV := ⟨166, by decide⟩
def pP2M : Fin VV := ⟨169, by decide⟩
def pP2K : Fin VV := ⟨170, by decide⟩
def pX3 : Fin VV := ⟨173, by decide⟩
def pX4 : Fin VV := ⟨174, by decide⟩
def pX5 : Fin VV := ⟨175, by decide⟩
def pX6 : Fin VV := ⟨176, by decide⟩

/-! ## A comparison flag -/

/-- `fl := [x ≤ y]`. -/
def flagLe (fl x y : Fin VV) : St VV := .seq (assign fl (.lit 1)) (.ite (.lt y x) (.op (.zero fl)) skipS)

theorem big_var (x : Fin VV) (hx : 15 ≤ x.val) : x ∉ [vZ, v1, v2, vPOS] ∧ x ≠ vJ ∧ vZ ∉ [x, vJ] ∧ v1 ∉ [x, vJ] ∧
    v2 ∉ [x, vJ] ∧ vPOS ∉ [x, vJ] := by
  have e0 : vZ.val = 0 := rfl
  have e1 : v1.val = 1 := rfl
  have e2 : v2.val = 2 := rfl
  have e3 : vJ.val = 3 := rfl
  have e4 : vPOS.val = 4 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, Fin.ext_iff]
  omega

theorem flagLe_spec (fl x y : Fin VV) (hfl : 15 ≤ fl.val ∧ fl.val < 200) (hxf : x ≠ fl)
    (hyf : y ≠ fl) (hyx : y ≠ x) (hxs : x.val < 200) (hys : y.val < 200) (hxJ : x ≠ vJ) (hyJ : y ≠ vJ)
    (a : DS VV) (hc : Cst a) (h1 : 1 < 2 ^ C.Wd) :
    Hs C (flagLe fl x y) a 10 (fun b => b.env fl = bnat (a.env x ≤ a.env y) ∧ AsgFr a b fl ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  obtain ⟨hP, hfJ, hZ, h1', h2', hPo⟩ := big_var fl hfl.1
  refine Hx.hs (Hs.then (assign_spec fl hfl.2 hP (.lit 1) a (by aevar) (by aevar) hc (by aeok []))
    (fun b ⟨p1, p2, p3, p4, p5, p6⟩ n1 hn1 => ?_))
  simp only [AE.eval] at p1
  have bx : b.env x = a.env x := p2 x hxs hxJ hxf
  have by' : b.env y = a.env y := p2 y hys hyJ hyf
  have step : Hs C (.ite (.lt y x) (.op (.zero fl)) skipS) b 2 (fun g => g.env fl = bnat (a.env x ≤ a.env y) ∧
      g.cp = b.cp ∧ g.wq = b.wq ∧ g.out = b.out ∧ Fr b g [fl, vJ]) := by
    refine Hs.ite (c := .lt y x) hyx (fun he => ?_) (fun he => ?_)
    · have hlt : a.env y < a.env x := by simpa [Cnd.eval, bx, by'] using he
      refine Hs.mono (hs_zero C fl b) le_rfl ?_
      rintro g rfl
      exact ⟨by rw [DS.set_env_self]; unfold bnat; simp [show ¬ a.env x ≤ a.env y by omega], rfl, rfl, rfl,
        Fr.set _ _ (by simp)⟩
    · have hle : a.env x ≤ a.env y := by simpa [Cnd.eval, bx, by'] using he
      refine Hs.mono (skip_spec b) le_rfl ?_
      rintro g rfl
      refine ⟨?_, rfl, rfl, rfl, Fr.set _ _ (by simp)⟩
      rw [DS.set_env_ne _ _ hfJ, p1]; unfold bnat; simp [hle]
  refine Hs.last step (fun g ⟨g1, g2, g3, g4, g5⟩ n2 hn2 => ⟨⟨g1, fun z hz hzJ hzf => by
      rw [g5 z (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hzf, hzJ⟩), p2 z hz hzJ hzf],
    by rw [g2, p3], by rw [g3, p4], by rw [g4, p5], Cst.of_fr p6 g5 ⟨hZ, h1', h2'⟩
      (by rw [g5 vPOS hPo, g2]; exact p6.pos)⟩, by simp only [AE.cost] at hn1; omega⟩)

/-! ## `m` and degree zero -/

theorem degreePass_zero (n k m : ℕ) : DegreePass n k m 0 ↔ 100 * (k + 2) ≤ m := by
  unfold DegreePass
  simp only [mul_zero, pow_zero, mul_one]
  exact Nat.pow_le_pow_iff_right (by norm_num)

open AE in
def pRule2a : St VV :=
  .seq (assign pX1 (sub (var vN) (var pK))) (.seq (assign pM (add (var pX1) (mod (var pX1) (lit 2))))
    (.seq (assign pX2 (mul (lit 100) (add (var pK) (lit 2)))) (needLe pX2 pM)))

theorem pRule2a_spec (a : DS VV) (hc : Cst a) (n k : ℕ) (hn : a.env vN = n) (hk : a.env pK = k) (P : Prop)
    [Decidable P] (hP : a.env vADM = bnat P) (hW : 100 * (k + 2) + 2 * n + 4 < 2 ^ C.Wd) :
    Hs C pRule2a a 400 (fun b => b.env pM = outer n k ∧ b.env vADM = bnat (P ∧ DegreePass n k (outer n k) 0) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b [pX1, pM, pX2, vADM, vJ]) := by
  refine Hx.hs (Hs.then (assign_spec pX1 (by decide) (by decide) (.sub (.var vN) (.var pK)) a (by aevar) (by aevar) hc
    (by simp [AE.ok])) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ n1 hn1 => ?_))
  simp only [AE.eval, hn, hk] at p1
  refine Hs.then (assign_spec pM (by decide) (by decide) (.add (.var pX1) (.mod (.var pX1) (.lit 2))) b1 (by aevar)
    (by aevar) p6 (by have := Nat.mod_lt (n - k) (show 2 > 0 by norm_num); aeok [p1])) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ n2 hn2 => ?_)
  simp only [AE.eval, p1] at q1
  have b2k : b2.env pK = k := by rw [q2 pK (by decide) (by decide) (by decide), p2 pK (by decide) (by decide) (by decide), hk]
  refine Hs.then (assign_spec pX2 (by decide) (by decide) (.mul (.lit 100) (.add (.var pK) (.lit 2))) b2 (by aevar)
    (by aevar) q6 (by aeok [b2k])) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ n3 hn3 => ?_)
  simp only [AE.eval, b2k] at r1
  have b3A : b3.env vADM = bnat P := by
    rw [r2 vADM (by decide) (by decide) (by decide), q2 vADM (by decide) (by decide) (by decide),
      p2 vADM (by decide) (by decide) (by decide), hP]
  refine Hs.last (needLe_spec pX2 pM (by decide) b3 P b3A) (fun g ⟨g1, g2, g3, g4, g5⟩ n4 hn4 => ?_)
  have b3M : b3.env pM = outer n k := by rw [r2 pM (by decide) (by decide) (by decide), q1]; rfl
  refine ⟨⟨by rw [g5 pM (by decide), b3M], by rw [g1, r1, b3M]; exact bnat_congr (by rw [degreePass_zero]),
    by rw [g2, r3, q3, p3], by rw [g3, r4, q4, p4], by rw [g4, r5, q5, p5],
    Cst.of_fr r6 g5 (by decide) (by rw [g5 vPOS (by decide), g2]; exact r6.pos),
    FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (g5.toS.weaken (by decide))))⟩, ?_⟩
  simp only [AE.cost] at hn1 hn2 hn3
  omega

/-! ## Frame rewriting helpers (conditional rewrite rules for `simp (disch := decide)`) -/

theorem AsgFr.ev {a b : DS VV} {x : Fin VV} (h : AsgFr a b x) {y : Fin VV} (hy : y.val < 200) (hJ : y ≠ vJ)
    (hx : y ≠ x) : b.env y = a.env y := h y hy hJ hx
theorem Fr.ev {a b : DS VV} {T : List (Fin VV)} (h : Fr a b T) {y : Fin VV} (hy : y ∉ T) : b.env y = a.env y := h y hy
theorem FrS.ev {a b : DS VV} {T : List (Fin VV)} (h : FrS a b T) {y : Fin VV} (hy : y.val < 200) (hT : y ∉ T) :
    b.env y = a.env y := h y hy hT

/-! ## `U` (`sec:finite`, rule 1) -/

theorem ub_facts (n m : ℕ) (hn : 1 ≤ n) :
    n ≤ n * n ∧ n * n ≤ n * n * (n * n) ∧ Bb n m * m ≤ Bb n m * m * ((m + 1) / 2) ∧
    2 * (2 * (n * n * (n * n))) ≤ 2 * (2 * (n * n * (n * n))) * mT n m ∧
    mT n m ≤ 2 * (2 * (n * n * (n * n))) * mT n m ∧ Ubase n m = 1 + 2 * (2 * (n * n * (n * n))) * mT n m ∧
    1 ≤ Ubase n m := by
  have h1 : 1 ≤ mT n m := by unfold mT; omega
  have h2 : 1 ≤ n * n * (n * n) := Nat.one_le_iff_ne_zero.2 (by positivity)
  refine ⟨Nat.le_mul_self n, Nat.le_mul_self _, ?_, Nat.le_mul_of_pos_right _ h1, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · exact Nat.le_mul_of_pos_right _ (by omega)
  · exact Nat.le_mul_of_pos_left _ (by omega)
  · unfold Ubase G0; ring
  · unfold Ubase; omega

open AE in
def pUB : St VV :=
  .seq (assign t3 (add (var vN) (lit 1))) (.seq clog2 (.seq (assign pX3 (var t5))
  (.seq (assign t3 (add (var pM) (lit 1))) (.seq clog2
  (.seq (assign pX4 (add (add (add (var vB0) (var pX3)) (var t5)) (lit 2)))
  (.seq (assign pX5 (add (lit 1) (mul (mul (var pX4) (var pM)) (div (add (var pM) (lit 1)) (lit 2)))))
    (assign pU (add (lit 1) (mul (mul (lit 2) (mul (lit 2) (mul (mul (var vN) (var vN)) (mul (var vN) (var vN)))))
      (var pX5))))))))))

def ubT : List (Fin VV) := [t3, t5, t6, pX3, pX4, pX5, pU, vJ]

theorem pUB_spec (a : DS VV) (hc : Cst a) (n m : ℕ) (hn : a.env vN = n) (hm : a.env pM = m)
    (hb : a.env vB0 = B0 n) (hn1 : 1 ≤ n)
    (hUW : 4 * Ubase n m + 4 * n + 4 * m + 4 * Bb n m + 16 < 2 ^ C.Wd) :
    Hs C pUB a (10 * n + 10 * m + 200) (fun b => b.env pU = Ubase n m ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ FrS a b ubT) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := ub_facts n m hn1
  have hBb : Bb n m = B0 n + Nat.clog 2 (n + 1) + Nat.clog 2 (m + 1) + 2 := rfl
  have hmT : mT n m = 1 + Bb n m * m * ((m + 1) / 2) := rfl
  have c1 : Nat.clog 2 (n + 1) ≤ n + 1 := clog_le_self _
  have c2 : Nat.clog 2 (m + 1) ≤ m + 1 := clog_le_self _
  refine Hx.hs (Hs.then (assign_spec t3 (by decide) (by decide) (.add (.var vN) (.lit 1)) a (by aevar) (by aevar) hc
    (by aeok [hn])) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, hn] at p1
  refine Hs.then (clog2_spec b1 p6 (by rw [p1]; omega)) (fun b2 ⟨q1, _, q3, q4, q5, q6, q7⟩ k2 hk2 => ?_)
  rw [p1] at q1 hk2
  refine Hs.then (assign_spec pX3 (by decide) (by decide) (.var t5) b2 (by aevar) (by aevar) q6 (by trivial))
    (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  simp only [AE.eval, q1] at r1
  have b3m : b3.env pM = m := by simp (disch := decide) only [r2.ev, q7.ev, p2.ev]; exact hm
  refine Hs.then (assign_spec t3 (by decide) (by decide) (.add (.var pM) (.lit 1)) b3 (by aevar) (by aevar) r6
    (by aeok [b3m])) (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval, b3m] at s1
  refine Hs.then (clog2_spec b4 s6 (by rw [s1]; omega)) (fun b5 ⟨u1, _, u3, u4, u5, u6, u7⟩ k5 hk5 => ?_)
  rw [s1] at u1 hk5
  have b5b : b5.env vB0 = B0 n := by simp (disch := decide) only [u7.ev, s2.ev, r2.ev, q7.ev, p2.ev]; exact hb
  have b5x : b5.env pX3 = Nat.clog 2 (n + 1) := by simp (disch := decide) only [u7.ev, s2.ev]; exact r1
  refine Hs.then (assign_spec pX4 (by decide) (by decide) (.add (.add (.add (.var vB0) (.var pX3)) (.var t5)) (.lit 2))
    b5 (by aevar) (by aevar) u6 (by aeok [b5b, b5x, u1])) (fun b6 ⟨v1', v2', v3', v4', v5', v6'⟩ k6 hk6 => ?_)
  simp only [AE.eval, b5b, b5x, u1] at v1'
  rw [← hBb] at v1'
  have b6m : b6.env pM = m := by simp (disch := decide) only [v2'.ev, u7.ev, s2.ev]; exact b3m
  refine Hs.then (assign_spec pX5 (by decide) (by decide)
    (.add (.lit 1) (.mul (.mul (.var pX4) (.var pM)) (.div (.add (.var pM) (.lit 1)) (.lit 2)))) b6 (by aevar)
    (by aevar) v6' (by aeok [v1', b6m])) (fun b7 ⟨w1, w2, w3, w4, w5, w6⟩ k7 hk7 => ?_)
  simp only [AE.eval, v1', b6m] at w1
  rw [← hmT] at w1
  have b7n : b7.env vN = n := by
    simp (disch := decide) only [w2.ev, v2'.ev, u7.ev, s2.ev, r2.ev, q7.ev, p2.ev]; exact hn
  refine Hs.last (assign_spec pU (by decide) (by decide) (.add (.lit 1) (.mul (.mul (.lit 2) (.mul (.lit 2)
    (.mul (.mul (.var vN) (.var vN)) (.mul (.var vN) (.var vN))))) (.var pX5))) b7 (by aevar) (by aevar) w6
    (by aeok [b7n, w1])) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k8 hk8 => ?_)
  simp only [AE.eval, b7n, w1] at g1
  refine ⟨⟨by rw [g1, f6], by rw [g3, w3, v3', u3, s3, r3, q3, p3], by rw [g4, w4, v4', u4, s4, r4, q4, p4],
    by rw [g5, w5, v5', u5, s5, r5, q5, p5], g6, ?_⟩, ?_⟩
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q7.toS.weaken (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (FrS.trans (u7.toS.weaken (by decide)) (FrS.trans (v2'.toS _ (by decide) (by decide))
      (FrS.trans (w2.toS _ (by decide) (by decide)) (g2.toS _ (by decide) (by decide))))))))
  · simp only [AE.cost] at hk1 hk3 hk4 hk6 hk7 hk8
    omega

/-! ## The two powers of two -/

open AE in
def pP2 : St VV :=
  .seq (assign P2E (mul (lit 100) (add (var pK) (lit 2)))) (.seq pow2v (.seq (assign pP2K (var P2X))
    (.seq (assign P2E (var pM)) (.seq pow2v (assign pP2M (var P2X))))))

def p2T : List (Fin VV) := [P2E, P2X, P2I, pP2K, pP2M, vJ]

theorem pP2_spec (a : DS VV) (hc : Cst a) (k m : ℕ) (hk : a.env pK = k) (hm : a.env pM = m)
    (hW : 100 * (k + 2) + m + 1 < C.Wd) :
    Hs C pP2 a (5 * m + 1000 * k + 3000) (fun b => b.env pP2K = 2 ^ (100 * (k + 2)) ∧ b.env pP2M = 2 ^ m ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b p2T) := by
  have hW' : 100 * (k + 2) + 2 < 2 ^ C.Wd := lt_of_le_of_lt (by omega : 100 * (k + 2) + 2 ≤ C.Wd) Nat.lt_two_pow_self
  refine Hx.hs (Hs.then (assign_spec P2E (by decide) (by decide) (.mul (.lit 100) (.add (.var pK) (.lit 2))) a
    (by aevar) (by aevar) hc (by aeok [hk])) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, hk] at p1
  refine Hs.then (pow2v_spec b1 p6 _ p1 (by omega)) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  refine Hs.then (assign_spec pP2K (by decide) (by decide) (.var P2X) b2 (by aevar) (by aevar) q5 (by trivial))
    (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  simp only [AE.eval, q1] at r1
  have b3m : b3.env pM = m := by simp (disch := decide) only [r2.ev, q6.ev, p2.ev]; exact hm
  refine Hs.then (assign_spec P2E (by decide) (by decide) (.var pM) b3 (by aevar) (by aevar) r6 (by trivial))
    (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval, b3m] at s1
  refine Hs.then (pow2v_spec b4 s6 _ s1 (by omega)) (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ k5 hk5 => ?_)
  refine Hs.last (assign_spec pP2M (by decide) (by decide) (.var P2X) b5 (by aevar) (by aevar) u5 (by trivial))
    (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k6 hk6 => ?_)
  simp only [AE.eval, u1] at g1
  refine ⟨⟨by simp (disch := decide) only [g2.ev, u6.ev, s2.ev]; exact r1, g1, by rw [g3, u2, s3, r3, q2, p3],
    by rw [g4, u3, s4, r4, q3, p4], by rw [g5, u4, s5, r5, q4, p5], g6, ?_⟩, ?_⟩
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q6.toS.weaken (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (FrS.trans (u6.toS.weaken (by decide)) (g2.toS _ (by decide) (by decide))))))
  · simp only [AE.cost] at hk1 hk3 hk4 hk6
    omega

/-! ## `D_max` (eq:degree-budget) -/

open AE in
def dTest : St VV :=
  .seq (assign PWB (var pU)) (.seq (assign PWE (mul (lit 100) (var pSI))) (.seq powv
    (.seq (assign pX6 (mul (var pP2K) (var PWX))) (flagLe pSF pX6 pP2M))))

def dT : List (Fin VV) := [pSI, pSF, PWB, PWE, PWX, PWI, PWT, pX6, vJ]

/-- The scan invariant. -/
def DInv (a : DS VV) (k m U : ℕ) (b : DS VV) : Prop :=
  b.env pU = U ∧ b.env pP2K = 2 ^ (100 * (k + 2)) ∧ b.env pP2M = 2 ^ m ∧ Cst b ∧ FrS a b dT

theorem dTest_spec (a : DS VV) (k m U : ℕ) (hU1 : 1 ≤ U) (hD : 2 ^ (100 * (k + 2)) * U ^ (100 * m) < 2 ^ C.Wd)
    (hmW : 100 * m + 200 < 2 ^ C.Wd) :
    FlagTest C dTest pSI pSF (fun D => 2 ^ (100 * (k + 2)) * U ^ (100 * D) ≤ 2 ^ m) (DInv a k m U)
      (700 * m + 300) m := by
  intro b ⟨i1, i2, i3, i4, i5⟩ hDm
  obtain ⟨D, hDd⟩ : ∃ D, b.env pSI = D := ⟨_, rfl⟩
  rw [hDd] at hDm ⊢
  have hpow : ∀ j ≤ 100 * D, U ^ j < 2 ^ C.Wd := fun j hj =>
    lt_of_le_of_lt (le_trans (Nat.pow_le_pow_right hU1 (by omega)) (Nat.le_mul_of_pos_left _ (by positivity))) hD
  have hprod : 2 ^ (100 * (k + 2)) * U ^ (100 * D) < 2 ^ C.Wd :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hU1 (by omega))) hD
  have h1W : 1 < 2 ^ C.Wd := by omega
  refine Hx.hs (Hs.then (assign_spec PWB (by decide) (by decide) (.var pU) b (by aevar) (by aevar) i4 (by trivial))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, i1] at p1
  have b1D : b1.env pSI = D := by simp (disch := decide) only [p2.ev]; exact hDd
  refine Hs.then (assign_spec PWE (by decide) (by decide) (.mul (.lit 100) (.var pSI)) b1 (by aevar) (by aevar) p6
    (by clear hpow hprod hD; aeok [b1D])) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  simp only [AE.eval, b1D] at q1
  have b2B : b2.env PWB = U := by simp (disch := decide) only [q2.ev]; exact p1
  refine Hs.then (powv_spec b2 q6 U (100 * D) b2B q1 hpow (by omega)) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  have b3K : b3.env pP2K = 2 ^ (100 * (k + 2)) := by simp (disch := decide) only [r6.ev, q2.ev, p2.ev]; exact i2
  refine Hs.then (assign_spec pX6 (by decide) (by decide) (.mul (.var pP2K) (.var PWX)) b3 (by aevar) (by aevar) r5
    (by clear hpow hD; aeok [b3K, r1])) (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval, b3K, r1] at s1
  refine Hs.last (flagLe_spec pSF pX6 pP2M (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) b4 s6 h1W) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k5 hk5 => ?_)
  have b4M : b4.env pP2M = 2 ^ m := by simp (disch := decide) only [s2.ev, r6.ev, q2.ev, p2.ev]; exact i3
  refine ⟨⟨by rw [g1, s1, b4M], by simp (disch := decide) only [g2.ev, s2.ev, r6.ev, q2.ev, p2.ev]; exact hDd,
    ⟨by simp (disch := decide) only [g2.ev, s2.ev, r6.ev, q2.ev, p2.ev]; exact i1,
      by simp (disch := decide) only [g2.ev, s2.ev]; exact b3K, by simp (disch := decide) only [g2.ev]; exact b4M, g6, ?_⟩,
    by rw [g3, s3, r2, q3, p3], by rw [g4, s4, r3, q4, p4], by rw [g5, s5, r4, q5, p5]⟩, ?_⟩
  · exact FrS.trans i5 (FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide))
      (FrS.trans (r6.toS.weaken (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (g2.toS _ (by decide) (by decide))))))
  · simp only [AE.cost] at hk1 hk2 hk4
    omega

theorem FlagTest.congr {test : St VV} {iv fl : Fin VV} {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    {Inv : DS VV → Prop} {tc B : ℕ} (h : FlagTest C test iv fl P Inv tc B) (hPQ : ∀ x, P x ↔ Q x) :
    FlagTest C test iv fl Q Inv tc B := by
  intro a ha hB
  refine Hs.mono (h a ha hB) le_rfl ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6⟩
  exact ⟨by rw [b1]; exact bnat_congr (hPQ _), b2, b3, b4, b5, b6⟩

def pDmax : St VV := .seq (assign pSI (.var pM)) (.seq (fgScan pSI pSF dTest) (assign pDM (.var pSI)))

def dmT : List (Fin VV) := pDM :: dT

def dmaxCost (m : ℕ) : ℕ := 800 * (m + 1) * (m + 1) + 1000

theorem pDmax_spec (a : DS VV) (hc : Cst a) (n k m : ℕ) (hm : a.env pM = m) (hU : a.env pU = Ubase n m)
    (hK : a.env pP2K = 2 ^ (100 * (k + 2))) (hM : a.env pP2M = 2 ^ m) (hU1 : 1 ≤ Ubase n m)
    (hD : 2 ^ (100 * (k + 2)) * Ubase n m ^ (100 * m) < 2 ^ C.Wd) (hmW : 100 * m + 200 < 2 ^ C.Wd) :
    Hs C pDmax a (dmaxCost m) (fun b => b.env pDM = greatestDegree n k m ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ FrS a b dmT) := by
  refine Hx.hs (Hs.then (assign_spec pSI (by decide) (by decide) (.var pM) a (by aevar) (by aevar) hc (by trivial))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, hm] at p1
  have hI : DInv b1 k m (Ubase n m) b1 := ⟨by simp (disch := decide) only [p2.ev]; exact hU,
    by simp (disch := decide) only [p2.ev]; exact hK, by simp (disch := decide) only [p2.ev]; exact hM, p6,
    fun _ _ _ => rfl⟩
  have ht := (dTest_spec (C := C) b1 k m (Ubase n m) hU1 hD hmW).congr (Q := DegreePass n k m) (fun _ => Iff.rfl)
  refine Hs.then (fgScan_spec pSI pSF (by decide) (by decide) (by decide) (by decide) dTest (DegreePass n k m)
    (DInv b1 k m (Ubase n m)) (700 * m + 300) (fun b hb => hb.2.2.2.1)
    (fun b v ⟨i1, i2, i3, i4, i5⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide), i1],
      by rw [DS.set_env_ne _ _ (by decide), i2], by rw [DS.set_env_ne _ _ (by decide), i3],
      Cst.set i4 _ _ (by decide), FrS.trans i5 (Fr.toS (Fr.set _ _ (by decide)))⟩)
    (fun b v ⟨i1, i2, i3, i4, i5⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide), i1],
      by rw [DS.set_env_ne _ _ (by decide), i2], by rw [DS.set_env_ne _ _ (by decide), i3],
      Cst.set i4 _ _ (by decide), FrS.trans i5 (Fr.toS (Fr.set _ _ (by decide)))⟩)
    m ht b1 hI p1) (fun b2 ⟨q1, ⟨_, _, _, q2, q3⟩, q4, q5, q6⟩ k2 hk2 => ?_)
  refine Hs.last (assign_spec pDM (by decide) (by decide) (.var pSI) b2 (by aevar) (by aevar) q2 (by trivial))
    (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k3 hk3 => ?_)
  simp only [AE.eval, q1] at g1
  refine ⟨⟨g1, by rw [g3, q4, p3], by rw [g4, q5, p4], by rw [g5, q6, p5], g6, ?_⟩, ?_⟩
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q3.weaken (by decide))
      (g2.toS _ (by decide) (by decide)))
  · simp only [AE.cost] at hk1 hk3
    have e1 : (m + 1) * (700 * m + 300 + 3 + 2) + 700 * m + 300 ≤ 800 * (m + 1) * (m + 1) := by
      ring_nf; nlinarith
    have hd : AE.eval a.env (AE.var pM) = m := by simp only [AE.eval, hm]
    unfold dmaxCost
    omega

end NearCubicGates.Close.Dispatch
