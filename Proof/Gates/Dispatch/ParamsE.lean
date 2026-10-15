import Proof.Gates.Dispatch.ParamsMath

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter

variable {C : Ctx}

def pHE : Fin VV := ⟨155, by decide⟩
def pH : Fin VV := ⟨156, by decide⟩
def pR0 : Fin VV := ⟨157, by decide⟩
def pEN : Fin VV := ⟨158, by decide⟩
def pED : Fin VV := ⟨159, by decide⟩
def pM1 : Fin VV := ⟨160, by decide⟩
def pXN : Fin VV := ⟨164, by decide⟩
def pXD : Fin VV := ⟨165, by decide⟩
def pBN : Fin VV := ⟨190, by decide⟩
def pBD : Fin VV := ⟨191, by decide⟩

/-! ## Bit bounds -/

theorem lt_pow_mul {x y a b : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ b) : x * y < 2 ^ (a + b) := by
  rw [pow_add]
  rcases Nat.eq_zero_or_pos y with h | h
  · rw [h, mul_zero]; positivity
  · exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hx h) (Nat.mul_le_mul_left _ hy.le)

theorem lt_pow_add {x y a : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ a) : x + y < 2 ^ (a + 1) := by
  rw [pow_succ]; omega

theorem lt_pow_mono {x a b : ℕ} (hx : x < 2 ^ a) (hab : a ≤ b) : x < 2 ^ b :=
  lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hab)

theorem lt_pow_of_le {x y a : ℕ} (hxy : x ≤ y) (hy : y < 2 ^ a) : x < 2 ^ a := lt_of_le_of_lt hxy hy

theorem lit_lt_pow (k a : ℕ) (hk : k < a) : k < 2 ^ a := lt_trans hk Nat.lt_two_pow_self

/-! ## `h_E`, `h`, `R₀` -/

open AE in
def pR4a : St VV :=
  .seq (assign pHE (div (var pP) (lit 4))) (.seq (assign SQX (mul (lit 2) (mul (var pHE) (var pHE))))
    (.seq sqrtv (.seq (assign pH (var SQS)) (.seq (assign SQX (add (sub (var vN) (var pK)) (lit 1)))
      (.seq sqrtv (assign pR0 (var SQS)))))))

def r4aT : List (Fin VV) := [pHE, SQX, SQS, SQF, SQT, SQU, pH, pR0, vJ]

theorem pR4a_spec (a : DS VV) (hc : Cst a) (n k P : ℕ) (hN : a.env vN = n) (hK : a.env pK = k) (hP : a.env pP = P)
    (hPn : P ≤ n) (hW : 4 * (n + 1) * (n + 1) * ((n + 1) * (n + 1)) + 16 < 2 ^ C.Wd) :
    Hs C pR4a a (40 * (n + 1) * (n + 1) + 200) (fun b => b.env pHE = P / 4 ∧ b.env pH = Nat.sqrt (2 * (P / 4) ^ 2) ∧
      b.env pR0 = Nat.sqrt (n - k + 1) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b r4aT) := by
  have hn1 : n + 1 ≤ (n + 1) * (n + 1) := Nat.le_mul_self _
  have hn2 : (n + 1) * (n + 1) ≤ (n + 1) * (n + 1) * ((n + 1) * (n + 1)) := Nat.le_mul_self _
  have hE : P / 4 ≤ n := le_trans (Nat.div_le_self _ _) hPn
  have hE2 : P / 4 * (P / 4) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hE4 : 2 * (P / 4 * (P / 4)) * (2 * (P / 4 * (P / 4))) ≤ 4 * (n + 1) * (n + 1) * ((n + 1) * (n + 1)) := by
    calc 2 * (P / 4 * (P / 4)) * (2 * (P / 4 * (P / 4))) = 4 * ((P / 4 * (P / 4)) * (P / 4 * (P / 4))) := by ring
      _ ≤ 4 * (((n + 1) * (n + 1)) * ((n + 1) * (n + 1))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hE2 hE2)
      _ = 4 * (n + 1) * (n + 1) * ((n + 1) * (n + 1)) := by ring
  have hR2 : (n - k + 1) * (n - k + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hf : 4 * (n + 1) * (n + 1) * ((n + 1) * (n + 1)) = 4 * ((n + 1) * (n + 1) * ((n + 1) * (n + 1))) := by ring
  refine Hx.hs (Hs.then (assign_spec pHE (by decide) (by decide) (.div (.var pP) (.lit 4)) a (by aevar) (by aevar) hc
    (by aeok [hP])) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, hP] at p1
  refine Hs.then (assign_spec SQX (by decide) (by decide) (.mul (.lit 2) (.mul (.var pHE) (.var pHE))) b1 (by aevar)
    (by aevar) p6 (by aeok [p1])) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  simp only [AE.eval, p1] at q1
  refine Hs.then (sqrtv_spec b2 q6 _ q1 (by omega)) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  refine Hs.then (assign_spec pH (by decide) (by decide) (.var SQS) b3 (by aevar) (by aevar) r5 (by trivial))
    (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval, r1] at s1
  have b4N : b4.env vN = n := by simp (disch := decide) only [s2.ev, r6.ev, q2.ev, p2.ev]; exact hN
  have b4K : b4.env pK = k := by simp (disch := decide) only [s2.ev, r6.ev, q2.ev, p2.ev]; exact hK
  refine Hs.then (assign_spec SQX (by decide) (by decide) (.add (.sub (.var vN) (.var pK)) (.lit 1)) b4 (by aevar)
    (by aevar) s6 (by aeok [b4N, b4K])) (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ k5 hk5 => ?_)
  simp only [AE.eval, b4N, b4K] at u1
  refine Hs.then (sqrtv_spec b5 u6 _ u1 (by omega)) (fun b6 ⟨v1', v2', v3', v4', v5', v6'⟩ k6 hk6 => ?_)
  refine Hs.last (assign_spec pR0 (by decide) (by decide) (.var SQS) b6 (by aevar) (by aevar) v5' (by trivial))
    (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k7 hk7 => ?_)
  simp only [AE.eval, v1'] at g1
  refine ⟨⟨by simp (disch := decide) only [g2.ev, v6'.ev, u2.ev, s2.ev, r6.ev, q2.ev]; exact p1,
    by simp (disch := decide) only [g2.ev, v6'.ev, u2.ev]; rw [s1, sq],
    g1, by rw [g3, v2', u3, s3, r2, q3, p3], by rw [g4, v3', u4, s4, r3, q4, p4], by rw [g5, v4', u5, s5, r4, q5, p5],
    g6, ?_⟩, ?_⟩
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide))
      (FrS.trans (r6.toS.weaken (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (FrS.trans (u2.toS _ (by decide) (by decide)) (FrS.trans (v6'.toS.weaken (by decide))
      (g2.toS _ (by decide) (by decide)))))))
  · simp only [AE.cost] at hk1 hk2 hk4 hk5 hk7
    have e1 : 2 * (P / 4 * (P / 4)) ≤ 2 * ((n + 1) * (n + 1)) := by omega
    have e2 : 40 * (n + 1) * (n + 1) = 40 * ((n + 1) * (n + 1)) := by ring
    omega

/-! ## The guards (line 1617) -/

open AE in
def pGuard : St VV :=
  .seq (assign pX1 (lit 3)) (.seq (needLe pX1 pP) (.seq (needLe v1 pNP) (.seq (assign pX1 (lit 100))
    (.seq (needLe pX1 pP) (.seq (assign pX1 (mul (lit 64) (var pT))) (.seq (needLe pX1 pH)
      (.seq (assign pX1 (mul (lit 2) (var pK))) (needLe pX1 pDM))))))))

theorem pGuard_spec (a : DS VV) (hc : Cst a) (Pr : Prop) [Decidable Pr] (hPr : a.env vADM = bnat Pr)
    (P np T h k Dm : ℕ) (hP : a.env pP = P) (hnp : a.env pNP = np) (hT : a.env pT = T) (hh : a.env pH = h)
    (hk : a.env pK = k) (hD : a.env pDM = Dm) (hW : 64 * T + 2 * k + 300 < 2 ^ C.Wd) :
    Hs C pGuard a 1000 (fun b => b.env vADM = bnat (Pr ∧ (3 ≤ P ∧ 1 ≤ np ∧ 100 ≤ P ∧ 64 * T ≤ h ∧ 2 * k ≤ Dm)) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b [pX1, vADM, vJ]) := by
  refine Hx.hs (Hs.then (assign_spec pX1 (by decide) (by decide) (.lit 3) a (by aevar) (by aevar) hc (by aeok []))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  have e1 : b1.env vADM = bnat Pr := by simp (disch := decide) only [p2.ev]; exact hPr
  refine Hs.then (needLe_spec pX1 pP (by decide) b1 Pr e1) (fun b2 ⟨q1, q2, q3, q4, q5⟩ k2 hk2 => ?_)
  refine Hs.then (needLe_spec v1 pNP (by decide) b2 _ q1) (fun b3 ⟨r1, r2, r3, r4, r5⟩ k3 hk3 => ?_)
  have c3 : Cst b3 := Cst.of_fr (Cst.of_fr p6 q5 (by decide) (by rw [q5 vPOS (by decide), q2]; exact p6.pos)) r5
    (by decide) (by rw [r5 vPOS (by decide), r2, q5 vPOS (by decide), q2]; exact p6.pos)
  refine Hs.then (assign_spec pX1 (by decide) (by decide) (.lit 100) b3 (by aevar) (by aevar) c3 (by aeok []))
    (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  have e4 : b4.env vADM = bnat ((Pr ∧ b1.env pX1 ≤ b1.env pP) ∧ b2.env v1 ≤ b2.env pNP) := by
    simp (disch := decide) only [s2.ev]; exact r1
  refine Hs.then (needLe_spec pX1 pP (by decide) b4 _ e4)
    (fun b5 ⟨u1, u2, u3, u4, u5⟩ k5 hk5 => ?_)
  have c5 : Cst b5 := Cst.of_fr s6 u5 (by decide) (by rw [u5 vPOS (by decide), u2]; exact s6.pos)
  have b5T : b5.env pT = T := by simp (disch := decide) only [u5.ev, s2.ev, r5.ev, q5.ev, p2.ev]; exact hT
  refine Hs.then (assign_spec pX1 (by decide) (by decide) (.mul (.lit 64) (.var pT)) b5 (by aevar) (by aevar) c5
    (by aeok [b5T])) (fun b6 ⟨v1', v2', v3', v4', v5', v6'⟩ k6 hk6 => ?_)
  have e6 : b6.env vADM = bnat (((Pr ∧ b1.env pX1 ≤ b1.env pP) ∧ b2.env v1 ≤ b2.env pNP) ∧
      b4.env pX1 ≤ b4.env pP) := by
    simp (disch := decide) only [v2'.ev]; exact u1
  refine Hs.then (needLe_spec pX1 pH (by decide) b6 _ e6)
    (fun b7 ⟨w1, w2, w3, w4, w5⟩ k7 hk7 => ?_)
  have c7 : Cst b7 := Cst.of_fr v6' w5 (by decide) (by rw [w5 vPOS (by decide), w2]; exact v6'.pos)
  have b7K : b7.env pK = k := by
    simp (disch := decide) only [w5.ev, v2'.ev, u5.ev, s2.ev, r5.ev, q5.ev, p2.ev]; exact hk
  refine Hs.then (assign_spec pX1 (by decide) (by decide) (.mul (.lit 2) (.var pK)) b7 (by aevar) (by aevar) c7
    (by aeok [b7K])) (fun b8 ⟨x1, x2, x3, x4, x5, x6⟩ k8 hk8 => ?_)
  have e8 : b8.env vADM = bnat ((((Pr ∧ b1.env pX1 ≤ b1.env pP) ∧ b2.env v1 ≤ b2.env pNP) ∧
      b4.env pX1 ≤ b4.env pP) ∧ b6.env pX1 ≤ b6.env pH) := by
    simp (disch := decide) only [x2.ev]; exact w1
  refine Hs.last (needLe_spec pX1 pDM (by decide) b8 _ e8)
    (fun g ⟨g1, g2, g3, g4, g5⟩ k9 hk9 => ?_)
  have vP1 : b1.env pP = P := by simp (disch := decide) only [p2.ev]; exact hP
  have vX1 : b1.env pX1 = 3 := by simp only [AE.eval] at p1; exact p1
  have vN2 : b2.env pNP = np := by simp (disch := decide) only [q5.ev, p2.ev]; exact hnp
  have vP4 : b4.env pP = P := by simp (disch := decide) only [s2.ev, r5.ev, q5.ev]; exact vP1
  have vX4 : b4.env pX1 = 100 := by simp only [AE.eval] at s1; exact s1
  have vX6 : b6.env pX1 = 64 * T := by simp only [AE.eval, b5T] at v1'; exact v1'
  have vH6 : b6.env pH = h := by simp (disch := decide) only [v2'.ev, u5.ev, s2.ev, r5.ev, q5.ev, p2.ev]; exact hh
  have vX8 : b8.env pX1 = 2 * k := by simp only [AE.eval, b7K] at x1; exact x1
  have vD8 : b8.env pDM = Dm := by
    simp (disch := decide) only [x2.ev, w5.ev, v2'.ev, u5.ev, s2.ev, r5.ev, q5.ev, p2.ev]; exact hD
  have b2one : b2.env v1 = 1 := by rw [q5 v1 (by decide)]; exact p6.one
  refine ⟨⟨?_, by rw [g2, x3, w2, v3', u2, s3, r2, q2, p3], by rw [g3, x4, w3, v4', u3, s4, r3, q3, p4],
    by rw [g4, x5, w4, v5', u4, s5, r4, q4, p5], Cst.of_fr x6 g5 (by decide) (by rw [g5 vPOS (by decide), g2]; exact x6.pos),
    ?_⟩, ?_⟩
  · rw [g1, vX8, vD8, vX6, vH6, vX4, vP4, b2one, vN2, vX1, vP1]
    exact bnat_congr (by tauto)
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q5.toS.weaken (by decide))
      (FrS.trans (r5.toS.weaken (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (FrS.trans (u5.toS.weaken (by decide)) (FrS.trans (v2'.toS _ (by decide) (by decide))
      (FrS.trans (w5.toS.weaken (by decide)) (FrS.trans (x2.toS _ (by decide) (by decide))
      (g5.toS.weaken (by decide)))))))))
  · simp only [AE.cost] at hk1 hk4 hk6 hk8
    omega

/-! ## `ℓ₀` reduced (line 1612) -/

open AE in
def pEll : St VV :=
  .seq (assign pX1 (mul (mul (var pW) (var pK)) (var vDEN))) (.seq (assign pX2 (mul (var vNUM) (var pR0)))
    (.seq (assign GCA (var pX1)) (.seq (assign GCB (var pX2)) (.seq gcdv
      (.seq (assign pEN (div (var pX1) (var GCA))) (assign pED (div (var pX2) (var GCA))))))))

def ellT : List (Fin VV) := [pX1, pX2, GCA, GCB, GCQ, GCR, pEN, pED, vJ]

theorem pEll_spec (a : DS VV) (hc : Cst a) (W k den num R0 S : ℕ) (hW : a.env pW = W) (hk : a.env pK = k)
    (hden : a.env vDEN = den) (hnum : a.env vNUM = num) (hR : a.env pR0 = R0) (hd1 : 1 ≤ den) (hn1 : 1 ≤ num)
    (hR1 : 1 ≤ R0) (hA : W * k * den < 2 ^ S) (hB : num * R0 < 2 ^ S) (hSW : S + 2 ≤ C.Wd) :
    Hs C pEll a (30 * S + 100) (fun b => b.env pX1 = W * k * den ∧ b.env pX2 = num * R0 ∧
      b.env pEN = W * k * den / Nat.gcd (W * k * den) (num * R0) ∧
      b.env pED = num * R0 / Nat.gcd (W * k * den) (num * R0) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ FrS a b ellT) := by
  have hAW : W * k * den < 2 ^ C.Wd := lt_pow_mono hA (by omega)
  have hBW : num * R0 < 2 ^ C.Wd := lt_pow_mono hB (by omega)
  have hWk : W * k ≤ W * k * den := Nat.le_mul_of_pos_right _ (by omega)
  have hBpos : 0 < num * R0 := Nat.mul_pos (by omega) (by omega)
  refine Hx.hs (Hs.then (assign_spec pX1 (by decide) (by decide) (.mul (.mul (.var pW) (.var pK)) (.var vDEN)) a
    (by aevar) (by aevar) hc (by aeok [hW, hk, hden])) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, hW, hk, hden] at p1
  have b1n : b1.env vNUM = num := by simp (disch := decide) only [p2.ev]; exact hnum
  have b1R : b1.env pR0 = R0 := by simp (disch := decide) only [p2.ev]; exact hR
  refine Hs.then (assign_spec pX2 (by decide) (by decide) (.mul (.var vNUM) (.var pR0)) b1 (by aevar) (by aevar) p6
    (by aeok [b1n, b1R])) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  simp only [AE.eval, b1n, b1R] at q1
  have b2A : b2.env pX1 = W * k * den := by simp (disch := decide) only [q2.ev]; exact p1
  refine Hs.then (assign_spec GCA (by decide) (by decide) (.var pX1) b2 (by aevar) (by aevar) q6 (by trivial))
    (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  simp only [AE.eval, b2A] at r1
  have b3B : b3.env pX2 = num * R0 := by simp (disch := decide) only [r2.ev]; exact q1
  refine Hs.then (assign_spec GCB (by decide) (by decide) (.var pX2) b3 (by aevar) (by aevar) r6 (by trivial))
    (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval, b3B] at s1
  have b4A : b4.env GCA = W * k * den := by simp (disch := decide) only [s2.ev]; exact r1
  have hM : 2 * (W * k * den + num * R0) ≤ 2 ^ C.Wd := by
    have := lt_pow_add hA hB
    have h2 : 2 ^ (S + 1) * 2 ≤ 2 ^ C.Wd := by rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine Hs.then (gcdv_spec b4 s6 _ _ (W * k * den + num * R0) b4A s1 (by omega) (by omega) hM)
    (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ k5 hk5 => ?_)
  set g := Nat.gcd (W * k * den) (num * R0) with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hBpos
  have hgB : g ≤ num * R0 := Nat.gcd_le_right _ hBpos
  have b5A : b5.env pX1 = W * k * den := by simp (disch := decide) only [u6.ev, s2.ev, r2.ev, q2.ev]; exact p1
  have b5B : b5.env pX2 = num * R0 := by simp (disch := decide) only [u6.ev, s2.ev, r2.ev]; exact q1
  refine Hs.then (assign_spec pEN (by decide) (by decide) (.div (.var pX1) (.var GCA)) b5 (by aevar) (by aevar) u5
    (by aeok [b5A, u1])) (fun b6 ⟨v1', v2', v3', v4', v5', v6'⟩ k6 hk6 => ?_)
  simp only [AE.eval, b5A, u1] at v1'
  have b6B : b6.env pX2 = num * R0 := by simp (disch := decide) only [v2'.ev]; exact b5B
  have b6g : b6.env GCA = g := by simp (disch := decide) only [v2'.ev]; exact u1
  refine Hs.last (assign_spec pED (by decide) (by decide) (.div (.var pX2) (.var GCA)) b6 (by aevar) (by aevar) v6'
    (by aeok [b6B, b6g])) (fun g' ⟨g1, g2, g3, g4, g5, g6⟩ k7 hk7 => ?_)
  simp only [AE.eval, b6B, b6g] at g1
  refine ⟨⟨by simp (disch := decide) only [g2.ev, v2'.ev]; exact b5A, by simp (disch := decide) only [g2.ev]; exact b6B,
    by simp (disch := decide) only [g2.ev]; exact v1', g1, by rw [g3, v3', u2, s3, r3, q3, p3],
    by rw [g4, v4', u3, s4, r4, q4, p4], by rw [g5, v5', u4, s5, r5, q5, p5], g6, ?_⟩, ?_⟩
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (FrS.trans (u6.toS.weaken (by decide)) (FrS.trans (v2'.toS _ (by decide) (by decide))
      (g2.toS _ (by decide) (by decide)))))))
  · simp only [AE.cost] at hk1 hk2 hk3 hk4 hk6 hk7
    have z1 : Nat.size (W * k * den) ≤ S := Nat.size_le.2 hA
    have z2 : Nat.size (num * R0) ≤ S := Nat.size_le.2 hB
    omega

/-! ## `ℓ̄`, `M₁`, `x₁` (lem:chain, lines 1118–1137, 1626–1630) -/

open AE in
def pBar : St VV :=
  .seq (assign pX3 (mul (mul (var pX1) (lit 256)) (var pT))) (.seq (assign pX4 (mul (mul (var pH) (var pH)) (var pX2)))
  (.seq (.ite (.lt pX4 pX3) (.seq (assign pBN (var pX1)) (assign pBD (var pX2)))
    (.seq (assign pBN (mul (var pH) (var pH))) (assign pBD (mul (lit 256) (var pT)))))
  (.seq (assign pX5 (mul (var pBD) (var pH)))
  (.seq (assign pM1 (div (sub (add (mul (lit 4) (var pBN)) (var pX5)) (lit 1)) (var pX5)))
  (.seq (assign pXN (mul (mul (lit 8) (var pT)) (var pBN)))
    (assign pXD (mul (mul (var pM1) (mul (var pH) (var pH))) (var pBD))))))))

def barT : List (Fin VV) := [pX3, pX4, pX5, pBN, pBD, pM1, pXN, pXD, vJ]

theorem pBar_spec (a : DS VV) (hc : Cst a) (A B h T S : ℕ) (hA : a.env pX1 = A) (hB : a.env pX2 = B)
    (hh : a.env pH = h) (hT : a.env pT = T) (hA0 : 0 < A) (hB0 : 0 < B) (hh0 : 0 < h) (hT0 : 0 < T)
    (hAS : A < 2 ^ S) (hBS : B < 2 ^ S) (hhS : h < 2 ^ S) (hTS : T < 2 ^ S) (hSW : 5 * S + 30 ≤ C.Wd) :
    Hs C pBar a 3000 (fun b => ((b.env pBN : ℚ) / b.env pBD = ellBar ((A : ℚ) / B) h T) ∧
      b.env pM1 = firstDen ((A : ℚ) / B) h T ∧ b.env pXN = 8 * T * b.env pBN ∧
      b.env pXD = firstDen ((A : ℚ) / B) h T * (h * h) * b.env pBD ∧
      firstRatio ((A : ℚ) / B) h T = (b.env pXN : ℚ) / b.env pXD ∧
      0 < b.env pXN ∧ 0 < b.env pXD ∧ b.env pXD ≤ (h + 32) * b.env pXN ∧ 4 * h * b.env pBN ≤ b.env pXD ∧
      b.env pXD < 2 ^ (5 * S + 22) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b barT) := by
  have w : ∀ x e, x < 2 ^ e → e ≤ C.Wd → x < 2 ^ C.Wd := fun x e h1 h2 => lt_pow_mono h1 h2
  have l256 : (256 : ℕ) < 2 ^ 9 := by norm_num
  have l8 : (8 : ℕ) < 2 ^ 4 := by norm_num
  have l4 : (4 : ℕ) < 2 ^ 3 := by norm_num
  have m1 := lt_pow_mul hAS l256
  have m2 := lt_pow_mul m1 hTS
  have m3 := lt_pow_mul hhS hhS
  have m4 := lt_pow_mul m3 hBS
  refine Hx.hs (Hs.then (assign_spec pX3 (by decide) (by decide) (.mul (.mul (.var pX1) (.lit 256)) (.var pT)) a
    (by aevar) (by aevar) hc (by
      simp only [AE.ok, AE.eval, hA, hT]
      exact ⟨⟨trivial, w _ _ l256 (by omega), w _ _ m1 (by omega)⟩, trivial,
        w _ _ m2 (by omega)⟩)) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, hA, hT] at p1
  have b1h : b1.env pH = h := by simp (disch := decide) only [p2.ev]; exact hh
  have b1B : b1.env pX2 = B := by simp (disch := decide) only [p2.ev]; exact hB
  refine Hs.then (assign_spec pX4 (by decide) (by decide) (.mul (.mul (.var pH) (.var pH)) (.var pX2)) b1
    (by aevar) (by aevar) p6 (by
      simp only [AE.ok, AE.eval, b1h, b1B]
      exact ⟨⟨trivial, trivial, w _ _ m3 (by omega)⟩, trivial, w _ _ m4 (by omega)⟩))
    (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  simp only [AE.eval, b1h, b1B] at q1
  have b2X3 : b2.env pX3 = A * 256 * T := by simp (disch := decide) only [q2.ev]; exact p1
  have b2A : b2.env pX1 = A := by simp (disch := decide) only [q2.ev, p2.ev]; exact hA
  have b2B : b2.env pX2 = B := by simp (disch := decide) only [q2.ev]; exact b1B
  have b2h : b2.env pH = h := by simp (disch := decide) only [q2.ev]; exact b1h
  have b2T : b2.env pT = T := by simp (disch := decide) only [q2.ev, p2.ev]; exact hT
  -- the branch: the pair `(BN, BD)` for `ℓ̄`
  have b2X4 : b2.env pX4 = h * h * B := q1
  have step : Hs C (.ite (.lt pX4 pX3) (.seq (assign pBN (.var pX1)) (assign pBD (.var pX2)))
      (.seq (assign pBN (.mul (.var pH) (.var pH))) (assign pBD (.mul (.lit 256) (.var pT))))) b2 600 (fun g =>
      g.env pBN = (if h * h * B < A * 256 * T then A else h * h) ∧
      g.env pBD = (if h * h * B < A * 256 * T then B else 256 * T) ∧ g.cp = b2.cp ∧ g.wq = b2.wq ∧
      g.out = b2.out ∧ Cst g ∧ FrS b2 g [pBN, pBD, vJ]) := by
    refine Hs.ite (show pX4 ≠ pX3 by decide) (fun he => ?_) (fun he => ?_)
    · have hlt : h * h * B < A * 256 * T := by simpa [Cnd.eval, b2X4, b2X3] using he
      rw [if_pos hlt, if_pos hlt]
      refine Hx.hs (Hs.then (assign_spec pBN (by decide) (by decide) (.var pX1) b2 (by aevar) (by aevar) q6
        (by trivial)) (fun d1 ⟨s1, s2, s3, s4, s5, s6⟩ k3 hk3 => ?_))
      refine Hs.last (assign_spec pBD (by decide) (by decide) (.var pX2) d1 (by aevar) (by aevar) s6 (by trivial))
        (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k4 hk4 => ?_)
      simp only [AE.eval] at s1 g1
      refine ⟨⟨by simp (disch := decide) only [g2.ev]; rw [s1, b2A],
        by rw [g1]; simp (disch := decide) only [s2.ev]; exact b2B, by rw [g3, s3], by rw [g4, s4], by rw [g5, s5], g6,
        FrS.trans (s2.toS _ (by decide) (by decide)) (g2.toS _ (by decide) (by decide))⟩, ?_⟩
      simp only [AE.cost] at hk3 hk4
      omega
    · have hlt : ¬ h * h * B < A * 256 * T := by simpa [Cnd.eval, b2X4, b2X3] using he
      rw [if_neg hlt, if_neg hlt]
      refine Hx.hs (Hs.then (assign_spec pBN (by decide) (by decide) (.mul (.var pH) (.var pH)) b2 (by aevar)
        (by aevar) q6 (by
          simp only [AE.ok, AE.eval, b2h]
          exact ⟨trivial, trivial, w _ _ m3 (by omega)⟩)) (fun d1 ⟨s1, s2, s3, s4, s5, s6⟩ k3 hk3 => ?_))
      have d1T : d1.env pT = T := by simp (disch := decide) only [s2.ev]; exact b2T
      refine Hs.last (assign_spec pBD (by decide) (by decide) (.mul (.lit 256) (.var pT)) d1 (by aevar) (by aevar) s6
        (by
          simp only [AE.ok, AE.eval, d1T]
          exact ⟨w _ _ l256 (by omega), trivial,
            w _ _ (lt_pow_mul l256 hTS) (by omega)⟩)) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k4 hk4 => ?_)
      simp only [AE.eval, b2h, d1T] at s1 g1
      refine ⟨⟨by simp (disch := decide) only [g2.ev]; exact s1, g1, by rw [g3, s3], by rw [g4, s4], by rw [g5, s5], g6,
        FrS.trans (s2.toS _ (by decide) (by decide)) (g2.toS _ (by decide) (by decide))⟩, ?_⟩
      simp only [AE.cost] at hk3 hk4
      omega
  refine Hs.then step (fun b3 ⟨r1, r2, r3, r4, r5, r6, r7⟩ k3 hk3 => ?_)
  obtain ⟨BN, hBN⟩ : ∃ BN, b3.env pBN = BN := ⟨_, rfl⟩
  obtain ⟨BD, hBD⟩ : ∃ BD, b3.env pBD = BD := ⟨_, rfl⟩
  have hbar : (BN : ℚ) / BD = ellBar ((A : ℚ) / B) h T := by
    rw [ellBar_eq A B h T hB0 hT0, ← hBN, ← hBD, r1, r2]
    split_ifs <;> push_cast <;> rfl
  have hBN0 : 0 < BN := by rw [← hBN, r1]; split_ifs; exact hA0; exact Nat.mul_pos hh0 hh0
  have hBD0 : 0 < BD := by rw [← hBD, r2]; split_ifs; exact hB0; omega
  have hBNS : BN < 2 ^ (2 * S) := by
    rw [← hBN, r1]; split_ifs
    · exact lt_pow_mono hAS (by omega)
    · rw [show 2 * S = S + S by ring]; exact m3
  have hBDS : BD < 2 ^ (S + 9) := by
    rw [← hBD, r2]; split_ifs
    · exact lt_pow_mono hBS (by omega)
    · exact lt_pow_mono (lt_pow_mul l256 hTS) (by omega)
  have hBDh : BD * (h * h) ≤ 256 * T * BN := by
    rw [← hBN, ← hBD, r1, r2]; split_ifs with hc'
    · have e1 : B * (h * h) = h * h * B := by ring
      have e2 : 256 * T * A = A * 256 * T := by ring
      omega
    · rw [mul_comm]
  have b3h : b3.env pH = h := by simp (disch := decide) only [r7.ev]; exact b2h
  have b3T : b3.env pT = T := by simp (disch := decide) only [r7.ev]; exact b2T
  have n1 := lt_pow_mul hBDS hhS
  refine Hs.then (assign_spec pX5 (by decide) (by decide) (.mul (.var pBD) (.var pH)) b3 (by aevar) (by aevar) r6
    (by
      simp only [AE.ok, AE.eval, hBD, b3h]
      exact ⟨trivial, trivial, w _ _ n1 (by omega)⟩)) (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval, hBD, b3h] at s1
  have b4N : b4.env pBN = BN := by simp (disch := decide) only [s2.ev]; exact hBN
  have hX5 : 0 < BD * h := Nat.mul_pos hBD0 hh0
  have n2 := lt_pow_mul l4 hBNS
  have n3 : 4 * BN + BD * h < 2 ^ (2 * S + 13) := by
    have a1 := lt_pow_mono n2 (show 3 + 2 * S ≤ 2 * S + 12 by omega)
    have a2 := lt_pow_mono n1 (show S + 9 + S ≤ 2 * S + 12 by omega)
    exact lt_pow_add a1 a2
  refine Hs.then (assign_spec pM1 (by decide) (by decide) (.div (.sub (.add (.mul (.lit 4) (.var pBN)) (.var pX5))
    (.lit 1)) (.var pX5)) b4 (by aevar) (by aevar) s6 (by
      simp only [AE.ok, AE.eval, b4N, s1]
      have z1 := w _ _ n2 (show 3 + 2 * S ≤ C.Wd by omega)
      have z2 := w _ _ n3 (show 2 * S + 13 ≤ C.Wd by omega)
      have z3 : BD * h + BD * h < 2 ^ C.Wd := w _ _ (lt_pow_add n1 n1) (by omega)
      have z5 : (4 : ℕ) < 2 ^ C.Wd := w _ _ l4 (by omega)
      refine ⟨⟨⟨⟨z5, trivial, by omega⟩, trivial, by omega⟩, by omega⟩, trivial, hX5, by omega⟩))
    (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ k5 hk5 => ?_)
  simp only [AE.eval, b4N, s1] at u1
  have hM1 : b5.env pM1 = firstDen ((A : ℚ) / B) h T := by
    rw [u1, firstDen_eq _ h T BN BD hbar.symm hBD0 hh0]
  obtain ⟨M1, hM1d⟩ : ∃ M1, (4 * BN + BD * h - 1) / (BD * h) = M1 := ⟨_, rfl⟩
  have hM1le : M1 * (BD * h) ≤ 4 * BN + BD * h - 1 := hM1d ▸ Nat.div_mul_le_self _ _
  have hM1pos : 0 < M1 := by
    rw [← hM1d]; exact Nat.div_pos (by omega) hX5
  have hM1S : M1 < 2 ^ (2 * S + 13) := by
    have : M1 ≤ M1 * (BD * h) := Nat.le_mul_of_pos_right _ hX5
    omega
  rw [hM1d] at u1
  have b5N : b5.env pBN = BN := by simp (disch := decide) only [u2.ev]; exact b4N
  have b5T : b5.env pT = T := by simp (disch := decide) only [u2.ev, s2.ev]; exact b3T
  have n4 := lt_pow_mul l8 hTS
  have n5 := lt_pow_mul n4 hBNS
  refine Hs.then (assign_spec pXN (by decide) (by decide) (.mul (.mul (.lit 8) (.var pT)) (.var pBN)) b5 (by aevar)
    (by aevar) u6 (by
      simp only [AE.ok, AE.eval, b5N, b5T]
      exact ⟨⟨w _ _ l8 (by omega), trivial, w _ _ n4 (by omega)⟩, trivial, w _ _ n5 (by omega)⟩))
    (fun b6 ⟨v1', v2', v3', v4', v5', v6'⟩ k6 hk6 => ?_)
  simp only [AE.eval, b5N, b5T] at v1'
  have b6M : b6.env pM1 = M1 := by simp (disch := decide) only [v2'.ev]; exact u1
  have b6h : b6.env pH = h := by simp (disch := decide) only [v2'.ev, u2.ev, s2.ev]; exact b3h
  have b6D : b6.env pBD = BD := by simp (disch := decide) only [v2'.ev, u2.ev, s2.ev]; exact hBD
  have n6 := lt_pow_mul hM1S m3
  have n7 := lt_pow_mul n6 hBDS
  refine Hs.last (assign_spec pXD (by decide) (by decide) (.mul (.mul (.var pM1) (.mul (.var pH) (.var pH))) (.var pBD))
    b6 (by aevar) (by aevar) v6' (by
      simp only [AE.ok, AE.eval, b6M, b6h, b6D]
      exact ⟨⟨trivial, ⟨trivial, trivial, w _ _ m3 (by omega)⟩, w _ _ n6 (by omega)⟩, trivial, w _ _ n7 (by omega)⟩))
    (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k7 hk7 => ?_)
  simp only [AE.eval, b6M, b6h, b6D] at g1
  have gN : g.env pBN = BN := by simp (disch := decide) only [g2.ev, v2'.ev]; exact b5N
  have gD : g.env pBD = BD := by simp (disch := decide) only [g2.ev]; exact b6D
  have gXN : g.env pXN = 8 * T * BN := by simp (disch := decide) only [g2.ev]; exact v1'
  have gM : g.env pM1 = M1 := by simp (disch := decide) only [g2.ev]; exact b6M
  have hfd : firstDen ((A : ℚ) / B) h T = M1 := by rw [firstDen_eq _ h T BN BD hbar.symm hBD0 hh0, hM1d]
  have hXN0 : 0 < 8 * T * BN := by positivity
  have hXD0 : 0 < M1 * (h * h) * BD := by positivity
  have hXDle : M1 * (h * h) * BD ≤ (h + 32) * (8 * T * BN) := by
    have e1 : M1 * (h * h) * BD = h * (M1 * (BD * h)) := by ring
    have e2 : h * (M1 * (BD * h)) ≤ h * (4 * BN + BD * h) := Nat.mul_le_mul_left _ (by omega)
    have e3 : h * (4 * BN + BD * h) = 4 * h * BN + BD * (h * h) := by ring
    have e4 : 4 * h * BN ≤ 8 * T * h * BN := by
      have : 4 * h * BN * 1 ≤ 4 * h * BN * (2 * T) := Nat.mul_le_mul_left _ (by omega)
      calc 4 * h * BN = 4 * h * BN * 1 := by ring
        _ ≤ 4 * h * BN * (2 * T) := this
        _ = 8 * T * h * BN := by ring
    have e5 : (h + 32) * (8 * T * BN) = 8 * T * h * BN + 256 * T * BN := by ring
    omega
  have hM1ge : 4 * BN ≤ M1 * (BD * h) := by
    rw [← hM1d]
    have h1 := Nat.div_add_mod (4 * BN + BD * h - 1) (BD * h)
    have h2 := Nat.mod_lt (4 * BN + BD * h - 1) hX5
    have h3 : (4 * BN + BD * h - 1) / (BD * h) * (BD * h) = BD * h * ((4 * BN + BD * h - 1) / (BD * h)) := mul_comm _ _
    omega
  have hXDge : 4 * h * BN ≤ M1 * (h * h) * BD := by
    have e1 : M1 * (h * h) * BD = h * (M1 * (BD * h)) := by ring
    have e2 : 4 * h * BN = h * (4 * BN) := by ring
    rw [e1, e2]; exact Nat.mul_le_mul_left _ hM1ge
  refine ⟨⟨by rw [gN, gD]; exact hbar, by rw [gM, hfd], by rw [gXN, gN], by rw [g1, hfd, gD], ?_, by rw [gXN]; exact hXN0,
    by rw [g1]; exact hXD0, by rw [g1, gXN]; exact hXDle, by rw [g1, gN]; exact hXDge, by rw [g1]; exact lt_pow_mono n7 (by omega), by rw [g3, v3', u3, s3, r3, q3, p3],
    by rw [g4, v4', u4, s4, r4, q4, p4], by rw [g5, v5', u5, s5, r5, q5, p5], g6, ?_⟩, ?_⟩
  · rw [gXN, g1, firstRatio_eq _ h T BN BD hbar.symm hBD0 hh0 hT0 hBN0 (by rw [hfd]; exact hM1pos), hfd]
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide))
      (FrS.trans (r7.weaken (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (FrS.trans (u2.toS _ (by decide) (by decide)) (FrS.trans (v2'.toS _ (by decide) (by decide))
      (g2.toS _ (by decide) (by decide)))))))
  · simp only [AE.cost] at hk1 hk2 hk4 hk5 hk6 hk7
    omega

end NearCubicGates.Close.Dispatch
