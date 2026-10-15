import Proof.Gates.Dispatch.ParamsE

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces

variable {C : Ctx}

def pA : Fin VV := ⟨162, by decide⟩
def pCI : Fin VV := ⟨192, by decide⟩
def pCN : Fin VV := ⟨193, by decide⟩
def pJ1 : Fin VV := ⟨194, by decide⟩
def pCG : Fin VV := ⟨195, by decide⟩
def pCF : Fin VV := ⟨196, by decide⟩

theorem natBitLength_le_succ (v : ℕ) : natBitLength v ≤ v + 1 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with h | h
  · subst h; simp
  · have := Nat.log_lt_self 2 (show v ≠ 0 by omega); omega

theorem chainFactors_succ (x : ℚ) (i : ℕ) :
    chainFactors x (i + 1) = chainFactors x i ++ [RationalRateChain.factorRat (RationalRateChain.ratio x i)] := by
  unfold chainFactors; rw [List.range_succ, List.map_append]; rfl

/-! ## The loop test -/

open AE in
def goP : St VV :=
  .seq (assign pX1 (add (mul (lit 256) (var pCN)) (lit 1))) (.seq (flagLe pCG pX1 pXD)
    (.seq (assign pX2 (add (var pCI) (lit 1))) (killIf (.lt pJ1 pX2) pCG)))

def goT : List (Fin VV) := [pX1, pX2, pCG, vJ]

theorem goP_spec (a : DS VV) (hc : Cst a) (N D i J1 : ℕ) (hN : a.env pCN = N) (hD : a.env pXD = D)
    (hi : a.env pCI = i) (hJ : a.env pJ1 = J1) (hW : 256 * N + i + 600 < 2 ^ C.Wd) :
    Hs C goP a 600 (fun b => b.env pCG = bnat (256 * N < D ∧ i < J1) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ FrS a b goT) := by
  have h1W : 1 < 2 ^ C.Wd := by omega
  refine Hx.hs (Hs.then (assign_spec pX1 (by decide) (by decide) (.add (.mul (.lit 256) (.var pCN)) (.lit 1)) a
    (by aevar) (by aevar) hc (by aeok [hN])) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, hN] at p1
  refine Hs.then (flagLe_spec pCG pX1 pXD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) b1 p6 h1W) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  have b2i : b2.env pCI = i := by simp (disch := decide) only [q2.ev, p2.ev]; exact hi
  have hD1 : b1.env pXD = D := by simp (disch := decide) only [p2.ev]; exact hD
  rw [p1, hD1] at q1
  refine Hs.then (assign_spec pX2 (by decide) (by decide) (.add (.var pCI) (.lit 1)) b2 (by aevar) (by aevar) q6
    (by aeok [b2i])) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  simp only [AE.eval, b2i] at r1
  refine Hs.last (killIf_spec (.lt pJ1 pX2) pCG (show pJ1 ≠ pX2 by decide) (by decide) b3)
    (fun g ⟨g1, g2, g3, g4, g5⟩ k4 hk4 => ?_)
  have b3J : b3.env pJ1 = J1 := by simp (disch := decide) only [r2.ev, q2.ev, p2.ev]; exact hJ
  have b3G : b3.env pCG = bnat (256 * N + 1 ≤ D) := by simp (disch := decide) only [r2.ev]; exact q1
  refine ⟨⟨?_, by rw [g2, r3, q3, p3], by rw [g3, r4, q4, p4], by rw [g4, r5, q5, p5],
    Cst.of_fr r6 g5 (by decide) (by rw [g5 vPOS (by decide), g2]; exact r6.pos), ?_⟩, ?_⟩
  · rw [g1]
    simp only [Cnd.eval, b3J, r1]
    by_cases hc' : J1 < i + 1
    · rw [if_pos (by simpa using hc')]
      symm; unfold bnat; simp only [Bool.toNat_eq_zero, decide_eq_false_iff_not]
      omega
    · rw [if_neg (by simpa using hc'), b3G]
      exact bnat_congr (by omega)
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (g5.toS.weaken (by decide))))
  · simp only [AE.cost] at hk1 hk3
    omega

/-! ## One step of the chain -/

/-- Print the factor (in `SQS`) when `pr`. -/
def emitIf (pr : Bool) : St VV := if pr then .seq (assign t3 (.var SQS)) emitNat else skipS

open AE in
def chainBody (pr : Bool) : St VV :=
  .seq (assign SQX (div (var pXD) (mul (lit 16) (var pCN)))) (.seq sqrtv (.seq (emitIf pr)
    (.seq (assign pCN (mul (var SQS) (var pCN))) (.seq (assign pA (mul (var pA) (var SQS)))
      (.seq (assign pCI (add (var pCI) (lit 1))) goP)))))

def chT : List (Fin VV) := [pCI, pCN, pA, pJ1, pCG, pCF, pX1, pX2, SQX, SQS, SQF, SQT, SQU, t3, t5, t6, t7, t8, t9,
  vJ]

/-- The chain invariant after `i` steps. -/
def ChI (a0 : DS VV) (pr : Bool) (x : ℚ) (N0 D J1 : ℕ) (b : DS VV) : Prop :=
  ∃ i, b.env pCI = i ∧ i ≤ J1 ∧ RationalRateChain.ratio x i = (b.env pCN : ℚ) / D ∧
    (∀ j < i, RationalRateChain.ratio x j < 1 / 256) ∧ b.env pA = (chainFactors x i).prod ∧
    b.env pA * N0 ≤ b.env pCN ∧ N0 ≤ b.env pCN ∧ b.env pCN ≤ D ∧
    b.env pCG = bnat (256 * b.env pCN < D ∧ i < J1) ∧ b.env pXD = D ∧ b.env pJ1 = J1 ∧
    b.out = a0.out ++ (if pr then (chainFactors x i).flatMap natWord else []) ∧ b.cp = a0.cp ∧ b.wq = a0.wq ∧
    Cst b ∧ FrS a0 b chT

def bodyCost (h : ℕ) : ℕ := 60 * h + 3000

theorem chainBody_spec (a0 : DS VV) (pr : Bool) (x : ℚ) (N0 D J1 h : ℕ) (hN0 : 0 < N0) (hDle : D ≤ (h + 32) * N0)
    (hW : 1024 * D + (h + 33) * (h + 33) + J1 + 1000 < 2 ^ C.Wd) (hW2 : 2 ≤ C.Wd)
    (b : DS VV) (hb : ChI a0 pr x N0 D J1 b) (hgo : (Cnd.eq pCG v1).eval b = true) :
    Hs C (chainBody pr) b (bodyCost h) (fun g => ChI a0 pr x N0 D J1 g ∧ J1 - g.env pCI < J1 - b.env pCI) := by
  obtain ⟨i, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16⟩ := hb
  obtain ⟨N, hNd⟩ : ∃ N, b.env pCN = N := ⟨_, rfl⟩
  rw [hNd] at i3 i6 i7 i8 i9
  have hgo' : 256 * N < D ∧ i < J1 := by
    have : b.env pCG = 1 := by simpa [Cnd.eval, i15.one] using hgo
    rw [i9] at this; exact (bnat_eq_one _).1 this
  have hNpos : 0 < N := by omega
  have hq16 : 16 ≤ D / (16 * N) := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
  have hqle : D / (16 * N) ≤ h + 32 := by
    calc D / (16 * N) ≤ D / N0 := Nat.div_le_div_left (by omega) hN0
      _ ≤ h + 32 := Nat.div_le_of_le_mul (by rw [mul_comm]; exact hDle)
  set q := D / (16 * N) with hq
  set s := Nat.sqrt q with hs
  have hs1 : 1 ≤ s := by
    have : Nat.sqrt 16 ≤ s := Nat.sqrt_le_sqrt hq16
    have h16 : Nat.sqrt 16 = 4 := by rw [show (16 : ℕ) = 4 * 4 by norm_num, Nat.sqrt_eq]
    omega
  have hss : s * s ≤ q := Nat.sqrt_le q
  have hsq : s ≤ q := Nat.sqrt_le_self q
  have hq16N : q * (16 * N) ≤ D := Nat.div_mul_le_self D (16 * N)
  have hsN : s * N ≤ D := by
    have : s * N ≤ s * s * N := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega))
    have : s * s * N ≤ q * (16 * N) := by
      calc s * s * N ≤ q * N := Nat.mul_le_mul_right _ hss
        _ ≤ q * (16 * N) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hAs : b.env pA * s * N0 ≤ s * N := by
    calc b.env pA * s * N0 = s * (b.env pA * N0) := by ring
      _ ≤ s * N := Nat.mul_le_mul_left _ i6
  have hD16 : 16 * N ≤ 16 * D := by omega
  -- the step
  refine Hx.hs (Hs.then (assign_spec SQX (by decide) (by decide) (.div (.var pXD) (.mul (.lit 16) (.var pCN))) b
    (by aevar) (by aevar) i15 (by aeok [i10, hNd])) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, i10, hNd] at p1
  rw [← hq] at p1
  have hqq : q * q < 2 ^ C.Wd := by
    have : q * q ≤ (h + 33) * (h + 33) := Nat.mul_le_mul (by omega) (by omega)
    omega
  refine Hs.then (sqrtv_spec b1 p6 q p1 hqq) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  rw [← hs] at q1
  -- the optional print
  have hemit : Hs C (emitIf pr) b2 (40 * (h + 34) + 50) (fun d => d.env SQS = s ∧
      d.out = b2.out ++ (if pr then natWord s else []) ∧ d.cp = b2.cp ∧ d.wq = b2.wq ∧ Cst d ∧
      FrS b2 d [t3, t5, t6, t7, t8, t9, vJ]) := by
    cases pr with
    | false =>
      refine Hs.mono (skip_spec b2) (by omega) ?_
      rintro d rfl
      exact ⟨by rw [DS.set_env_ne _ _ (by decide), q1], by simp, rfl, rfl, Cst.set q5 _ _ (by decide),
        Fr.toS (Fr.set _ _ (by decide))⟩
    | true =>
      refine Hx.hs (Hs.then (assign_spec t3 (by decide) (by decide) (.var SQS) b2 (by aevar) (by aevar) q5
        (by trivial)) (fun d1 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_))
      simp only [AE.eval, q1] at r1
      have hbl : natBitLength s ≤ h + 34 := le_trans (natBitLength_le_succ s) (by omega)
      have := Nat.le_mul_self (h + 33)
      refine Hs.last (emitNat_spec d1 r6 hW2 (by rw [r1]; omega)) (fun d ⟨g1, g2, g3, g4, g5⟩ k4 hk4 => ?_)
      rw [r1] at g1 hk4
      refine ⟨⟨by simp (disch := decide) only [g5.ev, r2.ev]; exact q1, by rw [g1, r5]; simp, by rw [g2, r3],
        by rw [g3, r4], g4, FrS.trans (r2.toS _ (by decide) (by decide)) (g5.toS.weaken (by decide))⟩, ?_⟩
      simp only [AE.cost] at hk3
      omega
  refine Hs.then hemit (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  have b3N : b3.env pCN = N := by simp (disch := decide) only [r6.ev, q6.ev, p2.ev]; exact hNd
  have hsNW : s * N < 2 ^ C.Wd := by omega
  refine Hs.then (assign_spec pCN (by decide) (by decide) (.mul (.var SQS) (.var pCN)) b3 (by aevar) (by aevar) r5
    (by aeok [r1, b3N])) (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval, r1, b3N] at s1
  have b4A : b4.env pA = b.env pA := by simp (disch := decide) only [s2.ev, r6.ev, q6.ev, p2.ev]
  have b4S : b4.env SQS = s := by simp (disch := decide) only [s2.ev]; exact r1
  have hAsW : b.env pA * s < 2 ^ C.Wd := by
    have : b.env pA * s ≤ b.env pA * s * N0 := Nat.le_mul_of_pos_right _ hN0
    omega
  refine Hs.then (assign_spec pA (by decide) (by decide) (.mul (.var pA) (.var SQS)) b4 (by aevar) (by aevar) s6
    (by aeok [b4A, b4S])) (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ k5 hk5 => ?_)
  simp only [AE.eval, b4A, b4S] at u1
  have b5i : b5.env pCI = i := by simp (disch := decide) only [u2.ev, s2.ev, r6.ev, q6.ev, p2.ev]; exact i1
  refine Hs.then (assign_spec pCI (by decide) (by decide) (.add (.var pCI) (.lit 1)) b5 (by aevar) (by aevar) u6
    (by aeok [b5i])) (fun b6 ⟨v1', v2', v3', v4', v5', v6'⟩ k6 hk6 => ?_)
  simp only [AE.eval, b5i] at v1'
  have b6N : b6.env pCN = s * N := by simp (disch := decide) only [v2'.ev, u2.ev]; exact s1
  have b6D : b6.env pXD = D := by simp (disch := decide) only [v2'.ev, u2.ev, s2.ev, r6.ev, q6.ev, p2.ev]; exact i10
  have b6J : b6.env pJ1 = J1 := by simp (disch := decide) only [v2'.ev, u2.ev, s2.ev, r6.ev, q6.ev, p2.ev]; exact i11
  refine Hs.last (goP_spec b6 v6' (s * N) D (i + 1) J1 b6N b6D v1' b6J (by omega))
    (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k7 hk7 => ?_)
  obtain ⟨hr1, hf⟩ := ratio_succ_lt x i N D i3 hNpos hgo'.1
  rw [← hq, ← hs] at hr1 hf
  have gi : g.env pCI = i + 1 := by simp (disch := decide) only [g6.ev]; exact v1'
  have gN : g.env pCN = s * N := by simp (disch := decide) only [g6.ev]; exact b6N
  have gA : g.env pA = b.env pA * s := by simp (disch := decide) only [g6.ev, v2'.ev]; exact u1
  have gD : g.env pXD = D := by simp (disch := decide) only [g6.ev]; exact b6D
  have gJ : g.env pJ1 = J1 := by simp (disch := decide) only [g6.ev]; exact b6J
  have gNle : N0 ≤ g.env pCN := by rw [gN]; exact le_trans i7 (Nat.le_mul_of_pos_left _ (by omega))
  have gcp : g.cp = a0.cp := by rw [g2, v3', u3, s3, r3, q2, p3, i13]
  have gwq : g.wq = a0.wq := by rw [g3, v4', u4, s4, r4, q3, p4, i14]
  have gmu : J1 - g.env pCI < J1 - b.env pCI := by rw [gi, i1]; omega
  refine ⟨⟨⟨i + 1, gi, by omega, by rw [gN, hr1], fun j hj => ?_, ?_, ?_, gNle, by rw [gN]; exact hsN,
      by rw [g1, gN], gD, gJ, ?_, gcp, gwq, g5, ?_⟩, gmu⟩, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact i4 j hj
    · subst hj; rw [i3]
      have := (ratio_ge_iff N D (by omega)).not.2 (by omega)
      exact lt_of_not_ge this
  · rw [gA, i5, chainFactors_succ, List.prod_append, List.prod_singleton, hf]
  · rw [gA, gN]; exact hAs
  · rw [g4, v5', u5, s5, r2, q4, p5, i12, chainFactors_succ, List.flatMap_append]
    cases pr <;> simp [hf]
  · exact FrS.trans i16 (FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q6.toS.weaken (by decide))
      (FrS.trans (r6.weaken (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (FrS.trans (u2.toS _ (by decide) (by decide)) (FrS.trans (v2'.toS _ (by decide) (by decide))
      (g6.weaken (by decide))))))))
  · simp only [AE.cost] at hk1 hk4 hk5 hk6
    unfold bodyCost
    omega

/-! ## The whole chain -/

open AE in
def chainP (pr : Bool) : St VV :=
  .seq (assign pCI (lit 0)) (.seq (assign pCN (var pXN)) (.seq (assign pA (lit 1))
    (.seq (assign pJ1 (sub (var pJM) (lit 1))) (.seq goP (.seq (.loop (.eq pCG v1) (chainBody pr))
      (.seq (assign pX1 (mul (lit 256) (var pCN))) (flagLe pCF pXD pX1)))))))

def chainCost (J h : ℕ) : ℕ := (J + 1) * (bodyCost h + 2) + 2000

theorem chainP_spec (a : DS VV) (hc : Cst a) (pr : Bool) (x : ℚ) (n N0 D h : ℕ) (hXN : a.env pXN = N0)
    (hXD : a.env pXD = D) (hJ : a.env pJM = Jmax n) (hx : x = (N0 : ℚ) / D) (hN0 : 0 < N0) (hND : N0 ≤ D)
    (hDle : D ≤ (h + 32) * N0) (hW : 1024 * D + (h + 33) * (h + 33) + Jmax n + 1000 < 2 ^ C.Wd) (hW2 : 2 ≤ C.Wd) :
    Hs C (chainP pr) a (chainCost (Jmax n) h) (fun b => (∃ i, b.env pCI = i ∧ b.env pA = (chainFactors x i).prod ∧
      b.out = a.out ++ (if pr then (chainFactors x i).flatMap natWord else []) ∧
      ((b.env pCF = 1 ∧ stopIndex x n = some i) ∨ (b.env pCF = 0 ∧ stopIndex x n = none))) ∧ b.env pA ≤ D ∧
      b.env pCI ≤ Jmax n - 1 ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ FrS a b chT) := by
  have h1W : 1 < 2 ^ C.Wd := by omega
  set J1 := Jmax n - 1 with hJ1
  refine Hx.hs (Hs.then (assign_spec pCI (by decide) (by decide) (.lit 0) a (by aevar) (by aevar) hc (by aeok []))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval] at p1
  refine Hs.then (assign_spec pCN (by decide) (by decide) (.var pXN) b1 (by aevar) (by aevar) p6 (by trivial))
    (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  have hN1 : b1.env pXN = N0 := by simp (disch := decide) only [p2.ev]; exact hXN
  simp only [AE.eval, hN1] at q1
  refine Hs.then (assign_spec pA (by decide) (by decide) (.lit 1) b2 (by aevar) (by aevar) q6 (by aeok []))
    (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  simp only [AE.eval] at r1
  have b3J : b3.env pJM = Jmax n := by simp (disch := decide) only [r2.ev, q2.ev, p2.ev]; exact hJ
  refine Hs.then (assign_spec pJ1 (by decide) (by decide) (.sub (.var pJM) (.lit 1)) b3 (by aevar) (by aevar) r6
    (by simp only [AE.ok]; exact ⟨trivial, h1W⟩)) (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval, b3J] at s1
  have b4N : b4.env pCN = N0 := by simp (disch := decide) only [s2.ev, r2.ev]; exact q1
  have b4D : b4.env pXD = D := by simp (disch := decide) only [s2.ev, r2.ev, q2.ev, p2.ev]; exact hXD
  have b4i : b4.env pCI = 0 := by simp (disch := decide) only [s2.ev, r2.ev, q2.ev]; exact p1
  refine Hs.then (goP_spec b4 s6 N0 D 0 J1 b4N b4D b4i s1 (by omega)) (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ k5 hk5 => ?_)
  have hI : ChI a pr x N0 D J1 b5 := by
    refine ⟨0, by simp (disch := decide) only [u6.ev]; exact b4i, Nat.zero_le _, ?_, fun j hj => absurd hj (by omega),
      ?_, ?_, ?_, ?_, ?_, by simp (disch := decide) only [u6.ev]; exact b4D,
      by simp (disch := decide) only [u6.ev]; exact s1, ?_, by rw [u2, s3, r3, q3, p3],
      by rw [u3, s4, r4, q4, p4], u5, ?_⟩
    · rw [hx]; simp (disch := decide) only [u6.ev]; rw [b4N]; rfl
    · simp (disch := decide) only [u6.ev, s2.ev]; rw [r1]; rfl
    · simp (disch := decide) only [u6.ev, s2.ev, r2.ev]; rw [r1, q1, one_mul]
    · simp (disch := decide) only [u6.ev]; rw [b4N]
    · simp (disch := decide) only [u6.ev]; rw [b4N]; exact hND
    · simp (disch := decide) only [u6.ev]; rw [b4N]; exact u1
    · rw [u4, s5, r5, q5, p5]; cases pr <;> simp [chainFactors]
    · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide))
        (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
        (u6.weaken (by decide)))))
  have l := Hs.loopM (C := C) (c := .eq pCG v1) (s := chainBody pr) (show pCG ≠ v1 by decide) (ChI a pr x N0 D J1)
    (fun b => J1 - b.env pCI) (bodyCost h)
    (fun b hb he => chainBody_spec a pr x N0 D J1 h hN0 hDle (by omega) hW2 b hb he) b5 hI
  refine Hs.then l (fun b6 ⟨⟨i, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16⟩, hstop⟩ k6 hk6 => ?_)
  obtain ⟨N, hNd⟩ : ∃ N, b6.env pCN = N := ⟨_, rfl⟩
  rw [hNd] at i3 i6 i7 i8 i9
  have hno : ¬ (256 * N < D ∧ i < J1) := by
    intro h'
    have : b6.env pCG = 1 := by rw [i9]; exact (bnat_eq_one _).2 h'
    simp [Cnd.eval, this, i15.one] at hstop
  refine Hs.then (assign_spec pX1 (by decide) (by decide) (.mul (.lit 256) (.var pCN)) b6 (by aevar) (by aevar) i15
    (by aeok [hNd])) (fun b7 ⟨v1', v2', v3', v4', v5', v6'⟩ k7 hk7 => ?_)
  simp only [AE.eval, hNd] at v1'
  refine Hs.last (flagLe_spec pCF pXD pX1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) b7 v6' h1W) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k8 hk8 => ?_)
  have b7D : b7.env pXD = D := by simp (disch := decide) only [v2'.ev]; exact i10
  rw [b7D, v1'] at g1
  have gi : g.env pCI = i := by simp (disch := decide) only [g2.ev, v2'.ev]; exact i1
  have gA : g.env pA = (chainFactors x i).prod := by simp (disch := decide) only [g2.ev, v2'.ev]; exact i5
  have hAD : b6.env pA ≤ D := by
    have : b6.env pA ≤ b6.env pA * N0 := Nat.le_mul_of_pos_right _ hN0
    omega
  refine ⟨⟨⟨i, gi, gA, by rw [g5, v5', i12], ?_⟩, by simp (disch := decide) only [g2.ev, v2'.ev]; exact hAD,
    by rw [gi]; exact i2, by rw [g3, v3', i13], by rw [g4, v4', i14], g6, ?_⟩, ?_⟩
  · by_cases hf : D ≤ 256 * N
    · left
      refine ⟨by rw [g1]; exact (bnat_eq_one _).2 hf, ?_⟩
      unfold stopIndex
      exact leastUpTo_eq _ _ _ i2 (by rw [i3]; exact (ratio_ge_iff N D (by omega)).2 hf)
        (fun j hj => not_le.2 (i4 j hj))
    · right
      refine ⟨by rw [g1]; unfold bnat; simp [hf], ?_⟩
      have hiJ : i = J1 := by omega
      unfold stopIndex
      exact lsScan_none _ _ (fun s hs hsB => by
        rcases Nat.lt_or_ge s i with h' | h'
        · exact not_le.2 (i4 s h')
        · have : s = i := by omega
          subst this
          rw [i3]; exact fun h'' => hf ((ratio_ge_iff N D (by omega)).1 h''))
  · exact FrS.trans i16 (FrS.trans (v2'.toS _ (by decide) (by decide)) (g2.toS _ (by decide) (by decide)))
  · simp only [AE.cost] at hk1 hk2 hk3 hk4 hk7
    have hμ : J1 - b5.env pCI = J1 := by
      have : b5.env pCI = 0 := by simp (disch := decide) only [u6.ev]; exact b4i
      rw [this]; rfl
    rw [hμ] at hk6
    have e1 : J1 * (bodyCost h + 2) ≤ Jmax n * (bodyCost h + 2) := Nat.mul_le_mul_right _ (by omega)
    have e2 : (Jmax n + 1) * (bodyCost h + 2) = Jmax n * (bodyCost h + 2) + (bodyCost h + 2) := by ring
    unfold chainCost
    omega

end NearCubicGates.Close.Dispatch
