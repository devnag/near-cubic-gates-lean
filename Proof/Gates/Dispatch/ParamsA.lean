import Proof.Gates.Dispatch.NumTh
import Proof.Gates.Dispatch.Expr
import Proof.Gates.Dispatch.Admit
import Proof.Gates.Counter.Pure

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter

variable {C : Ctx}

def pLAM : Fin VV := ⟨140, by decide⟩
def pMU : Fin VV := ⟨141, by decide⟩
def pJM : Fin VV := ⟨142, by decide⟩
def pK : Fin VV := ⟨143, by decide⟩
def pW : Fin VV := ⟨144, by decide⟩
def pT : Fin VV := ⟨146, by decide⟩
def pLHS : Fin VV := ⟨168, by decide⟩
def pTB : Fin VV := ⟨167, by decide⟩
def pX1 : Fin VV := ⟨171, by decide⟩
def pX2 : Fin VV := ⟨172, by decide⟩
def pSI : Fin VV := ⟨180, by decide⟩
def pSF : Fin VV := ⟨181, by decide⟩

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

/-! ## Frames on the variables below the expression stack -/

/-- Every variable below `200` outside `T` is unchanged. -/
def FrS (a b : DS VV) (T : List (Fin VV)) : Prop := ∀ y : Fin VV, y.val < 200 → y ∉ T → b.env y = a.env y

theorem FrS.trans {a b c : DS VV} {T : List (Fin VV)} (h1 : FrS a b T) (h2 : FrS b c T) : FrS a c T :=
  fun y hy hT => (h2 y hy hT).trans (h1 y hy hT)
theorem FrS.weaken {a b : DS VV} {T T' : List (Fin VV)} (h : FrS a b T) (hT : ∀ y ∈ T, y ∈ T') : FrS a b T' :=
  fun y hy hT' => h y hy (fun h' => hT' (hT y h'))
theorem Fr.toS {a b : DS VV} {T : List (Fin VV)} (h : Fr a b T) : FrS a b T := fun y _ hT => h y hT
theorem AsgFr.toS {a b : DS VV} {x : Fin VV} (h : AsgFr a b x) (T : List (Fin VV)) (hx : x ∈ T) (hJ : vJ ∈ T) :
    FrS a b T := fun y hy hT => h y hy (fun e => hT (e ▸ hJ)) (fun e => hT (e ▸ hx))
theorem Cst.of_frS {a b : DS VV} {T : List (Fin VV)} (hc : Cst a) (h : FrS a b T) (hT : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T)
    (hp : b.env vPOS = b.cp) : Cst b :=
  ⟨by rw [h vZ (by decide) hT.1]; exact hc.z, by rw [h v1 (by decide) hT.2.1]; exact hc.one,
    by rw [h v2 (by decide) hT.2.2]; exact hc.two, hp⟩

/-! ## The header -/

open AE in
def pHdr (cT : ℕ) : St VV :=
  .seq (assign t3 (var vN)) (.seq clog2 (.seq (assign pLAM (var t5)) (.seq (assign t3 (var pLAM)) (.seq clog2
  (.seq (assign pMU (var t5)) (.seq (assign pJM (add (var pMU) (lit 1)))
  (.seq (assign pK (mul (add (add (mul (lit 2) (var pJM)) (lit cT)) (var pMU)) (var pLAM)))
    (assign pW (add (var vTW1) (var vTW2))))))))))

def hdrT : List (Fin VV) := [t3, t5, t6, vJ, pLAM, pMU, pJM, pK, pW]

theorem pHdr_spec (cT : ℕ) (a : DS VV) (hc : Cst a) (n w1 w2 : ℕ) (hn : a.env vN = n) (h1 : a.env vTW1 = w1)
    (h2 : a.env vTW2 = w2) (hW : (3 * n + cT + 4) * (n + 1) + w1 + w2 + 2 * n + 4 < 2 ^ C.Wd) :
    Hs C (pHdr cT) a (20 * n + 2 * cT + 100) (fun b => b.env pLAM = Target.lambda n ∧ b.env pMU = Target.mu n ∧
      b.env pJM = Jmax n ∧ b.env pK = inner cT n ∧ b.env pW = w1 + w2 ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ FrS a b hdrT) := by
  have hl : Target.lambda n ≤ n := clog_le_self n
  have hm : Target.mu n ≤ n := le_trans (clog_le_self _) hl
  refine Hx.hs (Hs.then (assign_spec t3 (by decide) (by decide) (.var vN) a (by aevar) (by aevar) hc (by trivial))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ n1 hn1 => ?_))
  simp only [AE.eval, hn] at p1
  refine Hs.then (clog2_spec b1 p6 (by rw [p1]; omega)) (fun b2 ⟨c1, c2, c3, c4, c5, c6, c7⟩ n2 hn2 => ?_)
  rw [p1] at c1 hn2
  refine Hs.then (assign_spec pLAM (by decide) (by decide) (.var t5) b2 (by aevar) (by aevar) c6 (by trivial))
    (fun b3 ⟨q1, q2, q3, q4, q5, q6⟩ n3 hn3 => ?_)
  simp only [AE.eval, c1] at q1
  refine Hs.then (assign_spec t3 (by decide) (by decide) (.var pLAM) b3 (by aevar) (by aevar) q6 (by trivial))
    (fun b4 ⟨r1, r2, r3, r4, r5, r6⟩ n4 hn4 => ?_)
  simp only [AE.eval, q1] at r1
  refine Hs.then (clog2_spec b4 r6 (by rw [r1]; have : Nat.clog 2 n ≤ n := hl; omega))
    (fun b5 ⟨d1, d2, d3, d4, d5, d6, d7⟩ n5 hn5 => ?_)
  rw [r1] at d1 hn5
  refine Hs.then (assign_spec pMU (by decide) (by decide) (.var t5) b5 (by aevar) (by aevar) d6 (by trivial))
    (fun b6 ⟨s1, s2, s3, s4, s5, s6⟩ n6 hn6 => ?_)
  simp only [AE.eval, d1] at s1
  have s1' : b6.env pMU = Target.mu n := s1
  have hmu : Target.mu n + 1 < 2 ^ C.Wd := by omega
  have h2W : 4 < 2 ^ C.Wd := by omega
  refine Hs.then (assign_spec pJM (by decide) (by decide) (.add (.var pMU) (.lit 1)) b6 (by aevar) (by aevar) s6
    (by aeok [s1']))
    (fun b7 ⟨u1, u2, u3, u4, u5, u6⟩ n7 hn7 => ?_)
  simp only [AE.eval, s1] at u1
  have b7M : b7.env pMU = Target.mu n := by rw [u2 pMU (by decide) (by decide) (by decide), s1]; rfl
  have b7L : b7.env pLAM = Target.lambda n := by
    rw [u2 pLAM (by decide) (by decide) (by decide), s2 pLAM (by decide) (by decide) (by decide), d7 pLAM (by decide),
      r2 pLAM (by decide) (by decide) (by decide), q1]; rfl
  have hJ : Jmax n = Target.mu n + 1 := rfl
  have hk1 : 2 * Jmax n + cT + Target.mu n ≤ 3 * n + cT + 4 := by rw [hJ]; omega
  have hk2 : (2 * Jmax n + cT + Target.mu n) * Target.lambda n ≤ (3 * n + cT + 4) * (n + 1) :=
    Nat.mul_le_mul hk1 (by omega)
  have hk3 : 3 * n + cT + 4 ≤ (3 * n + cT + 4) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have u1' : b7.env pJM = Jmax n := by rw [u1, hJ]; rfl
  refine Hs.then (assign_spec pK (by decide) (by decide)
    (.mul (.add (.add (.mul (.lit 2) (.var pJM)) (.lit cT)) (.var pMU)) (.var pLAM)) b7 (by aevar) (by aevar) u6
    (by aeok [u1', b7M, b7L]))
    (fun b8 ⟨v1', v2', v3', v4', v5', v6'⟩ n8 hn8 => ?_)
  simp only [AE.eval, u1', b7M, b7L] at v1'
  have b8T1 : b8.env vTW1 = w1 := by
    rw [v2' vTW1 (by decide) (by decide) (by decide), u2 vTW1 (by decide) (by decide) (by decide),
      s2 vTW1 (by decide) (by decide) (by decide), d7 vTW1 (by decide), r2 vTW1 (by decide) (by decide) (by decide),
      q2 vTW1 (by decide) (by decide) (by decide), c7 vTW1 (by decide), p2 vTW1 (by decide) (by decide) (by decide), h1]
  have b8T2 : b8.env vTW2 = w2 := by
    rw [v2' vTW2 (by decide) (by decide) (by decide), u2 vTW2 (by decide) (by decide) (by decide),
      s2 vTW2 (by decide) (by decide) (by decide), d7 vTW2 (by decide), r2 vTW2 (by decide) (by decide) (by decide),
      q2 vTW2 (by decide) (by decide) (by decide), c7 vTW2 (by decide), p2 vTW2 (by decide) (by decide) (by decide), h2]
  refine Hs.last (assign_spec pW (by decide) (by decide) (.add (.var vTW1) (.var vTW2)) b8 (by aevar) (by aevar) v6'
    (by aeok [b8T1, b8T2])) (fun b9 ⟨w1', w2', w3', w4', w5', w6'⟩ n9 hn9 => ?_)
  simp only [AE.eval, b8T1, b8T2] at w1'
  have F : FrS a b9 hdrT := FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (c7.toS.weaken (by decide))
    (FrS.trans (q2.toS _ (by decide) (by decide)) (FrS.trans (r2.toS _ (by decide) (by decide))
    (FrS.trans (d7.toS.weaken (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
    (FrS.trans (u2.toS _ (by decide) (by decide)) (FrS.trans (v2'.toS _ (by decide) (by decide))
      (w2'.toS _ (by decide) (by decide)))))))))
  refine ⟨⟨by rw [w2' pLAM (by decide) (by decide) (by decide), v2' pLAM (by decide) (by decide) (by decide), b7L],
    by rw [w2' pMU (by decide) (by decide) (by decide), v2' pMU (by decide) (by decide) (by decide), b7M],
    by rw [w2' pJM (by decide) (by decide) (by decide), v2' pJM (by decide) (by decide) (by decide), u1'],
    by rw [w2' pK (by decide) (by decide) (by decide), v1']; rfl, w1',
    by rw [w3', v3', u3, s3, d3, r3, q3, c3, p3], by rw [w4', v4', u4, s4, d4, r4, q4, c4, p4],
    by rw [w5', v5', u5, s5, d5, r5, q5, c5, p5], w6', F⟩, ?_⟩
  have hc1 : Nat.clog 2 n ≤ n := hl
  have hc2 : Nat.clog 2 (Nat.clog 2 n) ≤ n := le_trans (clog_le_self _) hl
  simp only [AE.cost] at hn1 hn3 hn4 hn6 hn7 hn8 hn9
  omega

/-! ## Rule 1: `T` -/

theorem tpass_iff (k J t : ℕ) (β : ℚ) (num den : ℕ) (hn : β.num = num) (hd : β.den = den) :
    TPass k J β t ↔ 4 * J * 2 ^ k * den ≤ 2 ^ t * num := by
  unfold TPass
  have hd0 : (0 : ℚ) < den := by rw [← hd]; exact_mod_cast β.den_pos
  have hβ : β = (num : ℚ) / den := by rw [← Rat.num_div_den β, hn, hd]; push_cast; rfl
  rw [hβ, ← mul_div_assoc, le_div_iff₀ hd0]
  exact_mod_cast Iff.rfl

open AE in
/-- The test of `t = pSI`: `pSF := [LHS ≤ 2^t · num]`. -/
def tTest : St VV :=
  .seq (assign P2E (var pSI)) (.seq pow2v (.seq (assign pX2 (mul (var P2X) (var vNUM)))
    (.seq (assign pSF (lit 1)) (.ite (.lt pX2 pLHS) (.op (.zero pSF)) skipS))))

def teeT : List (Fin VV) := [P2E, P2X, P2I, pX2, pSF, pSI, vJ, pLHS, LGX, LGR, LGT, pTB]
def tTestT : List (Fin VV) := [P2E, P2X, P2I, pX2, pSF, vJ]

theorem tTest_spec (a : DS VV) (hc : Cst a) (L num : ℕ) (hlhs : a.env pLHS = L) (hnum : a.env vNUM = num)
    (t : ℕ) (ht : a.env pSI = t) (hW : t < C.Wd) (hW2 : 2 ^ t * num < 2 ^ C.Wd) :
    Hs C tTest a (5 * t + 50) (fun b => b.env pSF = bnat (L ≤ 2 ^ t * num) ∧ b.env pSI = t ∧ b.env pLHS = L ∧
      b.env vNUM = num ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b tTestT) := by
  refine Hx.hs (Hs.then (assign_spec P2E (by decide) (by decide) (.var pSI) a (by aevar) (by aevar) hc (by trivial))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ n1 hn1 => ?_))
  simp only [AE.eval, ht] at p1
  refine Hs.then (pow2v_spec b1 p6 t p1 hW) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ n2 hn2 => ?_)
  have b2N : b2.env vNUM = num := by rw [q6 vNUM (by decide), p2 vNUM (by decide) (by decide) (by decide), hnum]
  refine Hs.then (assign_spec pX2 (by decide) (by decide) (.mul (.var P2X) (.var vNUM)) b2 (by aevar) (by aevar) q5
    (by aeok [q1, b2N])) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ n3 hn3 => ?_)
  simp only [AE.eval, q1, b2N] at r1
  refine Hs.then (assign_spec pSF (by decide) (by decide) (.lit 1) b3 (by aevar) (by aevar) r6
    (by have h1W : 1 < 2 ^ C.Wd := Nat.one_lt_two_pow (by omega)
        aeok [])) (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ n4 hn4 => ?_)
  simp only [AE.eval] at s1
  have F4 : FrS a b4 tTestT := FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q6.toS.weaken (by decide))
    (FrS.trans (r2.toS _ (by decide) (by decide)) (s2.toS _ (by decide) (by decide))))
  have b4X : b4.env pX2 = 2 ^ t * num := by rw [s2 pX2 (by decide) (by decide) (by decide), r1]
  have b4L : b4.env pLHS = L := by
    rw [s2 pLHS (by decide) (by decide) (by decide), r2 pLHS (by decide) (by decide) (by decide),
      q6 pLHS (by decide), p2 pLHS (by decide) (by decide) (by decide), hlhs]
  have b4I : b4.env pSI = t := by
    rw [s2 pSI (by decide) (by decide) (by decide), r2 pSI (by decide) (by decide) (by decide), q6 pSI (by decide),
      p2 pSI (by decide) (by decide) (by decide), ht]
  have b4N : b4.env vNUM = num := by
    rw [s2 vNUM (by decide) (by decide) (by decide), r2 vNUM (by decide) (by decide) (by decide), b2N]
  have step : Hs C (.ite (.lt pX2 pLHS) (.op (.zero pSF)) skipS) b4 2 (fun g => g.env pSF = bnat (L ≤ 2 ^ t * num) ∧
      g.cp = b4.cp ∧ g.wq = b4.wq ∧ g.out = b4.out ∧ Fr b4 g [pSF, vJ]) := by
    refine Hs.ite (c := .lt pX2 pLHS) (show pX2 ≠ pLHS by decide) (fun he => ?_) (fun he => ?_)
    · have hlt : 2 ^ t * num < L := by simpa [Cnd.eval, b4X, b4L] using he
      refine Hs.mono (hs_zero C pSF b4) le_rfl ?_
      rintro g rfl
      exact ⟨by rw [DS.set_env_self]; unfold bnat; simp [show ¬ L ≤ 2 ^ t * num by omega], rfl, rfl, rfl,
        Fr.set _ _ (by decide)⟩
    · have hle : L ≤ 2 ^ t * num := by simpa [Cnd.eval, b4X, b4L] using he
      refine Hs.mono (skip_spec b4) le_rfl ?_
      rintro g rfl
      exact ⟨by rw [DS.set_env_ne _ _ (by decide), s1]; unfold bnat; simp [hle], rfl, rfl, rfl, Fr.set _ _ (by decide)⟩
  refine Hs.last step (fun g ⟨g1, g2, g3, g4, g5⟩ n5 hn5 => ?_)
  refine ⟨⟨g1, by rw [g5 pSI (by decide), b4I], by rw [g5 pLHS (by decide), b4L], by rw [g5 vNUM (by decide), b4N],
    by rw [g2, s3, r3, q2, p3], by rw [g3, s4, r4, q3, p4], by rw [g4, s5, r5, q4, p5],
    Cst.of_fr s6 g5 (by decide) (by rw [g5 vPOS (by decide), g2]; exact s6.pos), FrS.trans F4 (g5.toS.weaken (by decide))⟩,
    ?_⟩
  simp only [AE.cost] at hn1 hn3 hn4
  omega

theorem tee_cost (B : ℕ) : 5 * B + 50 + ((B + 2) * (5 * B + 50 + 4 + 2) + 2) + 1 ≤ (B + 3) * (5 * B + 60) := by
  nlinarith

open AE in
def pTee : St VV :=
  .seq (assign P2E (var pK)) (.seq pow2v (.seq (assign pLHS (mul (mul (mul (lit 4) (var pJM)) (var P2X)) (var vDEN)))
  (.seq (assign LGX (mul (mul (lit 4) (var pJM)) (var vDEN))) (.seq log2v (.seq (assign pTB (add (add (var pK) (var LGR))
    (lit 1))) (.seq (assign pSI (lit 0)) (lsScan pSI pSF pTB tTest)))))))

theorem pTee_spec (a : DS VV) (hc : Cst a) (k J num den : ℕ) (β : ℚ) (hβn : β.num = num) (hβd : β.den = den)
    (hK : a.env pK = k) (hJ : a.env pJM = J) (hnum : a.env vNUM = num) (hden : a.env vDEN = den)
    (hk : k < C.Wd) (hL : 4 * J * 2 ^ k * den < 2 ^ C.Wd)
    (hTB : 2 ^ TBound k J β * num < 2 ^ C.Wd) (hTB2 : TBound k J β + 2 < C.Wd) :
    Hs C pTee a (5 * k + 400 + 10 * TBound k J β + (TBound k J β + 3) * (5 * TBound k J β + 60)) (fun b =>
      ((b.env pSF = 1 ∧ leastT k J β = some (b.env pSI)) ∨ (b.env pSF = 2 ∧ leastT k J β = none)) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b teeT) := by
  have hden0 : 0 < den := by rw [← hβd]; exact β.den_pos
  have h1W : 1 < 2 ^ C.Wd := Nat.one_lt_two_pow (by omega)
  have h4W : 4 < 2 ^ C.Wd := by
    have : 2 ^ 3 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine Hx.hs (Hs.then (assign_spec P2E (by decide) (by decide) (.var pK) a (by aevar) (by aevar) hc (by trivial))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ n1 hn1 => ?_))
  simp only [AE.eval, hK] at p1
  refine Hs.then (pow2v_spec b1 p6 k p1 hk) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ n2 hn2 => ?_)
  have v2 : ∀ x, x ∈ [pJM, vDEN, pK, vNUM] → b2.env x = a.env x := by
    intro x hx
    rw [q6 x (by revert hx; decide +revert), p2 x (by revert hx; decide +revert) (by revert hx; decide +revert)
      (by revert hx; decide +revert)]
  refine Hs.then (assign_spec pLHS (by decide) (by decide) (.mul (.mul (.mul (.lit 4) (.var pJM)) (.var P2X)) (.var vDEN))
    b2 (by aevar) (by aevar) q5 (by
      have e1 := v2 pJM (by decide); have e2 := v2 vDEN (by decide)
      rw [hJ] at e1; rw [hden] at e2
      have h4J : 4 * J ≤ 4 * J * 2 ^ k := Nat.le_mul_of_pos_right _ (by positivity)
      have h4J2 : 4 * J * 2 ^ k ≤ 4 * J * 2 ^ k * den := Nat.le_mul_of_pos_right _ hden0
      aeok [e1, e2, q1]))
    (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ n3 hn3 => ?_)
  have e1 := v2 pJM (by decide); have e2 := v2 vDEN (by decide); have e3 := v2 pK (by decide)
  have e4 := v2 vNUM (by decide)
  rw [hJ] at e1; rw [hden] at e2; rw [hK] at e3; rw [hnum] at e4
  simp only [AE.eval, e1, e2, q1] at r1
  have v3 : ∀ x, x ∈ [pJM, vDEN, pK, vNUM] → b3.env x = a.env x := by
    intro x hx
    rw [r2 x (by revert hx; decide +revert) (by revert hx; decide +revert) (by revert hx; decide +revert), v2 x hx]
  have f1 := v3 pJM (by decide); have f2 := v3 vDEN (by decide)
  rw [hJ] at f1; rw [hden] at f2
  have h4 : 4 * J * den ≤ 4 * J * 2 ^ k * den := by
    have := Nat.one_le_two_pow (n := k); nlinarith
  refine Hs.then (assign_spec LGX (by decide) (by decide) (.mul (.mul (.lit 4) (.var pJM)) (.var vDEN))
    b3 (by aevar) (by aevar) r6 (by
      have h4J : 4 * J ≤ 4 * J * den := Nat.le_mul_of_pos_right _ hden0
      aeok [f1, f2]))
    (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ n4 hn4 => ?_)
  simp only [AE.eval, f1, f2] at s1
  refine Hs.then (log2v_spec b4 s6 _ s1 (lt_of_le_of_lt h4 hL)) (fun b5 ⟨t1, t2, t3', t4', t5', t6'⟩ n5 hn5 => ?_)
  have v5 : ∀ x, x ∈ [pJM, vDEN, pK, vNUM, pLHS] → b5.env x = b3.env x := by
    intro x hx
    rw [t6' x (by revert hx; decide +revert), s2 x (by revert hx; decide +revert) (by revert hx; decide +revert)
      (by revert hx; decide +revert)]
  have g3 : b5.env pK = k := by rw [v5 pK (by decide), v3 pK (by decide), hK]
  have hTBd : TBound k J β = k + Nat.log 2 (4 * J * den) + 1 := by unfold TBound; rw [hβd]
  have hWW : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hkl : k + Nat.log 2 (4 * J * den) + 1 + 2 < C.Wd := by rw [← hTBd]; exact hTB2
  refine Hs.then (assign_spec pTB (by decide) (by decide) (.add (.add (.var pK) (.var LGR)) (.lit 1))
    b5 (by aevar) (by aevar) t5' (by aeok [g3, t1])) (fun b6 ⟨u1, u2, u3, u4, u5, u6⟩ n6 hn6 => ?_)
  simp only [AE.eval, g3, t1] at u1
  rw [← hTBd] at u1
  refine Hs.then (assign_spec pSI (by decide) (by decide) (.lit 0) b6 (by aevar) (by aevar) u6 (by aeok []))
    (fun b7 ⟨w1, w2, w3, w4, w5, w6⟩ n7 hn7 => ?_)
  simp only [AE.eval] at w1
  have b7L : b7.env pLHS = 4 * J * 2 ^ k * den := by
    rw [w2 pLHS (by decide) (by decide) (by decide), u2 pLHS (by decide) (by decide) (by decide), v5 pLHS (by decide),
      r1]
  have b7T : b7.env pTB = TBound k J β := by rw [w2 pTB (by decide) (by decide) (by decide), u1]
  have b7N : b7.env vNUM = num := by
    rw [w2 vNUM (by decide) (by decide) (by decide), u2 vNUM (by decide) (by decide) (by decide), v5 vNUM (by decide),
      v3 vNUM (by decide), hnum]
  -- the scan
  let Inv : DS VV → Prop := fun b => Cst b ∧ b.env pLHS = 4 * J * 2 ^ k * den ∧ b.env pTB = TBound k J β ∧
    b.env vNUM = num ∧ FrS b7 b (pSI :: tTestT)
  have ht : FlagTest C tTest pSI pSF (TPass k J β) Inv (5 * TBound k J β + 50) (TBound k J β) := by
    rintro b ⟨i1, i2, i3, i4, i5⟩ hb
    have hp : 2 ^ b.env pSI * num < 2 ^ C.Wd :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hb)) hTB
    refine Hs.mono (tTest_spec b i1 _ num i2 i4 (b.env pSI) rfl (by omega) hp) (by omega) ?_
    rintro g ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    refine ⟨by rw [g1]; exact bnat_congr (tpass_iff k J _ β num den hβn hβd).symm, g2, ⟨g8, g3, ?_, g4,
      FrS.trans i5 (g9.weaken (by decide))⟩, g5, g6, g7⟩
    rw [g9 pTB (by decide) (by decide), i3]
  have Iinit : Inv b7 := ⟨w6, b7L, b7T, b7N, fun y _ _ => rfl⟩
  refine Hs.last (lsScan_spec pSI pSF pTB (by decide) (by decide) (by decide) (by decide) tTest (TPass k J β) Inv
    (5 * TBound k J β + 50) (fun b h => h.1)
    (fun b v ⟨i1, i2, i3, i4, i5⟩ => ⟨i1.set _ _ (by decide), by rw [DS.set_env_ne _ _ (by decide), i2],
      by rw [DS.set_env_ne _ _ (by decide), i3], by rw [DS.set_env_ne _ _ (by decide), i4],
      FrS.trans i5 (Fr.toS (Fr.set _ _ (by decide)))⟩)
    (fun b v ⟨i1, i2, i3, i4, i5⟩ => ⟨i1.set _ _ (by decide), by rw [DS.set_env_ne _ _ (by decide), i2],
      by rw [DS.set_env_ne _ _ (by decide), i3], by rw [DS.set_env_ne _ _ (by decide), i4],
      FrS.trans i5 (Fr.toS (Fr.set _ _ (by decide)))⟩)
    (TBound k J β) ht (by have := Nat.lt_two_pow_self (n := C.Wd); omega) b7 Iinit w1 (fun b h => h.2.2.1))
    (fun d ⟨⟨d1, d2, d3, d4, d5⟩, d6, d7, d8, d9, d10⟩ n8 hn8 => ?_)
  refine ⟨⟨?_, by rw [d6, w3, u3, t2, s3, r3, q2, p3], by rw [d7, w4, u4, t3', s4, r4, q3, p4],
    by rw [d8, w5, u5, t4', s5, r5, q4, p5], d1, ?_⟩, ?_⟩
  · unfold leastT
    rcases d10 with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, lsScan_found _ _ _ h3 h2 d9⟩
    · exact Or.inr ⟨h1, lsScan_none _ _ (fun s hs hsB => d9 s (by omega) hsB)⟩
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q6.toS.weaken (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (FrS.trans (t6'.toS.weaken (by decide)) (FrS.trans (u2.toS _ (by decide) (by decide))
      (FrS.trans (w2.toS _ (by decide) (by decide)) (d5.weaken (by decide))))))))
  · simp only [AE.cost] at hn1 hn3 hn4 hn6 hn7
    have hlog : Nat.log 2 (4 * J * den) ≤ TBound k J β := by rw [hTBd]; omega
    have hc := tee_cost (TBound k J β)
    clear * - hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hlog hc
    omega

end NearCubicGates.Close.Dispatch
