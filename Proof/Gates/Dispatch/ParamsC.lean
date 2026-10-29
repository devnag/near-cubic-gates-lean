import Proof.Gates.Dispatch.ParamsB

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter

variable {C : Ctx}

def pP : Fin VV := ⟨149, by decide⟩
def pE : Fin VV := ⟨150, by decide⟩
def pNP : Fin VV := ⟨151, by decide⟩
def pWIN : Fin VV := ⟨152, by decide⟩
def pL2 : Fin VV := ⟨153, by decide⟩
def pLW : Fin VV := ⟨154, by decide⟩
def pX7 : Fin VV := ⟨177, by decide⟩
def pX8 : Fin VV := ⟨178, by decide⟩
def pX9 : Fin VV := ⟨179, by decide⟩
def pEF : Fin VV := ⟨184, by decide⟩
def pEB : Fin VV := ⟨185, by decide⟩
def pPF : Fin VV := ⟨186, by decide⟩
def pQ : Fin VV := ⟨187, by decide⟩
def pL : Fin VV := ⟨188, by decide⟩
def pAF : Fin VV := ⟨189, by decide⟩

/-! ## Conditional reset -/

/-- `fl := 0` if `c` holds. -/
def killIf (c : Cnd VV) (fl : Fin VV) : St VV := .ite c (.op (.zero fl)) skipS

theorem killIf_spec (c : Cnd VV) (fl : Fin VV) (hcw : c.wf) (hfJ : fl ≠ vJ) (a : DS VV) :
    Hs C (killIf c fl) a 2 (fun b => b.env fl = (if c.eval a = true then 0 else a.env fl) ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Fr a b [fl, vJ]) := by
  refine Hs.ite hcw (fun he => ?_) (fun he => ?_)
  · refine Hs.mono (hs_zero C fl a) (by omega) ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_self, if_pos he], rfl, rfl, rfl, Fr.set _ _ (by simp)⟩
  · refine Hs.mono (skip_spec a) (by omega) ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_ne _ _ hfJ, if_neg (by simp [he])], rfl, rfl, rfl, Fr.set _ _ (by simp)⟩

/-! ## The lift exponent `e_P` (`sec:finite`, rule 3) -/

open AE in
def liftTest : St VV :=
  .seq (assign P2E (add (add (var pK) (lit 1)) (var pE))) (.seq pow2v (.seq (assign PWB (var pP))
    (.seq (assign PWE (var pE)) (.seq powv (.seq (flagLe pEF P2X PWX) (killIf (.eq pE vZ) pEF))))))

def liftT : List (Fin VV) := [pE, pEF, P2E, P2X, P2I, PWB, PWE, PWX, PWI, PWT, vJ]

/-- The inner scan's invariant. -/
def LInv (a : DS VV) (k P : ℕ) (b : DS VV) : Prop :=
  b.env pP = P ∧ b.env pK = k ∧ b.env pEB = 2 * (k + 1) ∧ Cst b ∧ FrS a b liftT

theorem liftTest_spec (a : DS VV) (k P : ℕ) (hkW : 3 * k + 4 < C.Wd)
    (hPW : ∀ j ≤ 2 * (k + 1), P ^ j < 2 ^ C.Wd) :
    FlagTest C liftTest pE pEF (LiftPass k P) (LInv a k P) (30 * k + 100) (2 * (k + 1)) := by
  intro b ⟨i1, i2, i3, i4, i5⟩ heB
  obtain ⟨e, hed⟩ : ∃ e, b.env pE = e := ⟨_, rfl⟩
  rw [hed] at heB ⊢
  have hW2 : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  refine Hx.hs (Hs.then (assign_spec P2E (by decide) (by decide) (.add (.add (.var pK) (.lit 1)) (.var pE)) b
    (by aevar) (by aevar) i4 (by clear hPW; aeok [i2, hed])) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, i2, hed] at p1
  refine Hs.then (pow2v_spec b1 p6 _ p1 (by omega)) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  have b2P : b2.env pP = P := by simp (disch := decide) only [q6.ev, p2.ev]; exact i1
  refine Hs.then (assign_spec PWB (by decide) (by decide) (.var pP) b2 (by aevar) (by aevar) q5 (by trivial))
    (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  simp only [AE.eval, b2P] at r1
  have b3e : b3.env pE = e := by simp (disch := decide) only [r2.ev, q6.ev, p2.ev]; exact hed
  refine Hs.then (assign_spec PWE (by decide) (by decide) (.var pE) b3 (by aevar) (by aevar) r6 (by trivial))
    (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval, b3e] at s1
  have b4B : b4.env PWB = P := by simp (disch := decide) only [s2.ev]; exact r1
  refine Hs.then (powv_spec b4 s6 P e b4B s1 (fun j hj => hPW j (by omega)) (by omega))
    (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ k5 hk5 => ?_)
  refine Hs.then (flagLe_spec pEF P2X PWX (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) b5 u5 (by omega)) (fun b6 ⟨v1', v2', v3', v4', v5', v6'⟩ k6 hk6 => ?_)
  have b5X : b5.env P2X = 2 ^ (k + 1 + e) := by simp (disch := decide) only [u6.ev, s2.ev, r2.ev]; exact q1
  rw [b5X, u1] at v1'
  refine Hs.last (killIf_spec (.eq pE vZ) pEF (show pE ≠ vZ by decide) (by decide) b6) (fun g ⟨g1, g2, g3, g4, g5⟩ k7 hk7 => ?_)
  have b6e : b6.env pE = e := by simp (disch := decide) only [v2'.ev, u6.ev, s2.ev]; exact b3e
  have b6z : b6.env vZ = 0 := v6'.z
  refine ⟨⟨?_, ?_, ⟨?_, ?_, ?_, Cst.of_fr v6' g5 (by decide) (by rw [g5 vPOS (by decide), g2]; exact v6'.pos), ?_⟩,
    by rw [g2, v3', u2, s3, r3, q2, p3], by rw [g3, v4', u3, s4, r4, q3, p4],
    by rw [g4, v5', u4, s5, r5, q4, p5]⟩, ?_⟩
  · rw [g1]
    simp only [Cnd.eval, b6e, b6z]
    unfold LiftPass
    by_cases he0 : e = 0
    · simp [he0, bnat]
    · rw [if_neg (by simp [he0]), v1']
      exact bnat_congr ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩
  · simp (disch := decide) only [g5.ev, v2'.ev, u6.ev, s2.ev, r2.ev, q6.ev, p2.ev]; exact hed
  · simp (disch := decide) only [g5.ev, v2'.ev, u6.ev, s2.ev, r2.ev, q6.ev, p2.ev]; exact i1
  · simp (disch := decide) only [g5.ev, v2'.ev, u6.ev, s2.ev, r2.ev, q6.ev, p2.ev]; exact i2
  · simp (disch := decide) only [g5.ev, v2'.ev, u6.ev, s2.ev, r2.ev, q6.ev, p2.ev]; exact i3
  · exact FrS.trans i5 (FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q6.toS.weaken (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (FrS.trans (u6.toS.weaken (by decide)) (FrS.trans (v2'.toS _ (by decide) (by decide))
      (g5.toS.weaken (by decide))))))))
  · simp only [AE.cost] at hk1 hk3 hk4
    omega

/-- `pE := liftExp k P` (found: flag `1`; none: flag `2`). -/
def liftV : St VV := .seq (assign pE (.lit 0)) (lsScan pE pEF pEB liftTest)

def liftVT : List (Fin VV) := liftT

def liftCost (k : ℕ) : ℕ := 70 * (k + 3) * (k + 3) + 200

theorem liftV_spec (a : DS VV) (hc : Cst a) (k P : ℕ) (hP : a.env pP = P) (hk : a.env pK = k)
    (hB : a.env pEB = 2 * (k + 1)) (hkW : 3 * k + 4 < C.Wd) (hPW : ∀ j ≤ 2 * (k + 1), P ^ j < 2 ^ C.Wd) :
    Hs C liftV a (liftCost k) (fun b => ((b.env pEF = 1 ∧ liftExp k P = some (b.env pE)) ∨
      (b.env pEF = 2 ∧ liftExp k P = none)) ∧ b.env pP = P ∧ b.env pK = k ∧ b.env pEB = 2 * (k + 1) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b liftVT) := by
  have hW2 : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  refine Hx.hs (Hs.then (assign_spec pE (by decide) (by decide) (.lit 0) a (by aevar) (by aevar) hc (by aeok []))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval] at p1
  have hI : LInv a k P b1 := ⟨by simp (disch := decide) only [p2.ev]; exact hP,
    by simp (disch := decide) only [p2.ev]; exact hk, by simp (disch := decide) only [p2.ev]; exact hB, p6,
    p2.toS _ (by decide) (by decide)⟩
  have hset : ∀ (x : Fin VV), x ∈ liftT → x ∉ [vZ, v1, v2, vPOS] → ∀ b v, LInv a k P b → LInv a k P (b.set x v) := by
    intro x hx hx2 b v ⟨i1, i2, i3, i4, i5⟩
    refine ⟨?_, ?_, ?_, Cst.set i4 _ _ hx2, FrS.trans i5 (Fr.toS (Fr.set _ _ (by simpa using hx)))⟩
    · rw [DS.set_env_ne _ _ (by intro h; subst h; revert hx; decide), i1]
    · rw [DS.set_env_ne _ _ (by intro h; subst h; revert hx; decide), i2]
    · rw [DS.set_env_ne _ _ (by intro h; subst h; revert hx; decide), i3]
  refine Hs.last (lsScan_spec pE pEF pEB (by decide) (by decide) (by decide) (by decide) liftTest (LiftPass k P)
    (LInv a k P) (30 * k + 100) (fun b hb => hb.2.2.2.1) (hset pEF (by decide) (by decide))
    (hset pE (by decide) (by decide)) (2 * (k + 1)) (liftTest_spec a k P hkW hPW) (by omega) b1 hI p1
    (fun b hb => hb.2.2.1)) (fun g ⟨⟨g1, g2, g3, g4, g5⟩, g6, g7, g8, g9, g10⟩ k2 hk2 => ?_)
  refine ⟨⟨?_, g1, g2, g3, by rw [g6, p3], by rw [g7, p4], by rw [g8, p5], g4, g5⟩, ?_⟩
  · rcases g10 with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, lsScan_found _ _ _ h3 h2 g9⟩
    · exact Or.inr ⟨h1, lsScan_none _ _ (fun s hs hsB => g9 s (by omega) hsB)⟩
  · simp only [AE.cost] at hk1
    have e1 : 30 * k + 100 + ((2 * (k + 1) + 2) * (30 * k + 100 + 4 + 2) + 2) + 1 ≤ 70 * (k + 3) * (k + 3) + 190 := by
      ring_nf; nlinarith
    unfold liftCost
    omega

/-! ## The candidate test (eq:prime-budget) -/

open AE in
def pTest : St VV :=
  .seq liftV (.seq (assign pPF (lit 0)) (.seq (.ite (.eq pEF v1)
    (.seq (assign pX8 (mul (mul (sub (mul (lit 2) (var pE)) (lit 1)) (add (mul (lit 2) (var pJM)) (lit 2)))
      (sub (var pP) (lit 1)))) (flagLe pPF pX8 pDM)) skipS) (killIf (.lt pP pX9) pPF)))

def pTT : List (Fin VV) := [pP, pPF, pX8, pE, pEF, P2E, P2X, P2I, PWB, PWE, PWX, PWI, PWT, vJ]

/-- The outer scan's invariant. -/
def PInv (a : DS VV) (k J Dm : ℕ) (b : DS VV) : Prop :=
  b.env pK = k ∧ b.env pEB = 2 * (k + 1) ∧ b.env pJM = J ∧ b.env pDM = Dm ∧ b.env pX9 = 3 ∧ Cst b ∧ FrS a b pTT

theorem pTest_spec (a : DS VV) (n k J Dm : ℕ) (hn : 1 ≤ n) (hkW : 3 * k + 4 < C.Wd)
    (hPW : ∀ j ≤ 2 * (k + 1), n ^ j < 2 ^ C.Wd) (hX : (4 * k + 4) * (2 * J + 2) * n + Dm + 4 < 2 ^ C.Wd) :
    FlagTest C pTest pP pPF (PrimeCandidate n k J Dm) (PInv a k J Dm) (liftCost k + 100) (min n (Dm + 1)) := by
  intro b ⟨i1, i2, i3, i4, i5, i6, i7⟩ hPB
  have hW2 : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  obtain ⟨P, hPd⟩ : ∃ P, b.env pP = P := ⟨_, rfl⟩
  rw [hPd] at hPB ⊢
  have hPn : P ≤ n := le_trans hPB (min_le_left _ _)
  have hPW' : ∀ j ≤ 2 * (k + 1), P ^ j < 2 ^ C.Wd := fun j hj =>
    lt_of_le_of_lt (Nat.pow_le_pow_left hPn j) (hPW j hj)
  refine Hx.hs (Hs.then (liftV_spec b i6 k P hPd i1 i2 hkW hPW') (fun b1 ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ k1 hk1 => ?_))
  have h1W : 1 < 2 ^ C.Wd := by omega
  refine Hs.then (assign_spec pPF (by decide) (by decide) (.lit 0) b1 (by aevar) (by aevar) p8 (by aeok []))
    (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  simp only [AE.eval] at q1
  have b2J : b2.env pJM = J := by simp (disch := decide) only [q2.ev, p9.ev]; exact i3
  have b2D : b2.env pDM = Dm := by simp (disch := decide) only [q2.ev, p9.ev]; exact i4
  have b2P : b2.env pP = P := by simp (disch := decide) only [q2.ev]; exact p2
  -- the lift branch
  have step : Hs C (.ite (.eq pEF v1) (.seq (assign pX8 (.mul (.mul (.sub (.mul (.lit 2) (.var pE)) (.lit 1))
      (.add (.mul (.lit 2) (.var pJM)) (.lit 2))) (.sub (.var pP) (.lit 1)))) (flagLe pPF pX8 pDM)) skipS) b2 80
      (fun g => g.env pPF = bnat (∃ e, liftExp k P = some e ∧ (2 * e - 1) * (2 * J + 2) * (P - 1) ≤ Dm) ∧
        g.cp = b2.cp ∧ g.wq = b2.wq ∧ g.out = b2.out ∧ Cst g ∧ FrS b2 g [pX8, pPF, vJ]) := by
    refine Hs.ite (show pEF ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have hF : b2.env pEF = 1 := by
        have := he; simp only [Cnd.eval, decide_eq_true_eq] at this; rw [this]; exact q6.one
      have hF1 : b1.env pEF = 1 := by rw [← hF]; simp (disch := decide) only [q2.ev]
      obtain ⟨e, he1, hle⟩ : ∃ e, liftExp k P = some e ∧ e ≤ 2 * (k + 1) ∧ b1.env pE = e := by
        rcases p1 with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact ⟨_, h2, (leastUpTo_spec _ _ _ h2).2.1, rfl⟩
        · omega
      have b2e : b2.env pE = e := by simp (disch := decide) only [q2.ev]; exact hle.2
      have f1 : (2 * e - 1) * (2 * J + 2) ≤ (4 * k + 4) * (2 * J + 2) * n := by
        calc (2 * e - 1) * (2 * J + 2) ≤ (4 * k + 4) * (2 * J + 2) := Nat.mul_le_mul_right _ (by omega)
          _ ≤ (4 * k + 4) * (2 * J + 2) * n := Nat.le_mul_of_pos_right _ (by omega)
      have f2 : (2 * e - 1) * (2 * J + 2) * (P - 1) ≤ (4 * k + 4) * (2 * J + 2) * n :=
        Nat.mul_le_mul (le_trans (Nat.mul_le_mul_right _ (by omega)) le_rfl) (by omega)
      have f3 : 2 * J + 2 ≤ (4 * k + 4) * (2 * J + 2) * n := by
        calc 2 * J + 2 ≤ (4 * k + 4) * (2 * J + 2) := Nat.le_mul_of_pos_left _ (by omega)
          _ ≤ (4 * k + 4) * (2 * J + 2) * n := Nat.le_mul_of_pos_right _ (by omega)
      have f4 : 4 * k + 4 ≤ (4 * k + 4) * (2 * J + 2) * n := by
        calc 4 * k + 4 ≤ (4 * k + 4) * (2 * J + 2) := Nat.le_mul_of_pos_right _ (by omega)
          _ ≤ (4 * k + 4) * (2 * J + 2) * n := Nat.le_mul_of_pos_right _ (by omega)
      refine Hs.mono (Hx.hs (Hs.then (assign_spec pX8 (by decide) (by decide) (.mul (.mul (.sub (.mul (.lit 2)
        (.var pE)) (.lit 1)) (.add (.mul (.lit 2) (.var pJM)) (.lit 2))) (.sub (.var pP) (.lit 1))) b2 (by aevar)
        (by aevar) q6 (by
          clear hPW hPW'
          simp only [AE.ok, AE.eval]
          rw [b2e, b2J, b2P]
          and_intros <;> first | trivial | omega)) (fun d1 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)))
        (le_refl 79) (fun g hg => hg)
      simp only [AE.eval, b2e, b2J, b2P] at r1
      refine Hs.last (flagLe_spec pPF pX8 pDM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) d1 r6 h1W) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k4 hk4 => ?_)
      have d1D : d1.env pDM = Dm := by simp (disch := decide) only [r2.ev]; exact b2D
      refine ⟨⟨by rw [g1, r1, d1D]; exact bnat_congr ⟨fun h => ⟨e, he1, h⟩, fun ⟨e', h1, h2⟩ => by
          rw [he1] at h1; cases h1; exact h2⟩, by rw [g3, r3], by rw [g4, r4], by rw [g5, r5], g6,
        FrS.trans (r2.toS _ (by decide) (by decide)) (g2.toS _ (by decide) (by decide))⟩, ?_⟩
      simp only [AE.cost] at hk3
      omega
    · have hF : b2.env pEF ≠ 1 := by
        have := he; simp only [Cnd.eval, decide_eq_false_iff_not] at this; rw [q6.one] at this; exact this
      have hF1 : b1.env pEF ≠ 1 := by intro h; apply hF; rw [← h]; simp (disch := decide) only [q2.ev]
      have hnone : liftExp k P = none := by
        rcases p1 with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd h1 hF1
        · exact h2
      refine Hs.mono (skip_spec b2) (by omega) ?_
      rintro g rfl
      refine ⟨?_, rfl, rfl, rfl, Cst.set q6 _ _ (by decide), Fr.toS (Fr.set _ _ (by decide))⟩
      rw [DS.set_env_ne _ _ (by decide), q1]
      unfold bnat; simp [hnone]
  refine Hs.then step (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  refine Hs.last (killIf_spec (.lt pP pX9) pPF (show pP ≠ pX9 by decide) (by decide) b3)
    (fun g ⟨g1, g2, g3, g4, g5⟩ k4 hk4 => ?_)
  have b3P : b3.env pP = P := by simp (disch := decide) only [r6.ev]; exact b2P
  have b3X : b3.env pX9 = 3 := by simp (disch := decide) only [r6.ev, q2.ev, p9.ev]; exact i5
  refine ⟨⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, Cst.of_fr r5 g5 (by decide) (by rw [g5 vPOS (by decide), g2]; exact r5.pos), ?_⟩,
    by rw [g2, r2, q3, p5], by rw [g3, r3, q4, p6], by rw [g4, r4, q5, p7]⟩, ?_⟩
  · rw [g1, r1]
    simp only [Cnd.eval, b3P, b3X]
    by_cases h3 : P < 3
    · rw [if_pos (by simpa using h3)]
      symm; unfold bnat
      simp only [Bool.toNat_eq_zero, decide_eq_false_iff_not]
      exact fun h => absurd h.1 (by omega)
    · rw [if_neg (by simp [h3])]
      exact bnat_congr (by unfold PrimeCandidate; exact ⟨fun h => ⟨by omega, hPB, h⟩, fun h => h.2.2⟩)
  · simp (disch := decide) only [g5.ev]; exact b3P
  · simp (disch := decide) only [g5.ev, r6.ev, q2.ev, p9.ev]; exact i1
  · simp (disch := decide) only [g5.ev, r6.ev, q2.ev, p9.ev]; exact i2
  · simp (disch := decide) only [g5.ev, r6.ev, q2.ev, p9.ev]; exact i3
  · simp (disch := decide) only [g5.ev, r6.ev, q2.ev, p9.ev]; exact i4
  · simp (disch := decide) only [g5.ev, r6.ev, q2.ev, p9.ev]; exact i5
  · exact FrS.trans i7 (FrS.trans (p9.weaken (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide))
      (FrS.trans (r6.weaken (by decide)) (g5.toS.weaken (by decide)))))
  · simp only [AE.cost] at hk2
    omega

/-! ## `P` and `e_P` -/

open AE in
def pPrime : St VV :=
  .seq (assign pX7 (add (var pDM) (lit 1))) (.seq (.ite (.lt vN pX7) (assign pX7 (var vN)) skipS)
  (.seq (assign pEB (mul (lit 2) (add (var pK) (lit 1)))) (.seq (assign pX9 (lit 3))
  (.seq (assign pP (var pX7)) (.seq (fgScan pP pPF pTest) liftV)))))

def primeT : List (Fin VV) := [pX7, pEB, pX9, pP, pPF, pX8, pE, pEF, P2E, P2X, P2I, PWB, PWE, PWX, PWI, PWT, vJ]

def primeCost (n k : ℕ) : ℕ := (n + 2) * (liftCost k + 110) + liftCost k + 300

theorem pPrime_spec (a : DS VV) (hc : Cst a) (n k J Dm : ℕ) (hN : a.env vN = n) (hK : a.env pK = k)
    (hJ : a.env pJM = J) (hD : a.env pDM = Dm) (hn : 1 ≤ n) (hkW : 3 * k + 4 < C.Wd)
    (hPW : ∀ j ≤ 2 * (k + 1), n ^ j < 2 ^ C.Wd) (hX : (4 * k + 4) * (2 * J + 2) * n + Dm + 4 < 2 ^ C.Wd) :
    Hs C pPrime a (primeCost n k) (fun b => b.env pP = Nat.findGreatest (PrimeCandidate n k J Dm) (min n (Dm + 1)) ∧
      ((b.env pEF = 1 ∧ liftExp k (b.env pP) = some (b.env pE)) ∨ (b.env pEF = 2 ∧ liftExp k (b.env pP) = none)) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b primeT) := by
  have hW2 : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have h1W : 1 < 2 ^ C.Wd := by omega
  refine Hx.hs (Hs.then (assign_spec pX7 (by decide) (by decide) (.add (.var pDM) (.lit 1)) a (by aevar) (by aevar) hc
    (by clear hPW; aeok [hD])) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, hD] at p1
  have b1N : b1.env vN = n := by simp (disch := decide) only [p2.ev]; exact hN
  have step : Hs C (.ite (.lt vN pX7) (assign pX7 (.var vN)) skipS) b1 4 (fun g => g.env pX7 = min n (Dm + 1) ∧
      g.cp = b1.cp ∧ g.wq = b1.wq ∧ g.out = b1.out ∧ Cst g ∧ AsgFr b1 g pX7) := by
    refine Hs.ite (show vN ≠ pX7 by decide) (fun he => ?_) (fun he => ?_)
    · have hlt : n < Dm + 1 := by simpa [Cnd.eval, b1N, p1] using he
      refine Hs.mono (assign_spec pX7 (by decide) (by decide) (.var vN) b1 (by aevar) (by aevar) p6 (by trivial))
        (by simp [AE.cost]) ?_
      rintro g ⟨g1, g2, g3, g4, g5, g6⟩
      exact ⟨by rw [g1]; simp only [AE.eval, b1N]; omega, g3, g4, g5, g6, g2⟩
    · have hle : Dm + 1 ≤ n := by simpa [Cnd.eval, b1N, p1] using he
      refine Hs.mono (skip_spec b1) (by omega) ?_
      rintro g rfl
      exact ⟨by rw [DS.set_env_ne _ _ (by decide), p1]; omega, rfl, rfl, rfl, Cst.set p6 _ _ (by decide),
        fun y _ hy _ => by rw [DS.set_env_ne _ _ hy]⟩
  refine Hs.then step (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  have b2K : b2.env pK = k := by simp (disch := decide) only [q6.ev, p2.ev]; exact hK
  refine Hs.then (assign_spec pEB (by decide) (by decide) (.mul (.lit 2) (.add (.var pK) (.lit 1))) b2 (by aevar)
    (by aevar) q5 (by clear hPW; aeok [b2K])) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  simp only [AE.eval, b2K] at r1
  refine Hs.then (assign_spec pX9 (by decide) (by decide) (.lit 3) b3 (by aevar) (by aevar) r6
    (by clear hPW; aeok [])) (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval] at s1
  refine Hs.then (assign_spec pP (by decide) (by decide) (.var pX7) b4 (by aevar) (by aevar) s6 (by trivial))
    (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ k5 hk5 => ?_)
  have b4X : b4.env pX7 = min n (Dm + 1) := by simp (disch := decide) only [s2.ev, r2.ev]; exact q1
  simp only [AE.eval, b4X] at u1
  have hI : PInv b5 k J Dm b5 := ⟨by simp (disch := decide) only [u2.ev, s2.ev, r2.ev]; exact b2K,
    by simp (disch := decide) only [u2.ev, s2.ev]; exact r1,
    by simp (disch := decide) only [u2.ev, s2.ev, r2.ev, q6.ev, p2.ev]; exact hJ,
    by simp (disch := decide) only [u2.ev, s2.ev, r2.ev, q6.ev, p2.ev]; exact hD,
    by simp (disch := decide) only [u2.ev]; exact s1, u6, fun _ _ _ => rfl⟩
  have hset : ∀ (x : Fin VV), x ∈ pTT → x ∉ [vZ, v1, v2, vPOS] → ∀ b v, PInv b5 k J Dm b →
      PInv b5 k J Dm (b.set x v) := by
    intro x hx hx2 b v ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hne : ∀ y : Fin VV, y ∉ pTT → y ≠ x := fun y hy h => hy (h ▸ hx)
    refine ⟨by rw [DS.set_env_ne _ _ (hne pK (by decide)), i1], by rw [DS.set_env_ne _ _ (hne pEB (by decide)), i2],
      by rw [DS.set_env_ne _ _ (hne pJM (by decide)), i3], by rw [DS.set_env_ne _ _ (hne pDM (by decide)), i4],
      by rw [DS.set_env_ne _ _ (hne pX9 (by decide)), i5], Cst.set i6 _ _ hx2,
      FrS.trans i7 (Fr.toS (Fr.set _ _ hx))⟩
  refine Hs.then (fgScan_spec pP pPF (by decide) (by decide) (by decide) (by decide) pTest (PrimeCandidate n k J Dm)
    (PInv b5 k J Dm) (liftCost k + 100) (fun b hb => hb.2.2.2.2.2.1) (hset pPF (by decide) (by decide))
    (hset pP (by decide) (by decide)) (min n (Dm + 1)) (pTest_spec b5 n k J Dm hn hkW hPW hX) b5 hI u1)
    (fun b6 ⟨v1', ⟨w1, w2, _, _, _, w6, w7⟩, v3', v4', v5'⟩ k6 hk6 => ?_)
  have hPn : b6.env pP ≤ n := by rw [v1']; exact le_trans (Nat.findGreatest_le _) (min_le_left _ _)
  refine Hs.last (liftV_spec b6 w6 k (b6.env pP) rfl w1 w2 hkW (fun j hj =>
    lt_of_le_of_lt (Nat.pow_le_pow_left hPn j) (hPW j hj))) (fun g ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ k7 hk7 => ?_)
  refine ⟨⟨by rw [g2, v1'], by rw [g2]; exact g1, by rw [g5, v3', u3, s3, r3, q2, p3], by rw [g6, v4', u4, s4, r4, q3, p4],
    by rw [g7, v5', u5, s5, r5, q4, p5], g8, ?_⟩, ?_⟩
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q6.toS _ (by decide) (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide))
      (FrS.trans (u2.toS _ (by decide) (by decide)) (FrS.trans (w7.weaken (by decide)) (g9.weaken (by decide)))))))
  · simp only [AE.cost] at hk1 hk3 hk4 hk5
    have e1 : (min n (Dm + 1) + 1) * (liftCost k + 100 + 3 + 2) ≤ (n + 1) * (liftCost k + 110) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e2 : (n + 2) * (liftCost k + 110) = (n + 1) * (liftCost k + 110) + (liftCost k + 110) := by ring
    unfold primeCost
    omega

end NearCubicGates.Close.Dispatch
