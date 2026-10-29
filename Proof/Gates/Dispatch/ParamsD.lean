import Proof.Gates.Dispatch.ParamsC

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter

variable {C : Ctx}

theorem sum_filter_range_succ (Q : ℕ → Prop) [DecidablePred Q] (f : ℕ → ℕ) (k : ℕ) :
    ∑ p ∈ (Finset.range (k + 1)).filter Q, f p = ∑ p ∈ (Finset.range k).filter Q, f p + (if Q k then f k else 0) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp), add_comm]
  · simp

/-- The dyadic-prime predicate. -/
def DyP (P p : ℕ) : Prop := Nat.Prime p ∧ P < 2 * p

instance (P : ℕ) : DecidablePred (DyP P) := fun p => by unfold DyP; infer_instance

theorem dyadicPrimes_eq (P : ℕ) : dyadicPrimes P = (Finset.range (P + 1)).filter (DyP P) := by
  unfold dyadicPrimes DyP; rfl

theorem sum_le_mul (s : Finset ℕ) (P : ℕ) (hs : ∀ p ∈ s, p ≤ P) : ∑ p ∈ s, (p - 1) ≤ s.card * P := by
  calc ∑ p ∈ s, (p - 1) ≤ ∑ _p ∈ s, P := Finset.sum_le_sum (fun p hp => by have := hs p hp; omega)
    _ = s.card * P := by rw [Finset.sum_const, smul_eq_mul]

theorem filter_range_bound (P j : ℕ) (hj : j ≤ P + 1) :
    ((Finset.range j).filter (DyP P)).card ≤ j ∧
    ∑ p ∈ (Finset.range j).filter (DyP P), (p - 1) ≤ j * P := by
  have hc : ((Finset.range j).filter (DyP P)).card ≤ j := le_trans (Finset.card_filter_le _ _) (by simp)
  refine ⟨hc, le_trans (sum_le_mul _ P (fun p hp => ?_)) (Nat.mul_le_mul_right _ hc)⟩
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  omega

/-! ## The prime set: count and window -/

open AE in
def prBody : St VV :=
  .seq (assign IPQ (var pQ)) (.seq isPrimeV (.seq (assign pX8 (mul (lit 2) (var pQ)))
    (.seq (.ite (.eq IPF v1) (.ite (.lt pP pX8) (.seq (assign pNP (add (var pNP) (lit 1)))
      (assign pWIN (sub (add (var pWIN) (var pQ)) (lit 1)))) skipS) skipS)
     (assign pQ (add (var pQ) (lit 1))))))

open AE in
def pPrimes : St VV :=
  .seq (assign pNP (lit 0)) (.seq (assign pWIN (lit 1)) (.seq (assign pQ (lit 0))
    (.seq (assign pX7 (add (var pP) (lit 1))) (.loop (.lt pQ pX7) prBody))))

def prT : List (Fin VV) := [pNP, pWIN, pQ, pX7, pX8, IPQ, IPF, IPD, IPQ2, IPR, vJ]

/-- The loop invariant after `j` passes. -/
def PrI (a : DS VV) (P j : ℕ) (b : DS VV) : Prop :=
  b.env pQ = j ∧ b.env pX7 = P + 1 ∧ b.env pP = P ∧ b.env pNP = ((Finset.range j).filter (DyP P)).card ∧
    b.env pWIN = 1 + ∑ p ∈ (Finset.range j).filter (DyP P), (p - 1) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧
    Cst b ∧ FrS a b prT

theorem prBody_spec (a : DS VV) (P j : ℕ) (hj : j < P + 1) (hW : 2 * (P + 1) * (P + 1) + 8 < 2 ^ C.Wd)
    (b : DS VV) (hb : PrI a P j b) : Hs C prBody b (9 * P + 100) (PrI a P (j + 1)) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := hb
  obtain ⟨bc, bs⟩ := filter_range_bound P j (by omega)
  have hjP : j * P ≤ (P + 1) * (P + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hPP : P + 1 ≤ (P + 1) * (P + 1) := Nat.le_mul_self _
  have e2 : 2 * (P + 1) * (P + 1) = 2 * ((P + 1) * (P + 1)) := by ring
  refine Hx.hs (Hs.then (assign_spec IPQ (by decide) (by decide) (.var pQ) b (by aevar) (by aevar) i9 (by trivial))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, i1] at p1
  refine Hs.then (isPrimeV_spec b1 p6 j p1 (by omega)) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  have b2Q : b2.env pQ = j := by simp (disch := decide) only [q6.ev, p2.ev]; exact i1
  refine Hs.then (assign_spec pX8 (by decide) (by decide) (.mul (.lit 2) (.var pQ)) b2 (by aevar) (by aevar) q5
    (by aeok [b2Q])) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  simp only [AE.eval, b2Q] at r1
  have b3P : b3.env pP = P := by simp (disch := decide) only [r2.ev, q6.ev, p2.ev]; exact i3
  have b3N : b3.env pNP = ((Finset.range j).filter (DyP P)).card := by
    simp (disch := decide) only [r2.ev, q6.ev, p2.ev]; exact i4
  have b3W : b3.env pWIN = 1 + ∑ p ∈ (Finset.range j).filter (DyP P), (p - 1) := by
    simp (disch := decide) only [r2.ev, q6.ev, p2.ev]; exact i5
  have b3F : b3.env IPF = bnat (Nat.Prime j) := by simp (disch := decide) only [r2.ev]; exact q1
  have b3Q : b3.env pQ = j := by simp (disch := decide) only [r2.ev]; exact b2Q
  -- the update
  have step : Hs C (.ite (.eq IPF v1) (.ite (.lt pP pX8) (.seq (assign pNP (.add (.var pNP) (.lit 1)))
      (assign pWIN (.sub (.add (.var pWIN) (.var pQ)) (.lit 1)))) skipS) skipS) b3 40 (fun g =>
      g.env pNP = ((Finset.range (j + 1)).filter (DyP P)).card ∧
      g.env pWIN = 1 + ∑ p ∈ (Finset.range (j + 1)).filter (DyP P), (p - 1) ∧ g.cp = b3.cp ∧ g.wq = b3.wq ∧
      g.out = b3.out ∧ Cst g ∧ FrS b3 g [pNP, pWIN, vJ]) := by
    rw [card_filter_range_succ, sum_filter_range_succ]
    by_cases hd : DyP P j
    · have hp : Nat.Prime j := hd.1
      have hlt : P < 2 * j := hd.2
      have hF : b3.env IPF = 1 := by rw [b3F]; unfold bnat; simp [hp]
      rw [if_pos hd, if_pos hd]
      refine Hs.iteT (show IPF ≠ v1 by decide) (by simp [Cnd.eval, hF, r6.one]) ?_
      refine Hs.iteT (show pP ≠ pX8 by decide) (by simp [Cnd.eval, b3P, r1, hlt]) ?_
      refine Hx.hs (Hs.then (assign_spec pNP (by decide) (by decide) (.add (.var pNP) (.lit 1)) b3 (by aevar)
        (by aevar) r6 (by aeok [b3N])) (fun d1 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_))
      simp only [AE.eval, b3N] at s1
      have d1W : d1.env pWIN = 1 + ∑ p ∈ (Finset.range j).filter (DyP P), (p - 1) := by
        simp (disch := decide) only [s2.ev]; exact b3W
      have d1Q : d1.env pQ = j := by simp (disch := decide) only [s2.ev]; exact b3Q
      refine Hs.last (assign_spec pWIN (by decide) (by decide) (.sub (.add (.var pWIN) (.var pQ)) (.lit 1)) d1
        (by aevar) (by aevar) s6 (by aeok [d1W, d1Q])) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k5 hk5 => ?_)
      simp only [AE.eval, d1W, d1Q] at g1
      refine ⟨⟨by simp (disch := decide) only [g2.ev]; exact s1, by rw [g1]; have := hp.two_le; omega,
        by rw [g3, s3], by rw [g4, s4], by rw [g5, s5], g6,
        FrS.trans (s2.toS _ (by decide) (by decide)) (g2.toS _ (by decide) (by decide))⟩, ?_⟩
      simp only [AE.cost] at hk4 hk5
      omega
    · rw [if_neg hd, if_neg hd, Nat.add_zero, Nat.add_zero]
      have skip' : ∀ d : DS VV, Cst d → d.env pNP = ((Finset.range j).filter (DyP P)).card →
          d.env pWIN = 1 + ∑ p ∈ (Finset.range j).filter (DyP P), (p - 1) →
          Hs C skipS d 38 (fun g => g.env pNP = ((Finset.range j).filter (DyP P)).card ∧
            g.env pWIN = 1 + ∑ p ∈ (Finset.range j).filter (DyP P), (p - 1) ∧ g.cp = d.cp ∧ g.wq = d.wq ∧
            g.out = d.out ∧ Cst g ∧ FrS d g [pNP, pWIN, vJ]) := by
        intro d hc hn hw
        refine Hs.mono (skip_spec d) (by omega) ?_
        rintro g rfl
        exact ⟨by rw [DS.set_env_ne _ _ (by decide), hn], by rw [DS.set_env_ne _ _ (by decide), hw], rfl, rfl, rfl,
          Cst.set hc _ _ (by decide), Fr.toS (Fr.set _ _ (by decide))⟩
      refine Hs.ite (show IPF ≠ v1 by decide) (fun he => ?_) (fun _ => Hs.mono (skip' b3 r6 b3N b3W) (by omega)
        (fun g hg => hg))
      have hp : Nat.Prime j := by
        have : b3.env IPF = 1 := by simpa [Cnd.eval, r6.one] using he
        rw [b3F] at this; unfold bnat at this; by_contra h; simp [h] at this
      have hle : ¬ P < 2 * j := fun h => hd ⟨hp, h⟩
      refine Hs.iteF (show pP ≠ pX8 by decide) (by simp [Cnd.eval, b3P, r1, hle]) ?_
      exact Hs.mono (skip' b3 r6 b3N b3W) (by omega) (fun g hg => hg)
  refine Hs.then step (fun b4 ⟨s1, s2, s3, s4, s5, s6, s7⟩ k4 hk4 => ?_)
  have b4Q : b4.env pQ = j := by simp (disch := decide) only [s7.ev]; exact b3Q
  refine Hs.last (assign_spec pQ (by decide) (by decide) (.add (.var pQ) (.lit 1)) b4 (by aevar) (by aevar) s6
    (by aeok [b4Q])) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k5 hk5 => ?_)
  simp only [AE.eval, b4Q] at g1
  refine ⟨⟨g1, ?_, ?_, ?_, ?_, by rw [g3, s3, r3, q2, p3, i6], by rw [g4, s4, r4, q3, p4, i7],
    by rw [g5, s5, r5, q4, p5, i8], g6, ?_⟩, ?_⟩
  · simp (disch := decide) only [g2.ev, s7.ev, r2.ev, q6.ev, p2.ev]; exact i2
  · simp (disch := decide) only [g2.ev, s7.ev, r2.ev, q6.ev, p2.ev]; exact i3
  · simp (disch := decide) only [g2.ev]; exact s1
  · simp (disch := decide) only [g2.ev]; exact s2
  · exact FrS.trans i10 (FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q6.toS.weaken (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s7.weaken (by decide))
      (g2.toS _ (by decide) (by decide))))))
  · simp only [AE.cost] at hk1 hk3 hk5
    omega

def primesCost (P : ℕ) : ℕ := (P + 1) * (9 * P + 100 + 2) + 100

theorem pPrimes_spec (a : DS VV) (hc : Cst a) (P : ℕ) (hP : a.env pP = P)
    (hW : 2 * (P + 1) * (P + 1) + 8 < 2 ^ C.Wd) :
    Hs C pPrimes a (primesCost P) (fun b => b.env pNP = (dyadicPrimes P).card ∧
      b.env pWIN = ScalarWindow.window (dyadicPrimes P) ∧ b.env pP = P ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ FrS a b prT) := by
  have hPP : P + 1 ≤ (P + 1) * (P + 1) := Nat.le_mul_self _
  have e2 : 2 * (P + 1) * (P + 1) = 2 * ((P + 1) * (P + 1)) := by ring
  have h1W : 1 < 2 ^ C.Wd := by omega
  refine Hx.hs (Hs.then (assign_spec pNP (by decide) (by decide) (.lit 0) a (by aevar) (by aevar) hc (by aeok []))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  refine Hs.then (assign_spec pWIN (by decide) (by decide) (.lit 1) b1 (by aevar) (by aevar) p6 (by aeok []))
    (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  refine Hs.then (assign_spec pQ (by decide) (by decide) (.lit 0) b2 (by aevar) (by aevar) q6 (by aeok []))
    (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  have b3P : b3.env pP = P := by simp (disch := decide) only [r2.ev, q2.ev, p2.ev]; exact hP
  refine Hs.then (assign_spec pX7 (by decide) (by decide) (.add (.var pP) (.lit 1)) b3 (by aevar) (by aevar) r6
    (by aeok [b3P])) (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  simp only [AE.eval, b3P] at s1 p1 q1 r1
  have hI : PrI b4 P 0 b4 := ⟨by simp (disch := decide) only [s2.ev]; exact r1, s1,
    by simp (disch := decide) only [s2.ev]; exact b3P,
    by simp (disch := decide) only [s2.ev, r2.ev, q2.ev]; rw [p1]; rfl,
    by simp (disch := decide) only [s2.ev, r2.ev]; rw [q1]; rfl, rfl, rfl, rfl, s6, fun _ _ _ => rfl⟩
  have l := Hs.loopN (C := C) (c := .lt pQ pX7) (s := prBody) (show pQ ≠ pX7 by decide) (PrI b4 P) (P + 1)
    (9 * P + 100) (fun j hj d hd => ⟨by simp [Cnd.eval, hd.1, hd.2.1, hj], prBody_spec b4 P j hj hW d hd⟩)
    (fun d hd => by simp [Cnd.eval, hd.1, hd.2.1]) b4 hI
  refine Hs.last l (fun g ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ k5 hk5 => ?_)
  refine ⟨⟨by rw [g4, dyadicPrimes_eq], by rw [g5, dyadicPrimes_eq]; unfold ScalarWindow.window; rfl, g3,
    by rw [g6, s3, r3, q3, p3], by rw [g7, s4, r4, q4, p4], by rw [g8, s5, r5, q5, p5], g9, ?_⟩, ?_⟩
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s2.toS _ (by decide) (by decide)) g10)))
  · simp only [AE.cost] at hk1 hk2 hk3 hk4
    unfold primesCost
    omega

/-! ## `L₂` (lem:window-size) -/

open AE in
def aTest : St VV :=
  .seq (assign pAF (lit 0)) (.ite (.lt pL v2) skipS
    (.seq (assign DSQ1 (add (div (sub (var pWIN) (lit 1)) (sub (var pL) (lit 1))) (lit 1)))
      (.seq degSumV (flagLe pAF pL DSS))))

def aT : List (Fin VV) := [pL, pAF, DSQ1, DSS, DSM, DST, TOM, TOC, TOJ, GCA, GCB, GCQ, GCR, vJ]

def AInv (a : DS VV) (D : ℕ) (b : DS VV) : Prop := b.env pWIN = D ∧ Cst b ∧ FrS a b aT

def aCost (D : ℕ) : ℕ := D * (D * (28 * D + 30) + 30) + 100

theorem cube_mono {q D : ℕ} (h : q ≤ D) : q * (q * (28 * q + 30) + 30) ≤ D * (D * (28 * D + 30) + 30) :=
  Nat.mul_le_mul h (Nat.add_le_add_right (Nat.mul_le_mul h (by omega)) _)

theorem aTest_spec (a : DS VV) (D : ℕ) (hW : 2 * (D * (D * D)) + 2 * D + 8 < 2 ^ C.Wd) :
    FlagTest C aTest pL pAF (Admissible D) (AInv a D) (aCost D) D := by
  intro b ⟨i1, i2, i3⟩ hLD
  obtain ⟨L, hLd⟩ : ∃ L, b.env pL = L := ⟨_, rfl⟩
  rw [hLd] at hLD ⊢
  have h1W : 1 < 2 ^ C.Wd := by omega
  refine Hx.hs (Hs.then (assign_spec pAF (by decide) (by decide) (.lit 0) b (by aevar) (by aevar) i2 (by aeok []))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval] at p1
  have b1L : b1.env pL = L := by simp (disch := decide) only [p2.ev]; exact hLd
  have b1W : b1.env pWIN = D := by simp (disch := decide) only [p2.ev]; exact i1
  refine Hs.last (Hs.ite (show pL ≠ v2 by decide) (fun he => ?_) (fun he => ?_)) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k2 hk2 =>
    ⟨⟨g1, by simp (disch := decide) only [g6.ev, p2.ev]; exact hLd, ⟨by simp (disch := decide) only [g6.ev, p2.ev]; exact i1,
      g5, FrS.trans i3 (FrS.trans (p2.toS _ (by decide) (by decide)) (g6.weaken (by decide)))⟩, by rw [g2, p3],
      by rw [g3, p4], by rw [g4, p5]⟩,
      by simp only [AE.cost] at hk1; unfold aCost; omega⟩)
    (R1 := fun g => g.env pAF = bnat (Admissible D L) ∧ g.cp = b1.cp ∧ g.wq = b1.wq ∧ g.out = b1.out ∧ Cst g ∧
      FrS b1 g [pAF, DSQ1, DSS, DSM, DST, TOM, TOC, TOJ, GCA, GCB, GCQ, GCR, vJ])
    (t := D * (D * (28 * D + 30) + 30) + 92)
  · have hlt : L < 2 := by simpa [Cnd.eval, b1L, p6.two] using he
    refine Hs.mono (skip_spec b1) (by omega) ?_
    rintro g rfl
    refine ⟨?_, rfl, rfl, rfl, Cst.set p6 _ _ (by decide), Fr.toS (Fr.set _ _ (by decide))⟩
    rw [DS.set_env_ne _ _ (by decide), p1]
    unfold bnat
    symm; simp only [Bool.toNat_eq_zero, decide_eq_false_iff_not]
    exact fun h => absurd h.1 (by omega)
  · have hle : 2 ≤ L := by have := he; simp [Cnd.eval, b1L, p6.two] at this; omega
    have hD3 : D ≤ D * (D * D) := by
      calc D ≤ D * D := Nat.le_mul_self D
        _ ≤ D * (D * D) := Nat.mul_le_mul_left _ (Nat.le_mul_self D)
    have hq : (D - 1) / (L - 1) ≤ D := le_trans (Nat.div_le_self _ _) (by omega)
    refine Hx.hs (Hs.then (assign_spec DSQ1 (by decide) (by decide) (.add (.div (.sub (.var pWIN) (.lit 1))
      (.sub (.var pL) (.lit 1))) (.lit 1)) b1 (by aevar) (by aevar) p6 (by
        simp only [AE.ok, AE.eval, b1W, b1L]
        and_intros <;> first | trivial | omega)) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k3 hk3 => ?_))
    simp only [AE.eval, b1W, b1L] at q1
    have hq3 : (D - 1) / (L - 1) * ((D - 1) / (L - 1) * ((D - 1) / (L - 1))) ≤ D * (D * D) :=
      Nat.mul_le_mul hq (Nat.mul_le_mul hq hq)
    refine Hs.then (degSumV_spec b2 q6 ((D - 1) / (L - 1)) q1 (by omega))
      (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k4 hk4 => ?_)
    refine Hs.last (flagLe_spec pAF pL DSS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) b3 r5 h1W) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k5 hk5 => ?_)
    have b3L : b3.env pL = L := by simp (disch := decide) only [r6.ev, q2.ev]; exact b1L
    refine ⟨⟨by rw [g1, b3L, r1]; exact bnat_congr (by unfold Admissible; exact ⟨fun h => ⟨hle, h⟩, fun h => h.2⟩),
      by rw [g3, r2, q3], by rw [g4, r3, q4], by rw [g5, r4, q5], g6,
      FrS.trans (q2.toS _ (by decide) (by decide)) (FrS.trans (r6.toS.weaken (by decide))
        (g2.toS _ (by decide) (by decide)))⟩, ?_⟩
    have hc := cube_mono hq
    simp only [AE.cost] at hk3
    omega

/-- `L₂ := pairSide D'`. -/
def pPair : St VV := .seq (assign pL (.var pWIN)) (.seq (fgScan pL pAF aTest)
  (.ite (.eq pL vZ) (assign pL2 (.lit 1)) (assign pL2 (.var pL))))

def pairT : List (Fin VV) := pL2 :: aT

def pairCost (D : ℕ) : ℕ := (D + 2) * (aCost D + 10) + 20

theorem pPair_spec (a : DS VV) (hc : Cst a) (D : ℕ) (hD : a.env pWIN = D)
    (hW : 2 * (D * (D * D)) + 2 * D + 8 < 2 ^ C.Wd) :
    Hs C pPair a (pairCost D) (fun b => b.env pL2 = pairSide D ∧ b.env pWIN = D ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ FrS a b pairT) := by
  have h1W : 1 < 2 ^ C.Wd := by omega
  refine Hx.hs (Hs.then (assign_spec pL (by decide) (by decide) (.var pWIN) a (by aevar) (by aevar) hc (by trivial))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval, hD] at p1
  have hI : AInv b1 D b1 := ⟨by simp (disch := decide) only [p2.ev]; exact hD, p6, fun _ _ _ => rfl⟩
  have hset : ∀ (x : Fin VV), x ∈ aT → x ∉ [vZ, v1, v2, vPOS] → ∀ b v, AInv b1 D b → AInv b1 D (b.set x v) := by
    intro x hx hx2 b v ⟨i1, i2, i3⟩
    exact ⟨by rw [DS.set_env_ne _ _ (fun h => by subst h; revert hx; decide), i1], Cst.set i2 _ _ hx2,
      FrS.trans i3 (Fr.toS (Fr.set _ _ hx))⟩
  refine Hs.then (fgScan_spec pL pAF (by decide) (by decide) (by decide) (by decide) aTest (Admissible D) (AInv b1 D)
    (aCost D) (fun b hb => hb.2.1) (hset pAF (by decide) (by decide)) (hset pL (by decide) (by decide)) D
    (aTest_spec b1 D hW) b1 hI p1) (fun b2 ⟨q1, ⟨q2, q3, q4⟩, q5, q6, q7⟩ k2 hk2 => ?_)
  have step : Hs C (.ite (.eq pL vZ) (assign pL2 (.lit 1)) (assign pL2 (.var pL))) b2 8 (fun g =>
      g.env pL2 = pairSide D ∧ g.cp = b2.cp ∧ g.wq = b2.wq ∧ g.out = b2.out ∧ Cst g ∧ AsgFr b2 g pL2) := by
    refine Hs.ite (show pL ≠ vZ by decide) (fun he => ?_) (fun he => ?_)
    · have h0 : b2.env pL = 0 := by simpa [Cnd.eval, q3.z] using he
      refine Hs.mono (assign_spec pL2 (by decide) (by decide) (.lit 1) b2 (by aevar) (by aevar) q3 (by aeok []))
        (by simp [AE.cost]) ?_
      rintro g ⟨g1, g2, g3, g4, g5, g6⟩
      exact ⟨by rw [g1]; unfold pairSide; rw [if_pos (by rw [← q1, h0])]; rfl, g3, g4, g5, g6, g2⟩
    · have h0 : b2.env pL ≠ 0 := by simpa [Cnd.eval, q3.z] using he
      refine Hs.mono (assign_spec pL2 (by decide) (by decide) (.var pL) b2 (by aevar) (by aevar) q3 (by trivial))
        (by simp [AE.cost]) ?_
      rintro g ⟨g1, g2, g3, g4, g5, g6⟩
      exact ⟨by rw [g1]; unfold pairSide; rw [if_neg (by rw [← q1]; exact h0)]; simp only [AE.eval, q1], g3, g4, g5,
        g6, g2⟩
  refine Hs.last step (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k3 hk3 => ?_)
  refine ⟨⟨g1, by simp (disch := decide) only [g6.ev]; exact q2, by rw [g2, q5, p3], by rw [g3, q6, p4],
    by rw [g4, q7, p5], g5, FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q4.weaken (by decide))
      (g6.toS _ (by decide) (by decide)))⟩, ?_⟩
  simp only [AE.cost] at hk1
  have e1 : (D + 1) * (aCost D + 3 + 2) ≤ (D + 1) * (aCost D + 10) := Nat.mul_le_mul_left _ (by omega)
  have e2 : (D + 2) * (aCost D + 10) = (D + 1) * (aCost D + 10) + (aCost D + 10) := by ring
  unfold pairCost
  omega

/-! ## `L_w` (`sec:finite`, rule 3) -/

def pLw : St VV := .ite (.eq vTAG v1) (assign pLW (.var pL2)) (assign pLW (.var pWIN))

theorem pLw_spec (a : DS VV) (hc : Cst a) (pr : Bool) (L2 D : ℕ) (hT : a.env vTAG = 1 ↔ pr = true)
    (hL : a.env pL2 = L2) (hD : a.env pWIN = D) :
    Hs C pLw a 4 (fun b => b.env pLW = windowInUse pr L2 D ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      AsgFr a b pLW) := by
  refine Hs.ite (show vTAG ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
  · have h1 : pr = true := hT.1 (by simpa [Cnd.eval, hc.one] using he)
    refine Hs.mono (assign_spec pLW (by decide) (by decide) (.var pL2) a (by aevar) (by aevar) hc (by trivial))
      (by simp [AE.cost]) ?_
    rintro g ⟨g1, g2, g3, g4, g5, g6⟩
    exact ⟨by rw [g1]; simp [AE.eval, hL, windowInUse, h1], g3, g4, g5, g6, g2⟩
  · have h1 : pr = false := by
      cases hpr : pr
      · rfl
      · exfalso; have := hT.2 hpr; simp [Cnd.eval, hc.one, this] at he
    refine Hs.mono (assign_spec pLW (by decide) (by decide) (.var pWIN) a (by aevar) (by aevar) hc (by trivial))
      (by simp [AE.cost]) ?_
    rintro g ⟨g1, g2, g3, g4, g5, g6⟩
    exact ⟨by rw [g1]; simp [AE.eval, hD, windowInUse, h1], g3, g4, g5, g6, g2⟩

end NearCubicGates.Close.Dispatch
