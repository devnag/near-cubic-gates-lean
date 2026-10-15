import Proof.Gates.Dispatch.ParamsF

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

/-! ## The exits of `selectParams` -/

section Exits
variable (cT : ℕ) (hd : Header)
local notation "kk" => inner cT hd.n
local notation "mm" => outer hd.n (inner cT hd.n)
local notation "DD" => greatestDegree hd.n (inner cT hd.n) (outer hd.n (inner cT hd.n))
local notation "PP" => Nat.findGreatest (PrimeCandidate hd.n (inner cT hd.n) (Jmax hd.n)
      (greatestDegree hd.n (inner cT hd.n) (outer hd.n (inner cT hd.n))))
      (min hd.n (greatestDegree hd.n (inner cT hd.n) (outer hd.n (inner cT hd.n)) + 1))

theorem sp_none1 (h : ¬ kk < hd.n) : selectParams cT hd = none := by
  unfold selectParams; simp only []; rw [if_neg (fun h' => h h'.1)]

theorem sp_none2 (h1 : kk < hd.n) (hb : 0 < hd.beta) (hT : leastT kk (Jmax hd.n) hd.beta = none) :
    selectParams cT hd = none := by
  unfold selectParams; simp only []; rw [if_pos ⟨h1, hb⟩, hT]

theorem sp_none3 (h1 : kk < hd.n) (hb : 0 < hd.beta) (T : ℕ) (hT : leastT kk (Jmax hd.n) hd.beta = some T)
    (h2 : ¬ DegreePass hd.n kk mm 0) : selectParams cT hd = none := by
  unfold selectParams; simp only []; rw [if_pos ⟨h1, hb⟩, hT]; simp only []; rw [if_neg h2]

theorem sp_none4 (h1 : kk < hd.n) (hb : 0 < hd.beta) (T : ℕ) (hT : leastT kk (Jmax hd.n) hd.beta = some T)
    (h2 : DegreePass hd.n kk mm 0) (he : liftExp kk PP = none) : selectParams cT hd = none := by
  unfold selectParams; simp only []; rw [if_pos ⟨h1, hb⟩, hT]; simp only []; rw [if_pos h2, he]

theorem sp_none5 (h1 : kk < hd.n) (hb : 0 < hd.beta) (T : ℕ) (hT : leastT kk (Jmax hd.n) hd.beta = some T)
    (h2 : DegreePass hd.n kk mm 0) (e : ℕ) (he : liftExp kk PP = some e)
    (hg : ¬ (3 ≤ PP ∧ (dyadicPrimes PP).Nonempty ∧ 100 ≤ PP ∧ 64 * T ≤ Nat.sqrt (2 * (PP / 4) ^ 2) ∧ 2 * kk ≤ DD)) :
    selectParams cT hd = none := by
  unfold selectParams; simp only []; rw [if_pos ⟨h1, hb⟩, hT]; simp only []; rw [if_pos h2, he]; simp only []
  rw [if_neg hg]

theorem sp_none6 (h1 : kk < hd.n) (hb : 0 < hd.beta) (T : ℕ) (hT : leastT kk (Jmax hd.n) hd.beta = some T)
    (h2 : DegreePass hd.n kk mm 0) (e : ℕ) (he : liftExp kk PP = some e)
    (hg : (3 ≤ PP ∧ (dyadicPrimes PP).Nonempty ∧ 100 ≤ PP ∧ 64 * T ≤ Nat.sqrt (2 * (PP / 4) ^ 2) ∧ 2 * kk ≤ DD))
    (hs : stopIndex (firstRatio (((hd.W * kk : ℕ) : ℚ) / (hd.beta * Nat.sqrt (hd.n - kk + 1)))
      (Nat.sqrt (2 * (PP / 4) ^ 2)) T) hd.n = none) :
    selectParams cT hd = none := by
  unfold selectParams; simp only []; rw [if_pos ⟨h1, hb⟩, hT]; simp only []; rw [if_pos h2, he]; simp only []
  rw [if_pos hg, hs]

theorem sp_some (h1 : kk < hd.n) (hb : 0 < hd.beta) (T : ℕ) (hT : leastT kk (Jmax hd.n) hd.beta = some T)
    (h2 : DegreePass hd.n kk mm 0) (e : ℕ) (he : liftExp kk PP = some e)
    (hg : (3 ≤ PP ∧ (dyadicPrimes PP).Nonempty ∧ 100 ≤ PP ∧ 64 * T ≤ Nat.sqrt (2 * (PP / 4) ^ 2) ∧ 2 * kk ≤ DD))
    (Jl : ℕ) (hs : stopIndex (firstRatio (((hd.W * kk : ℕ) : ℚ) / (hd.beta * Nat.sqrt (hd.n - kk + 1)))
      (Nat.sqrt (2 * (PP / 4) ^ 2)) T) hd.n = some Jl) :
    ∃ p, selectParams cT hd = some p := by
  apply Option.isSome_iff_exists.1
  unfold selectParams; simp only []; rw [if_pos ⟨h1, hb⟩, hT]; simp only []; rw [if_pos h2, he]; simp only []
  rw [if_pos hg, hs]; rfl

end Exits

/-! ## Guarded stages -/

/-- Run `X` only while the flag is one. -/
def guard (X : St VV) : St VV := .ite (.eq vADM v1) X skipS

theorem guard_spec (X : St VV) (a : DS VV) (hc : Cst a) (t : ℕ) (R : DS VV → Prop)
    (h1 : a.env vADM = 1 → Hs C X a t R) (h0 : a.env vADM ≠ 1 → R (a.set vJ 0)) : Hs C (guard X) a (t + 2) R := by
  refine Hs.ite (show vADM ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
  · exact Hs.mono (h1 (by simpa [Cnd.eval, hc.one] using he)) (by omega) (fun b hb => hb)
  · refine Hs.mono (skip_spec a) (by omega) ?_
    rintro b rfl
    exact h0 (by simpa [Cnd.eval, hc.one] using he)

/-! ## Stage 0: the header and `k < n` (lines 1569–1572) -/

open AE in
def pS0 (cT : ℕ) : St VV :=
  .seq (pHdr cT) (.seq (assign vADM (lit 1)) (.seq (assign pX1 (add (var pK) (lit 1))) (needLe pX1 vN)))

def s0T : List (Fin VV) := hdrT ++ [vADM, pX1]

theorem pS0_spec (cT : ℕ) (c : Call) (a : DS VV) (hc : Cst a) (hp : ParseOut c a)
    (hW : (3 * c.n + cT + 4) * (c.n + 1) + c.W + 2 * c.n + 4 < 2 ^ C.Wd) :
    Hs C (pS0 cT) a (20 * c.n + 2 * cT + 200) (fun b => b.env vADM = bnat (inner cT c.n < c.n) ∧
      b.env pLAM = Target.lambda c.n ∧ b.env pMU = Target.mu c.n ∧ b.env pJM = Jmax c.n ∧
      b.env pK = inner cT c.n ∧ b.env pW = c.W ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b s0T) := by
  have hk : inner cT c.n ≤ (3 * c.n + cT + 4) * (c.n + 1) := by
    unfold Counter.inner Jmax
    have hl : Target.lambda c.n ≤ c.n := clog_le_self _
    have hm : Target.mu c.n ≤ c.n := le_trans (clog_le_self _) hl
    exact Nat.mul_le_mul (by omega) (by omega)
  refine Hx.hs (Hs.then (pHdr_spec cT a hc c.n _ _ hp.n hp.c1.tw hp.c2.tw (by unfold Call.W at hW; omega))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ k1 hk1 => ?_))
  have h1W : 1 < 2 ^ C.Wd := by omega
  refine Hs.then (assign_spec vADM (by decide) (by decide) (.lit 1) b1 (by aevar) (by aevar) p9 (by aeok []))
    (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  have b2K : b2.env pK = inner cT c.n := by simp (disch := decide) only [q2.ev]; exact p4
  refine Hs.then (assign_spec pX1 (by decide) (by decide) (.add (.var pK) (.lit 1)) b2 (by aevar) (by aevar) q6
    (by aeok [b2K])) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  simp only [AE.eval, b2K] at r1
  have b3A : b3.env vADM = bnat True := by
    simp (disch := decide) only [r2.ev]; simp only [AE.eval] at q1; rw [q1]; rfl
  refine Hs.last (needLe_spec pX1 vN (by decide) b3 True b3A) (fun g ⟨g1, g2, g3, g4, g5⟩ k4 hk4 => ?_)
  have b3N : b3.env vN = c.n := by
    simp (disch := decide) only [r2.ev, q2.ev, p10.ev]; exact hp.n
  refine ⟨⟨by rw [g1, r1, b3N]; exact bnat_congr ⟨fun h => by omega, fun h => ⟨trivial, by omega⟩⟩, ?_, ?_, ?_, ?_, ?_, by rw [g2, r3, q3, p6],
    by rw [g3, r4, q4, p7], by rw [g4, r5, q5, p8], Cst.of_fr r6 g5 (by decide)
      (by rw [g5 vPOS (by decide), g2]; exact r6.pos), ?_⟩, ?_⟩
  · simp (disch := decide) only [g5.ev, r2.ev, q2.ev]; exact p1
  · simp (disch := decide) only [g5.ev, r2.ev, q2.ev]; exact p2
  · simp (disch := decide) only [g5.ev, r2.ev, q2.ev]; exact p3
  · simp (disch := decide) only [g5.ev, r2.ev]; exact b2K
  · simp (disch := decide) only [g5.ev, r2.ev, q2.ev]; rw [p5]; rfl
  · exact FrS.trans (p10.weaken (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (g5.toS.weaken (by decide))))
  · simp only [AE.cost] at hk2 hk3
    omega

/-! ## Stage 1: `T` (rule 1) and the degree-zero guard (line 1587) -/

def pS1 : St VV := .seq pTee (.seq (killIf (.lt v1 pSF) vADM) (.seq (assign pT (.var pSI)) pRule2a))

def s1T : List (Fin VV) := teeT ++ [vADM, pT, pX1, pM, pX2, vJ]

theorem pS1_spec (a : DS VV) (hc : Cst a) (n k J num den : ℕ) (β : ℚ) (hβn : β.num = num) (hβd : β.den = den)
    (hN : a.env vN = n) (hK : a.env pK = k) (hJ : a.env pJM = J) (hnum : a.env vNUM = num) (hden : a.env vDEN = den)
    (hA : a.env vADM = 1) (hk : k < C.Wd) (hL : 4 * J * 2 ^ k * den < 2 ^ C.Wd)
    (hTB : 2 ^ TBound k J β * num < 2 ^ C.Wd) (hTB2 : TBound k J β + 2 < C.Wd)
    (hW : 100 * (k + 2) + 2 * n + 4 < 2 ^ C.Wd) :
    Hs C pS1 a (5 * k + 400 + 10 * TBound k J β + (TBound k J β + 3) * (5 * TBound k J β + 60) + 500) (fun b =>
      b.env vADM = bnat ((leastT k J β).isSome = true ∧ DegreePass n k (outer n k) 0) ∧
      ((leastT k J β).isSome = true → leastT k J β = some (b.env pT)) ∧ b.env pM = outer n k ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b s1T) := by
  refine Hx.hs (Hs.then (pTee_spec a hc k J num den β hβn hβd hK hJ hnum hden hk hL hTB hTB2)
    (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  refine Hs.then (killIf_spec (.lt v1 pSF) vADM (show v1 ≠ pSF by decide) (by decide) b1)
    (fun b2 ⟨q1, q2, q3, q4, q5⟩ k2 hk2 => ?_)
  have c2 : Cst b2 := Cst.of_fr p5 q5 (by decide) (by rw [q5 vPOS (by decide), q2]; exact p5.pos)
  have hA1 : b1.env vADM = 1 := by simp (disch := decide) only [p6.ev]; exact hA
  have b2A : b2.env vADM = bnat ((leastT k J β).isSome = true) := by
    rw [q1]; simp only [Cnd.eval, p5.one]
    rcases p1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, if_neg (by simp), hA1, h2]; rfl
    · rw [h1, if_pos (by simp), h2]; rfl
  refine Hs.then (assign_spec pT (by decide) (by decide) (.var pSI) b2 (by aevar) (by aevar) c2 (by trivial))
    (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  simp only [AE.eval] at r1
  have b3N : b3.env vN = n := by simp (disch := decide) only [r2.ev, q5.ev, p6.ev]; exact hN
  have b3K : b3.env pK = k := by simp (disch := decide) only [r2.ev, q5.ev, p6.ev]; exact hK
  have b3A : b3.env vADM = bnat ((leastT k J β).isSome = true) := by simp (disch := decide) only [r2.ev]; exact b2A
  refine Hs.last (pRule2a_spec b3 r6 n k b3N b3K _ b3A hW) (fun g ⟨g1, g2, g3, g4, g5, g6, g7⟩ k4 hk4 => ?_)
  have gT : g.env pT = b1.env pSI := by
    simp (disch := decide) only [g7.ev]; rw [r1]; simp (disch := decide) only [q5.ev]
  refine ⟨⟨g2, fun hs => ?_, g1, by rw [g3, r3, q2, p2], by rw [g4, r4, q3, p3], by rw [g5, r5, q4, p4], g6, ?_⟩, ?_⟩
  · rw [gT]
    rcases p1 with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · rw [h2] at hs; simp at hs
  · exact FrS.trans (p6.weaken (by decide)) (FrS.trans (q5.toS.weaken (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (g7.weaken (by decide))))
  · simp only [AE.cost] at hk3
    omega

/-! ## Stage 2: `U`, `D_max`, `P`, `e_P` (lines 1581–1598) -/

def pS2 : St VV := .seq pUB (.seq pP2 (.seq pDmax (.seq pPrime (killIf (.lt v1 pEF) vADM))))

def s2T : List (Fin VV) := ubT ++ p2T ++ dmT ++ primeT ++ [vADM, vJ]

def s2Cost (n k m : ℕ) : ℕ := 10 * n + 10 * m + 200 + (5 * m + 1000 * k + 3000) + dmaxCost m + primeCost n k + 10

theorem pS2_spec (a : DS VV) (hc : Cst a) (n k m J : ℕ) (hN : a.env vN = n) (hK : a.env pK = k)
    (hM : a.env pM = m) (hB : a.env vB0 = B0 n) (hJ : a.env pJM = J) (hA : a.env vADM = 1) (hn1 : 1 ≤ n)
    (hUW : 4 * Ubase n m + 4 * n + 4 * m + 4 * Bb n m + 16 < 2 ^ C.Wd) (hPW2 : 100 * (k + 2) + m + 1 < C.Wd)
    (hD : 2 ^ (100 * (k + 2)) * Ubase n m ^ (100 * m) < 2 ^ C.Wd) (hmW : 100 * m + 200 < 2 ^ C.Wd)
    (hkW : 3 * k + 4 < C.Wd) (hPW : ∀ j ≤ 2 * (k + 1), n ^ j < 2 ^ C.Wd)
    (hX : (4 * k + 4) * (2 * J + 2) * n + greatestDegree n k m + 4 < 2 ^ C.Wd) :
    Hs C pS2 a (s2Cost n k m) (fun b => b.env pDM = greatestDegree n k m ∧
      b.env pP = Nat.findGreatest (PrimeCandidate n k J (greatestDegree n k m)) (min n (greatestDegree n k m + 1)) ∧
      b.env vADM = bnat ((liftExp k (b.env pP)).isSome = true) ∧
      ((liftExp k (b.env pP)).isSome = true → liftExp k (b.env pP) = some (b.env pE)) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b s2T) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := ub_facts n m hn1
  refine Hx.hs (Hs.then (pUB_spec a hc n m hN hM hB hn1 hUW) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  have b1K : b1.env pK = k := by simp (disch := decide) only [p6.ev]; exact hK
  have b1M : b1.env pM = m := by simp (disch := decide) only [p6.ev]; exact hM
  refine Hs.then (pP2_spec b1 p5 k m b1K b1M hPW2) (fun b2 ⟨q1, q2, q3, q4, q5, q6, q7⟩ k2 hk2 => ?_)
  have b2M : b2.env pM = m := by simp (disch := decide) only [q7.ev]; exact b1M
  have b2U : b2.env pU = Ubase n m := by simp (disch := decide) only [q7.ev]; exact p1
  refine Hs.then (pDmax_spec b2 q6 n k m b2M b2U q1 q2 f7 hD hmW) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  have b3N : b3.env vN = n := by simp (disch := decide) only [r6.ev, q7.ev, p6.ev]; exact hN
  have b3K : b3.env pK = k := by simp (disch := decide) only [r6.ev, q7.ev]; exact b1K
  have b3J : b3.env pJM = J := by simp (disch := decide) only [r6.ev, q7.ev, p6.ev]; exact hJ
  refine Hs.then (pPrime_spec b3 r5 n k J (greatestDegree n k m) b3N b3K b3J r1 hn1 hkW hPW hX)
    (fun b4 ⟨s1, s2, s3, s4, s5, s6, s7⟩ k4 hk4 => ?_)
  refine Hs.last (killIf_spec (.lt v1 pEF) vADM (show v1 ≠ pEF by decide) (by decide) b4)
    (fun g ⟨g1, g2, g3, g4, g5⟩ k5 hk5 => ?_)
  have b4A : b4.env vADM = 1 := by simp (disch := decide) only [s7.ev, r6.ev, q7.ev, p6.ev]; exact hA
  have gP : g.env pP = b4.env pP := by simp (disch := decide) only [g5.ev]
  have gE : g.env pE = b4.env pE := by simp (disch := decide) only [g5.ev]
  refine ⟨⟨by simp (disch := decide) only [g5.ev, s7.ev]; exact r1, by rw [gP, s1], ?_, ?_,
    by rw [g2, s3, r2, q3, p2], by rw [g3, s4, r3, q4, p3], by rw [g4, s5, r4, q5, p4],
    Cst.of_fr s6 g5 (by decide) (by rw [g5 vPOS (by decide), g2]; exact s6.pos), ?_⟩, ?_⟩
  · rw [g1, gP]; simp only [Cnd.eval, s6.one]
    rcases s2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, if_neg (by simp), b4A, h2]; rfl
    · rw [h1, if_pos (by simp), h2]; rfl
  · intro hs; rw [gP, gE]
    rcases s2 with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · rw [gP, h2] at hs; simp at hs
  · exact FrS.trans (p6.weaken (by decide)) (FrS.trans (q7.weaken (by decide))
      (FrS.trans (r6.weaken (by decide)) (FrS.trans (s7.weaken (by decide)) (g5.toS.weaken (by decide)))))
  · unfold s2Cost
    omega

/-! ## Stage 3: the prime set, the windows, `h_E`, `h`, `R₀`, the guards (lines 1599–1617) -/

def pS3 : St VV := .seq pPrimes (.seq pPair (.seq pLw (.seq pR4a pGuard)))

def s3T : List (Fin VV) := prT ++ pairT ++ [pLW] ++ r4aT ++ [pX1, vADM, vJ]

def s3Cost (n P D : ℕ) : ℕ := primesCost P + pairCost D + 4 + (40 * (n + 1) * (n + 1) + 200) + 1000 + 10

theorem pS3_spec (a : DS VV) (hc : Cst a) (n k P T Dm : ℕ) (pr : Bool) (hN : a.env vN = n) (hK : a.env pK = k)
    (hP : a.env pP = P) (hT : a.env pT = T) (hD : a.env pDM = Dm) (hTag : a.env vTAG = 1 ↔ pr = true)
    (hA : a.env vADM = 1) (hPn : P ≤ n)
    (hW1 : 2 * (P + 1) * (P + 1) + 8 < 2 ^ C.Wd)
    (hW2 : 2 * (ScalarWindow.window (dyadicPrimes P) * (ScalarWindow.window (dyadicPrimes P) *
      ScalarWindow.window (dyadicPrimes P))) + 2 * ScalarWindow.window (dyadicPrimes P) + 8 < 2 ^ C.Wd)
    (hW3 : 4 * (n + 1) * (n + 1) * ((n + 1) * (n + 1)) + 16 < 2 ^ C.Wd) (hW4 : 64 * T + 2 * k + 300 < 2 ^ C.Wd) :
    Hs C pS3 a (s3Cost n P (ScalarWindow.window (dyadicPrimes P))) (fun b =>
      b.env pNP = (dyadicPrimes P).card ∧ b.env pWIN = ScalarWindow.window (dyadicPrimes P) ∧
      b.env pL2 = pairSide (ScalarWindow.window (dyadicPrimes P)) ∧
      b.env pLW = windowInUse pr (pairSide (ScalarWindow.window (dyadicPrimes P))) (ScalarWindow.window (dyadicPrimes P)) ∧
      b.env pHE = P / 4 ∧ b.env pH = Nat.sqrt (2 * (P / 4) ^ 2) ∧ b.env pR0 = Nat.sqrt (n - k + 1) ∧
      b.env vADM = bnat (3 ≤ P ∧ (dyadicPrimes P).Nonempty ∧ 100 ≤ P ∧ 64 * T ≤ Nat.sqrt (2 * (P / 4) ^ 2) ∧ 2 * k ≤ Dm) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b s3T) := by
  refine Hx.hs (Hs.then (pPrimes_spec a hc P hP hW1) (fun b1 ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ k1 hk1 => ?_))
  refine Hs.then (pPair_spec b1 p7 _ p2 hW2) (fun b2 ⟨q1, q2, q3, q4, q5, q6, q7⟩ k2 hk2 => ?_)
  have b2T : b2.env vTAG = 1 ↔ pr = true := by
    rw [show b2.env vTAG = a.env vTAG by simp (disch := decide) only [q7.ev, p8.ev]]; exact hTag
  refine Hs.then (pLw_spec b2 q6 pr _ _ b2T q1 q2) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ k3 hk3 => ?_)
  have b3N : b3.env vN = n := by simp (disch := decide) only [r6.ev, q7.ev, p8.ev]; exact hN
  have b3K : b3.env pK = k := by simp (disch := decide) only [r6.ev, q7.ev, p8.ev]; exact hK
  have b3P : b3.env pP = P := by simp (disch := decide) only [r6.ev, q7.ev]; exact p3
  refine Hs.then (pR4a_spec b3 r5 n k P b3N b3K b3P hPn hW3) (fun b4 ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ k4 hk4 => ?_)
  have b4A : b4.env vADM = bnat True := by
    simp (disch := decide) only [s8.ev, r6.ev, q7.ev, p8.ev]; rw [hA]; rfl
  have b4P : b4.env pP = P := by simp (disch := decide) only [s8.ev]; exact b3P
  have b4NP : b4.env pNP = (dyadicPrimes P).card := by simp (disch := decide) only [s8.ev, r6.ev, q7.ev]; exact p1
  have b4T : b4.env pT = T := by simp (disch := decide) only [s8.ev, r6.ev, q7.ev, p8.ev]; exact hT
  have b4K : b4.env pK = k := by simp (disch := decide) only [s8.ev]; exact b3K
  have b4D : b4.env pDM = Dm := by simp (disch := decide) only [s8.ev, r6.ev, q7.ev, p8.ev]; exact hD
  refine Hs.last (pGuard_spec b4 s7 True b4A P _ T _ k Dm b4P b4NP b4T s2 b4K b4D hW4)
    (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k5 hk5 => ?_)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [g2, s4, r2, q3, p4], by rw [g3, s5, r3, q4, p5],
    by rw [g4, s6, r4, q5, p6], g5, ?_⟩, ?_⟩
  · simp (disch := decide) only [g6.ev]; exact b4NP
  · simp (disch := decide) only [g6.ev, s8.ev, r6.ev]; exact q2
  · simp (disch := decide) only [g6.ev, s8.ev, r6.ev]; exact q1
  · simp (disch := decide) only [g6.ev, s8.ev]; exact r1
  · simp (disch := decide) only [g6.ev]; exact s1
  · simp (disch := decide) only [g6.ev]; exact s2
  · simp (disch := decide) only [g6.ev]; exact s3
  · rw [g1]; exact bnat_congr (by
      constructor
      · rintro ⟨-, h1, h2, h3, h4, h5⟩; exact ⟨h1, Finset.card_pos.1 (by omega), h3, h4, h5⟩
      · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨trivial, h1, Finset.card_pos.2 h2, h3, h4, h5⟩)
  · exact FrS.trans (p8.weaken (by decide)) (FrS.trans (q7.weaken (by decide))
      (FrS.trans (r6.toS _ (by decide) (by decide)) (FrS.trans (s8.weaken (by decide)) (g6.weaken (by decide)))))
  · unfold s3Cost
    omega

/-! ## Stage 4: `ℓ₀`, `ℓ̄`, `M₁`, the rate chain, `J`, `A`, `Λ` (lines 1608–1630) -/

def pJ : Fin VV := ⟨161, by decide⟩
def pLB : Fin VV := ⟨163, by decide⟩

open AE in
def pS4 : St VV :=
  .seq pEll (.seq pBar (.seq (chainP false) (.seq (killIf (.lt pCF v1) vADM)
    (.seq (assign pJ (add (var pCI) (lit 1)))
      (assign pLB (add (div (mul (sub (var pLW) (lit 1)) (var pA)) (lit 2)) (lit 1)))))))

def s4T : List (Fin VV) := ellT ++ barT ++ chT ++ [vADM, pJ, pLB, vJ]

def s4Cost (n S h : ℕ) : ℕ := 30 * S + 100 + 3000 + chainCost (Jmax n) h + 200

theorem pS4_spec (a : DS VV) (hc : Cst a) (n W k den num R0 h T Lw S : ℕ) (β : ℚ) (hβ : β = (num : ℚ) / den)
    (hW : a.env pW = W) (hk : a.env pK = k) (hden : a.env vDEN = den) (hnum : a.env vNUM = num)
    (hR : a.env pR0 = R0) (hh : a.env pH = h) (hT : a.env pT = T) (hJ : a.env pJM = Jmax n) (hLw : a.env pLW = Lw)
    (hA : a.env vADM = 1) (hW0 : 1 ≤ W) (hk0 : 1 ≤ k) (hd0 : 1 ≤ den) (hn0 : 1 ≤ num) (hR1 : 1 ≤ R0)
    (hT0 : 1 ≤ T) (hhT : 64 * T ≤ h)
    (hAS : W * k * den < 2 ^ S) (hBS : num * R0 < 2 ^ S) (hhS : h < 2 ^ S) (hTS : T < 2 ^ S) (hLS : Lw < 2 ^ S)
    (hJS : Jmax n < 2 ^ S) (hSW : 6 * S + 40 ≤ C.Wd) :
    Hs C pS4 a (s4Cost n S h) (fun b =>
      ((((W * k : ℕ) : ℚ) / (β * R0)).num = (b.env pEN : ℤ)) ∧ (((W * k : ℕ) : ℚ) / (β * R0)).den = b.env pED ∧
      b.env pM1 = firstDen (((W * k : ℕ) : ℚ) / (β * R0)) h T ∧
      firstRatio (((W * k : ℕ) : ℚ) / (β * R0)) h T = (b.env pXN : ℚ) / b.env pXD ∧
      0 < b.env pXN ∧ b.env pXN ≤ b.env pXD ∧ b.env pXD ≤ (h + 32) * b.env pXN ∧ b.env pXD < 2 ^ (5 * S + 22) ∧
      1024 * b.env pXD + (h + 33) * (h + 33) + Jmax n + 1000 < 2 ^ C.Wd ∧
      b.env vADM = bnat ((stopIndex (firstRatio (((W * k : ℕ) : ℚ) / (β * R0)) h T) n).isSome = true) ∧
      ((stopIndex (firstRatio (((W * k : ℕ) : ℚ) / (β * R0)) h T) n).isSome = true →
        stopIndex (firstRatio (((W * k : ℕ) : ℚ) / (β * R0)) h T) n = some (b.env pCI) ∧ b.env pJ = b.env pCI + 1 ∧
        b.env pA = (chainFactors (firstRatio (((W * k : ℕ) : ℚ) / (β * R0)) h T) (b.env pCI)).prod ∧
        b.env pLB = (Lw - 1) * b.env pA / 2 + 1) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b s4T) := by
  have hWd2 : 2 ≤ C.Wd := by omega
  have hell : ((W * k : ℕ) : ℚ) / (β * R0) = ((W * k * den : ℕ) : ℚ) / ((num * R0 : ℕ) : ℚ) :=
    ell0_eq W k R0 num den β hβ (by omega) (by omega) (by omega)
  have hBpos : 0 < num * R0 := Nat.mul_pos (by omega) (by omega)
  have hApos : 0 < W * k * den := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  obtain ⟨hnum', hden'⟩ := rat_div_reduce (W * k * den) (num * R0) hBpos
  refine Hx.hs (Hs.then (pEll_spec a hc W k den num R0 S hW hk hden hnum hR hd0 hn0 hR1 hAS hBS (by omega))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ k1 hk1 => ?_))
  have b1h : b1.env pH = h := by simp (disch := decide) only [p9.ev]; exact hh
  have b1T : b1.env pT = T := by simp (disch := decide) only [p9.ev]; exact hT
  refine Hs.then (pBar_spec b1 p8 (W * k * den) (num * R0) h T S p1 p2 b1h b1T hApos hBpos (by omega) (by omega)
    hAS hBS hhS hTS (by omega)) (fun b2 ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15⟩ k2 hk2 => ?_)
  have b2J : b2.env pJM = Jmax n := by simp (disch := decide) only [q15.ev, p9.ev]; exact hJ
  rw [← hell] at q1 q2 q4 q5
  obtain ⟨XN, hXN⟩ : ∃ XN, b2.env pXN = XN := ⟨_, rfl⟩
  obtain ⟨XD, hXD⟩ : ∃ XD, b2.env pXD = XD := ⟨_, rfl⟩
  rw [hXN, hXD] at q5 q8
  rw [hXN] at q6
  rw [hXD] at q7 q9 q10
  have hND : XN ≤ XD := by
    rw [hXN] at q3
    have : 8 * T * b2.env pBN ≤ 4 * h * b2.env pBN := Nat.mul_le_mul_right _ (by omega)
    omega
  have hh33 : (h + 33) * (h + 33) < 2 ^ (2 * S + 12) := by
    have : h + 33 < 2 ^ (S + 6) := by
      have : (2 : ℕ) ^ (S + 6) = 64 * 2 ^ S := by ring
      have : 1 ≤ 2 ^ S := Nat.one_le_two_pow
      omega
    rw [show 2 * S + 12 = (S + 6) + (S + 6) by ring]; exact lt_pow_mul this this
  have hchW : 1024 * XD + (h + 33) * (h + 33) + Jmax n + 1000 < 2 ^ C.Wd := by
    have e1 : 1024 * XD < 2 ^ (5 * S + 32) := by
      have : (2 : ℕ) ^ (5 * S + 32) = 1024 * 2 ^ (5 * S + 22) := by ring
      omega
    have e2 : (h + 33) * (h + 33) < 2 ^ (5 * S + 32) := lt_pow_mono hh33 (by omega)
    have e3 : Jmax n + 1000 < 2 ^ (5 * S + 32) := by
      have : 1000 < 2 ^ 10 := by norm_num
      exact lt_of_lt_of_le (Nat.add_lt_add hJS this) (by
        have h1 : 2 ^ S ≤ 2 ^ (5 * S + 30) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ^ 10 ≤ 2 ^ (5 * S + 30) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 : (2 : ℕ) ^ (5 * S + 32) = 4 * 2 ^ (5 * S + 30) := by ring
        omega)
    have e4 : (2 : ℕ) ^ (5 * S + 32) * 4 ≤ 2 ^ C.Wd := by
      rw [show (2 : ℕ) ^ (5 * S + 32) * 4 = 2 ^ (5 * S + 34) by ring]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine Hs.then (chainP_spec b2 q14 false _ n XN XD h hXN hXD b2J q5 q6 hND q8 hchW hWd2)
    (fun b3 ⟨⟨i, r1, r2, r3, r4⟩, r5, r10, r6, r7, r8, r9⟩ k3 hk3 => ?_)
  refine Hs.then (killIf_spec (.lt pCF v1) vADM (show pCF ≠ v1 by decide) (by decide) b3)
    (fun b4 ⟨s1, s2, s3, s4, s5⟩ k4 hk4 => ?_)
  have c4 : Cst b4 := Cst.of_fr r8 s5 (by decide) (by rw [s5 vPOS (by decide), s2]; exact r8.pos)
  have b4i : b4.env pCI = i := by simp (disch := decide) only [s5.ev]; exact r1
  have hiJ : i ≤ Jmax n - 1 := by rw [← r1]; exact r10
  have h1W : 1 < 2 ^ C.Wd := lt_pow_mono (show 1 < 2 ^ 1 by norm_num) (by omega)
  have hJW : Jmax n + 1 < 2 ^ C.Wd := by
    have h1 : 1 ≤ 2 ^ S := Nat.one_le_two_pow
    have h2 : Jmax n + 1 < 2 ^ (S + 1) := by rw [pow_succ]; omega
    exact lt_pow_mono h2 (by omega)
  refine Hs.then (assign_spec pJ (by decide) (by decide) (.add (.var pCI) (.lit 1)) b4 (by aevar) (by aevar) c4
    (by
      simp only [AE.ok, AE.eval, b4i]
      exact ⟨trivial, h1W, by omega⟩)) (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ k5 hk5 => ?_)
  simp only [AE.eval, b4i] at u1
  have b5L : b5.env pLW = Lw := by simp (disch := decide) only [u2.ev, s5.ev, r9.ev, q15.ev, p9.ev]; exact hLw
  have b5A : b5.env pA = b3.env pA := by simp (disch := decide) only [u2.ev, s5.ev]
  have hLA : (Lw - 1) * b3.env pA < 2 ^ C.Wd := by
    have : (Lw - 1) * b3.env pA ≤ Lw * XD := Nat.mul_le_mul (Nat.sub_le _ _) r5
    have := lt_pow_mul hLS q10
    have : Lw * XD < 2 ^ C.Wd := lt_pow_mono this (by omega)
    omega
  refine Hs.last (assign_spec pLB (by decide) (by decide) (.add (.div (.mul (.sub (.var pLW) (.lit 1)) (.var pA))
    (.lit 2)) (.lit 1)) b5 (by aevar) (by aevar) u6 (by
      simp only [AE.ok, AE.eval, b5L, b5A]
      have h4 : 4 ≤ 2 ^ C.Wd := lt_pow_mono (show 3 < 2 ^ 2 by norm_num) (by omega)
      have : (Lw - 1) * b3.env pA / 2 ≤ (Lw - 1) * b3.env pA := Nat.div_le_self _ _
      refine ⟨⟨⟨⟨trivial, h1W⟩, trivial, hLA⟩, ?_, by norm_num, by omega⟩, h1W, ?_⟩
      · exact lt_pow_mono (show 2 < 2 ^ 2 by norm_num) (by omega)
      · have hl2 : (Lw - 1) * b3.env pA < 2 ^ (6 * S + 22) := by
          have : (Lw - 1) * b3.env pA ≤ Lw * XD := Nat.mul_le_mul (Nat.sub_le _ _) r5
          have := lt_pow_mul hLS q10
          have e : S + (5 * S + 22) = 6 * S + 22 := by ring
          rw [e] at this; omega
        have : (2 : ℕ) ^ (6 * S + 23) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : (2 : ℕ) ^ (6 * S + 23) = 2 * 2 ^ (6 * S + 22) := by ring
        omega)) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k6 hk6 => ?_)
  simp only [AE.eval, b5L, b5A] at g1
  have gX : ∀ y : Fin VV, y.val < 200 → y ∉ [pLB, pJ, vJ] → g.env y = b4.env y := fun y hy hT => by
    rw [g2 y hy (fun h => hT (by simp [h])) (fun h => hT (by simp [h])), u2 y hy (fun h => hT (by simp [h]))
      (fun h => hT (by simp [h]))]
  have gxn : g.env pXN = XN := by rw [gX pXN (by decide) (by decide)]; simp (disch := decide) only [s5.ev, r9.ev]; exact hXN
  have gxd : g.env pXD = XD := by rw [gX pXD (by decide) (by decide)]; simp (disch := decide) only [s5.ev, r9.ev]; exact hXD
  have gA : g.env pA = b3.env pA := by rw [gX pA (by decide) (by decide)]; simp (disch := decide) only [s5.ev]
  have gi : g.env pCI = i := by rw [gX pCI (by decide) (by decide)]; exact b4i
  have hA3 : b3.env vADM = 1 := by simp (disch := decide) only [r9.ev, q15.ev, p9.ev]; exact hA
  refine ⟨⟨?_, ?_, ?_, by rw [gxn, gxd]; exact q5, by rw [gxn]; exact q6, by rw [gxn, gxd]; exact hND,
    by rw [gxn, gxd]; exact q8, by rw [gxd]; exact q10, by rw [gxd]; exact hchW, ?_, ?_, by rw [g3, u3, s2, r6, q11, p5],
    by rw [g4, u4, s3, r7, q12, p6], by rw [g5, u5, s4, r3]; simp only [Bool.false_eq_true, if_false, List.append_nil]; rw [q13, p7], g6, ?_⟩, ?_⟩
  · rw [gX pEN (by decide) (by decide)]; simp (disch := decide) only [s5.ev, r9.ev, q15.ev]
    rw [p3, hell, hnum']
  · rw [gX pED (by decide) (by decide)]; simp (disch := decide) only [s5.ev, r9.ev, q15.ev]
    rw [p4, hell, hden']
  · rw [gX pM1 (by decide) (by decide)]; simp (disch := decide) only [s5.ev, r9.ev]; exact q2
  · rw [gX vADM (by decide) (by decide), s1]
    simp only [Cnd.eval, r8.one]
    rcases r4 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, if_neg (by simp), hA3, h2]; rfl
    · rw [h1, if_pos (by simp), h2]; rfl
  · intro hs
    rcases r4 with ⟨_, h2⟩ | ⟨_, h2⟩
    · refine ⟨by rw [gi]; exact h2, by rw [g2 pJ (by decide) (by decide) (by decide), u1, gi], by rw [gA, gi]; exact r2,
        by rw [g1, gA]⟩
    · rw [h2] at hs; simp at hs
  · exact FrS.trans (p9.weaken (by decide)) (FrS.trans (q15.weaken (by decide)) (FrS.trans (r9.weaken (by decide))
      (FrS.trans (s5.toS.weaken (by decide)) (FrS.trans (u2.toS _ (by decide) (by decide))
      (g2.toS _ (by decide) (by decide))))))
  · simp only [AE.cost] at hk5 hk6
    unfold s4Cost
    omega

end NearCubicGates.Close.Dispatch
