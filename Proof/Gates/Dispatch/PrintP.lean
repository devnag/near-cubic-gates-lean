import Proof.Gates.Dispatch.Print

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

variable {C : Ctx}

def pPR : Fin VV := ⟨197, by decide⟩

def pvs1 : List (Fin VV) := [vN, pPR, pW, vSG, vNUM, vDEN, pK, pT, pM, pDM, pP, pE, pNP]
def pvs2 : List (Fin VV) := [pWIN, pL2, pLW, pHE, pH, pR0, vZ, pEN, pED, pM1, pJ, pX9]
def pvs3 : List (Fin VV) := [pA, pLB]

open AE in
def printParams : St VV :=
  .seq (assign pPR (lit 1)) (.seq (.ite (.eq vTAG v1) skipS (.op (.zero pPR)))
  (.seq (assign pX9 (sub (var pJ) (lit 1)))
  (.seq (printVars pvs1) (.seq prPrint (.seq (printVars pvs2) (.seq (chainP true) (printVars pvs3)))))))

def printT : List (Fin VV) := [pPR, pX9, vJ] ++ pvT ++ prPT ++ chT

def printCost (P J h W : ℕ) : ℕ :=
  100 + 13 * (pvCost W + 1) + 1 + prPrintCost P W + 12 * (pvCost W + 1) + 1 + chainCost J h + 2 * (pvCost W + 1) + 1 + 20

theorem valid_set {a : DS VV} (hv : Valid C a) (x : Fin VV) (v : ℕ) (hx : v < 2 ^ C.Wd) : Valid C (a.set x v) :=
  ⟨fun y => by
    by_cases hy : y = x
    · subst hy; rw [DS.set_env_self]; exact hx
    · rw [DS.set_env_ne _ _ hy]; exact hv.env_lt y, hv.cp_le, hv.wq_le⟩

theorem printParams_spec (cT : ℕ) (c : Call) (p : Params) (hS : Spec cT (header c) p) (a : DS VV) (hc : Cst a)
    (hv : Valid C a) (hpv : PV p a) (hpo : ParseOut c a) (hW3 : 3 ≤ C.Wd)
    (hrep : 1024 * a.env pXD + (p.h + 33) * (p.h + 33) + Jmax p.n + 1000 < 2 ^ C.Wd)
    (hPW : 2 * (p.P + 1) + 8 < 2 ^ C.Wd) :
    Hs C printParams a (printCost p.P (Jmax p.n) p.h C.Wd) (fun b => b.out = a.out ++ paramsWord p ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ Cst b ∧ Valid C b ∧ FrS a b printT) := by
  have hW1 : 1 ≤ C.Wd := by omega
  have h1W : 1 < 2 ^ C.Wd := Nat.one_lt_two_pow (by omega)
  refine Hx.hs (Hs.then (Hs.addValid hW1 hv (assign_spec pPR (by decide) (by decide) (.lit 1) a (by aevar) (by aevar)
    hc (by aeok []))) (fun b1 ⟨⟨p1, p2, p3, p4, p5, p6⟩, p7⟩ k1 hk1 => ?_))
  simp only [AE.eval] at p1
  -- the pair bit
  have step : Hs C (.ite (.eq vTAG v1) skipS (.op (.zero pPR))) b1 2 (fun g =>
      g.env pPR = (if p.pair then 1 else 0) ∧ g.cp = b1.cp ∧ g.wq = b1.wq ∧ g.out = b1.out ∧ Cst g ∧ Valid C g ∧
      Fr b1 g [pPR, vJ]) := by
    have hpair : p.pair = decide (c.kind = .pair) := hS.pair_eq
    have hT1 : b1.env vTAG = kindTag c.kind := by simp (disch := decide) only [p2.ev]; exact hpo.tag
    refine Hs.ite (show vTAG ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have h1 : c.kind = .pair := (kindTag_eq_one _).1 (by rw [← hT1]; simpa [Cnd.eval, p6.one] using he)
      refine Hs.mono (skip_spec b1) (by omega) ?_
      rintro g rfl
      exact ⟨by rw [DS.set_env_ne _ _ (by decide), p1, hpair]; simp [h1], rfl, rfl, rfl, Cst.set p6 _ _ (by decide),
        valid_set p7 _ _ (by omega), Fr.set _ _ (by decide)⟩
    · have h1 : c.kind ≠ .pair := fun h => by
        have : b1.env vTAG = 1 := by rw [hT1, h]; rfl
        simp [Cnd.eval, p6.one, this] at he
      refine Hs.mono (hs_zero C pPR b1) (by omega) ?_
      rintro g rfl
      exact ⟨by rw [DS.set_env_self, hpair]; simp [h1], rfl, rfl, rfl, Cst.set p6 _ _ (by decide),
        valid_set p7 _ _ (by omega), Fr.set _ _ (by decide)⟩
  refine Hs.then step (fun b2 ⟨q1, q2, q3, q4, q5, q6, q7⟩ k2 hk2 => ?_)
  have b2J : b2.env pJ = p.J := by simp (disch := decide) only [q7.ev, p2.ev]; exact hpv.J
  refine Hs.then (Hs.addValid hW1 q6 (assign_spec pX9 (by decide) (by decide) (.sub (.var pJ) (.lit 1)) b2 (by aevar)
    (by aevar) q5 (by simp only [AE.ok]; exact ⟨trivial, h1W⟩))) (fun b3 ⟨⟨r1, r2, r3, r4, r5, r6⟩, r7⟩ k3 hk3 => ?_)
  simp only [AE.eval, b2J] at r1
  -- the first block of fields
  refine Hs.then (printVars_spec pvs1 (by decide) hW3 b3 r6 r7) (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  have b4P : b4.env pP = p.P := by simp (disch := decide) only [s6.ev, r2.ev, q7.ev, p2.ev]; exact hpv.P
  refine Hs.then (prPrint_spec b4 s4 s5 p.P b4P hW3 hPW) (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ k5 hk5 => ?_)
  refine Hs.then (printVars_spec pvs2 (by decide) hW3 b5 u4 u5) (fun b6 ⟨v1', v2', v3', v4', v5', v6'⟩ k6 hk6 => ?_)
  -- the factors
  have hx1 := hpv.x1
  have B3 : ∀ y : Fin VV, y.val < 200 → y ∉ [pPR, pX9, vJ] → b3.env y = a.env y := by
    intro y hy hT
    rw [r2 y hy (fun h => hT (by simp [h])) (fun h => hT (by simp [h])),
      q7 y (fun h => hT (by simp at h; rcases h with h | h <;> simp [h])),
      p2 y hy (fun h => hT (by simp [h])) (fun h => hT (by simp [h]))]
  have F6 : ∀ y : Fin VV, y.val < 200 → y ∉ [pPR, pX9, vJ] ++ pvT ++ prPT → b6.env y = a.env y := by
    intro y hy hT
    simp only [List.mem_append, not_or] at hT
    rw [v6' y hy hT.1.2, u6 y hy hT.2, s6 y hy hT.1.2, B3 y hy hT.1.1]
  have b6N : b6.env pXN = a.env pXN := F6 pXN (by decide) (by decide)
  have b6D : b6.env pXD = a.env pXD := F6 pXD (by decide) (by decide)
  have b6J : b6.env pJM = Jmax p.n := by rw [F6 pJM (by decide) (by decide)]; exact hpv.JM
  have hstop : stopIndex (firstRatio p.ell0 p.h p.T) p.n = some (p.J - 1) := by
    have := hS.J_eq; rw [← hS.n_eq] at this; exact this
  refine Hs.then (Hs.addValid hW1 v5' (chainP_spec b6 v4' true _ p.n (a.env pXN) (a.env pXD) p.h b6N b6D b6J hx1
    hpv.xn hpv.xnd hpv.xd hrep (by omega))) (fun b7 ⟨⟨⟨i, w1, w2, w3, w4⟩, w5, w6, w7, w8, w9, w10⟩, hv7⟩ k7 hk7 => ?_)
  have hi : i = p.J - 1 := by
    rcases w4 with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [hstop] at h2; exact (Option.some.inj h2).symm
    · rw [hstop] at h2; exact absurd h2 (by simp)
  subst hi
  refine Hs.last (printVars_spec pvs3 (by decide) hW3 b7 w9 hv7) (fun g ⟨g1, g2, g3, g4, g5, g6⟩ k8 hk8 => ?_)
  have gA : b7.env pA = p.A := by rw [w2, hS.A_eq, hS.factors_eq]
  have gL : b7.env pLB = p.Lambda := by
    rw [w10 pLB (by decide) (by decide), F6 pLB (by decide) (by decide)]; exact hpv.Lam
  refine ⟨⟨?_, by rw [g2, w7, v2', u2, s2, r3, q2, p3], by rw [g3, w8, v3', u3, s3, r4, q3, p4], g4, g5, ?_⟩, ?_⟩
  · have B5 : ∀ y : Fin VV, y.val < 200 → y ∉ [pPR, pX9, vJ] ++ pvT ++ prPT → b5.env y = a.env y := by
      intro y hy hT
      simp only [List.mem_append, not_or] at hT
      rw [u6 y hy hT.2, s6 y hy hT.1.2, B3 y hy hT.1.1]
    have e3PR : b3.env pPR = (if p.pair then 1 else 0) := by simp (disch := decide) only [r2.ev]; exact q1
    have e5X9 : b5.env pX9 = p.J - 1 := by simp (disch := decide) only [u6.ev, s6.ev]; exact r1
    have hfac : chainFactors (firstRatio p.ell0 p.h p.T) (p.J - 1) = p.factors := hS.factors_eq.symm
    have hflen : p.factors.length = p.J - 1 := by rw [← hfac]; simp [chainFactors]
    have hen : p.ell0.num = (a.env pEN : ℤ) := hpv.en
    rw [g1, w3, v1', u1, s1, r5, q4, p5]
    simp only [pvs1, pvs2, pvs3, List.flatMap_cons, List.flatMap_nil, List.append_nil, if_true, hfac]
    rw [B3 vN (by decide) (by decide), e3PR, B3 pW (by decide) (by decide), B3 vSG (by decide) (by decide),
      B3 vNUM (by decide) (by decide), B3 vDEN (by decide) (by decide), B3 pK (by decide) (by decide),
      B3 pT (by decide) (by decide), B3 pM (by decide) (by decide), B3 pDM (by decide) (by decide),
      B3 pP (by decide) (by decide), B3 pE (by decide) (by decide), B3 pNP (by decide) (by decide),
      B5 pWIN (by decide) (by decide), B5 pL2 (by decide) (by decide), B5 pLW (by decide) (by decide),
      B5 pHE (by decide) (by decide), B5 pH (by decide) (by decide), B5 pR0 (by decide) (by decide),
      B5 vZ (by decide) (by decide), B5 pEN (by decide) (by decide), B5 pED (by decide) (by decide),
      B5 pM1 (by decide) (by decide), B5 pJ (by decide) (by decide), e5X9, gA, gL]
    rw [hpv.n, hpv.W, hpo.sg, hpo.num, hpo.den, hpv.k, hpv.T, hpv.m, hpv.Dmax, hpv.P, hpv.e, hpv.card,
      hpv.window, hpv.L2, hpv.Lw, hpv.hE, hpv.h, hpv.R0, hc.z, ← hpv.ed, hpv.M1, hpv.J]
    have hbeta : p.beta = c.radius := hS.beta_eq
    unfold paramsWord listWord ratWord Interfaces.intWord bitWord
    rw [hbeta, hen, Finset.length_sort, hflen, hS.primes_eq]
    simp only [List.append_assoc, Int.natAbs_natCast, Nat.cast_nonneg, not_lt.2, if_false]
  · exact FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans ((Fr.toS q7).weaken (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s6.weaken (by decide)) (FrS.trans (u6.weaken
      (by decide)) (FrS.trans (v6'.weaken (by decide)) (FrS.trans (w10.weaken (by decide)) (g6.weaken (by decide))))))))
  · simp only [AE.cost] at hk1 hk3
    have hc7 := chainCost_mono (J := Jmax p.n) (h := p.h) (B := 0)
    unfold printCost
    simp only [pvs1, pvs2, pvs3, List.length_cons, List.length_nil] at hk4 hk6 hk8
    omega
