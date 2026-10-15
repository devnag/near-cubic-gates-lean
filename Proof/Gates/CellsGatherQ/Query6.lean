import Proof.Gates.CellsGatherQ.Query5

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.QueryPass

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter
open NearCubicGates.Close.Cells.RecordEmission (GW eG2 qScratch QPre)
open NearCubicGates.Close.Cells.QueryKey (kPC kQ kT kS kKey keyScratch KeyGoal KeyClass qKey)

/-! ## The part loop -/

def partL (kP : St VV MM) : St VV MM := forS qPi qNP (partB kP)

theorem partL_spec (kP : St VV MM) (kc : Ctx → Call → Params → ℕ → ℕ) (hk : KeyGoal kP kc) (C : Ctx) (c : Call)
    (p : Params) (wt : Wit c.n) (i : ℕ) (a0 : DS VV MM) (Big : ℕ) (hy : Hy C c p wt Big) (d : DS VV MM)
    (S Wc : List ℕ) (hQ : QPre c p wt i a0 d) (hG : GW d S Wc) (hT : d.env qT = 0)
    (hNP : d.env qNP = (parts c).length) :
    Hs C (partL kP) d ((parts c).length * (4 + costC kc C c p wt Big + 1 + 4) + 4) (fun e =>
      QPre c p wt i a0 e ∧ GW e S (Wc ++ QR (GatherPhase.gZ c p) (GatherPhase.rowKeys c p wt (cellOf wt.I i)) 0) ∧ Fr d e aT) := by
  obtain ⟨cT, hs⟩ := hy.spec
  have h2 := two_pow_gt C c p wt Big hy.wd
  have hp2 : (parts c).length ≤ 2 := GatherPhase.parts_len c
  have hrk := GatherPhase.rowKeys_lt c p wt (cellOf wt.I i) hs
  rw [rowKeys_loops] at hrk ⊢
  have hl := emitLoop (C := C) qPi qNP qT (by decide) (by decide) (partB kP) d (parts c).length (by omega)
    (fun k => lT c p wt (cellOf wt.I i) (pOf c k)) (GatherPhase.gZ c p) S Wc 0
    (fun _ e => QPre c p wt i a0 e ∧ Fr d e aT) (4 + costC kc C c p wt Big + 1)
    (fun k e v ⟨h1, h2⟩ => ⟨QPre.set h1 qPi (by unfold gScratch; decide) v, RecordEmission.Fr.set_r h2 v (by decide)⟩)
    ⟨hQ, Fr.refl _ _⟩ hG hT hNP ?_
  · exact Hs.mono hl le_rfl (fun e ⟨⟨h1, h2⟩, h3, _, _, _⟩ => ⟨h1, h3, h2⟩)
  · intro k hkN e ⟨hQe, hFe⟩ hGe hTe hie hme
    have ev : ∀ x, x ∉ aT → e.env x = d.env x := hFe
    have hpre := pre_le (fun k => lT c p wt (cellOf wt.I i) (pOf c k)) k _ hkN
    refine Hs.mono (partB_spec kP kc hk C c p wt i a0 Big hy e S _ _ k hkN hQe hGe hTe hie (by omega)) le_rfl ?_
    rintro f ⟨f1, f2, f3, f4⟩
    have fv : ∀ x, x ∉ kPC :: cT' → f.env x = e.env x := f4
    refine ⟨⟨f1, Fr.trans hFe (Fr.weaken f4 (by decide))⟩, f2, by rw [f3], ?_, ?_⟩
    · rw [fv qPi (by decide)]; exact hie
    · rw [fv qNP (by decide)]; exact hme

/-! ## The pass -/

def npS : St VV MM := .ite (.eq gKd v2) (.op (.copy qNP v2)) (.op (.copy qNP v1))

theorem npS_spec (C : Ctx) (c : Call) (d : DS VV MM) (hc : Cst d) (hkd : d.env gKd = kindTag c.kind) :
    Hs C npS d 2 (fun e => e.env qNP = (parts c).length ∧ Fr d e [qNP] ∧ Same d e) := by
  rw [parts_len_eq]
  refine Hs.ite (t := 1) (show gKd ≠ v2 by decide) (fun h => ?_) (fun h => ?_)
  · have h2 : kindTag c.kind = 2 := by
      simp only [Cnd.eval, decide_eq_true_eq] at h; rw [hkd, hc.two] at h; exact h
    refine Hs.mono (hs_copy C qNP v2 d (by decide)) le_rfl ?_
    rintro e rfl
    refine ⟨by vsimp [h2, hc.two], fun y hy => ?_, Same.of_sh (by simp)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [DS.set, Function.update_apply, hy]
  · have h2 : kindTag c.kind ≠ 2 := by
      simp only [Cnd.eval, decide_eq_false_iff_not] at h; rw [hkd, hc.two] at h; exact h
    refine Hs.mono (hs_copy C qNP v1 d (by decide)) le_rfl ?_
    rintro e rfl
    refine ⟨by vsimp [h2, hc.one], fun y hy => ?_, Same.of_sh (by simp)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [DS.set, Function.update_apply, hy]

def qPOf (kP : St VV MM) : St VV MM := .seq (.op (.zero qT)) (.seq npS (partL kP))

def qCostOf (kc : Ctx → Call → Params → ℕ → ℕ) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) : ℕ :=
  1100 * (wWin p ^ nDig c p + 1) * (c.n + 2) ^ 6 * (kc C c p Big + 1)

theorem cost_arith (BN NP NL P n K : ℕ) (hNL : NL ≤ 70 * (n + 1) ^ 5) (hP : P ≤ n) (hNP : NP ≤ P + 1) :
    2 * (BN * (NP * (6 * NL + P ^ 2 * (K + 24) + 64) + 8) + 13) + 9 ≤
      1100 * (BN + 1) * (n + 2) ^ 6 * (K + 1) := by
  have hN1 : 1 ≤ n + 2 := by omega
  have e1 : (n + 1) ^ 5 ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have e2 : P ^ 2 ≤ (n + 2) ^ 5 :=
    (Nat.pow_le_pow_left (show P ≤ n + 2 by omega) 2).trans (Nat.pow_le_pow_right hN1 (by norm_num))
  have e3 : 1 ≤ (n + 2) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hM6 : (n + 2) ^ 6 * (K + 1) = (n + 2) * ((n + 2) ^ 5 * (K + 1)) := by ring
  generalize (n + 2) ^ 5 = M at e1 e2 e3 hM6
  have f0 : M ≤ M * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have f1 : 6 * NL + P ^ 2 * (K + 24) + 64 ≤ 508 * (M * (K + 1)) := by
    have g1 : P ^ 2 * (K + 24) ≤ M * (24 * (K + 1)) := Nat.mul_le_mul e2 (by omega)
    have g2 : M * (24 * (K + 1)) = 24 * (M * (K + 1)) := by ring
    omega
  generalize M * (K + 1) = Q at f0 f1 hM6
  have f2 : NP * (6 * NL + P ^ 2 * (K + 24) + 64) ≤ (n + 2) * (508 * Q) := Nat.mul_le_mul (by omega) f1
  have f3 : 1 ≤ (n + 2) * Q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have f4 : (n + 2) * (508 * Q) + 8 ≤ 516 * ((n + 2) * Q) := by
    have : (n + 2) * (508 * Q) = 508 * ((n + 2) * Q) := by ring
    omega
  have f5 : BN * (NP * (6 * NL + P ^ 2 * (K + 24) + 64) + 8) ≤ BN * (516 * ((n + 2) * Q)) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_assoc, hM6]
  generalize (n + 2) * Q = R at f3 f5
  have f6 : BN * (516 * R) = 516 * (BN * R) := by ring
  have f7 : 1100 * (BN + 1) * R = 1100 * (BN * R) + 1100 * R := by ring
  omega

theorem qPOf_spec (kP : St VV MM) (kc : Ctx → Call → Params → ℕ → ℕ) (hk : KeyGoal kP kc) :
    RecordEmission.QryGoal (qPOf kP) (qCostOf kc) := by
  intro C cT c p wt i a0 a Big S W0 hs hdec hadm _ _ hbits hwd hQ hG
  have hy : Hy C c p wt Big := ⟨⟨cT, hs⟩, hdec, hadm, hbits, hwd⟩
  obtain ⟨w, hw⟩ := hdec
  obtain ⟨B1, B2, hadm'⟩ := hadm
  obtain ⟨hc, -, -, -, -, -, -, hkd, -, -, -⟩ := QPre.vals hQ
  suffices H : Hs C (qPOf kP) a (qCostOf kc C c p Big) (fun b =>
      GW b S (W0 ++ RecordEmission.qRecs c p wt i) ∧ (∀ m, m ≠ sG → b.ram m = a.ram m) ∧ (∀ m, b.rc m ≤ (b.ram m).length) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ x : Fin VV, ¬ qScratch x → b.env x = a.env x)) by
    obtain ⟨b, n, hx, hn, hb⟩ := H
    exact ⟨b, n, hx, hn, hb⟩
  apply Hx.hs
  refine Hs.then (hs_zero C qT a) (fun a1 ha1 m1 hm1 => ?_); subst ha1
  refine Hs.then (npS_spec C c _ (cst_of hc (Fr.set a 0 (show qT ∈ [qT] by simp)) (by decide))
    (by vsimp [hkd])) (fun a2 ⟨h21, h22, h23⟩ m2 hm2 => ?_)
  have fr2 : Fr a a2 [qT, qNP] :=
    Fr.trans (Fr.weaken (Fr.set a 0 (show qT ∈ [qT] by simp)) (by decide)) (Fr.weaken h22 (by decide))
  have Q2 : QPre c p wt i a0 a2 :=
    QPre.step hQ ⟨fun m _ => by rw [h23.ram]; rfl, by rw [h23.ip]; rfl, by rw [h23.out]; rfl, by rw [h23.kin]; rfl,
      by rw [h23.kout]; rfl, by rw [h23.kc]; rfl⟩
      (fun m => by rw [h23.rc, h23.ram]; exact hQ.rcur m) [qT, qNP] (by unfold gScratch; decide) fr2
  have G2 : GW a2 S W0 := GW.congr hG (by rw [h23.ram]; rfl) (by rw [h23.rc]; rfl)
  have T2 : a2.env qT = 0 := by rw [h22 qT (by decide)]; vsimp []
  refine Hs.last (partL_spec kP kc hk C c p wt i a0 Big hy a2 S W0 Q2 G2 T2 h21)
    (fun b ⟨b1, b2, b3⟩ m3 hm3 => ?_)
  have frb : Fr a b (aT ++ [qT, qNP]) :=
    Fr.trans (Fr.weaken fr2 (by decide)) (Fr.weaken b3 (by decide))
  refine ⟨⟨by unfold RecordEmission.qRecs; exact b2, fun m hm => (b1.ram m hm).trans (hQ.ram m hm).symm, b1.rcur,
    b1.ip.trans hQ.ip.symm, b1.out.trans hQ.out.symm, b1.kin.trans hQ.kin.symm, b1.kout.trans hQ.kout.symm,
    b1.kc.trans hQ.kc.symm, fun x hx => frb x (fun hm => hx ?_)⟩, ?_⟩
  · have hall : ∀ y ∈ aT ++ [qT, qNP], qScratch y := by
      unfold aT cT' tT pT sT uT kList qScratch; decide
    exact hall x hm
  · obtain ⟨cT0, hs0⟩ := hy.spec
    have hP := P_le_n c p hs0
    have hNP := GatherPhase.nP_le c p hs0
    have hNL := cellN_len c p wt hadm' hs0 w hw
    have hp2 : (parts c).length ≤ 2 := GatherPhase.parts_len c
    have ha := cost_arith (wWin p ^ nDig c p) (p.primes.sort (· ≤ ·)).length
      (CounterMachine.cellN c p wt).length p.P c.n (kc C c p Big) hNL hP hNP
    have hm : (parts c).length * (4 + costC kc C c p wt Big + 1 + 4) ≤ 2 * (4 + costC kc C c p wt Big + 1 + 4) :=
      Nat.mul_le_mul_right _ hp2
    have hcC : costC kc C c p wt Big = wWin p ^ nDig c p * ((p.primes.sort (· ≤ ·)).length *
        (6 * (CounterMachine.cellN c p wt).length + p.P ^ 2 * (kc C c p Big + 24) + 64) + 8) + 4 := by
      unfold costC costP; ring
    rw [hcC] at hm hm3
    unfold qCostOf
    generalize wWin p ^ nDig c p * ((p.primes.sort (· ≤ ·)).length *
        (6 * (CounterMachine.cellN c p wt).length + p.P ^ 2 * (kc C c p Big + 24) + 64) + 8) = X at hm hm3 ha
    omega

/-! ## The class -/

theorem qCostOf_class (kc : Ctx → Call → Params → ℕ → ℕ) (hk : KeyClass kc) : RecordEmission.QryClass (qCostOf kc) := by
  obtain ⟨Kk, ek, hkc⟩ := hk
  refine ⟨1100 * (Kk + 1), 6 + ek, fun C c p Big => ?_⟩
  have h := hkc C c p Big
  unfold qCostOf
  set X := c.n + Big + C.Wd + 2 with hX
  have hX1 : 1 ≤ X := by omega
  have e1 : (c.n + 2) ^ 6 ≤ X ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have e2 : 1 ≤ X ^ ek := Nat.one_le_pow _ _ (by omega)
  have e3 : kc C c p Big + 1 ≤ (Kk + 1) * X ^ ek := by nlinarith
  have e4 : wWin p ^ nDig c p + 1 ≤ (reqIds c p).length + wWin p ^ nDig c p + 1 := by omega
  calc 1100 * (wWin p ^ nDig c p + 1) * (c.n + 2) ^ 6 * (kc C c p Big + 1)
      ≤ 1100 * ((reqIds c p).length + wWin p ^ nDig c p + 1) * X ^ 6 * ((Kk + 1) * X ^ ek) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ e4) e1) e3
    _ = 1100 * (Kk + 1) * ((reqIds c p).length + wWin p ^ nDig c p + 1) * X ^ (6 + ek) := by
        rw [pow_add]; ring

end NearCubicGates.Close.Cells.QueryPass
