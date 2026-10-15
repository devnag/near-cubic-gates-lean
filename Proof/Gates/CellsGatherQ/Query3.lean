import Proof.Gates.CellsGatherQ.Query2
import Proof.Gates.Cells.Width

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
open NearCubicGates.Close.Cells.QueryKey (kPC kQ kT kS kKey keyScratch KeyGoal qKey)

theorem len_single (f : ℕ → ℕ) (k : ℕ) : ((List.range k).flatMap fun s => [f s]).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp

/-! ## The residue loop -/

def sL (kP : St VV MM) : St VV MM := forS kS qQR (uB kP)

def sT : List (Fin VV) := kS :: uT

theorem sT_ok : ∀ x ∈ sT, gScratch x ∧ x ≠ eG2 := by unfold sT uT kList gScratch; decide

theorem sL_spec (kP : St VV MM) (kc : Ctx → Call → Params → ℕ → ℕ) (hk : KeyGoal kP kc) (C : Ctx) (c : Call)
    (p : Params) (wt : Wit c.n) (i : ℕ) (a0 : DS VV MM) (Big : ℕ) (hy : Hy C c p wt Big) (d : DS VV MM)
    (S Wc : List ℕ) (n1 : ℕ) (part : Option Bool) (t q : ℕ) (hpart : part ∈ parts c)
    (hq : q ∈ p.primes.sort (· ≤ ·)) (ht : t < wWin p ^ nDig c p)
    (hQ : QPre c p wt i a0 d) (hG : GW d S Wc) (hT : d.env qT = n1) (hpc : d.env kPC = partCode part)
    (hqv : d.env kQ = q) (htv : d.env kT = t) (hQR : d.env qQR = q ^ roleCount c.kind)
    (hn : n1 + q ^ roleCount c.kind ≤ 2 ^ keyW c p) :
    Hs C (sL kP) d (q ^ roleCount c.kind * (kc C c p Big + 24) + 4) (fun e => QPre c p wt i a0 e ∧
      GW e S (Wc ++ QR (GatherPhase.gZ c p) ((List.range (q ^ roleCount c.kind)).flatMap
        fun s => [qKey c p wt (cellOf wt.I i) part t q s]) n1) ∧
      e.env qT = n1 + q ^ roleCount c.kind ∧ Fr d e sT) := by
  have hw := widths C c p wt Big hy.wd
  have hKW : 2 ^ keyW c p < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hl := emitLoop (C := C) kS qQR qT (by decide) (by decide) (uB kP) d (q ^ roleCount c.kind) (by omega)
    (fun s => [qKey c p wt (cellOf wt.I i) part t q s]) (GatherPhase.gZ c p) S Wc n1
    (fun _ e => QPre c p wt i a0 e ∧ Fr d e sT) (kc C c p Big + 20)
    (fun k e v ⟨h1, h2⟩ => ⟨QPre.set h1 kS (by unfold gScratch; decide) v, RecordEmission.Fr.set_r h2 v (by decide)⟩)
    ⟨hQ, Fr.refl _ _⟩ hG hT hQR ?_
  · refine Hs.mono hl le_rfl (fun e ⟨⟨h1, h2⟩, h3, h4, _, _⟩ => ⟨h1, h3, ?_, h2⟩)
    rw [h4, len_single]
  · intro k hkN e ⟨hQe, hFe⟩ hGe hTe hie hme
    rw [len_single] at hTe ⊢
    have ev : ∀ x, x ∉ sT → e.env x = d.env x := hFe
    refine Hs.mono (uB_spec kP kc hk C c p wt i a0 Big hy e S _ _ part t q k hpart hq ht hkN hQe hGe hTe (by omega)
      (by rw [ev kPC (by decide)]; exact hpc) (by rw [ev kQ (by decide)]; exact hqv)
      (by rw [ev kT (by decide)]; exact htv) hie) le_rfl ?_
    rintro f ⟨f1, f2, f3, f4⟩
    have fv : ∀ x, x ∉ uT → f.env x = e.env x := f4
    refine ⟨⟨f1, Fr.trans hFe (Fr.weaken f4 (by decide))⟩, f2, by rw [f3]; simp, ?_, ?_⟩
    · rw [fv kS (by decide)]; exact hie
    · rw [fv qQR (by decide)]; exact hme

/-! ## `q^{roleCount}` -/

def pwB : St VV MM := .seq (.op (.mul qQR kQ qX)) (.op (.copy qQR qX))

def pwL : St VV MM := forS qPw gRC pwB

theorem pwL_spec (C : Ctx) (d : DS VV MM) (q rc : ℕ) (hq : d.env kQ = q) (hrc : d.env gRC = rc)
    (h1 : d.env qQR = 1) (hq1 : 1 ≤ q) (hW : q ^ rc < 2 ^ C.Wd) (hrcW : rc < 2 ^ C.Wd) :
    Hs C pwL d (rc * 7 + 4) (fun e => e.env qQR = q ^ rc ∧ Fr d e [qQR, qX, qPw] ∧ Same d e) := by
  have hl := forS_spec' (C := C) qPw gRC (by decide) pwB d rc hrcW
    (fun k e => e.env qQR = q ^ k ∧ Fr d e [qQR, qX, qPw] ∧ Same d e) 3
    (fun k e v ⟨e1, e2, e3⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact e1, RecordEmission.Fr.set_r e2 v (by decide),
      e3.trans (Same.set e qPw v)⟩)
    ⟨by rw [h1, pow_zero], Fr.refl _ _, Same.refl _⟩ hrc ?_
  · exact Hs.mono hl le_rfl (fun e ⟨h, _, _⟩ => h)
  · intro k hk e ⟨e1, e2, e3⟩ hie hme
    have eq : e.env kQ = q := by rw [e2 kQ (by decide)]; exact hq
    have hpow : q ^ (k + 1) ≤ q ^ rc := Nat.pow_le_pow_right hq1 hk
    apply Hx.hs
    refine Hs.then (hs_mul C qQR kQ qX e (by decide) (by decide) (by decide) (by
      rw [e1, eq, ← pow_succ]; omega)) (fun f1 hf1 m1 hm1 => ?_); subst hf1
    refine Hs.last (hs_copy C qQR qX _ (by decide)) (fun f2 hf2 m2 hm2 => ?_); subst hf2
    refine ⟨⟨⟨by vsimp [e1, eq, pow_succ], ?_, e3.trans (Same.of_sh (by simp))⟩, by vsimp [hie], by vsimp [hme]⟩,
      by omega⟩
    refine Fr.trans e2 (fun y hy => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [DS.set, Function.update_apply, hy.1, hy.2.1, if_false]

/-! ## The prime body -/

theorem prime_at (L Ps : List ℕ) (v : ℕ) (hIPr : L.drop v = Ps ++ L.drop (v + Ps.length)) (j : ℕ)
    (hj : j < Ps.length) : v + j < L.length ∧ L.getD (v + j) 0 = Ps.getD j 0 := by
  have hl := congrArg List.length hIPr
  simp only [List.length_drop, List.length_append] at hl
  refine ⟨by omega, ?_⟩
  have : (L.drop v).getD j 0 = L.getD (v + j) 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [← this, hIPr, List.getD_append _ _ _ _ hj]

def pB (kP : St VV MM) : St VV MM :=
  .seq (.op (.copy qIdx vIPr)) (.seq (.op (.add qIdx qJ)) (.seq (fetch sN qIdx kQ) (.seq (.op (.zero qQR))
  (.seq (.op (.inc qQR)) (.seq pwL (sL kP))))))

def pT : List (Fin VV) := [qIdx, kQ, c0, vJ, qQR, qPw, qX] ++ sT

theorem pT_ok : ∀ x ∈ pT, gScratch x ∧ x ≠ eG2 := by unfold pT sT uT kList gScratch; decide

/-- The `j`-th prime (increasing). -/
noncomputable def prJ (p : Params) (j : ℕ) : ℕ := (p.primes.sort (· ≤ ·)).getD j 0

/-- The query keys of one prime. -/
noncomputable def lS (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) (t q : ℕ) :
    List ℕ := (List.range (q ^ roleCount c.kind)).flatMap fun s => [qKey c p wt y part t q s]

theorem pB_spec (kP : St VV MM) (kc : Ctx → Call → Params → ℕ → ℕ) (hk : KeyGoal kP kc) (C : Ctx) (c : Call)
    (p : Params) (wt : Wit c.n) (i : ℕ) (a0 : DS VV MM) (Big : ℕ) (hy : Hy C c p wt Big) (d : DS VV MM)
    (S Wc : List ℕ) (n1 : ℕ) (part : Option Bool) (t j : ℕ) (hpart : part ∈ parts c)
    (hj : j < (p.primes.sort (· ≤ ·)).length) (ht : t < wWin p ^ nDig c p)
    (hQ : QPre c p wt i a0 d) (hG : GW d S Wc) (hT : d.env qT = n1) (hpc : d.env kPC = partCode part)
    (htv : d.env kT = t) (hjv : d.env qJ = j) (hn : n1 + prJ p j ^ roleCount c.kind ≤ 2 ^ keyW c p) :
    Hs C (pB kP) d (6 * (CounterMachine.cellN c p wt).length + p.P ^ 2 * (kc C c p Big + 24) + 60)
      (fun e => QPre c p wt i a0 e ∧ GW e S (Wc ++ QR (GatherPhase.gZ c p) (lS c p wt (cellOf wt.I i) part t (prJ p j)) n1) ∧
        e.env qT = n1 + prJ p j ^ roleCount c.kind ∧ Fr d e pT) := by
  obtain ⟨cT, hs⟩ := hy.spec
  obtain ⟨w, hw⟩ := hy.dec
  obtain ⟨B1, B2, hadm⟩ := hy.adm
  obtain ⟨hc, hE, hN, hhE, hJ, hrc, hKB, -, -, -, hIP⟩ := QPre.vals hQ
  have hwd := widths C c p wt Big hy.wd
  have hKW : 2 ^ keyW c p < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  set q := prJ p j with hqdef
  have hqm : q ∈ p.primes.sort (· ≤ ·) := by
    rw [hqdef, prJ, List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
  have hq1 : 1 ≤ q := GatherPhase.prime_pos_of c p hs q hqm
  have hqP : q ≤ p.P := primes_le hs q (by simpa using hqm)
  have hrc2 : roleCount c.kind ≤ 2 := roleCount_le_two c
  have hrc1 : 1 ≤ roleCount c.kind := roleCount_pos c.kind
  have hP1 : 1 ≤ p.P := by have := hs.P_large; omega
  have hqP2 : q ^ roleCount c.kind ≤ p.P ^ 2 :=
    (Nat.pow_le_pow_left hqP _).trans (Nat.pow_le_pow_right hP1 hrc2)
  have ⟨hix, hiv⟩ := prime_at (CounterMachine.cellN c p wt) (p.primes.sort (· ≤ ·)) (a0.env vIPr) hQ.pre.IPr j hj
  have hNL := cellN_len_lt c p wt hadm hs w hw
  have hNW : (CounterMachine.cellN c p wt).length < 2 ^ C.Wd := by
    refine lt_of_lt_of_le hNL (Nat.pow_le_pow_right (by norm_num) ?_)
    have := hy.wd; unfold wdNeed at this
    have : c.n + 16 ≤ (p.J + 4) * (Big + c.n + 16) := le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))
    nlinarith
  apply Hx.hs
  refine Hs.then (hs_copy C qIdx vIPr d (by decide)) (fun e1 he1 m1 hm1 => ?_); subst he1
  refine Hs.then (hs_add C qIdx qJ _ (by decide) (by vsimp [hIP, hjv]; omega)) (fun e2 he2 m2 hm2 => ?_)
  subst he2
  refine Hs.then (o_fetch sN qIdx kQ (by decide) (by decide) (by decide) _ (by vsimp [hIP, hjv, hN]; omega)
    (by vsimp [hIP, hjv]; omega)) (fun e3 ⟨h31, h32, h33, h34⟩ m3 hm3 => ?_)
  have k3 : e3.env kQ = q := by rw [h31]; vsimp [hIP, hjv, hN]; exact hiv
  have ram3 : e3.ram = d.ram := h33.ram
  have rc3 : e3.rc = Function.update d.rc sN (a0.env vIPr + j + 1) := by rw [h34]; vsimp [hIP, hjv]
  have m3b : m3 ≤ 6 * (CounterMachine.cellN c p wt).length + 9 := by
    have := hQ.rcur sN
    rw [hN] at this
    vsimp [hIP, hjv] at hm3
    omega
  have fr3 : Fr d e3 [qIdx, c0, vJ, kQ] := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [h32 y (by simp [hy.2.1, hy.2.2.1, hy.2.2.2])]
    simp [DS.set, Function.update_apply, hy.1]
  have rcok3 : RcOK e3 := by
    refine RcOK.fetch ?_ h33 h34 ?_
    · exact fun m => hQ.rcur m
    · vsimp [hIP, hjv, hN]; omega
  clear h31 h32 h34 hm3
  refine Hs.then (hs_zero C qQR e3) (fun e4 he4 m4 hm4 => ?_); subst he4
  refine Hs.then (hs_inc C qQR _ (by vsimp []; omega)) (fun e5 he5 m5 hm5 => ?_); subst he5
  have hqW : q ^ roleCount c.kind < 2 ^ C.Wd := by omega
  have h4W : 2 ^ 2 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine Hs.then (pwL_spec C _ q (roleCount c.kind) (by vsimp [k3]) (by vsimp [fr3 gRC (by decide), hrc])
    (by vsimp []) hq1 hqW (by norm_num at h4W; omega)) (fun e6 ⟨h61, h62, h63⟩ m6 hm6 => ?_)
  have fr6 : Fr d e6 [qIdx, kQ, c0, vJ, qQR, qPw, qX] := by
    refine Fr.trans (Fr.weaken fr3 (by decide)) (Fr.trans (fun y hy => ?_) (Fr.weaken h62 (by decide)))
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [DS.set, Function.update_apply, hy.2.2.2.2.1]
  have ke6 : RecordEmission.Ke d e6 := by
    refine ⟨fun m _ => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h63.ram]; show e3.ram m = d.ram m; rw [ram3]
    · rw [h63.ip]; exact h33.ip
    · rw [h63.out]; exact h33.out
    · rw [h63.kin]; exact h33.kin
    · rw [h63.kout]; exact h33.kout
    · rw [h63.kc]; exact h33.kc
  have rc6 : ∀ m, e6.rc m ≤ (e6.ram m).length := by
    intro m; rw [h63.rc, h63.ram]; exact rcok3 m
  have Q6 : QPre c p wt i a0 e6 := QPre.step hQ ke6 rc6 _ (by unfold gScratch; decide) fr6
  have G6 : GW e6 S Wc := GW.congr hG (by rw [h63.ram]; show e3.ram sG = d.ram sG; rw [ram3])
    (by rw [h63.rc]; show e3.rc sG = d.rc sG; rw [rc3, Function.update_of_ne (by decide)])
  have ev6 : ∀ x, x ∉ [qIdx, kQ, c0, vJ, qQR, qPw, qX] → e6.env x = d.env x := fr6
  refine Hs.last (sL_spec kP kc hk C c p wt i a0 Big hy e6 S Wc n1 part t q hpart hqm ht Q6 G6
    (by rw [ev6 qT (by decide)]; exact hT) (by rw [ev6 kPC (by decide)]; exact hpc)
    (by rw [h62 kQ (by decide)]; vsimp [k3]) (by rw [ev6 kT (by decide)]; exact htv) h61 hn)
    (fun e7 ⟨h71, h72, h73, h74⟩ m7 hm7 => ?_)
  refine ⟨⟨h71, h72, h73, Fr.trans (Fr.weaken fr6 (by decide)) (Fr.weaken h74 (by decide))⟩, ?_⟩
  have e8 : q ^ roleCount c.kind * (kc C c p Big + 24) ≤ p.P ^ 2 * (kc C c p Big + 24) :=
    Nat.mul_le_mul_right _ hqP2
  have e9 : roleCount c.kind * 7 ≤ 14 := by omega
  omega

end NearCubicGates.Close.Cells.QueryPass
