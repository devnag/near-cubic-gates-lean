import Proof.Gates.CellsGatherQ.Query3

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

/-- The query keys of one digit vector (all primes, increasing). -/
noncomputable def lJ (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) (t : ℕ) :
    List ℕ := (List.range (p.primes.sort (· ≤ ·)).length).flatMap fun j => lS c p wt y part t (prJ p j)

/-- The query keys of one part (all digit vectors in counter order). -/
noncomputable def lT (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) : List ℕ :=
  (List.range (wWin p ^ nDig c p)).flatMap fun t => lJ c p wt y part t

/-- The per-prime cost bound. -/
def costP (kc : Ctx → Call → Params → ℕ → ℕ) (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) : ℕ :=
  6 * (CounterMachine.cellN c p wt).length + p.P ^ 2 * (kc C c p Big + 24) + 60

theorem lS_len (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) (t q : ℕ) :
    (lS c p wt y part t q).length = q ^ roleCount c.kind := len_single _ _

theorem two_pow_gt (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) (hwd : wdNeed c p wt Big ≤ C.Wd) :
    c.n + 2 < 2 ^ C.Wd := by
  have h1 : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have h2 : c.n + 16 ≤ wdNeed c p wt Big := by
    unfold wdNeed
    have : c.n + 16 ≤ (p.J + 4) * (Big + c.n + 16) := le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))
    nlinarith
  omega

/-! ## The prime loop -/

def tL (kP : St VV MM) : St VV MM := forS qJ vNP (pB kP)

def tT : List (Fin VV) := qJ :: pT

theorem tT_ok : ∀ x ∈ tT, gScratch x ∧ x ≠ eG2 := by unfold tT pT sT uT kList gScratch; decide

theorem tL_spec (kP : St VV MM) (kc : Ctx → Call → Params → ℕ → ℕ) (hk : KeyGoal kP kc) (C : Ctx) (c : Call)
    (p : Params) (wt : Wit c.n) (i : ℕ) (a0 : DS VV MM) (Big : ℕ) (hy : Hy C c p wt Big) (d : DS VV MM)
    (S Wc : List ℕ) (n1 : ℕ) (part : Option Bool) (t : ℕ) (hpart : part ∈ parts c)
    (ht : t < wWin p ^ nDig c p)
    (hQ : QPre c p wt i a0 d) (hG : GW d S Wc) (hT : d.env qT = n1) (hpc : d.env kPC = partCode part)
    (htv : d.env kT = t) (hn : n1 + (lJ c p wt (cellOf wt.I i) part t).length ≤ 2 ^ keyW c p) :
    Hs C (tL kP) d ((p.primes.sort (· ≤ ·)).length * (costP kc C c p wt Big + 4) + 4) (fun e =>
      QPre c p wt i a0 e ∧ GW e S (Wc ++ QR (GatherPhase.gZ c p) (lJ c p wt (cellOf wt.I i) part t) n1) ∧
      e.env qT = n1 + (lJ c p wt (cellOf wt.I i) part t).length ∧ Fr d e tT) := by
  obtain ⟨cT, hs⟩ := hy.spec
  have hNP := GatherPhase.nP_le c p hs
  have hPn := P_le_n c p hs
  have h2 := two_pow_gt C c p wt Big hy.wd
  have hNPv : d.env vNP = (p.primes.sort (· ≤ ·)).length := (QPre.vals hQ).2.2.2.2.2.2.2.2.2.1
  have hl := emitLoop (C := C) qJ vNP qT (by decide) (by decide) (pB kP) d (p.primes.sort (· ≤ ·)).length
    (by omega) (fun j => lS c p wt (cellOf wt.I i) part t (prJ p j)) (GatherPhase.gZ c p) S Wc n1
    (fun _ e => QPre c p wt i a0 e ∧ Fr d e tT) (costP kc C c p wt Big)
    (fun k e v ⟨h1, h2⟩ => ⟨QPre.set h1 qJ (by unfold gScratch; decide) v, RecordEmission.Fr.set_r h2 v (by decide)⟩)
    ⟨hQ, Fr.refl _ _⟩ hG hT hNPv ?_
  · exact Hs.mono hl le_rfl (fun e ⟨⟨h1, h2⟩, h3, h4, _, _⟩ => ⟨h1, h3, h4, h2⟩)
  · intro k hkN e ⟨hQe, hFe⟩ hGe hTe hie hme
    have ev : ∀ x, x ∉ tT → e.env x = d.env x := hFe
    have hpre := pre_le (fun j => lS c p wt (cellOf wt.I i) part t (prJ p j)) k _ hkN
    rw [lS_len] at hpre
    refine Hs.mono (pB_spec kP kc hk C c p wt i a0 Big hy e S _ _ part t k hpart hkN ht hQe hGe hTe
      (by rw [ev kPC (by decide)]; exact hpc) (by rw [ev kT (by decide)]; exact htv) hie
      (by unfold lJ at hn; omega)) le_rfl ?_
    rintro f ⟨f1, f2, f3, f4⟩
    have fv : ∀ x, x ∉ pT → f.env x = e.env x := f4
    refine ⟨⟨f1, Fr.trans hFe (Fr.weaken f4 (by decide))⟩, f2, by rw [f3, lS_len], ?_, ?_⟩
    · rw [fv qJ (by decide)]; exact hie
    · rw [fv vNP (by decide)]; exact hme

/-! ## The digit-vector loop -/

def cL (kP : St VV MM) : St VV MM := forS kT vBN (tL kP)

def cT' : List (Fin VV) := kT :: tT

theorem cT'_ok : ∀ x ∈ cT', gScratch x ∧ x ≠ eG2 := by unfold cT' tT pT sT uT kList gScratch; decide

theorem BN_le (c : Call) (p : Params) {cT : ℕ} (hs : Spec cT (header c) p) :
    wWin p ^ nDig c p ≤ 2 ^ keyW c p := by
  have h1 := GatherPhase.wWin_le_P c p hs
  have h2 := GatherPhase.P1_lt_keyBits p
  calc wWin p ^ nDig c p ≤ (2 ^ keyBits p) ^ nDig c p := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ (keyBits p * nDig c p) := by rw [← pow_mul]
    _ ≤ 2 ^ keyW c p := by
      apply Nat.pow_le_pow_right (by norm_num)
      unfold keyW keyLen nDig
      apply Nat.mul_le_mul_left
      nlinarith

theorem cL_spec (kP : St VV MM) (kc : Ctx → Call → Params → ℕ → ℕ) (hk : KeyGoal kP kc) (C : Ctx) (c : Call)
    (p : Params) (wt : Wit c.n) (i : ℕ) (a0 : DS VV MM) (Big : ℕ) (hy : Hy C c p wt Big) (d : DS VV MM)
    (S Wc : List ℕ) (n1 : ℕ) (part : Option Bool) (hpart : part ∈ parts c)
    (hQ : QPre c p wt i a0 d) (hG : GW d S Wc) (hT : d.env qT = n1) (hpc : d.env kPC = partCode part)
    (hn : n1 + (lT c p wt (cellOf wt.I i) part).length ≤ 2 ^ keyW c p) :
    Hs C (cL kP) d (wWin p ^ nDig c p * ((p.primes.sort (· ≤ ·)).length * (costP kc C c p wt Big + 4) + 4 + 4) + 4)
      (fun e => QPre c p wt i a0 e ∧ GW e S (Wc ++ QR (GatherPhase.gZ c p) (lT c p wt (cellOf wt.I i) part) n1) ∧
        e.env qT = n1 + (lT c p wt (cellOf wt.I i) part).length ∧ Fr d e cT') := by
  obtain ⟨cT, hs⟩ := hy.spec
  have hw := widths C c p wt Big hy.wd
  have hKW : 2 ^ keyW c p < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hBN := BN_le c p hs
  have hBNv : d.env vBN = wWin p ^ nDig c p := (QPre.vals hQ).2.2.2.2.2.2.2.2.1
  have hl := emitLoop (C := C) kT vBN qT (by decide) (by decide) (tL kP) d (wWin p ^ nDig c p)
    (by omega) (fun t => lJ c p wt (cellOf wt.I i) part t) (GatherPhase.gZ c p) S Wc n1
    (fun _ e => QPre c p wt i a0 e ∧ Fr d e cT')
    ((p.primes.sort (· ≤ ·)).length * (costP kc C c p wt Big + 4) + 4)
    (fun k e v ⟨h1, h2⟩ => ⟨QPre.set h1 kT (by unfold gScratch; decide) v, RecordEmission.Fr.set_r h2 v (by decide)⟩)
    ⟨hQ, Fr.refl _ _⟩ hG hT hBNv ?_
  · exact Hs.mono hl le_rfl (fun e ⟨⟨h1, h2⟩, h3, h4, _, _⟩ => ⟨h1, h3, h4, h2⟩)
  · intro k hkN e ⟨hQe, hFe⟩ hGe hTe hie hme
    have ev : ∀ x, x ∉ cT' → e.env x = d.env x := hFe
    have hpre := pre_le (fun t => lJ c p wt (cellOf wt.I i) part t) k _ hkN
    refine Hs.mono (tL_spec kP kc hk C c p wt i a0 Big hy e S _ _ part k hpart hkN hQe hGe hTe
      (by rw [ev kPC (by decide)]; exact hpc) hie (by unfold lT at hn; omega)) le_rfl ?_
    rintro f ⟨f1, f2, f3, f4⟩
    have fv : ∀ x, x ∉ tT → f.env x = e.env x := f4
    refine ⟨⟨f1, Fr.trans hFe (Fr.weaken f4 (by decide))⟩, f2, by rw [f3], ?_, ?_⟩
    · rw [fv kT (by decide)]; exact hie
    · rw [fv vBN (by decide)]; exact hme

end NearCubicGates.Close.Cells.QueryPass
