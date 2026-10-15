import Proof.Gates.Cells.CellInv

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

def passP (gP sP : St VV MM) : St VV MM := .seq zbP (.seq formsP (.seq opP (.seq gP sP)))

/-- The cost bound of a passing cell (parameters: `n`, `|cellN|`, `|ctrL|`, `|kxL|`, `gWork`, the forms cost, the
gathering and systems costs). -/
def passCost (n L E X gW FC TG TS : ℕ) : ℕ :=
  40 * n + 7 * L + E + X + 2 * gW + FC + n * (6 * n + 26 + 4) + TG + TS + 100

theorem membL_length {n : ℕ} (I : Finset (Fin n)) : (membL I).length = n := by simp [membL]

theorem iface_not_scratch : ∀ x ∈ ifaceList, ¬ gScratch x := by unfold gScratch; decide

theorem iface_sys : ∀ x ∈ ifaceList, (x.val < 50 ∨ 99 < x.val) ∧ x ≠ t0 ∧ x ≠ t1 ∧ x ≠ t2 ∧ x ≠ t3 ∧ x ≠ t4 ∧
    x ≠ t5 ∧ x ≠ t6 ∧ x ≠ t7 ∧ x ≠ t8 ∧ x ≠ t9 ∧ x ≠ c0 ∧ x ≠ c1 ∧ x ≠ c2 ∧ x ≠ c3 ∧ x ≠ c4 ∧ x ≠ c5 ∧ x ≠ vCnt ∧
    x ≠ vJ := by decide

theorem sys_keep (x : Fin VV) (h : (x.val < 50 ∨ 99 < x.val) ∧ x ≠ t0 ∧ x ≠ t1 ∧ x ≠ t2 ∧ x ≠ t3 ∧ x ≠ t4 ∧
    x ≠ t5 ∧ x ≠ t6 ∧ x ≠ t7 ∧ x ≠ t8 ∧ x ≠ t9 ∧ x ≠ c0 ∧ x ≠ c1 ∧ x ≠ c2 ∧ x ≠ c3 ∧ x ≠ c4 ∧ x ≠ c5 ∧ x ≠ vCnt ∧
    x ≠ vJ) (a b : DS VV MM)
    (hf : ∀ x : Fin VV, (x.val < 50 ∨ 99 < x.val) → x ≠ t0 → x ≠ t1 → x ≠ t2 → x ≠ t3 → x ≠ t4 → x ≠ t5 → x ≠ t6 →
      x ≠ t7 → x ≠ t8 → x ≠ t9 → x ≠ c0 → x ≠ c1 → x ≠ c2 → x ≠ c3 → x ≠ c4 → x ≠ c5 → x ≠ vCnt → x ≠ vJ →
      b.env x = a.env x) : b.env x = a.env x := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact hf x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19

section P
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

theorem iPar_lt : iPar (cellN c p wt) + 1 ≤ (cellN c p wt).length := by
  have h := drop_eq_len (lay c p wt).params (by simp [paramsN])
  have e : iPsi (cellN c p wt) = iPar (cellN c p wt) + 4 + fld (cellN c p wt) (iPar (cellN c p wt)) := rfl
  simp only [List.length_append] at h
  omega

include hadm hs hw in
theorem twoJ_le_gWork (y : Cells wt.I) : 2 * p.J ≤ gWork c p wt y := by
  have hdf := Call.drop_factors c p wt
  have hfsl := drop_eq_len hdf (by simp)
  simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at hfsl
  have hnf := nfactors_eq c p wt hadm hs w hw
  have hJ1 := hs.J_pos
  have hR : roleCount c.kind * (p.J + 1) ≤ (reqIds c p).length := by
    unfold reqIds
    rw [List.length_append]
    have : ((List.range (roleCount c.kind)).flatMap fun r =>
        (List.range p.J).map (fun j => ReqId.digitMoment r j) ++ [ReqId.phiMoment r]).length =
        roleCount c.kind * (p.J + 1) := by
      simp [List.length_flatMap, List.map_const', List.sum_replicate]
    omega
  have hr1 := roleCount_pos c.kind
  have : p.J + 1 ≤ roleCount c.kind * (p.J + 1) := Nat.le_mul_of_pos_left _ hr1
  unfold gWork; omega

include hadm hs hw in
/-- **A passing cell.** -/
theorem passP_spec (S : SolveMachine) (gP sysPr : St VV MM) (tg : Ctx → Call → Params → ℕ → ℕ)
    (ts : SolveMachine → Ctx → Call → Params → ℕ → ℕ) (hG : GatherGoal gP tg) (hS : SysGoal sysPr ts)
    (hK : C.K = Callee.ofSolve S) (Big : ℕ) (hBig : ∀ x ∈ cellN c p wt, natBitLength x ≤ Big)
    (hWd : wdNeed c p wt Big ≤ C.Wd)
    (hLB : ∀ (y : Cells wt.I) part κ, κ ∈ digitVectors c p wt y →
      (sysWord (sysOf c p wt y κ part)).length ≤ C.Lk ∧ S.budget (sysOf c p wt y κ part) ≤ C.Bk)
    (i : ℕ) (hi : i < 2 ^ cellBits wt.I) (ht : CellTests c p wt (cellOf wt.I i))
    (a : DS VV MM) (hI : Iface c p wt a) (hSt : Sto c p wt a) (hCT : a.ram sCT = blk c p wt i)
    (hcI : a.env cI = i) (hcnt : a.env vCnt ≤ 2 ^ c.n) :
    Hs C (passP gP sysPr) a (passCost c.n (cellN c p wt).length (ctrL c p wt (cellOf wt.I i)).length
      (kxL c p wt (cellOf wt.I i)).length (gWork c p wt (cellOf wt.I i)) (formsCost (cellN c p wt).length c.n)
      (tg C c p Big) (ts S C c p Big)) (fun b =>
      Iface c p wt b ∧ Sto c p wt b ∧ b.ram sCT = a.ram sCT ∧ b.ip = a.ip ∧
      (b.env vCnt : ℚ) = a.env vCnt + cellCount c p wt (cellOf wt.I i) ∧ b.env vUnc = a.env vUnc ∧
      b.env cI = a.env cI) := by
  have hJ1 := hs.J_pos
  have hwd : 256 * (p.J + 4) * (Big + c.n + 16) + 4 * recWidth c p wt ≤ C.Wd := hWd
  have hW1 : 3 * Big + 6 * c.n + 20 ≤ C.Wd := by nlinarith
  have hW64 : 64 * (p.J + 4) * (Big + c.n + 16) ≤ C.Wd := by nlinarith
  have hnW : c.n < 2 ^ C.Wd := lt_of_lt_of_le Nat.lt_two_pow_self (pw_mono (by omega))
  have hW4 : 4 ≤ 2 ^ C.Wd := by
    have : 2 ^ 2 ≤ 2 ^ C.Wd := pw_mono (by omega)
    simpa using this
  have hLW := sz_len c p wt hadm hs w hw Big C.Wd hW1
  have hpar := iPar_lt c p wt
  have hzl := zbL_length c wt i
  -- step 1: the z-bits
  have hz := Hs.rc_le (zbP_spec (C := C) wt.I a hI.cst hI.n hnW hW4 hSt.sR hSt.lZb) hSt.rcur hSt.kc
  have hzc : 1 + (a.rc sR + 1 + (a.rc sZb + 1 + (c.n * (8 + 4) + 4) + 1) + 1) + 1 ≤ 20 * c.n + 20 := by
    have h1 := hSt.rcur sR
    have h2 := hSt.rcur sZb
    rw [hSt.sR, membL_length] at h1
    have h3 := hSt.lZb
    omega
  refine Hs.bseq (Hs.mono hz hzc (fun _ h => h)) (by unfold passCost; omega)
    (fun e1 ⟨⟨z1, z2, z3, z4, z5, z6, z7, z8⟩, zr, zk⟩ => ?_)
  have I1 : Iface c p wt e1 := hI.of_fr z8 (by decide)
  have e1N : e1.ram sN = cellN c p wt := by rw [z1, Function.update_of_ne (by decide), hSt.sN]
  have e1Z : e1.ram sZb = zbL wt.I i := by rw [z1, Function.update_self, hcI]
  have e1ram : ∀ m, m ≠ sZb → e1.ram m = a.ram m := fun m hm => by rw [z1, Function.update_of_ne hm]
  have e1rc : ∀ m, m ≠ sZb → m ≠ sR → e1.rc m = a.rc m := fun m h1 h2 => by
    rw [z2, Function.update_of_ne h1, Function.update_of_ne h2]
  -- step 2: the forms
  have hfp : FormsPre c p wt i e1 := ⟨I1.cst, e1N, e1Z, I1.n, I1.rc, I1.J, I1.B1, I1.WS, I1.FS,
    by rw [e1ram sE (by decide)]; exact hSt.lE (cellOf wt.I i), by rw [e1ram sX (by decide)]; exact hSt.lX (cellOf wt.I i)⟩
  have hf := Hs.rc_le (formsP_spec (C := C) c p wt hadm hs w hw i Big hBig hW1 e1 hfp) zr zk
  have hfc : e1.rc sE + e1.rc sX + e1.rc sZb + e1.rc sN + e1.rc sB + e1.rc sG +
      formsCost (cellN c p wt).length c.n ≤ (ctrL c p wt (cellOf wt.I i)).length + (kxL c p wt (cellOf wt.I i)).length + c.n +
      (cellN c p wt).length + 2 * gWork c p wt (cellOf wt.I i) + formsCost (cellN c p wt).length c.n := by
    have r1 := hSt.rcur sE
    have r2 := hSt.rcur sX
    have r4 := hSt.rcur sN
    have r5 := hSt.rcur sB
    have r6 := hSt.rcur sG
    rw [e1rc sE (by decide) (by decide), e1rc sX (by decide) (by decide), e1rc sN (by decide) (by decide),
      e1rc sB (by decide) (by decide), e1rc sG (by decide) (by decide), z2, Function.update_self]
    rw [hSt.sN] at r4
    have := hSt.lE (cellOf wt.I i)
    have := hSt.lX (cellOf wt.I i)
    have := hSt.lB (cellOf wt.I i)
    have := hSt.lG (cellOf wt.I i)
    omega
  refine Hs.bseq (Hs.mono hf hfc (fun _ h => h)) (by unfold passCost; omega)
    (fun e2 ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, ag2⟩, fr, fk⟩ => ?_)
  have I2 : Iface c p wt e2 := I1.of_fr ag2.fr (by decide)
  -- step 3: the outer parity
  obtain ⟨Rp, hRp⟩ := (lay c p wt).parl
  have hpl : c.parity.length ≤ c.n := hadm.2.2.2.2.2.2.2.2.2.2
  have e2N : e2.ram sN = cellN c p wt := by rw [f5, e1N]
  have ho := Hs.rc_le (opP_spec (C := C) e2 I2.cst (zbL wt.I i) c.parity Rp (by rw [f13, e1Z])
    (zbL_le_one wt.I i) (fun x hx => by rw [hzl]; exact hadm.2.2.2.2.2.1 x hx) (by rw [e2N, I2.Par]; exact hRp)
    (by rw [e2N, I2.Par]; exact hpar) I2.PL (by rw [I2.Par]; omega) (by omega) (by rw [hzl]; exact hnW) hW4
    (by rw [f9]; omega)) fr fk
  have hoc : e2.rc sN + 5 * e2.env gPar + c.parity.length * (6 * (zbL wt.I i).length + 26 + 4) + 20 ≤
      6 * (cellN c p wt).length + c.n * (6 * c.n + 26 + 4) + 20 := by
    rw [I2.Par, hzl]
    have := Nat.mul_le_mul_right (6 * c.n + 26 + 4) hpl
    omega
  refine Hs.bseq (Hs.mono ho hoc (fun _ h => h)) (by unfold passCost; omega)
    (fun e3 ⟨⟨o1, o2, o3, o4, ag3⟩, orc, ok⟩ => ?_)
  have I3 : Iface c p wt e3 := I2.of_fr ag3.fr (by decide)
  have e3op : e3.env vOP = if outerParity c wt (cellOf wt.I i) then 1 else 0 := by rw [o1, outerParity_eq]
  -- step 4: the gathering
  have e3ram : ∀ m, m ≠ sN → m ≠ sB → m ≠ sG → m ≠ sE → m ≠ sX → m ≠ sZb → e3.ram m = a.ram m := by
    intro m h0 h1 h2 h3 h4 h5
    have hm : m ∉ formsMs := by
      simp only [formsMs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h0, h1, h2, h3, h4, h5⟩
    rw [o2, ag2.ram m hm, e1ram m h5]
  have hgw := twoJ_le_gWork c p wt hadm hs w hw (cellOf wt.I i)
  have hLg : (cellN c p wt).length ≤ gWork c p wt (cellOf wt.I i) := by unfold gWork; omega
  have hgp : GatherPre c p wt i e3 := by
    refine ⟨I3.cst, by rw [o2, e2N], by rw [e3ram sCT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hCT],
      by rw [o2, f1], ?_, ?_, ?_, orc, I3.n, I3.kind, I3.J, I3.rc, I3.hE, I3.BN, I3.NP, I3.IPr, I3.VW, I3.KW, I3.KB, I3.NL⟩
    · rw [o2]
      have h1 := f11
      rw [e1ram sG (by decide)] at h1
      have h2 := hSt.lG (cellOf wt.I i)
      omega
    · rw [o2]
      have h1 := f10
      rw [e1ram sB (by decide)] at h1
      have h2 := hSt.lB (cellOf wt.I i)
      omega
    · rw [e3ram sA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hSt.lA (cellOf wt.I i)
  have hg : Hs C gP e3 (tg C c p Big) (fun b =>
      b.ram sA = rowVals c p wt (cellOf wt.I i) ∧
      (∀ m, m ≠ sG → m ≠ sB → m ≠ sA → b.ram m = e3.ram m) ∧
      (b.ram sG).length ≤ gWork c p wt (cellOf wt.I i) ∧ (b.ram sB).length ≤ gWork c p wt (cellOf wt.I i) ∧
      (∀ m, b.rc m ≤ (b.ram m).length) ∧
      b.ip = e3.ip ∧ b.out = e3.out ∧ b.kin = e3.kin ∧ b.kout = e3.kout ∧ b.kc = e3.kc ∧
      (∀ x : Fin VV, ¬ gScratch x → b.env x = e3.env x)) :=
    hG C c p wt i e3 Big hs ⟨w, hw⟩ ⟨B1, B2, hadm⟩ hi ht hgp hBig hWd
  refine Hs.bseq hg (by unfold passCost; omega)
    (fun e4 ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ => ?_)
  have I4 : Iface c p wt e4 := I3.of_eq (fun x hx => g11 x (iface_not_scratch x hx))
  -- step 5: the systems
  have keep4 : ∀ x, x ∉ zbT → x ∉ formsT → x ∉ opT → ¬ gScratch x → e4.env x = a.env x := by
    intro x h1 h2 h3 h4
    rw [g11 x h4, ag3.fr x h3, ag2.fr x h2, z8 x h1]
  have e4ram : ∀ m, m ≠ sN → m ≠ sB → m ≠ sG → m ≠ sE → m ≠ sX → m ≠ sZb → m ≠ sA → e4.ram m = a.ram m :=
    fun m h0 h1 h2 h3 h4 h5 h6 => by rw [g2 m h2 h1 h6, e3ram m h0 h1 h2 h3 h4 h5]
  have e4N : e4.ram sN = cellN c p wt := by rw [g2 sN (by decide) (by decide) (by decide), o2, e2N]
  have e4E : e4.ram sE = ctrL c p wt (cellOf wt.I i) := by rw [g2 sE (by decide) (by decide) (by decide), o2, f1]
  have e4X : e4.ram sX = kxL c p wt (cellOf wt.I i) := by rw [g2 sX (by decide) (by decide) (by decide), o2, f3]
  have e4Z : e4.ram sZb = zbL wt.I i := by rw [g2 sZb (by decide) (by decide) (by decide), o2, f13, e1Z]
  have e4kin : e4.kin = [] := by rw [g8, ag3.kin, ag2.kin, z5, hSt.kin]
  have e4kc : e4.kc ≤ e4.kout.length := by rw [g10, g9]; exact ok
  have e4cnt : e4.env vCnt = a.env vCnt := keep4 vCnt (by decide) (by decide) (by decide) (by unfold gScratch; decide)
  have hpre : SysPre S C c p wt (cellOf wt.I i) e4 := ⟨hK, I4.cst, e4N, g1, e4E, e4X,
    by rw [e4ram sP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hSt.sP],
    e4kin, e4kc, by rw [g11 vOP (by unfold gScratch; decide), e3op], I4.rc, I4.J, I4.hE, I4.M1, I4.A, I4.Lam, I4.BN,
    I4.NP, I4.IPr, I4.TS0, I4.TS1, I4.TW0, I4.TW1, I4.kind, g5, by rw [e4cnt]; exact hcnt⟩
  obtain ⟨b, nb, hex, hnb, s1, s2, s3, s4, s5, s6⟩ :=
    hS S C c p wt (cellOf wt.I i) e4 Big hs ⟨w, hw⟩ ⟨B1, B2, hadm⟩ ht hpre hBig hW64 (hLB (cellOf wt.I i))
  refine Hs.mono ⟨b, nb, hex, le_rfl, rfl⟩ (by unfold passCost; omega) ?_
  rintro b' rfl
  have hrc := hex.rc_le g5
  have hkc := hex.kc_le e4kc
  have Ib : Iface c p wt b := I4.of_eq (fun x hx => sys_keep x (iface_sys x hx) e4 b s6)
  refine ⟨Ib, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrc, ?_, s5, hkc⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s2, e4N]
  · rw [s2, e4ram sP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hSt.sP]
  · rw [s2, e4ram sR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hSt.sR]
  · rw [s2, e4ram sCT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hCT,
      blk_length]
  · rw [s2, e4Z, hzl]
  · intro y'; rw [s2, e4E, ctrL_len c p wt _ y']
  · intro y'; rw [s2, e4X, kxL_len c p wt _ y']
  · intro y'; rw [s2, ← gWork_eq c p wt (cellOf wt.I i) y']; exact g3
  · intro y'; rw [s2, ← gWork_eq c p wt (cellOf wt.I i) y']; exact g4
  · intro y'; rw [s2, g1, rowVals_len c p wt _ y']
  · rw [s4, g7, ag3.out, ag2.out, z4, hSt.out]
  · rw [s2, e4ram sCT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [s3, g6, ag3.ip, ag2.ip, z3]
  · rw [s1, e4cnt]
  · rw [sys_keep vUnc (by decide) e4 b s6]
    exact keep4 vUnc (by decide) (by decide) (by decide) (by unfold gScratch; decide)
  · rw [sys_keep cI (by decide) e4 b s6]
    exact keep4 cI (by decide) (by decide) (by decide) (by unfold gScratch; decide)

end P

end NearCubicGates.Close.Cells
