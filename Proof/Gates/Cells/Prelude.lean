import Proof.Gates.Cells.ConstSpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)

variable {C : Ctx}

def initP : St VV MM := .seq (.op (.inc v1)) (.seq (.op (.inc v2)) (.op (.inc v2)))
def preludeP (cP : St VV MM) : St VV MM :=
  .seq initP (.seq loadP (.seq walkCall (.seq walkP1 (.seq walkP2 (.seq walkP3 cP)))))

/-- Cost pieces of the prelude (opaque for linear arithmetic). -/
@[irreducible] def ldCost (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) : ℕ :=
  loadCost (callN c).length (paramsN p).length (witN c p wt).length (srList c p).length Big
@[irreducible] def wcCost (L : ℕ) : ℕ := L + 25 * L + 400
@[irreducible] def w2Cost (PR : ℕ) : ℕ := PR * 5 + 200
@[irreducible] def w3Cost (L JR : ℕ) : ℕ := L * 30 + JR * (10 * L + 20 + 4) + 200

/-- The prelude's cost before the constants phase. -/
def preCost (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) : ℕ :=
  10 + ldCost c p wt Big + 1 + wcCost (cellN c p wt).length + 1 + 200 + 1 +
    w2Cost (p.primes.sort (· ≤ ·)).length + 1 + w3Cost (cellN c p wt).length (p.J * roleCount c.kind) + 1

theorem initP_spec (a : DS VV MM) (h0 : a.env vZ = 0) (h1 : a.env v1 = 0) (h2 : a.env v2 = 0)
    (hW : 2 < 2 ^ C.Wd) :
    Hs C initP a 5 (fun b => Cst b ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧
      b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [v1, v2]) := by
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_inc C v1 a (by rw [h1]; omega)) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_inc C v2 _ (by rw [DS.set_env_ne _ _ (by decide), h2]; omega))
    (fun e he => ?_)
  subst he
  refine Hs.mono (hs_inc C v2 _ (by vsimp [h2]; omega)) le_rfl ?_
  rintro b rfl
  refine ⟨⟨by vsimp [h0], by vsimp [h1], by vsimp [h2]⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  vsimp [hy.1, hy.2]

section Pr
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

include hadm hs hw in
/-- **The prelude.** -/
theorem prelude_spec (cP : St VV MM) (tc : Ctx → Call → Params → ℕ → ℕ) (hCg : ConstGoal cP tc) (Big : ℕ)
    (hBig : ∀ x ∈ cellN c p wt, natBitLength x ≤ Big) (hWd : wdNeed c p wt Big ≤ C.Wd)
    (hinp : C.inp = (cellN c p wt).flatMap natWord ++ cellWord c p wt) :
    Hs C (preludeP cP) (a0 : DS VV MM) (preCost c p wt Big + 1 + tc C c p Big) (fun b =>
      Iface c p wt b ∧ Sto c p wt b ∧ b.ip = ((cellN c p wt).flatMap natWord).length ∧ b.env vCnt = 0 ∧
      b.env vUnc = 0) := by
  have hwd : 256 * (p.J + 4) * (Big + c.n + 16) + 4 * recWidth c p wt ≤ C.Wd := hWd
  have hW1 : 3 * Big + 6 * c.n + 20 ≤ C.Wd := by nlinarith
  have hLlt := cellN_len_lt c p wt hadm hs w hw
  have hJn := (J_le_Jmax c p hs).trans (Jmax_le c p hadm hs)
  have hLW : (cellN c p wt).length + 4 * (c.n + 1) + 30 < 2 ^ C.Wd := by
    have h1 : 2 ^ (5 * c.n + 7) * 2 ^ 1 ≤ 2 ^ C.Wd := by rw [← pow_add]; exact pw_mono (by omega)
    have h2 : 4 * (c.n + 1) + 30 < 2 ^ (5 * c.n + 7) := by
      have h3 : c.n + 1 ≤ 2 ^ c.n := Nat.lt_two_pow_self
      have h4 : 2 ^ c.n * 2 ^ 7 ≤ 2 ^ (5 * c.n + 7) := by rw [← pow_add]; exact pw_mono (by omega)
      have h5 : 1 ≤ 2 ^ c.n := Nat.one_le_two_pow
      omega
    omega
  -- constants
  refine Hs.bseq (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega)) (by unfold preCost; omega)
    (fun e1 ⟨c1, i1, i2, i3, i4, i5, i6, i7, i8⟩ => ?_)
  -- loading
  have hram1 : e1.ram = Function.update e1.ram sN (e1.ram sN ++ []) := by
    funext m; by_cases hm : m = sN
    · subst hm; simp
    · simp [Function.update_of_ne hm]
  have hrc1 : e1.rc = Function.update e1.rc sN ((e1.ram sN).length + ([] : List ℕ).length) := by
    rw [i2, i1]; funext m; by_cases hm : m = sN
    · subst hm; simp [a0]
    · simp [Function.update_of_ne hm]
  have hls : LS (C := C) e1 e1 [] (cellN c p wt) (cellWord c p wt) :=
    ⟨⟨hram1, hrc1, by simp, rfl, rfl, rfl, rfl⟩, by rw [i3, hinp]; simp [a0], c1, by rw [i2, i1]; rfl⟩
  have hld := loadP_spec (C := C) e1 c p wt (cellWord c p wt) Big hls hBig (by omega) (by omega)
  rw [show loadCost (callN c).length (paramsN p).length (witN c p wt).length (srList c p).length Big =
    ldCost c p wt Big by unfold ldCost; rfl] at hld
  refine Hs.bseq hld (by unfold preCost; omega) (fun e2 ⟨l2, n2, k2, s2, j2, r2, jr2, f2⟩ => ?_)
  obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7⟩, -, c2, -⟩ := l2
  have e2ram : ∀ m, e2.ram m = if m = sN then cellN c p wt else [] := by
    intro m; rw [q1, i1]; by_cases hm : m = sN
    · subst hm; simp [a0]
    · simp [Function.update_of_ne hm, hm, a0]
  have e2N : e2.ram sN = cellN c p wt := by rw [e2ram]; simp
  have e2rc : ∀ m, e2.rc m ≤ (e2.ram m).length := by
    intro m; rw [q2, i2, i1]; by_cases hm : m = sN
    · subst hm; simp [a0, e2N]
    · simp [Function.update_of_ne hm, a0]
  have e2kc : e2.kc ≤ e2.kout.length := by rw [q7, q6, i7, i6]; simp [a0]
  have hpsiL : iPsi (cellN c p wt) + 27 + (p.primes.sort (· ≤ ·)).length + p.factors.length +
      (witN c p wt).length = (cellN c p wt).length := by
    have h1 := drop_eq_len (lay c p wt).params (by simp [paramsN])
    have h2 : (paramsN p).length = 27 + (p.primes.sort (· ≤ ·)).length + p.factors.length := by
      simp [paramsN, ratN_length]; omega
    simp only [List.length_append] at h1; omega
  -- the walks
  have hwc := Hs.rc_le (walkCall_spec (C := C) c p wt hadm e2 c2 e2N (by rw [s2]) (by omega)) e2rc e2kc
  refine Hs.bseq (Hs.mono hwc (show e2.rc sN + 25 * (cellN c p wt).length + 400 ≤
      wcCost (cellN c p wt).length by
      unfold wcCost; have := e2rc sN; rw [e2N] at this; omega) (fun _ h => h))
    (by unfold preCost; omega)
    (fun e3 ⟨⟨w3, ts0, ts1, tw0, tw1, gb1, gpl, gpar, ag3⟩, rc3, kc3⟩ => ?_)
  have hw1 := Hs.rc_le (walkP1_spec (C := C) c p wt e3 _ w3 (by omega)) rc3 kc3
  refine Hs.bseq hw1 (by unfold preCost; omega) (fun e4 ⟨⟨w4, uW, uK, uP, uNP, uIPr, ag4⟩, rc4, kc4⟩ => ?_)
  have hw2 := Hs.rc_le (walkP2_spec (C := C) (cellN c p wt) p _ e4 _ w4 uNP (by omega)) rc4 kc4
  rw [show (p.primes.sort (· ≤ ·)).length * 5 + 200 = w2Cost (p.primes.sort (· ≤ ·)).length by
    unfold w2Cost; rfl] at hw2
  refine Hs.bseq hw2 (by unfold preCost; omega) (fun e5 ⟨⟨w5, uHE, uM1, uFS, uNF, ag5⟩, rc5, kc5⟩ => ?_)
  have e5JR : e5.env gJR = p.J * roleCount c.kind := by
    rw [ag5.fr gJR (by decide), ag4.fr gJR (by decide), ag3.fr gJR (by decide), jr2]
  have hw3 := Hs.rc_le (walkP3_spec (C := C) c p wt e5 _ w5 uNF e5JR (by omega)) rc5 kc5
  rw [show (cellN c p wt).length * 30 + p.J * roleCount c.kind * (10 * (cellN c p wt).length + 20 + 4) + 200 =
    w3Cost (cellN c p wt).length (p.J * roleCount c.kind) by unfold w3Cost; rfl] at hw3
  refine Hs.bseq hw3 (by unfold preCost; omega)
    (fun e6 ⟨⟨uA, uLam, uWS, uNL, uCo, e6N, ag6⟩, rc6, kc6⟩ => ?_)
  have ag36 : Agr e2 e6 [sN] (walkCallT ++ wp1T ++ wp2T ++ wp3T) :=
    (ag3.weaken (by simp) (fun y hy => by simp [hy])).trans ((ag4.weaken (by simp) (fun y hy => by simp [hy])).trans
      ((ag5.weaken (by simp) (fun y hy => by simp [hy])).trans (ag6.weaken (by simp) (fun y hy => by simp [hy]))))
  have f6 : ∀ y, y ∉ walkCallT ++ wp1T ++ wp2T ++ wp3T → e6.env y = e2.env y := ag36.fr
  have c6 : Cst e6 := Cst.of_fr c2 ag36.fr (by decide)
  have e6ram : ∀ m, m ≠ sN → e6.ram m = [] := by
    intro m hm; rw [ag36.ram m (by simpa using hm), e2ram]; simp [hm]
  have hnp := (lay c p wt).np
  have hnf := (lay c p wt).nf
  have hIPr : (cellN c p wt).drop (e6.env vIPr) = p.primes.sort (· ≤ ·) ++
      (cellN c p wt).drop (e6.env vIPr + (p.primes.sort (· ≤ ·)).length) := by
    rw [ag6.fr vIPr (by decide), ag5.fr vIPr (by decide), uIPr]
    have := w4.dr
    rw [drop_split this]; exact this
  have hcp : ConstPre c p wt e6 := by
    refine ⟨c6, e6N, e6ram sP (by decide), e6ram sR (by decide), rc6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hIPr, ?_, ?_, ?_, ?_, ?_, ?_, uCo⟩
    · rw [f6 gN (by decide), n2]
    · rw [f6 gKd (by decide), k2]
    · rw [f6 gJ (by decide), j2]
    · rw [f6 gRC (by decide), r2]
    · rw [ag6.fr vHE (by decide), uHE]
    · rw [ag6.fr vM1 (by decide), uM1]
    · exact uA
    · exact uLam
    · rw [ag6.fr vNP (by decide), ag5.fr vNP (by decide), uNP]
    · rw [ag6.fr gFS (by decide), uFS, hnp]; omega
    · rw [uWS, Call.wit_fld]; unfold iOm; rw [hnp, hnf]; omega
    · rw [ag6.fr wW (by decide), ag5.fr wW (by decide), uW]
    · rw [ag6.fr wK (by decide), ag5.fr wK (by decide), uK]
    · rw [ag6.fr wP (by decide), ag5.fr wP (by decide), uP]
    · rw [ag6.fr wNF (by decide), uNF]
  obtain ⟨b, nb, hex, hnb, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19⟩ :=
    hCg C c p wt e6 Big hs ⟨w, hw⟩ ⟨B1, B2, hadm⟩ hcp hBig hWd
  refine Hs.mono ⟨b, nb, hex, le_rfl, rfl⟩ (by unfold preCost; omega) ?_
  rintro b' rfl
  have fb : ∀ y, ¬ cScratch y → b.env y = e6.env y := o19
  have nsc : ∀ y ∈ [vZ, v1, v2, gN, gKd, gJ, gRC, vHE, vM1, vA, vLam, vNP, vIPr, vTS0, vTS1, vTW0, vTW1, gB1, gWS,
      gFS, gPar, gPL, vNL, vCnt, vUnc], ¬ cScratch y := by unfold cScratch gScratch; decide
  have g6 : ∀ y, y ∈ [vZ, v1, v2, gN, gKd, gJ, gRC, vHE, vM1, vA, vLam, vNP, vIPr, vTS0, vTS1, vTW0, vTW1, gB1, gWS,
      gFS, gPar, gPL, vNL, vCnt, vUnc] → b.env y = e6.env y := fun y hy => fb y (nsc y hy)
  have hts0 : e6.env vTS0 = e3.env vTS0 := by
    rw [ag6.fr vTS0 (by decide), ag5.fr vTS0 (by decide), ag4.fr vTS0 (by decide)]
  have hts1 : e6.env vTS1 = e3.env vTS1 := by
    rw [ag6.fr vTS1 (by decide), ag5.fr vTS1 (by decide), ag4.fr vTS1 (by decide)]
  refine ⟨⟨⟨by rw [g6 vZ (by simp)]; exact c6.z, by rw [g6 v1 (by simp)]; exact c6.one,
      by rw [g6 v2 (by simp)]; exact c6.two⟩, by rw [g6 gN (by simp)]; exact hcp.n,
    by rw [g6 gKd (by simp)]; exact hcp.kind, by rw [g6 gJ (by simp)]; exact hcp.J,
    by rw [g6 gRC (by simp)]; exact hcp.rc, by rw [g6 vHE (by simp)]; exact hcp.hE,
    by rw [g6 vM1 (by simp)]; exact hcp.M1, by rw [g6 vA (by simp)]; exact hcp.A,
    by rw [g6 vLam (by simp)]; exact hcp.Lam, o8, by rw [g6 vNP (by simp)]; exact hcp.NP,
    by rw [g6 vIPr (by simp)]; exact hIPr, by rw [g6 vTS0 (by simp), hts0]; exact ts0,
    by rw [g6 vTS1 (by simp), hts1]; exact ts1,
    by rw [g6 vTW0 (by simp), ag6.fr vTW0 (by decide), ag5.fr vTW0 (by decide), ag4.fr vTW0 (by decide)]; exact tw0,
    by rw [g6 vTW1 (by simp), ag6.fr vTW1 (by decide), ag5.fr vTW1 (by decide), ag4.fr vTW1 (by decide)]; exact tw1,
    o3, o4, o5, o1, o2, o7, o6,
    by rw [g6 gB1 (by simp), ag6.fr gB1 (by decide), ag5.fr gB1 (by decide), ag4.fr gB1 (by decide)]; exact gb1,
    by rw [g6 gWS (by simp)]; exact hcp.WS, by rw [g6 gFS (by simp)]; exact hcp.FS,
    by rw [g6 gPar (by simp), ag6.fr gPar (by decide), ag5.fr gPar (by decide), ag4.fr gPar (by decide)]; exact gpar,
    by rw [g6 gPL (by simp), ag6.fr gPL (by decide), ag5.fr gPL (by decide), ag4.fr gPL (by decide)]; exact gpl,
    o9, by rw [g6 vNL (by simp)]; exact uNL⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [o12 sN (by decide) (by decide)]; exact e6N, o10, o11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, o13, ?_, ?_, ?_⟩
    · rw [o12 sCT (by decide) (by decide), e6ram sCT (by decide)]; simp
    · rw [o12 sZb (by decide) (by decide), e6ram sZb (by decide)]; simp
    · intro y; rw [o12 sE (by decide) (by decide), e6ram sE (by decide)]; simp
    · intro y; rw [o12 sX (by decide) (by decide), e6ram sX (by decide)]; simp
    · intro y; rw [o12 sG (by decide) (by decide), e6ram sG (by decide)]; simp
    · intro y; rw [o12 sB (by decide) (by decide), e6ram sB (by decide)]; simp
    · intro y; rw [o12 sA (by decide) (by decide), e6ram sA (by decide)]; simp
    · rw [o15, ag36.out, q4, i4]; rfl
    · rw [o16, ag36.kin, q5, i5]; rfl
    · rw [o18, o17]; exact kc6
  · rw [o14, ag36.ip, q3, i3]; simp [a0]
  · rw [g6 vCnt (by simp), f6 vCnt (by decide), f2 vCnt (by decide), i8 vCnt (by decide)]; rfl
  · rw [g6 vUnc (by simp), f6 vUnc (by decide), f2 vUnc (by decide), i8 vUnc (by decide)]; rfl

end Pr

end NearCubicGates.Close.Cells
