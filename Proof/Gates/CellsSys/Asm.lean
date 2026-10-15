import Proof.Gates.CellsSys.Loops2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def setupP : St VV MM :=
  .seq (.op (.rwM sA)) (.seq (.op (.copy wW vHE)) (.seq (.op (.shl wW)) (.seq (.op (.sub wW v1))
    (.seq (.op (.mul vRC vJ' nDg)) (.ite (.eq vKd v2) (.op (.copy nPa v2)) (.op (.copy nPa v1)))))))

def sysPOf (pr : PrFrag) (cf : CallFrag) : St VV MM := .seq setupP (pLoop pr cf)

theorem Rw_length (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) (t : ℕ) :
    (Rw c p wt y part t).length = ((p.primes.sort (· ≤ ·)).map fun q => q ^ roleCount c.kind).sum := by
  simp [Rw, rowsOf, List.length_flatMap, vecs_eq_vecsM, vecsM_length]

theorem rows_n3 {cT : ℕ} (c : Call) (p : Params) (hs : Spec cT (header c) p) :
    ((p.primes.sort (· ≤ ·)).map fun q => q ^ roleCount c.kind).sum ≤ c.n ^ 3 := by
  rw [← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  exact (rows_le c p hs).trans (Nat.pow_le_pow_left (P_le_n c p hs) 3)

theorem rowVals_len {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (hs : Spec cT (header c) p) :
    (rowVals c p wt y).length ≤ 2 * (BN c p * c.n ^ 3) := by
  rw [rowVals_eq, length_flatMap_const _ _ (BN c p * ((p.primes.sort (· ≤ ·)).map fun q => q ^ roleCount c.kind).sum)
    (fun part _ => by rw [length_flatMap_const _ _ _ (fun t _ => Rw_length c p wt y part t), List.length_range])]
  have h1 := parts_length_le c
  have h2 := rows_n3 c p hs
  have h3 : BN c p * ((p.primes.sort (· ≤ ·)).map fun q => q ^ roleCount c.kind).sum ≤ BN c p * c.n ^ 3 :=
    Nat.mul_le_mul_left _ h2
  calc _ ≤ 2 * (BN c p * ((p.primes.sort (· ≤ ·)).map fun q => q ^ roleCount c.kind).sum) := Nat.mul_le_mul_right _ h1
    _ ≤ _ := Nat.mul_le_mul_left _ h3

theorem setup_spec {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big : ℕ}
    {a : DS VV MM} (G : Glob S C c p wt y Big) (h0 : SysPre S C c p wt y a) :
    Hs C setupP a (2 * (BN c p * c.n ^ 3) + 12) (fun b => Keep a b ∧ b.kin = [] ∧ b.env wW = wWin p ∧
      b.env nDg = nDig c p ∧ b.env nPa = (parts c).length ∧ (b.ram sA).drop (b.rc sA) = rowVals c p wt y ∧
      ∀ x : Fin VV, x ≠ wW → x ≠ nDg → x ≠ nPa → b.env x = a.env x) := by
  obtain ⟨cT, hs⟩ := G.spec
  have N := nums G
  have hE1 := hE_ge c p wt y G
  have hEl := hE_lt G.bits
  have hJn := J_le_n c p wt y G
  have hrc2 := roleCount_le_two c
  have hBQ := N.BQ
  have h64 := N.q64
  have hc := h0.cst
  have hrcA : a.rc sA ≤ 2 * (BN c p * c.n ^ 3) := by
    have := h0.rcur sA; rw [h0.rows] at this; exact this.trans (rowVals_len c p wt y hs)
  refine Hx.hs (Hs.then (hs_rwM C sA a) (fun e1 he1 k1 hk1 => ?_))
  subst he1
  refine Hs.then (o_copy wW vHE (a.rew sA) (by decide)) (fun e2 ⟨p1, p2, p3⟩ k2 hk2 => ?_)
  have e2h : e2.env wW = p.hE := by rw [p1]; exact h0.hE
  refine Hs.then (o_shl wW e2 (by rw [e2h]; omega)) (fun e3 ⟨q1, q2, q3⟩ k3 hk3 => ?_)
  rw [e2h] at q1
  have c3 : Cst e3 := cst_of (cst_of hc p2 (by decide)) q2 (by decide)
  refine Hs.then (o_sub wW v1 e3 (by decide) (by rw [q1, c3.one]; omega)) (fun e4 ⟨r1, r2, r3⟩ k4 hk4 => ?_)
  rw [q1, c3.one] at r1
  have e4rc : e4.env vRC = roleCount c.kind := by simp (disch := decide) only [r2.ev, q2.ev, p2.ev]; exact h0.rc
  have e4J : e4.env vJ' = p.J := by simp (disch := decide) only [r2.ev, q2.ev, p2.ev]; exact h0.J
  refine Hs.then (o_mul vRC vJ' nDg e4 (by decide) (by decide) (by decide) (by
      rw [e4rc, e4J]
      have : roleCount c.kind * p.J ≤ 2 * (c.n + 1) := by nlinarith
      have h5 : 2 * (c.n + 1) < 2 ^ C.Wd := by
        have := G.wd
        exact lt_of_lt_of_le (show 2 * (c.n + 1) < 2 ^ (2 * (c.n + 1)) from Nat.lt_two_pow_self)
          (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
      omega)) (fun e5 ⟨s1, s2, s3⟩ k5 hk5 => ?_)
  rw [e4rc, e4J] at s1
  have c5 : Cst e5 := cst_of (cst_of c3 r2 (by decide)) s2 (by decide)
  have e5k : e5.env vKd = kindTag c.kind := by
    simp (disch := decide) only [s2.ev, r2.ev, q2.ev, p2.ev]; exact h0.kind
  refine Hs.last (Hs.ite (c := .eq vKd v2) (show vKd ≠ v2 by decide)
    (R := fun g => g.env nPa = (parts c).length ∧ Fr e5 g [nPa] ∧ Same e5 g) (t := 1) (fun he => ?_) (fun he => ?_))
    (fun g ⟨g1, g2, g3⟩ k6 hk6 => ?_)
  · have hk : c.kind = .parity := by
      have : kindTag c.kind = 2 := by simpa [Cnd.eval, e5k, c5.two] using he
      cases h : c.kind <;> simp_all [kindTag]
    refine Hs.mono (o_copy nPa v2 e5 (by decide)) le_rfl (fun g ⟨g1, g2, g3⟩ => ⟨?_, g2, g3⟩)
    rw [g1, c5.two]; simp [parts, hk]
  · have hk : c.kind ≠ .parity := by
      have : kindTag c.kind ≠ 2 := by simpa [Cnd.eval, e5k, c5.two] using he
      intro h; rw [h] at this; exact this rfl
    refine Hs.mono (o_copy nPa v1 e5 (by decide)) le_rfl (fun g ⟨g1, g2, g3⟩ => ⟨?_, g2, g3⟩)
    rw [g1, c5.one]; simp [parts, hk]
  · have SM : Same (a.rew sA) g := Same.trans p3 (Same.trans q3 (Same.trans r3 (Same.trans s3 g3)))
    have FR : Fr (a.rew sA) g [wW, nDg, nPa] := Fr.trans (p2.weaken (by decide)) (Fr.trans (q2.weaken (by decide))
      (Fr.trans (r2.weaken (by decide)) (Fr.trans (s2.weaken (by decide)) (g2.weaken (by decide)))))
    have hfr : ∀ x : Fin VV, x ≠ wW → x ≠ nDg → x ≠ nPa → g.env x = a.env x := fun x h1 h2 h3 => by
      rw [FR x (by simp [h1, h2, h3])]; rfl
    refine ⟨⟨⟨by rw [SM.ram]; rfl, by rw [SM.ip]; rfl, by rw [SM.out]; rfl, ?_, fun x hx _ => hfr x
        (fun e => by subst e; revert hx; decide) (fun e => by subst e; revert hx; decide)
        (fun e => by subst e; revert hx; decide)⟩,
      by rw [SM.kin]; exact h0.kin, by simp (disch := decide) only [g2.ev, s2.ev]; rw [r1],
      by simp (disch := decide) only [g2.ev]; exact s1, g1, ?_, hfr⟩, by omega⟩
    · intro m; rw [SM.rc, SM.ram]
      by_cases hm : m = sA
      · subst hm; simp [DS.rew]
      · simp only [DS.rew]; rw [Function.update_of_ne hm]; exact h0.rcur m
    · rw [SM.rc, SM.ram]; simp [DS.rew, h0.rows]

end NearCubicGates.Close.Cells.SystemsPhase
