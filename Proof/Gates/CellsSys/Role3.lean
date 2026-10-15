import Proof.Gates.CellsSys.Role2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

theorem kx_getD_le {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big V Q : ℕ}
    (N : Nums C c p wt y Big V Q) (i : ℕ) : (kxL c p wt y).getD i 0 ≤ V := by
  rcases Nat.lt_or_ge i (kxL c p wt y).length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact N.XV _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ h]; omega

/-- The centre pairs are below `Q`. -/
theorem cp_le {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big V Q : ℕ}
    (N : Nums C c p wt y Big V Q) (r t : ℕ) : cpV c p wt y r t ≤ Q ∧ cnV c p wt y r ≤ Q := by
  have h1 := accPf_le (tailL p) (ctrL c p wt y) r p.J (nDig c p) (wWin p) t p.J V N.PV N.EV N.wV N.w1
  have h2 := accNf_le (tailL p) (ctrL c p wt y) r p.J p.hE p.J V N.PV N.EV N.hE
  have hk1 := kx_getD_le N (4 * r + 1)
  have hk0 := kx_getD_le N (4 * r)
  constructor
  · unfold cpV
    calc _ ≤ 2 ^ Big * (p.J * (V * (2 * V + 2)) + V) := Nat.mul_le_mul N.M1b (by omega)
      _ ≤ Q := N.cQ
  · unfold cnV
    calc _ ≤ 2 ^ Big * (p.J * (V * (2 * V + 2)) + V) := Nat.mul_le_mul N.M1b (by omega)
      _ ≤ Q := N.cQ

def boxT1 : List (Fin VV) :=
  [jI, iI, q3, pw, f1, c1, f2, dV, ix, f3, q1, q2, accP, accN, c0, vJ, kP, kN, xP, xN, Cp, Cn]

/-- First half: digit sums, `K` and `X`, the centre. -/
theorem boxR1_spec {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big V Q : ℕ}
    (N : Nums C c p wt y Big V Q) (d : DS VV MM) (hc : Cst d) (hrc : RcOK d) (r t : ℕ) (hr : r < roleCount c.kind)
    (hrI : d.env rI = r) (htI : d.env tI = t) (hJ : d.env vJ' = p.J) (hHE : d.env vHE = p.hE)
    (hw : d.env wW = wWin p) (hnD : d.env nDg = nDig c p) (hM : d.env vM1 = p.M1) (hP : d.ram sP = tailL p)
    (hE : d.ram sE = ctrL c p wt y) (hX : d.ram sX = kxL c p wt y) :
    Hs C boxR1 d (accCost p.J (nDig c p) (tailL p).length (ctrL c p wt y).length +
        (24 * (kxL c p wt y).length + 60 + 11 + 1) + 1)
      (fun g => g.env Cp = cpV c p wt y r t ∧ g.env Cn = cnV c p wt y r ∧
        g.env xP = (kxL c p wt y).getD (4 * r + 2) 0 ∧ g.env xN = (kxL c p wt y).getD (4 * r + 3) 0 ∧
        Fr d g boxT1 ∧ Kp d g ∧ RcOK g ∧ Cst g) := by
  have hrc2 := roleCount_le_two c
  have hEL := ctrL_length c p wt y
  have hXL := kxL_length c p wt y
  have hPL := tailL_length p
  have hEL2 : roleCount c.kind * (p.J * 2) ≤ 4 * p.J := by
    have := Nat.mul_le_mul_right (p.J * 2) hrc2; omega
  have hr1 : r ≤ 1 := by omega
  have hrJ : r * p.J ≤ p.J := by have := Nat.mul_le_mul_right p.J hr1; omega
  have hnD2 : nDig c p ≤ 2 * p.J := by unfold nDig; exact (Nat.mul_le_mul_right _ hrc2)
  have hbig : (p.J + 1) * (V * (2 * V + 2)) + (ctrL c p wt y).length + nDig c p + r * p.J + p.J < 2 ^ C.Wd := by
    have := N.big; rw [hEL]; omega
  have hDig : DigI (tailL p) (ctrL c p wt y) r t p.J p.hE (wWin p) (nDig c p) d :=
    ⟨hrI, htI, hJ, hHE, hw, hnD, hP, hE, hrc, hc⟩
  have hrJn : (r + 1) * p.J ≤ nDig c p := by unfold nDig; exact Nat.mul_le_mul_right _ hr
  have hEL3 : 2 * ((r + 1) * p.J) ≤ (ctrL c p wt y).length := by
    rw [hEL]
    have := Nat.mul_le_mul_right (p.J * 2) (show r + 1 ≤ roleCount c.kind by omega)
    rw [show 2 * ((r + 1) * p.J) = (r + 1) * (p.J * 2) by ring]; exact this
  refine Hx.hs (Hs.then (accL_spec (C := C) (tailL p) (ctrL c p wt y) r t p.J p.hE (wWin p) (nDig c p) V d hDig hrJn
    (by rw [hPL]) hEL3 N.w1 N.pw N.PV N.EV N.hE N.wV hbig) (fun e1 ⟨a1, a2, a3, a4, a5⟩ k1 hk1 => ?_))
  have hX2 : 2 * (kxL c p wt y).length < 2 ^ C.Wd := by have := N.q64; have := N.q8; rw [hXL]; omega
  refine Hs.then (kxB_spec (C := C) e1 a3.cst a3.rc r (kxL c p wt y) a3.r (by rw [a5.ram]; exact hX)
    (by rw [hXL]; omega) hX2) (fun e2 ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ k2 hk2 => ?_)
  have hcq := cp_le N r t
  have h64 := N.q64
  have hq8 := N.q8
  refine Hs.last (ctrB_spec (C := C) e2 _ _ _ _ p.M1 (by simp (disch := decide) only [b5.ev]; exact a1)
    (by simp (disch := decide) only [b5.ev]; exact a2) b1 b2
    (by simp (disch := decide) only [b5.ev, a4.ev]; exact hM) N.M1a
    (by have := hcq.1; unfold cpV at this; omega) (by have := hcq.2; unfold cnV at this; omega))
    (fun g ⟨c1', c2', c3', c4'⟩ k3 hk3 => ⟨⟨c1', c2', by simp (disch := decide) only [c3'.ev]; exact b3,
      by simp (disch := decide) only [c3'.ev]; exact b4,
      Fr.trans (a4.weaken (by decide)) (Fr.trans (b5.weaken (by decide)) (c3'.weaken (by decide))),
      Kp.trans a5 (Kp.trans b6 (Kp.of_same c4')), RcOK.same b7 c4', cst_of b8 c3' (by decide)⟩, by omega⟩)

def boxT2 : List (Fin VV) := [Wv, f2, f3, q1, q2, q3, q4, lP, lN, vJ, hP, hN, nL]

theorem box_lo_le {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big V Q : ℕ}
    (N : Nums C c p wt y Big V Q) (r t : ℕ) (hr : r < roleCount c.kind) :
    (boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat + (-boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat ≤ 6 * Q := by
  have hcq := cp_le N r t
  have hxp := kx_getD_le N (4 * r + 2)
  have hxn := kx_getD_le N (4 * r + 3)
  have hW := N.TW r
  have hVQ := N.VQ
  have hAQ : p.A ≤ Q := N.Ab.trans N.BQ
  have hLQ : p.Lambda ≤ Q := N.Lb.trans N.BQ
  have hfl := fdivP_le (cpV c p wt y r t + p.A) (cnV c p wt y r + p.Lambda) p.A N.Aa
  rw [← lo_eq c p wt y r hr t N.Aa]
  unfold loP zOf
  split_ifs <;> simp only <;> omega

/-- Second half: the ends and the side length. -/
theorem boxR2_spec {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big V Q : ℕ}
    (N : Nums C c p wt y Big V Q) (a : DS VV MM) (hc : Cst a) (r t : ℕ) (hr : r < roleCount c.kind)
    (hrI : a.env rI = r) (hCp : a.env Cp = cpV c p wt y r t) (hCn : a.env Cn = cnV c p wt y r)
    (hxp : a.env xP = (kxL c p wt y).getD (4 * r + 2) 0) (hxn : a.env xN = (kxL c p wt y).getD (4 * r + 3) 0)
    (hA : a.env vA = p.A) (hL : a.env vLam = p.Lambda) (hT0 : a.env vTW0 = (circ c 0).topWeight)
    (hT1 : a.env vTW1 = (circ c 1).topWeight) :
    Hs C boxR2 a (2 + (60 + (4 + (60 + 16 + 1) + 1) + 1) + 1)
      (fun g => g.env lP = (boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat ∧
        g.env lN = (-boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat ∧
        g.env nL = (boxHi c p wt y (kap c p wt y t) ⟨r, hr⟩ - boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩ + 1).toNat ∧
        Fr a g boxT2 ∧ Same a g) := by
  have hxpV := kx_getD_le N (4 * r + 2)
  have hxnV := kx_getD_le N (4 * r + 3)
  have hcq := cp_le N r t
  have hW := N.TW r
  have hVQ := N.VQ
  have hAQ : p.A ≤ Q := N.Ab.trans N.BQ
  have hLQ : p.Lambda ≤ Q := N.Lb.trans N.BQ
  have h64 := N.q64
  have hq8 := N.q8
  have hU : cpV c p wt y r t + cnV c p wt y r + (kxL c p wt y).getD (4 * r + 2) 0 +
      (kxL c p wt y).getD (4 * r + 3) 0 + p.A + p.Lambda + (circ c r).topWeight ≤ 7 * Q := by omega
  have hU8 : 8 * (7 * Q) + 8 < 2 ^ C.Wd := by omega
  refine Hx.hs (Hs.then (setW_spec (C := C) a hc r _ _ hrI hT0 hT1) (fun e4 ⟨d1, d2, d3⟩ k1 hk1 => ?_))
  have hWr : (if r = 0 then (circ c 0).topWeight else (circ c 1).topWeight) = (circ c r).topWeight := by
    split_ifs with h
    · rw [h]
    · unfold circ; rw [if_neg h, if_neg (by norm_num)]
  rw [hWr] at d1
  have e4c : Cst e4 := cst_of hc d2 (by decide)
  refine Hs.then (loB_spec (C := C) e4 e4c _ _ _ _ _ _ _ (7 * Q) (by simp (disch := decide) only [d2.ev]; exact hCp)
    (by simp (disch := decide) only [d2.ev]; exact hCn) (by simp (disch := decide) only [d2.ev]; exact hxp)
    (by simp (disch := decide) only [d2.ev]; exact hxn) (by simp (disch := decide) only [d2.ev]; exact hA)
    (by simp (disch := decide) only [d2.ev]; exact hL) d1 N.Aa hU hU8) (fun e5 ⟨f1', f2', f3', f4'⟩ k2 hk2 => ?_)
  refine Hs.then (normB_spec (C := C) e5 _ _ f1' f2') (fun e6 ⟨g1, g2, g3, g4⟩ k3 hk3 => ?_)
  rw [lo_eq c p wt y r hr t N.Aa] at g1 g2
  have e6c : Cst e6 := cst_of (cst_of e4c f3' (by decide)) g3 (by decide)
  refine Hs.then (hiB_spec (C := C) e6 e6c _ _ _ _ _ _ _ (7 * Q)
    (by simp (disch := decide) only [g3.ev, f3'.ev, d2.ev]; exact hCp)
    (by simp (disch := decide) only [g3.ev, f3'.ev, d2.ev]; exact hCn)
    (by simp (disch := decide) only [g3.ev, f3'.ev, d2.ev]; exact hxp)
    (by simp (disch := decide) only [g3.ev, f3'.ev, d2.ev]; exact hxn)
    (by simp (disch := decide) only [g3.ev, f3'.ev, d2.ev]; exact hA)
    (by simp (disch := decide) only [g3.ev, f3'.ev, d2.ev]; exact hL)
    (by simp (disch := decide) only [g3.ev, f3'.ev]; exact d1) N.Aa hU hU8)
    (fun e7 ⟨h1', h2', h3', h4'⟩ k4 hk4 => ?_)
  have hlP : e7.env lP = (boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat := by
    simp (disch := decide) only [h3'.ev]; exact g1
  have hlN : e7.env lN = (-boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat := by
    simp (disch := decide) only [h3'.ev]; exact g2
  have hfh := fdivP_le (cpV c p wt y r t + p.Lambda) (cnV c p wt y r + 1) p.A N.Aa
  have hloB := box_lo_le N r t hr
  have hhiB : (hiP (cpV c p wt y r t) (cnV c p wt y r) ((kxL c p wt y).getD (4 * r + 2) 0)
      ((kxL c p wt y).getD (4 * r + 3) 0) p.A p.Lambda (circ c r).topWeight).1 +
      (hiP (cpV c p wt y r t) (cnV c p wt y r) ((kxL c p wt y).getD (4 * r + 2) 0)
      ((kxL c p wt y).getD (4 * r + 3) 0) p.A p.Lambda (circ c r).topWeight).2 ≤ 6 * Q := by
    unfold hiP
    split_ifs <;> simp only <;> omega
  refine Hs.last (lenB_spec (C := C) e7 _ _ _ _ hlP hlN h1' h2' (by omega)) (fun g ⟨l1, l2, l3⟩ k5 hk5 => ?_)
  have hhi := hi_eq c p wt y r hr t N.Aa
  have hlen : lenP ((boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat, (-boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat)
      (hiP (cpV c p wt y r t) (cnV c p wt y r) ((kxL c p wt y).getD (4 * r + 2) 0)
        ((kxL c p wt y).getD (4 * r + 3) 0) p.A p.Lambda (circ c r).topWeight) =
      (boxHi c p wt y (kap c p wt y t) ⟨r, hr⟩ - boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩ + 1).toNat := by
    rw [lenP_eq, hhi]
    unfold zOf; simp only; congr 1; omega
  refine ⟨⟨by simp (disch := decide) only [l2.ev]; exact hlP, by simp (disch := decide) only [l2.ev]; exact hlN,
    by rw [l1, hlen], ?_, Same.trans d3 (Same.trans f4' (Same.trans g4 (Same.trans h4' l3)))⟩, by omega⟩
  exact Fr.trans (d2.weaken (by decide)) (Fr.trans (f3'.weaken (by decide)) (Fr.trans (g3.weaken (by decide))
    (Fr.trans (h3'.weaken (by decide)) (l2.weaken (by decide)))))

end NearCubicGates.Close.Cells.SystemsPhase
