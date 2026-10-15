import Proof.Gates.CellsSys.Role3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

/-- The interface values the box program reads. -/
structure BoxIn (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (t : ℕ) (d : DS VV MM) : Prop where
  cst : Cst d
  rc : RcOK d
  tI : d.env tI = t
  J : d.env vJ' = p.J
  hE : d.env vHE = p.hE
  w : d.env wW = wWin p
  nD : d.env nDg = nDig c p
  M1 : d.env vM1 = p.M1
  A : d.env vA = p.A
  Lam : d.env vLam = p.Lambda
  T0 : d.env vTW0 = (circ c 0).topWeight
  T1 : d.env vTW1 = (circ c 1).topWeight
  RC : d.env vRC = roleCount c.kind
  P : d.ram sP = tailL p
  E : d.ram sE = ctrL c p wt y
  X : d.ram sX = kxL c p wt y

theorem boxR_spec {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big V Q : ℕ}
    (N : Nums C c p wt y Big V Q) (t : ℕ) (d : DS VV MM) (hB : BoxIn c p wt y t d) (r : ℕ)
    (hr : r < roleCount c.kind) (hrI : d.env rI = r) :
    Hs C boxR d (boxCost p.J) (fun g => g.env lP = (boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat ∧
      g.env lN = (-boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat ∧
      g.env nL = (boxHi c p wt y (kap c p wt y t) ⟨r, hr⟩ - boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩ + 1).toNat ∧
      Fr d g boxT ∧ Kp d g ∧ RcOK g) := by
  refine Hx.hs (Hs.then (boxR1_spec N d hB.cst hB.rc r t hr hrI hB.tI hB.J hB.hE hB.w hB.nD hB.M1 hB.P hB.E hB.X)
    (fun e ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ k1 hk1 => ?_))
  refine Hs.last (boxR2_spec N e a8 r t hr (by simp (disch := decide) only [a5.ev]; exact hrI) a1 a2 a3 a4
    (by simp (disch := decide) only [a5.ev]; exact hB.A) (by simp (disch := decide) only [a5.ev]; exact hB.Lam)
    (by simp (disch := decide) only [a5.ev]; exact hB.T0) (by simp (disch := decide) only [a5.ev]; exact hB.T1))
    (fun g ⟨b1, b2, b3, b4, b5⟩ k2 hk2 => ⟨⟨b1, b2, b3, Fr.trans (a5.weaken (by decide)) (b4.weaken (by decide)),
      Kp.trans a6 (Kp.of_same b5), RcOK.same a7 b5⟩, ?_⟩)
  have hrc2 := roleCount_le_two c
  have hc1 : accCost p.J (nDig c p) (tailL p).length (ctrL c p wt y).length ≤ accCost p.J (2 * p.J) p.J (4 * p.J) := by
    unfold accCost digCost; rw [tailL_length, ctrL_length]
    have h1 : nDig c p ≤ 2 * p.J := by unfold nDig; exact Nat.mul_le_mul_right _ hrc2
    have h2 : roleCount c.kind * (p.J * 2) ≤ 4 * p.J := by have := Nat.mul_le_mul_right (p.J * 2) hrc2; omega
    gcongr
  have hc2 : (kxL c p wt y).length ≤ 8 := by rw [kxL_length]; omega
  unfold boxCost
  omega

/-! ## Both roles -/

def boxes : St VV MM :=
  .seq (.op (.zero rI)) (.seq boxR (.seq (.op (.copy l0P lP)) (.seq (.op (.copy l0N lN)) (.seq (.op (.copy n0 nL))
    (.ite (.lt v1 vRC)
      (.seq (.op (.inc rI)) (.seq boxR (.seq (.op (.copy l1P lP)) (.seq (.op (.copy l1N lN)) (.op (.copy n1 nL))))))
      (.seq (.op (.zero l1P)) (.seq (.op (.zero l1N)) (.seq (.op (.zero n1)) (.op (.inc n1))))))))))

def boxesT : List (Fin VV) := rI :: boxT ++ [l0P, l0N, n0, l1P, l1N, n1]

def boxesCost (J : ℕ) : ℕ := 2 * boxCost J + 20

theorem loR_zero {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} (κ : Role c × Fin p.J → ℤ) :
    loR c p wt y κ 0 = boxLo c p wt y κ ⟨0, roleCount_pos c.kind⟩ := by
  unfold loR; rw [dif_pos (roleCount_pos c.kind)]

theorem lenR_zero {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} (κ : Role c × Fin p.J → ℤ) :
    lenR c p wt y κ 0 = (boxHi c p wt y κ ⟨0, roleCount_pos c.kind⟩ - boxLo c p wt y κ ⟨0, roleCount_pos c.kind⟩ + 1).toNat := by
  unfold lenR; rw [dif_pos (roleCount_pos c.kind)]

theorem boxes_spec {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big V Q : ℕ}
    (N : Nums C c p wt y Big V Q) (t : ℕ) (d : DS VV MM) (hB : BoxIn c p wt y t d) :
    Hs C boxes d (boxesCost p.J) (fun g => BoxV c p wt y (kap c p wt y t) g ∧ Fr d g boxesT ∧ Kp d g ∧ RcOK g) := by
  have hrc2 := roleCount_le_two c
  have hrc1 := roleCount_pos c.kind
  have hW1 : 1 < 2 ^ C.Wd := by have := N.q64; have := N.q8; omega
  obtain ⟨BC, hBC⟩ : ∃ BC, BC = boxCost p.J := ⟨_, rfl⟩
  have hR : ∀ (e : DS VV MM), BoxIn c p wt y t e → ∀ (r : ℕ) (hr : r < roleCount c.kind), e.env rI = r →
      Hs C boxR e BC (fun g => g.env lP = (boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat ∧
        g.env lN = (-boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩).toNat ∧
        g.env nL = (boxHi c p wt y (kap c p wt y t) ⟨r, hr⟩ - boxLo c p wt y (kap c p wt y t) ⟨r, hr⟩ + 1).toNat ∧
        Fr e g boxT ∧ Kp e g ∧ RcOK g) := fun e hb r hr hrI => by
    rw [hBC]; exact boxR_spec (C := C) N t e hb r hr hrI
  unfold boxesCost; rw [← hBC]
  refine Hx.hs (Hs.then (o_zero rI d) (fun e1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  have hB1 : BoxIn c p wt y t e1 := by
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩ := hB
    refine ⟨cst_of b1 p2 (by decide), RcOK.same b2 p3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by rw [p3.ram]; exact b14, by rw [p3.ram]; exact b15, by rw [p3.ram]; exact b16⟩ <;>
    simp (disch := decide) only [p2.ev] <;> assumption
  refine Hs.then (hR e1 hB1 0 hrc1 p1) (fun e2 ⟨q1, q2, q3, q4, q5, q6⟩ k2 hk2 => ?_)
  refine Hs.then (o_copy l0P lP e2 (by decide)) (fun e3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  refine Hs.then (o_copy l0N lN e3 (by decide)) (fun e4 ⟨s1, s2, s3⟩ k4 hk4 => ?_)
  refine Hs.then (o_copy n0 nL e4 (by decide)) (fun e5 ⟨u1, u2, u3⟩ k5 hk5 => ?_)
  have e5l0P : e5.env l0P = (loR c p wt y (kap c p wt y t) 0).toNat := by
    rw [loR_zero]; simp (disch := decide) only [u2.ev, s2.ev]; rw [r1]; exact q1
  have e5l0N : e5.env l0N = (-loR c p wt y (kap c p wt y t) 0).toNat := by
    rw [loR_zero]; simp (disch := decide) only [u2.ev]; rw [s1]; simp (disch := decide) only [r2.ev]; exact q2
  have e5n0 : e5.env n0 = lenR c p wt y (kap c p wt y t) 0 := by
    rw [lenR_zero, u1]; simp (disch := decide) only [s2.ev, r2.ev]; exact q3
  have FR5 : Fr d e5 boxesT := Fr.trans (p2.weaken (by decide)) (Fr.trans (q4.weaken (by decide)) (Fr.trans
    (r2.weaken (by decide)) (Fr.trans (s2.weaken (by decide)) (u2.weaken (by decide)))))
  have KP5 : Kp d e5 := Kp.trans (Kp.of_same p3) (Kp.trans q5 (Kp.of_same (Same.trans r3 (Same.trans s3 u3))))
  have RC5 : RcOK e5 := RcOK.same q6 (Same.trans r3 (Same.trans s3 u3))
  have e5c : Cst e5 := cst_of hB.cst FR5 (by decide)
  have e5RC : e5.env vRC = roleCount c.kind := by rw [FR5 vRC (by decide)]; exact hB.RC
  refine Hs.last (t := BC + 9 + 1) (Hs.ite (c := .lt v1 vRC) (show v1 ≠ vRC by decide) (fun he => ?_) (fun he => ?_))
    (fun g ⟨g1, g2, g3, g4⟩ k6 hk6 => ⟨⟨g1, Fr.trans FR5 g2, Kp.trans KP5 g3, g4⟩, by omega⟩)
    (R1 := fun g => BoxV c p wt y (kap c p wt y t) g ∧ Fr e5 g boxesT ∧ Kp e5 g ∧ RcOK g)
  · -- two roles
    have h2 : 1 < roleCount c.kind := by simpa [Cnd.eval, e5c.one, e5RC] using he
    have e5rI : e5.env rI = 0 := by simp (disch := decide) only [u2.ev, s2.ev, r2.ev]; rw [q4 rI (by decide)]; exact p1
    refine Hx.hs (Hs.then (o_inc rI e5 (by rw [e5rI]; omega)) (fun f1' ⟨v1', v2', v3'⟩ k7 hk7 => ?_))
    rw [e5rI] at v1'
    have hB5 : BoxIn c p wt y t f1' := by
      have FR : Fr d f1' boxesT := Fr.trans FR5 (v2'.weaken (by decide))
      have KP : Kp d f1' := Kp.trans KP5 (Kp.of_same v3')
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩ := hB
      refine ⟨cst_of b1 FR (by decide), RcOK.same RC5 v3', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        by rw [KP.ram]; exact b14, by rw [KP.ram]; exact b15, by rw [KP.ram]; exact b16⟩ <;>
      rw [FR _ (by decide)] <;> assumption
    refine Hs.then (hR f1' hB5 1 h2 v1') (fun f2' ⟨w1, w2, w3, w4, w5, w6⟩ k8 hk8 => ?_)
    refine Hs.then (o_copy l1P lP f2' (by decide)) (fun f3' ⟨x1, x2, x3⟩ k9 hk9 => ?_)
    refine Hs.then (o_copy l1N lN f3' (by decide)) (fun f4' ⟨y1, y2, y3⟩ k10 hk10 => ?_)
    refine Hs.last (o_copy n1 nL f4' (by decide)) (fun g ⟨z1, z2, z3⟩ k11 hk11 => ⟨⟨?_, ?_, Kp.trans (Kp.of_same v3')
      (Kp.trans w5 (Kp.of_same (Same.trans x3 (Same.trans y3 z3)))), RcOK.same w6 (Same.trans x3 (Same.trans y3 z3))⟩,
      by omega⟩)
    · have hl1 : loR c p wt y (kap c p wt y t) 1 = boxLo c p wt y (kap c p wt y t) ⟨1, h2⟩ := by
        unfold loR; rw [dif_pos h2]
      have hn1 : lenR c p wt y (kap c p wt y t) 1 =
          (boxHi c p wt y (kap c p wt y t) ⟨1, h2⟩ - boxLo c p wt y (kap c p wt y t) ⟨1, h2⟩ + 1).toNat := by
        unfold lenR; rw [dif_pos h2]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp (disch := decide) only [z2.ev, y2.ev, x2.ev, w4.ev, v2'.ev]; exact e5l0P
      · simp (disch := decide) only [z2.ev, y2.ev, x2.ev, w4.ev, v2'.ev]; exact e5l0N
      · simp (disch := decide) only [z2.ev, y2.ev, x2.ev, w4.ev, v2'.ev]; exact e5n0
      · simp (disch := decide) only [z2.ev, y2.ev]; rw [x1, hl1]; exact w1
      · simp (disch := decide) only [z2.ev]; rw [y1, hl1]; simp (disch := decide) only [x2.ev]; exact w2
      · rw [z1, hn1]; simp (disch := decide) only [y2.ev, x2.ev]; exact w3
    · exact Fr.trans (v2'.weaken (by decide)) (Fr.trans (w4.weaken (by decide)) (Fr.trans (x2.weaken (by decide))
        (Fr.trans (y2.weaken (by decide)) (z2.weaken (by decide)))))
  · -- one role
    have h1 : ¬ 1 < roleCount c.kind := by simpa [Cnd.eval, e5c.one, e5RC] using he
    refine Hx.hs (Hs.then (o_zero l1P e5) (fun f1' ⟨v1', v2', v3'⟩ k7 hk7 => ?_))
    refine Hs.then (o_zero l1N f1') (fun f2' ⟨w1, w2, w3⟩ k8 hk8 => ?_)
    refine Hs.then (o_zero n1 f2') (fun f3' ⟨x1, x2, x3⟩ k9 hk9 => ?_)
    refine Hs.last (o_inc n1 f3' (by rw [x1]; omega)) (fun g ⟨y1, y2, y3⟩ k10 hk10 => ⟨⟨?_, ?_,
      Kp.of_same (Same.trans v3' (Same.trans w3 (Same.trans x3 y3))),
      RcOK.same RC5 (Same.trans v3' (Same.trans w3 (Same.trans x3 y3)))⟩, by omega⟩)
    · have hl1 : loR c p wt y (kap c p wt y t) 1 = 0 := by unfold loR; rw [dif_neg h1]
      have hn1 : lenR c p wt y (kap c p wt y t) 1 = 1 := by unfold lenR; rw [dif_neg h1]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp (disch := decide) only [y2.ev, x2.ev, w2.ev, v2'.ev]; exact e5l0P
      · simp (disch := decide) only [y2.ev, x2.ev, w2.ev, v2'.ev]; exact e5l0N
      · simp (disch := decide) only [y2.ev, x2.ev, w2.ev, v2'.ev]; exact e5n0
      · rw [hl1]; simp (disch := decide) only [y2.ev, x2.ev, w2.ev]; exact v1'
      · rw [hl1]; simp (disch := decide) only [y2.ev, x2.ev]; exact w1
      · rw [hn1, y1, x1]
    · exact Fr.trans (v2'.weaken (by decide)) (Fr.trans (w2.weaken (by decide)) (Fr.trans (x2.weaken (by decide))
        (y2.weaken (by decide))))

end NearCubicGates.Close.Cells.SystemsPhase
