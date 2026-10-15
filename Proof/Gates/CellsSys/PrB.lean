import Proof.Gates.CellsSys.PrA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

theorem drop_range_cons' (N k : ℕ) (hk : k < N) : (List.range N).drop k = k :: (List.range N).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk), List.getElem_range]

/-- The word of the point `(a, b)` (numeric form). -/
def ptWn (d X0 Y0 X1 Y1 a b : ℕ) : List Bool :=
  natWord d ++ Interfaces.intWord (zOf (X0 + a) Y0) ++ (if 1 < d then Interfaces.intWord (zOf (X1 + b) Y1) else [])

def ptB : St VV MM :=
  .seq (.op (.copy t3 vRC)) (.seq emitNatK (.seq (.op (.copy mV l0P)) (.seq (.op (.add mV a0I)) (.seq (prIntP mV l0N)
    (.ite (.lt v1 vRC) (.seq (.op (.copy mV l1P)) (.seq (.op (.add mV a1I)) (prIntP mV l1N))) skipS)))))

def ptT : List (Fin VV) := [t3, t5, t6, t7, t8, t9, mV, vJ]

theorem ptT_frag : ∀ x ∈ ptT, FragVar x := by decide

/-- The numeric data of the box as the printer sees it. -/
structure BoxN (e : DS VV MM) (d X0 Y0 X1 Y1 N0 N1 Bw : ℕ) (C : Ctx) : Prop where
  hd : e.env vRC = d
  hx0 : e.env l0P = X0
  hy0 : e.env l0N = Y0
  hx1 : e.env l1P = X1
  hy1 : e.env l1N = Y1
  hn0 : e.env n0 = N0
  hn1 : e.env n1 = N1
  d12 : 1 ≤ d ∧ d ≤ 2
  bd : natBitLength d ≤ Bw
  b0 : ∀ a < N0, natBitLength (zOf (X0 + a) Y0).natAbs ≤ Bw
  b1 : 1 < d → ∀ b < N1, natBitLength (zOf (X1 + b) Y1).natAbs ≤ Bw
  B1 : 1 ≤ Bw
  BW : Bw + 2 < 2 ^ C.Wd
  W2 : 2 ≤ C.Wd
  wn0 : N0 < 2 ^ C.Wd
  wn1 : N1 < 2 ^ C.Wd
  w0 : 0 < N0 → X0 + N0 < 2 ^ C.Wd
  w1 : 0 < N1 → X1 + N1 < 2 ^ C.Wd

def ptCost (Bw : ℕ) : ℕ := 3 * (2 * (40 * Bw + 40) + 8) + 20

theorem ptB_spec {e st : DS VV MM} {W R : List Bool} {Ra : List ℕ} {d X0 Y0 X1 Y1 N0 N1 Bw : ℕ}
    (hB : BoxN e d X0 Y0 X1 Y1 N0 N1 Bw C) (hL : W.length ≤ C.Lk) (a k : ℕ) (ha : a < N0) (hk : k < N1)
    (h : PS e W (ptWn d X0 Y0 X1 Y1 a k ++ R) Ra st) (h0 : st.env a0I = a) (h1 : st.env a1I = k) :
    Hs C ptB st (ptCost Bw) (fun st' => PS e W R Ra st' ∧ Fr st st' ptT) := by
  have ev : ∀ {s : DS VV MM} {Rk : List Bool}, PS e W Rk Ra s → ∀ x : Fin VV, ¬ FragVar x → s.env x = e.env x :=
    fun hs x hx => hs.fr x hx
  have Bw1 := hB.B1
  unfold ptWn at h
  simp only [List.append_assoc] at h
  refine Hx.hs (Hs.then (o_copy t3 vRC st (by decide)) (fun s1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  rw [ev h vRC (by decide), hB.hd] at p1
  refine Hs.then (ps_emit d Bw (h.step p3 p2 (by decide)) p1 hB.bd hB.BW hB.W2 hL) (fun s2 ⟨q1, q2⟩ k2 hk2 => ?_)
  refine Hs.then (o_copy mV l0P s2 (by decide)) (fun s3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  rw [ev q1 l0P (by decide), hB.hx0] at r1
  have s3a : s3.env a0I = a := by
    rw [r2 a0I (by decide), q2 a0I (by decide), p2 a0I (by decide)]; exact h0
  refine Hs.then (o_add mV a0I s3 (by decide) (by rw [r1, s3a]; have := hB.w0 (by omega); omega))
    (fun s4 ⟨u1, u2, u3⟩ k4 hk4 => ?_)
  rw [r1, s3a] at u1
  have P4 := (q1.step r3 r2 (by decide)).step u3 u2 (by decide)
  refine Hs.then (ps_prInt mV l0N (by decide) (by decide) (by decide) (X0 + a) Y0 Bw P4 u1
    (by rw [ev P4 l0N (by decide), hB.hy0]) (hB.b0 a ha) Bw1 hB.BW hB.W2 hL) (fun s5 ⟨v1', v2'⟩ k5 hk5 => ?_)
  have F5 : Fr st s5 ptT := Fr.trans (p2.weaken (by decide)) (Fr.trans (q2.weaken (by decide)) (Fr.trans
    (r2.weaken (by decide)) (Fr.trans (u2.weaken (by decide)) (v2'.weaken (by decide)))))
  have c5 := v1'.cst
  have s5d : s5.env vRC = d := by rw [ev v1' vRC (by decide), hB.hd]
  refine Hs.last (t := 2 * (40 * Bw + 40) + 8 + 4 + 1) (Hs.ite (c := .lt v1 vRC) (show v1 ≠ vRC by decide)
    (R := fun st' => PS e W R Ra st' ∧ Fr s5 st' ptT) (fun he => ?_) (fun he => ?_))
    (fun st' ⟨g1, g2⟩ k6 hk6 => ⟨⟨g1, Fr.trans F5 g2⟩, by unfold ptCost; omega⟩)
  · have hd : 1 < d := by simpa [Cnd.eval, c5.one, s5d] using he
    rw [if_pos hd] at v1'
    refine Hx.hs (Hs.then (o_copy mV l1P s5 (by decide)) (fun s6 ⟨w1, w2, w3⟩ k7 hk7 => ?_))
    rw [ev v1' l1P (by decide), hB.hx1] at w1
    have s6k : s6.env a1I = k := by
      rw [w2 a1I (by decide), F5 a1I (by decide)]; exact h1
    refine Hs.then (o_add mV a1I s6 (by decide) (by rw [w1, s6k]; have := hB.w1 (by omega); omega))
      (fun s7 ⟨x1, x2, x3⟩ k8 hk8 => ?_)
    rw [w1, s6k] at x1
    have P7 := (v1'.step w3 w2 (by decide)).step x3 x2 (by decide)
    refine Hs.last (ps_prInt mV l1N (by decide) (by decide) (by decide) (X1 + k) Y1 Bw P7 x1
      (by rw [ev P7 l1N (by decide), hB.hy1]) (hB.b1 hd k hk) Bw1 hB.BW hB.W2 hL)
      (fun st' ⟨y1', y2'⟩ k9 hk9 => ⟨⟨y1', Fr.trans (w2.weaken (by decide)) (Fr.trans (x2.weaken (by decide))
        (y2'.weaken (by decide)))⟩, by omega⟩)
  · have hd : ¬ 1 < d := by simpa [Cnd.eval, c5.one, s5d] using he
    rw [if_neg hd, List.nil_append] at v1'
    refine Hs.mono (skip_spec (C := C) s5) (by omega) ?_
    rintro st' rfl
    exact ⟨v1'.set (by decide) 0, Fr.set s5 0 (by decide)⟩

/-- The points of row `a` (numeric). -/
def rowPts (d X0 Y0 X1 Y1 N1 a : ℕ) : List Bool := (List.range N1).flatMap (ptWn d X0 Y0 X1 Y1 a)

def ptsIn : St VV MM := forS a1I n1 ptB
def ptsP : St VV MM := forS a0I n0 ptsIn

def ptsInT : List (Fin VV) := a1I :: ptT
def ptsPT : List (Fin VV) := a0I :: ptsInT

theorem ptsIn_spec {e st : DS VV MM} {W R : List Bool} {Ra : List ℕ} {d X0 Y0 X1 Y1 N0 N1 Bw : ℕ}
    (hB : BoxN e d X0 Y0 X1 Y1 N0 N1 Bw C) (hL : W.length ≤ C.Lk) (a : ℕ) (ha : a < N0)
    (h : PS e W (rowPts d X0 Y0 X1 Y1 N1 a ++ R) Ra st) (h0 : st.env a0I = a) :
    Hs C ptsIn st (N1 * (ptCost Bw + 4) + 4) (fun st' => PS e W R Ra st' ∧ Fr st st' ptsInT) := by
  have hN1 : st.env n1 = N1 := by rw [h.fr n1 (by decide), hB.hn1]
  let I : ℕ → DS VV MM → Prop := fun k s =>
    PS e W (((List.range N1).drop k).flatMap (ptWn d X0 Y0 X1 Y1 a) ++ R) Ra s ∧ s.env a0I = a ∧ Fr st s ptsInT
  refine Hs.mono (forS_spec' (C := C) a1I n1 (by decide) ptB st N1 hB.wn1 I (ptCost Bw)
    (fun k s v ⟨i1, i2, i3⟩ => ⟨i1.set (by decide) v, by rw [DS.set_env_ne _ _ (by decide)]; exact i2,
      Fr.trans i3 (Fr.set s v (by decide))⟩) ⟨by rw [List.drop_zero]; exact h, h0, Fr.refl _ _⟩ hN1 ?_) le_rfl ?_
  · intro k hk s ⟨i1, i2, i3⟩ hsk hsN
    rw [drop_range_cons' _ _ hk, List.flatMap_cons, List.append_assoc] at i1
    refine Hs.mono (ptB_spec hB hL a k ha hk i1 i2 hsk) le_rfl ?_
    rintro s' ⟨g1, g2⟩
    exact ⟨⟨g1, by rw [g2 a0I (by decide)]; exact i2, Fr.trans i3 (g2.weaken (by decide))⟩,
      by rw [g2 a1I (by decide)]; exact hsk, by rw [g2 n1 (by decide)]; exact hsN⟩
  · rintro s ⟨⟨i1, _, i3⟩, _, _⟩
    rw [List.drop_eq_nil_of_le (by simp), List.flatMap_nil, List.nil_append] at i1
    exact ⟨i1, i3⟩

theorem ptsP_spec {e st : DS VV MM} {W R : List Bool} {Ra : List ℕ} {d X0 Y0 X1 Y1 N0 N1 Bw : ℕ}
    (hB : BoxN e d X0 Y0 X1 Y1 N0 N1 Bw C) (hL : W.length ≤ C.Lk)
    (h : PS e W ((List.range N0).flatMap (rowPts d X0 Y0 X1 Y1 N1) ++ R) Ra st) :
    Hs C ptsP st (N0 * ((N1 * (ptCost Bw + 4) + 4) + 4) + 4) (fun st' => PS e W R Ra st' ∧ Fr st st' ptsPT) := by
  have hN0 : st.env n0 = N0 := by rw [h.fr n0 (by decide), hB.hn0]
  let I : ℕ → DS VV MM → Prop := fun k s =>
    PS e W (((List.range N0).drop k).flatMap (rowPts d X0 Y0 X1 Y1 N1) ++ R) Ra s ∧ Fr st s ptsPT
  refine Hs.mono (forS_spec' (C := C) a0I n0 (by decide) ptsIn st N0 hB.wn0 I _
    (fun k s v ⟨i1, i3⟩ => ⟨i1.set (by decide) v, Fr.trans i3 (Fr.set s v (by decide))⟩)
    ⟨by rw [List.drop_zero]; exact h, Fr.refl _ _⟩ hN0 ?_) le_rfl ?_
  · intro k hk s ⟨i1, i3⟩ hsk hsN
    rw [drop_range_cons' _ _ hk, List.flatMap_cons, List.append_assoc] at i1
    refine Hs.mono (ptsIn_spec hB hL k hk i1 hsk) le_rfl ?_
    rintro s' ⟨g1, g2⟩
    exact ⟨⟨g1, Fr.trans i3 (g2.weaken (by decide))⟩, by rw [g2 a0I (by decide)]; exact hsk,
      by rw [g2 n0 (by decide)]; exact hsN⟩
  · rintro s ⟨⟨i1, i3⟩, _, _⟩
    rw [List.drop_eq_nil_of_le (by simp), List.flatMap_nil, List.nil_append] at i1
    exact ⟨i1, i3⟩

end NearCubicGates.Close.Cells.SystemsPhase
