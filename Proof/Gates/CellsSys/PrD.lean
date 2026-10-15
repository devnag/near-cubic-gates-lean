import Proof.Gates.CellsSys.PrC

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def rowB : St VV MM :=
  .seq (.op (.copy t3 qV)) (.seq emitNatK (.seq (.op (.copy t3 vRC)) (.seq emitNatK (.seq (.op (.copy t3 s0I))
    (.seq emitNatK (.seq (.ite (.lt v1 vRC) (.seq (.op (.copy t3 s1I)) emitNatK) skipS)
      (.seq (.op (.rdM sA t3)) emitNatK)))))))

def rowT : List (Fin VV) := [t3, t5, t6, t7, t8, t9, vJ]

def rowCost (Bw : ℕ) : ℕ := 5 * (40 * Bw + 40) + 20

theorem rowB_spec {e st : DS VV MM} {W R : List Bool} {v : ℕ} {Ra : List ℕ} {d IPr : ℕ} {Ps : List ℕ}
    {Jf : ℕ → ℕ → ℕ → ℕ} {QB Bw : ℕ} (hR : RowN e d IPr Ps Jf QB Bw C) (hL : W.length ≤ C.Lk)
    (q s0 s1 : ℕ) (hb : natBitLength q ≤ Bw ∧ natBitLength s0 ≤ Bw ∧ natBitLength s1 ≤ Bw ∧ natBitLength v ≤ Bw)
    (h : PS e W (rowWn d q s0 s1 v ++ R) (v :: Ra) st) (hq : st.env qV = q) (h0 : st.env s0I = s0)
    (h1 : st.env s1I = s1) :
    Hs C rowB st (rowCost Bw) (fun st' => PS e W R Ra st' ∧ Fr st st' rowT) := by
  unfold rowWn at h
  simp only [List.append_assoc] at h
  have BW := hR.BW; have W2 := hR.W2
  refine Hx.hs (Hs.then (o_copy t3 qV st (by decide)) (fun s1' ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  rw [hq] at p1
  refine Hs.then (ps_emit q Bw (h.step p3 p2 (by decide)) p1 hb.1 BW W2 hL) (fun s2 ⟨q1, q2⟩ k2 hk2 => ?_)
  refine Hs.then (o_copy t3 vRC s2 (by decide)) (fun s3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  rw [q1.fr vRC (by decide), hR.hd] at r1
  refine Hs.then (ps_emit d Bw (q1.step r3 r2 (by decide)) r1 hR.bd BW W2 hL) (fun s4 ⟨u1, u2⟩ k4 hk4 => ?_)
  refine Hs.then (o_copy t3 s0I s4 (by decide)) (fun s5 ⟨w1, w2, w3⟩ k5 hk5 => ?_)
  have F4 : Fr st s4 rowT := Fr.trans (p2.weaken (by decide)) (Fr.trans (q2.weaken (by decide))
    (Fr.trans (r2.weaken (by decide)) (u2.weaken (by decide))))
  rw [F4 s0I (by decide), h0] at w1
  refine Hs.then (ps_emit s0 Bw (u1.step w3 w2 (by decide)) w1 hb.2.1 BW W2 hL) (fun s6 ⟨x1, x2⟩ k6 hk6 => ?_)
  have F6 : Fr st s6 rowT := Fr.trans F4 (Fr.trans (w2.weaken (by decide)) (x2.weaken (by decide)))
  have c6 := x1.cst
  have s6d : s6.env vRC = d := by rw [x1.fr vRC (by decide), hR.hd]
  refine Hs.then (t := 1 + (40 * Bw + 40) + 1 + 1) (Hs.ite (c := .lt v1 vRC) (show v1 ≠ vRC by decide)
    (R := fun st' => PS e W (natWord v ++ R) (v :: Ra) st' ∧ Fr s6 st' rowT) (fun he => ?_) (fun he => ?_))
    (fun s7 ⟨y1, y2⟩ k7 hk7 => ?_)
  · have hd : 1 < d := by simpa [Cnd.eval, c6.one, s6d] using he
    rw [if_pos hd] at x1
    refine Hx.hs (Hs.then (o_copy t3 s1I s6 (by decide)) (fun s7 ⟨z1, z2, z3⟩ k8 hk8 => ?_))
    rw [F6 s1I (by decide), h1] at z1
    refine Hs.last (ps_emit s1 Bw (x1.step z3 z2 (by decide)) z1 hb.2.2.1 BW W2 hL)
      (fun s8 ⟨a1, a2⟩ k9 hk9 => ⟨⟨a1, Fr.trans (z2.weaken (by decide)) (a2.weaken (by decide))⟩, by omega⟩)
  · have hd : ¬ 1 < d := by simpa [Cnd.eval, c6.one, s6d] using he
    rw [if_neg hd, List.nil_append] at x1
    refine Hs.mono (skip_spec (C := C) s6) (by omega) ?_
    rintro st' rfl
    exact ⟨x1.set (by decide) 0, Fr.set s6 0 (by decide)⟩
  refine Hs.then (ps_rdA y1 t3 (by decide)) (fun s8 ⟨b1, b2, b3⟩ k8 hk8 => ?_)
  refine Hs.last (ps_emit v Bw b2 b1 hb.2.2.2 BW W2 hL) (fun s9 ⟨c1', c2'⟩ k9 hk9 => ⟨⟨c1', ?_⟩, ?_⟩)
  · exact Fr.trans F6 (Fr.trans y2 (Fr.trans (b3.weaken (by decide)) (c2'.weaken (by decide))))
  · unfold rowCost; omega

/-! ## Words of the loops -/

def rowsS1W (d : ℕ) (Jf : ℕ → ℕ → ℕ → ℕ) (q s0 : ℕ) : List Bool :=
  (List.range (qBn q d)).flatMap fun s1 => rowWn d q s0 s1 (Jf q s0 s1)
def rowsS1A (d : ℕ) (Jf : ℕ → ℕ → ℕ → ℕ) (q s0 : ℕ) : List ℕ := (List.range (qBn q d)).map (Jf q s0)
def rowsS0W (d : ℕ) (Jf : ℕ → ℕ → ℕ → ℕ) (q : ℕ) : List Bool := (List.range q).flatMap (rowsS1W d Jf q)
def rowsS0A (d : ℕ) (Jf : ℕ → ℕ → ℕ → ℕ) (q : ℕ) : List ℕ := (List.range q).flatMap (rowsS1A d Jf q)

def rowsS1 : St VV MM := forS s1I qB rowB
def rowsS0 : St VV MM := forS s0I qV rowsS1
def rowsQ : St VV MM := forS qI vNP (.seq fetchQB rowsS0)

def rowsS1T : List (Fin VV) := s1I :: rowT
def rowsS0T : List (Fin VV) := s0I :: rowsS1T
def rowsQT : List (Fin VV) := qI :: fqT ++ rowsS0T

def s1Cost (QB Bw : ℕ) : ℕ := QB * (rowCost Bw + 4) + 4
def s0Cost (QB Bw : ℕ) : ℕ := QB * (s1Cost QB Bw + 4) + 4

theorem rowsS1_spec {e st : DS VV MM} {W R : List Bool} {Ra : List ℕ} {d IPr : ℕ} {Ps : List ℕ}
    {Jf : ℕ → ℕ → ℕ → ℕ} {QB Bw : ℕ} (hR : RowN e d IPr Ps Jf QB Bw C) (hL : W.length ≤ C.Lk)
    (q s0 : ℕ) (hqP : q ∈ Ps) (hs0 : s0 < q)
    (h : PS e W (rowsS1W d Jf q s0 ++ R) (rowsS1A d Jf q s0 ++ Ra) st) (hq : st.env qV = q)
    (hqB : st.env qB = qBn q d) (h0 : st.env s0I = s0) :
    Hs C rowsS1 st (s1Cost QB Bw) (fun st' => PS e W R Ra st' ∧ Fr st st' rowsS1T) := by
  have hqQ := hR.qle q hqP
  have hBq : qBn q d ≤ QB := (qBn_le _ _).trans (by have := hR.qpos q hqP; omega)
  have hw := hR.wq
  let I : ℕ → DS VV MM → Prop := fun k s =>
    PS e W (((List.range (qBn q d)).drop k).flatMap (fun s1 => rowWn d q s0 s1 (Jf q s0 s1)) ++ R)
      (((List.range (qBn q d)).drop k).map (Jf q s0) ++ Ra) s ∧ Fr st s rowsS1T
  refine Hs.mono (forS_spec' (C := C) s1I qB (by decide) rowB st (qBn q d) (by
      have : QB ≤ QB * QB := Nat.le_mul_self QB
      omega) I (rowCost Bw)
    (fun k s v ⟨i1, i3⟩ => ⟨i1.set (by decide) v, Fr.trans i3 (Fr.set s v (by decide))⟩)
    ⟨by simp only [List.drop_zero]; exact h, Fr.refl _ _⟩ hqB ?_)
    (by unfold s1Cost; have := Nat.mul_le_mul_right (rowCost Bw + 4) hBq; omega) ?_
  · intro k hk s ⟨i1, i3⟩ hsk hsN
    rw [drop_range_cons' _ _ hk, List.flatMap_cons, List.map_cons, List.append_assoc, List.cons_append] at i1
    have hkq : k < q := by unfold qBn at hk; split_ifs at hk <;> omega
    have hbq := hR.bq q hqP
    refine Hs.mono (rowB_spec hR hL q s0 k ⟨hbq, (nbl_mono hs0.le).trans hbq, (nbl_mono hkq.le).trans hbq,
      hR.bJ q hqP s0 hs0 k hk⟩ i1 (by rw [i3 qV (by decide)]; exact hq) (by rw [i3 s0I (by decide)]; exact h0) hsk)
      le_rfl ?_
    rintro s' ⟨g1, g2⟩
    exact ⟨⟨g1, Fr.trans i3 (g2.weaken (by decide))⟩, by rw [g2 s1I (by decide)]; exact hsk,
      by rw [g2 qB (by decide)]; exact hsN⟩
  · rintro s ⟨⟨i1, i3⟩, _, _⟩
    rw [List.drop_eq_nil_of_le (by simp), List.flatMap_nil, List.nil_append, List.map_nil, List.nil_append] at i1
    exact ⟨i1, i3⟩

theorem rowsS0_spec {e st : DS VV MM} {W R : List Bool} {Ra : List ℕ} {d IPr : ℕ} {Ps : List ℕ}
    {Jf : ℕ → ℕ → ℕ → ℕ} {QB Bw : ℕ} (hR : RowN e d IPr Ps Jf QB Bw C) (hL : W.length ≤ C.Lk)
    (q : ℕ) (hqP : q ∈ Ps)
    (h : PS e W (rowsS0W d Jf q ++ R) (rowsS0A d Jf q ++ Ra) st) (hq : st.env qV = q)
    (hqB : st.env qB = qBn q d) :
    Hs C rowsS0 st (s0Cost QB Bw) (fun st' => PS e W R Ra st' ∧ Fr st st' rowsS0T) := by
  have hqQ := hR.qle q hqP
  have hw := hR.wq
  let I : ℕ → DS VV MM → Prop := fun k s =>
    PS e W (((List.range q).drop k).flatMap (rowsS1W d Jf q) ++ R)
      (((List.range q).drop k).flatMap (rowsS1A d Jf q) ++ Ra) s ∧ Fr st s rowsS0T
  refine Hs.mono (forS_spec' (C := C) s0I qV (by decide) rowsS1 st q (by
      have : QB ≤ QB * QB := Nat.le_mul_self QB
      omega) I (s1Cost QB Bw)
    (fun k s v ⟨i1, i3⟩ => ⟨i1.set (by decide) v, Fr.trans i3 (Fr.set s v (by decide))⟩)
    ⟨by simp only [List.drop_zero]; exact h, Fr.refl _ _⟩ hq ?_)
    (by unfold s0Cost; have := Nat.mul_le_mul_right (s1Cost QB Bw + 4) hqQ; omega) ?_
  · intro k hk s ⟨i1, i3⟩ hsk hsN
    rw [drop_range_cons' _ _ hk, List.flatMap_cons, List.flatMap_cons, List.append_assoc, List.append_assoc] at i1
    refine Hs.mono (rowsS1_spec hR hL q k hqP hk i1 hsN (by rw [i3 qB (by decide)]; exact hqB) hsk) le_rfl ?_
    rintro s' ⟨g1, g2⟩
    exact ⟨⟨g1, Fr.trans i3 (g2.weaken (by decide))⟩, by rw [g2 s0I (by decide)]; exact hsk,
      by rw [g2 qV (by decide)]; exact hsN⟩
  · rintro s ⟨⟨i1, i3⟩, _, _⟩
    rw [List.drop_eq_nil_of_le (by simp), List.flatMap_nil, List.nil_append, List.flatMap_nil, List.nil_append] at i1
    exact ⟨i1, i3⟩

theorem rowsQ_spec {e st : DS VV MM} {W R : List Bool} {Ra : List ℕ} {d IPr : ℕ} {Ps : List ℕ}
    {Jf : ℕ → ℕ → ℕ → ℕ} {QB Bw : ℕ} (hR : RowN e d IPr Ps Jf QB Bw C) (hL : W.length ≤ C.Lk)
    (h : PS e W (Ps.flatMap (rowsS0W d Jf) ++ R) (Ps.flatMap (rowsS0A d Jf) ++ Ra) st) :
    Hs C rowsQ st (Ps.length * (fqCost (e.ram sN).length + s0Cost QB Bw + 1 + 4) + 4)
      (fun st' => PS e W R Ra st' ∧ Fr st st' rowsQT) := by
  have hw := hR.wq
  have hNP : st.env vNP = Ps.length := by rw [h.fr vNP (by decide), hR.hnp]
  let I : ℕ → DS VV MM → Prop := fun k s =>
    PS e W ((Ps.drop k).flatMap (rowsS0W d Jf) ++ R) ((Ps.drop k).flatMap (rowsS0A d Jf) ++ Ra) s ∧ Fr st s rowsQT
  refine Hs.mono (forS_spec' (C := C) qI vNP (by decide) (.seq fetchQB rowsS0) st Ps.length (by omega) I
    (fqCost (e.ram sN).length + s0Cost QB Bw + 1)
    (fun k s v ⟨i1, i3⟩ => ⟨i1.set (by decide) v, Fr.trans i3 (Fr.set s v (by decide))⟩)
    ⟨by simp only [List.drop_zero]; exact h, Fr.refl _ _⟩ hNP ?_) le_rfl ?_
  · intro k hk s ⟨i1, i3⟩ hsk hsN
    have hPk : Ps.getD k 0 = Ps[k] := List.getD_eq_getElem _ _ hk
    rw [List.drop_eq_getElem_cons hk, List.flatMap_cons, List.flatMap_cons, List.append_assoc,
      List.append_assoc] at i1
    refine Hs.seq (fetchQ_spec hR i1 k hk hsk) (fun s2 ⟨q1, q2, q3, q4⟩ => ?_)
    rw [hPk] at q1 q2
    refine Hs.mono (rowsS0_spec hR hL Ps[k] (List.getElem_mem _) q3 q1 q2) le_rfl ?_
    rintro s' ⟨g1, g2⟩
    exact ⟨⟨g1, Fr.trans i3 (Fr.trans (q4.weaken (by decide)) (g2.weaken (by decide)))⟩,
      by rw [g2 qI (by decide), q4 qI (by decide)]; exact hsk, by rw [g2 vNP (by decide), q4 vNP (by decide)]; exact hsN⟩
  · rintro s ⟨⟨i1, i3⟩, _, _⟩
    rw [List.drop_eq_nil_of_le le_rfl, List.flatMap_nil, List.nil_append, List.flatMap_nil, List.nil_append] at i1
    exact ⟨i1, i3⟩

end NearCubicGates.Close.Cells.SystemsPhase
