import Proof.Gates.CellsSys.PrB

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

/-- The inner radix of a prime: `q` for two roles, `1` for one. -/
def qBn (q d : ℕ) : ℕ := if 1 < d then q else 1

/-- The word of one row (numeric form). -/
def rowWn (d q s0 s1 v : ℕ) : List Bool :=
  natWord q ++ natWord d ++ natWord s0 ++ (if 1 < d then natWord s1 else []) ++ natWord v

/-- The numeric data of the rows as the printer sees it. -/
structure RowN (e : DS VV MM) (d IPr : ℕ) (Ps : List ℕ) (Jf : ℕ → ℕ → ℕ → ℕ) (QB Bw : ℕ) (C : Ctx) : Prop where
  hd : e.env vRC = d
  hip : e.env vIPr = IPr
  hnp : e.env vNP = Ps.length
  hN : ∀ i < Ps.length, (e.ram sN).getD (IPr + i) 0 = Ps.getD i 0 ∧ IPr + i < (e.ram sN).length
  d12 : 1 ≤ d ∧ d ≤ 2
  qle : ∀ q ∈ Ps, q ≤ QB
  qpos : ∀ q ∈ Ps, 1 ≤ q
  bq : ∀ q ∈ Ps, natBitLength q ≤ Bw
  bd : natBitLength d ≤ Bw
  bJ : ∀ q ∈ Ps, ∀ s0 < q, ∀ s1 < qBn q d, natBitLength (Jf q s0 s1) ≤ Bw
  bc : natBitLength ((Ps.map fun q => q * qBn q d).sum) ≤ Bw
  B1 : 1 ≤ Bw
  BW : Bw + 2 < 2 ^ C.Wd
  W2 : 2 ≤ C.Wd
  wq : QB * QB + (Ps.map fun q => q * qBn q d).sum + IPr + Ps.length + (e.ram sN).length < 2 ^ C.Wd

theorem nbl_mono {u v : ℕ} (h : u ≤ v) : natBitLength u ≤ natBitLength v := by
  unfold natBitLength; exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem qBn_le (q d : ℕ) : qBn q d ≤ max q 1 := by unfold qBn; split_ifs <;> omega

/-! ## Fetching the `i`-th prime -/

def qBset : St VV MM := .ite (.lt v1 vRC) (.op (.copy qB qV)) (.op (.copy qB v1))

def fetchQB : St VV MM := .seq (.op (.copy prd vIPr)) (.seq (.op (.add prd qI)) (.seq (fetch sN prd qV) qBset))

def fqT : List (Fin VV) := [prd, c0, vJ, qV, qB]

theorem fqT_frag : ∀ x ∈ fqT, FragVar x := by decide

def fqCost (LN : ℕ) : ℕ := 6 * LN + 20

theorem fetchQ_spec {e st : DS VV MM} {W Rk : List Bool} {Ra : List ℕ} {d IPr : ℕ} {Ps : List ℕ}
    {Jf : ℕ → ℕ → ℕ → ℕ} {QB Bw : ℕ} (hR : RowN e d IPr Ps Jf QB Bw C) (h : PS e W Rk Ra st) (i : ℕ)
    (hi : i < Ps.length) (hqi : st.env qI = i) :
    Hs C fetchQB st (fqCost (e.ram sN).length) (fun st' => st'.env qV = Ps.getD i 0 ∧
      st'.env qB = qBn (Ps.getD i 0) d ∧ PS e W Rk Ra st' ∧ Fr st st' fqT) := by
  obtain ⟨hv, hlt⟩ := hR.hN i hi
  have hw := hR.wq
  refine Hx.hs (Hs.then (o_copy prd vIPr st (by decide)) (fun s1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  rw [h.fr vIPr (by decide), hR.hip] at p1
  have s1q : s1.env qI = i := by rw [p2 qI (by decide)]; exact hqi
  refine Hs.then (o_add prd qI s1 (by decide) (by rw [p1, s1q]; omega)) (fun s2 ⟨q1, q2, q3⟩ k2 hk2 => ?_)
  rw [p1, s1q] at q1
  have P2 := (h.step p3 p2 (by decide)).step q3 q2 (by decide)
  have hrc := P2.rc sN
  rw [P2.ram] at hrc
  refine Hs.then (ps_fetchN P2 prd qV (by decide) (by decide) (by decide) (by rw [q1, P2.ram]; exact hlt)
    (by rw [q1]; omega)) (fun s3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  rw [q1, P2.ram, hv] at r1
  have c3 := r2.cst
  have s3d : s3.env vRC = d := by rw [r2.fr vRC (by decide), hR.hd]
  refine Hs.last (t := 1 + 1) (Hs.ite (c := .lt v1 vRC) (show v1 ≠ vRC by decide)
    (R := fun st' => st'.env qB = qBn (Ps.getD i 0) d ∧ Fr s3 st' [qB] ∧ Same s3 st') (fun he => ?_) (fun he => ?_))
    (fun st' ⟨g1, g2, g3⟩ k4 hk4 => ⟨⟨by rw [g2 qV (by decide)]; exact r1, g1, r2.step g3 g2 (by decide),
      Fr.trans (p2.weaken (by decide)) (Fr.trans (q2.weaken (by decide)) (Fr.trans (r3.weaken (by decide))
        (g2.weaken (by decide))))⟩, by unfold fqCost; omega⟩)
  · have hd : 1 < d := by simpa [Cnd.eval, c3.one, s3d] using he
    refine Hs.mono (o_copy qB qV s3 (by decide)) (by omega) ?_
    rintro st' ⟨g1, g2, g3⟩
    exact ⟨by rw [g1, r1]; unfold qBn; rw [if_pos hd], g2, g3⟩
  · have hd : ¬ 1 < d := by simpa [Cnd.eval, c3.one, s3d] using he
    refine Hs.mono (o_copy qB v1 s3 (by decide)) (by omega) ?_
    rintro st' ⟨g1, g2, g3⟩
    exact ⟨by rw [g1, c3.one]; unfold qBn; rw [if_neg hd], g2, g3⟩

/-! ## The row count -/

def cntB : St VV MM := .seq fetchQB (.seq (.op (.mul qV qB mV)) (.op (.add cnt mV)))
def cntP : St VV MM := .seq (.op (.zero cnt)) (forS qI vNP cntB)

def cntT : List (Fin VV) := [cnt, qI, prd, c0, vJ, qV, qB, mV]

theorem cntP_spec {e st : DS VV MM} {W Rk : List Bool} {Ra : List ℕ} {d IPr : ℕ} {Ps : List ℕ}
    {Jf : ℕ → ℕ → ℕ → ℕ} {QB Bw : ℕ} (hR : RowN e d IPr Ps Jf QB Bw C) (h : PS e W Rk Ra st) :
    Hs C cntP st (1 + (Ps.length * (fqCost (e.ram sN).length + 4 + 4) + 4) + 1) (fun st' =>
      st'.env cnt = (Ps.map fun q => q * qBn q d).sum ∧ PS e W Rk Ra st' ∧ Fr st st' cntT) := by
  have hw := hR.wq
  refine Hs.seq (o_zero cnt st) (fun s1 ⟨p1, p2, p3⟩ => ?_)
  have P1 := h.step p3 p2 (by decide)
  have hNP : s1.env vNP = Ps.length := by rw [P1.fr vNP (by decide), hR.hnp]
  let I : ℕ → DS VV MM → Prop := fun k s => s.env cnt = ((Ps.take k).map fun q => q * qBn q d).sum ∧
    PS e W Rk Ra s ∧ Fr st s cntT
  have hsum_le : ∀ k, ((Ps.take k).map fun q => q * qBn q d).sum ≤ (Ps.map fun q => q * qBn q d).sum := by
    intro k
    have := List.take_append_drop k (Ps.map fun q => q * qBn q d)
    rw [← List.map_take] at this
    have h2 := congrArg List.sum this
    rw [List.sum_append] at h2
    omega
  refine Hs.mono (forS_spec' (C := C) qI vNP (by decide) cntB s1 Ps.length (by omega) I (fqCost (e.ram sN).length + 4)
    (fun k s v ⟨i1, i2, i3⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1, i2.set (by decide) v,
      Fr.trans i3 (Fr.set s v (by decide))⟩)
    ⟨by rw [p1]; simp, P1, p2.weaken (by decide)⟩ hNP ?_) le_rfl ?_
  · intro k hk s ⟨i1, i2, i3⟩ hsk hsN
    refine Hx.hs (Hs.then (fetchQ_spec hR i2 k hk hsk) (fun s2 ⟨q1, q2, q3, q4⟩ k2 hk2 => ?_))
    have hq : Ps.getD k 0 ∈ Ps := by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
    have hqQ := hR.qle _ hq
    have hBq : qBn (Ps.getD k 0) d ≤ QB := (qBn_le _ _).trans (by have := hR.qle _ hq; have := hR.qpos _ hq; omega)
    have hmw : Ps.getD k 0 * qBn (Ps.getD k 0) d < 2 ^ C.Wd := lt_of_le_of_lt (Nat.mul_le_mul hqQ hBq) (by omega)
    refine Hs.then (o_mul qV qB mV s2 (by decide) (by decide) (by decide) (by rw [q1, q2]; exact hmw))
      (fun s3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
    rw [q1, q2] at r1
    have s3c : s3.env cnt = ((Ps.take k).map fun q => q * qBn q d).sum := by
      rw [r2 cnt (by decide), q4 cnt (by decide)]; exact i1
    have htk : ((Ps.take (k + 1)).map fun q => q * qBn q d).sum =
        ((Ps.take k).map fun q => q * qBn q d).sum + Ps.getD k 0 * qBn (Ps.getD k 0) d := by
      rw [List.getD_eq_getElem _ _ hk, List.take_add_one, List.getElem?_eq_getElem hk]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, Nat.add_zero]
    refine Hs.last (o_add cnt mV s3 (by decide) (by rw [s3c, r1, ← htk]; have := hsum_le (k + 1); omega))
      (fun s4 ⟨u1, u2, u3⟩ k4 hk4 => ⟨⟨⟨by rw [u1, s3c, r1, htk], (q3.step r3 r2 (by decide)).step u3 u2 (by decide),
        Fr.trans i3 (Fr.trans (q4.weaken (by decide)) (Fr.trans (r2.weaken (by decide)) (u2.weaken (by decide))))⟩,
        by rw [u2 qI (by decide), r2 qI (by decide), q4 qI (by decide)]; exact hsk,
        by rw [u2 vNP (by decide), r2 vNP (by decide), q4 vNP (by decide)]; exact hsN⟩, by omega⟩)
  · rintro s ⟨⟨i1, i2, i3⟩, _, _⟩
    exact ⟨by rw [i1, List.take_of_length_le le_rfl], i2, i3⟩

end NearCubicGates.Close.Cells.SystemsPhase
