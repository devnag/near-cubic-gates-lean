import SourceAdapters.Compile.CNFGenB

/-!
# Token generator, part C: action values, selected values, one round

proof of `lem:multitape-refuter`: the next value of window bit `j` is selected by the current state and scanned symbols from the
finite table (`transT`), one round is every window bit (`tmplT`). These cell procedures append exactly
`CNFTokens.actT`, `valT`, `transT`, `tmplT` of the table `GD.td`.
-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {C : Ctx}

/-- `cst (eval c)`. -/
def cstP (c : Cnd VV) : St VV MM := .ite c (emitR kc8) (emitR vZ)

theorem cstP_spec (c : Cnd VV) (hc : c.wf) (a : DS VV MM) (hT : TTend a) (hk : KC a) :
    Hs C (cstP c) a 2 (fun b => Ext a b [.cst (c.eval a)] ∧ Fr a b []) := by
  refine Hs.ite hc (fun he => ?_) (fun he => ?_)
  · exact Hs.mono (emitR_spec kc8 _ a hT (by rw [hk.k8, he]; rfl)) le_rfl (fun b h => h)
  · exact Hs.mono (emitR_spec vZ _ a hT (by rw [hk.z, he]; rfl)) le_rfl (fun b h => h)

/-- `gY := cell(ta, po)`, then `wir gY`. -/
def cellWirP (ta po : Fin VV) : St VV MM :=
  .seq (.op (.mul dWd ta gY)) (.seq (.op (.add gY po)) (.seq (.op (.add gY dS)) (.seq (.op (.add gY dTW))
    (emitWir gY))))

theorem cellWirP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (ta po : Fin VV)
    (hta : ta ∉ [gY, gX, dWd, dS, dTW]) (hpo : po ∉ [gY, gX, dWd, dS, dTW]) (a : DS VV MM) (hG : GC D a)
    (tv pv : ℕ) (htv : a.env ta = tv) (hpv : a.env po = pv) (ht : tv < D.t) (hp : pv < D.width) :
    Hs C (cellWirP ta po) a 13 (fun b => Ext a b [.wir (cellI D.t D.s D.width tv pv)] ∧ Fr a b [gY, gX]) := by
  have hta' : ta ≠ gY ∧ ta ≠ gX ∧ ta ≠ dWd ∧ ta ≠ dS ∧ ta ≠ dTW := by simpa using hta
  have hpo' : po ≠ gY ∧ po ≠ gX ∧ po ≠ dWd ∧ po ≠ dS ∧ po ≠ dTW := by simpa using hpo
  have hk := hG.kc
  have hT := hG.tt
  unfold TTend at hT
  have hWl : D.s + (D.t * D.width + D.t * D.width) ≤ Λ := hOk.WΛ
  have h1 := D.head_lt ht hp
  apply hs_of_wpc
  simp only [cellWirP, emitWir, emitR, wpc, opwp]
  vsimp [hk.k8, hk.two, htv, hpv, hG.wd, hG.s, hG.tw, DS.put, putAt, hT, Ne.symm hta'.2.2.1, hta'.1, hpo'.1,
    Ne.symm hta'.1, Ne.symm hpo'.1]
  and_split
  all_goals try omega
  all_goals try fr_tac
  ext_tac [hT, cellI]

/-! ## Action values -/

def actCtlP : St VV MM := .seq ncP (cstP (.eq gE gJ))

theorem actCtlP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m j : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t) (hR : a.env gR = D.base q m) (hj : a.env gJ = j) :
    Hs C actCtlP a (Λ * (6 * Λ + 40) + 13) (fun b => Ext a b [.cst (decide (D.td.nc q m = j))] ∧ Fr a b ncT) := by
  refine Hs.seqc (t1 := Λ * (6 * Λ + 40) + 10) (t2 := 2) (ncP_spec D Λ hOk hΛ a hG q m hq hm hR) (fun b hb => ?_)
    (by omega)
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have hGb : GC D b := hG.of hb2 hb3 (by decide)
  refine Hs.mono (cstP_spec (C := C) (.eq gE gJ) (show gE ≠ gJ by decide) b hGb.tt hGb.kc) le_rfl ?_
  rintro d ⟨hd1, hd2⟩
  refine ⟨(hb2.trans hd1).congr ?_, hb3.trans (Fr.weaken hd2 (by simp))⟩
  simp [Cnd.eval, hb1, hb3 gJ (by decide), hj]

def actHeadBodyP : St VV MM := .seq (headWirP gL gB) (.seq (mvP gL gB) (cmpTailP (.eq gV gE)))

def actHeadBodyT : List (Fin VV) := [gY, gX, gU, gS, gV, gT]

theorem actHeadBodyP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m ta pos old : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t) (hR : a.env gR = D.base q m)
    (hta : a.env gL = ta) (hpos : a.env gE = pos) (hold : a.env gB = old) (ht : ta < D.t) (hp : old < D.width) :
    Hs C actHeadBodyP a (14 * Λ + 80) (fun b => Ext a b [.wir (headI D.s D.width ta old),
      .cst (decide (D.td.mv q m ta old = pos)), .conj] ∧ Fr a b actHeadBodyT) := by
  have hwΛ := D.width_le Λ hOk
  refine Hs.seqc (t1 := 12) (t2 := 14 * Λ + 66) (headWirP_spec D Λ hOk hΛ gL gB (by decide) (by decide) a hG
    ta old hta hold ht hp) (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hb2⟩ := hb
  have hGb : GC D b := hG.of hb1 hb2 (by decide)
  refine Hs.seqc (t1 := 14 * Λ + 60) (t2 := 5) (mvP_spec D Λ hOk hΛ gL gB (by decide) (by decide) (by decide) b
    hGb q m hq hm (by rw [hb2 gR (by decide), hR]) (by rw [hb2 gL (by decide), hta]; exact ht)
    (by rw [hb2 gB (by decide), hold]; omega)) (fun d hd => ?_) (by omega)
  obtain ⟨hd1, hd2, hd3⟩ := hd
  have hGd : GC D d := hGb.of hd2 hd3 (by decide)
  refine Hs.mono (cmpTailP_spec (C := C) (.eq gV gE) (show gV ≠ gE by decide) d hGd.tt hGd.kc) (by omega) ?_
  rintro e ⟨he1, he2⟩
  have hbL : b.env gL = ta := by rw [hb2 gL (by decide), hta]
  have hbB : b.env gB = old := by rw [hb2 gB (by decide), hold]
  have hdE : d.env gE = pos := by rw [hd3 gE (by decide), hb2 gE (by decide), hpos]
  refine ⟨(hb1.trans (hd2.trans he1)).congr ?_, ?_⟩
  · simp [Cnd.eval, hd1, hbL, hbB, hdE]
  · exact (Fr.weaken hb2 (by simp [actHeadBodyT])).trans ((Fr.weaken hd3 (by simp [actHeadBodyT, mvT])).trans
      (Fr.weaken he2 (by simp)))

def actHeadP : St VV MM := .seq (.op (.dm gZ dWd gL gE)) (anyP gB dWd actHeadBodyP)

def headCost (D : GD) (Λ : ℕ) : ℕ := D.width * ((14 * Λ + 80) + 4) + D.width * 5 + 12

theorem actHeadP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m i : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t) (hR : a.env gR = D.base q m)
    (hi : a.env gZ = i) (hit : i < D.t * D.width) :
    Hs C actHeadP a (headCost D Λ + 2) (fun b => Ext a b (anyT D.width (fun old =>
      [.wir (headI D.s D.width (i / D.width) old), .cst (decide (D.td.mv q m (i / D.width) old = i % D.width)),
        .conj])) ∧ Fr a b (gL :: gE :: gB :: actHeadBodyT)) := by
  have hw0 := hOk.width
  have hwΛ := D.width_le Λ hOk
  have hdiv : i / D.width < D.t := (Nat.div_lt_iff_lt_mul hw0).2 hit
  refine Hs.seqc (t1 := 1) (t2 := headCost D Λ) (hs_dm C gZ dWd gL gE a (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [hG.wd]; omega) (by rw [hG.wd]; omega)) (fun b hb => ?_) (by omega)
  subst hb
  have hGb : GC D ((a.set gL (a.env gZ / a.env dWd)).set gE (a.env gZ % a.env dWd)) :=
    hG.of (Ext.of_eq rfl rfl rfl rfl) (T := [gL, gE]) (by fr_tac) (by decide)
  refine Hs.mono (anyP_spec gB dWd actHeadBodyP actHeadBodyT (by decide) (by decide)
    (fun d => GC D d ∧ d.env gR = D.base q m ∧ d.env gL = i / D.width ∧ d.env gE = i % D.width) D.width
    (14 * Λ + 80) _ (fun d hd => hd.1.wd) (fun d hd => ⟨hd.1.tt, hd.1.kc⟩)
    (fun d e toks hd hE hF => ⟨hd.1.of hE hF (by decide), by rw [hF gR (by decide), hd.2.1],
      by rw [hF gL (by decide), hd.2.2.1], by rw [hF gE (by decide), hd.2.2.2]⟩) (by omega)
    (fun old hold d hd hdB => actHeadBodyP_spec D Λ hOk hΛ d hd.1 q m _ _ old hq hm hd.2.1 hd.2.2.1 hd.2.2.2 hdB
      hdiv hold) _ ⟨hGb, by vsimp [hR], by vsimp [hi, hG.wd], by vsimp [hi, hG.wd]⟩) le_rfl ?_
  rintro d ⟨hd1, hd2⟩
  have hE0 : Ext a ((a.set gL (a.env gZ / a.env dWd)).set gE (a.env gZ % a.env dWd)) [] := Ext.of_eq rfl rfl rfl rfl
  refine ⟨(hE0.trans hd1).congr (by simp), ?_⟩
  exact (show Fr a ((a.set gL (a.env gZ / a.env dWd)).set gE (a.env gZ % a.env dWd)) (gL :: gE :: gB ::
    actHeadBodyT) by fr_tac).trans (Fr.weaken hd2 (by simp [actHeadBodyT]))

/-- The eight tokens of a written cell. -/
def actWriteP : St VV MM :=
  .seq (headWirP gL gE) (.seq (cstP (.eq gV v1)) (.seq (emitR kc4) (.seq (headWirP gL gE) (.seq (emitR kc3)
    (.seq (cellWirP gL gE) (.seq (emitR kc4) (emitR kc5)))))))

theorem actWriteP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (ta pos c : ℕ) (hta : a.env gL = ta) (hpos : a.env gE = pos) (hc : a.env gV = c)
    (ht : ta < D.t) (hp : pos < D.width) :
    Hs C actWriteP a 60 (fun b => Ext a b [.wir (headI D.s D.width ta pos), .cst (decide (c = 1)), .conj,
      .wir (headI D.s D.width ta pos), .neg, .wir (cellI D.t D.s D.width ta pos), .conj, .disj] ∧
      Fr a b [gY, gX]) := by
  have hk := hG.kc
  have hT := hG.tt
  unfold TTend at hT
  have hWl : D.s + (D.t * D.width + D.t * D.width) ≤ Λ := hOk.WΛ
  have h1 := D.head_lt ht hp
  apply hs_of_wpc
  simp only [actWriteP, headWirP, cstP, cellWirP, emitWir, emitR, wpc, opwp, Cnd.eval, Cnd.wf]
  by_cases hc1 : c = 1
  · vsimp [hk.k8, hk.two, hk.k3, hk.k4, hk.k5, hk.one, hta, hpos, hc, hc1, hG.wd, hG.s, hG.tw, DS.put, putAt, hT]
    and_split
    all_goals try omega
    all_goals try fr_tac
    ext_tac [hT, headI, cellI, hc1]
  · vsimp [hk.k8, hk.two, hk.k3, hk.k4, hk.k5, hk.z, hk.one, hta, hpos, hc, hc1, hG.wd, hG.s, hG.tw, DS.put, putAt,
      hT]
    and_split
    all_goals try omega
    all_goals try fr_tac
    ext_tac [hT, headI, cellI, hc1]

/-- `gY := base + 1 + w + 4·gL`, the address of the write bits. -/
def wrAddrP : St VV MM :=
  .seq (.op (.mul gL kc4 gY)) (.seq (.op (.add gY gR)) (.seq (.op (.add gY dWb)) (.op (.inc gY))))

def actCellP : St VV MM :=
  .seq (.seq (.op (.dm gZ dWd gL gE)) wrAddrP) (.seq (lookP sCB gY gU) (.seq (.op (.inc gY))
    (.seq (lookP sCB gY gV) (.ite (.eq gU v1) actWriteP (cellWirP gL gE)))))

def actCellT : List (Fin VV) := [gL, gE, gY, gU, gS, gV, gX]

/-- The tokens of written cell `(tape, pos)`. -/
def cellToks (D : GD) (q m tape pos : ℕ) : List RTok :=
  match D.td.wr q m tape with
  | none => [.wir (cellI D.t D.s D.width tape pos)]
  | some v => [.wir (headI D.s D.width tape pos), .cst v, .conj, .wir (headI D.s D.width tape pos), .neg,
      .wir (cellI D.t D.s D.width tape pos), .conj, .disj]

theorem actCellP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m i : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t) (hR : a.env gR = D.base q m)
    (hi : a.env gZ = i) (hit : i < D.t * D.width) :
    Hs C actCellP a (12 * Λ + 120) (fun b => Ext a b (cellToks D q m (i / D.width) (i % D.width)) ∧
      Fr a b actCellT) := by
  have hw0 := hOk.width
  have hcb := hOk.cbΛ
  have hwΛ := D.width_le Λ hOk
  have hdiv : i / D.width < D.t := (Nat.div_lt_iff_lt_mul hw0).2 hit
  have hmod : i % D.width < D.width := Nat.mod_lt _ hw0
  set tp := i / D.width with htp
  set ps := i % D.width with hps
  set p0 := D.base q m + (1 + D.w + 4 * tp) with hp0
  have hlt0 : p0 + 1 < D.cb.length := by
    have := D.rec_lt hq hm (j := 1 + D.w + 4 * tp + 1) (by unfold GD.R; omega)
    rw [hOk.len]; omega
  -- the address
  have s1 : Hs C (.seq (.op (.dm gZ dWd gL gE)) wrAddrP) a 10 (fun b => b.env gY = p0 ∧ b.env gL = tp ∧
      b.env gE = ps ∧ Ext a b [] ∧ Fr a b [gL, gE, gY]) := by
    apply hs_of_wpc
    simp only [wrAddrP, wpc, opwp]
    vsimp [hG.wd, hi, hG.kc.k4, hR, hG.wb, ← htp, ← hps]
    and_split
    all_goals first | omega | exact Ext.of_eq rfl rfl rfl rfl | fr_tac | skip
  refine Hs.seqc (t1 := 10) (t2 := 12 * Λ + 109) s1 (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hbL, hbE, hb2, hb3⟩ := hb
  have hGb : GC D b := hG.of hb2 hb3 (by decide)
  refine Hs.seqc (t1 := 6 * p0 + 10) (t2 := 6 * Λ + 78) (lookP_at (C := C) sCB gY gU (by decide) (by decide)
    (by decide) b p0 hb1 hGb.rcb (by rw [hGb.cb]; omega) (by omega)) (fun d hd => ?_) (by omega)
  obtain ⟨hd1, hd2, hd3⟩ := hd
  rw [hGb.cb] at hd1
  have hGd : GC D d := hGb.of hd2 hd3 (by decide)
  refine Hs.seqc (t1 := 1) (t2 := 6 * Λ + 76) (hs_inc C gY d (by rw [hd3 gY (by decide), hb1]; omega))
    (fun e he => ?_) (by omega)
  subst he
  have hGe : GC D (d.set gY (d.env gY + 1)) := hGd.of (Ext.of_eq rfl rfl rfl rfl) (T := [gY]) (by fr_tac)
    (by decide)
  refine Hs.seqc (t1 := 6 * (p0 + 1) + 10) (t2 := 61) (lookP_at (C := C) sCB gY gV (by decide) (by decide)
    (by decide) _ (p0 + 1) (by vsimp [hd3 gY (by decide), hb1]) hGe.rcb (by rw [hGe.cb]; omega) (by omega))
    (fun g hg => ?_) (by omega)
  obtain ⟨hg1, hg2, hg3⟩ := hg
  rw [hGe.cb] at hg1
  have hGg : GC D g := hGe.of hg2 hg3 (by decide)
  have gL' : g.env gL = tp := by rw [hg3 gL (by decide), DS.set_env_ne _ _ (by decide), hd3 gL (by decide), hbL]
  have gE' : g.env gE = ps := by rw [hg3 gE (by decide), DS.set_env_ne _ _ (by decide), hd3 gE (by decide), hbE]
  have gU' : g.env gU = D.cb.getD p0 0 := by
    rw [hg3 gU (by decide), DS.set_env_ne _ _ (by decide), hd1]
  have hwr : D.td.wr q m tp = if D.cb.getD p0 0 = 1 then some (decide (D.cb.getD (p0 + 1) 0 = 1)) else none := by
    simp only [GD.td, TD.ofBits, bitAt]
    rw [show D.o3 + (q * 2 ^ D.t + m) * D.R = D.base q m from rfl,
      show D.base q m + 1 + D.w + 4 * tp = p0 by omega, show p0 + 1 = p0 + 1 from rfl]
    by_cases h : D.cb.getD p0 0 = 1 <;> simp [h]
  have hext : ∀ x toks, Ext g x toks → Ext a x toks := fun x toks hx =>
    ((hb2.trans hd2).trans ((Ext.of_eq (a := d) (b := d.set gY (d.env gY + 1)) rfl rfl rfl rfl).trans
      (hg2.trans hx))).congr (by simp)
  have hfr : ∀ x, Fr g x [gY, gX] → Fr a x actCellT := fun x hx =>
    ((Fr.weaken hb3 (by simp [actCellT])).trans (Fr.weaken hd3 (by simp [actCellT]))).trans
      ((Fr.set (T := actCellT) d _ (by simp [actCellT])).trans ((Fr.weaken hg3 (by simp [actCellT])).trans
        (Fr.weaken hx (by simp [actCellT]))))
  refine Hs.ite (show gU ≠ v1 by decide) (fun hc => ?_) (fun hc => ?_)
  · have h1 : D.cb.getD p0 0 = 1 := by
      simp only [Cnd.eval, decide_eq_true_eq, gU', hGg.kc.one] at hc; exact hc
    refine Hs.mono (actWriteP_spec D Λ hOk hΛ g hGg tp ps _ gL' gE' hg1 hdiv hmod) le_rfl ?_
    rintro x ⟨hx1, hx2⟩
    refine ⟨hext _ _ (hx1.congr ?_), hfr _ hx2⟩
    rw [cellToks, hwr, if_pos h1]
  · have h1 : ¬ D.cb.getD p0 0 = 1 := by
      simp only [Cnd.eval, decide_eq_false_iff_not, gU', hGg.kc.one] at hc; exact hc
    refine Hs.mono (cellWirP_spec D Λ hOk hΛ gL gE (by decide) (by decide) g hGg tp ps gL' gE' hdiv hmod)
      (by omega) ?_
    rintro x ⟨hx1, hx2⟩
    refine ⟨hext _ _ (hx1.congr ?_), hfr _ hx2⟩
    rw [cellToks, hwr, if_neg h1]

/-- The new value of window bit `gJ` under the action of `(q, m)`. -/
def actP : St VV MM :=
  .ite (.lt gJ dS) actCtlP (.seq (.op (.copy gZ gJ)) (.seq (.op (.sub gZ dS))
    (.ite (.lt gZ dTW) actHeadP (.seq (.op (.sub gZ dTW)) actCellP))))

def actT' : List (Fin VV) := [gE, gP, gK, gY, gU, gS, gV, gZ, gL, gB, gX, gT]

def actCost (D : GD) (Λ : ℕ) : ℕ := Λ * (6 * Λ + 40) + headCost D Λ + 12 * Λ + 150

theorem actP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m j : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t) (hR : a.env gR = D.base q m)
    (hj : a.env gJ = j) (hjW : j < D.W) :
    Hs C actP a (actCost D Λ) (fun b => Ext a b (actT D.td D.t D.s D.width q m j) ∧ Fr a b actT') := by
  unfold GD.W windowBits at hjW
  have hAC : actCost D Λ = Λ * (6 * Λ + 40) + headCost D Λ + 12 * Λ + 150 := rfl
  refine Hs.ite (show gJ ≠ dS by decide) (fun hc => ?_) (fun hc => ?_)
  · have hjs : j < D.s := by simpa [Cnd.eval, hj, hG.s] using hc
    refine Hs.mono (actCtlP_spec D Λ hOk hΛ a hG q m j hq hm hR hj) (by omega) ?_
    rintro b ⟨hb1, hb2⟩
    exact ⟨hb1.congr (by simp [actT, hjs]), Fr.weaken hb2 (by simp [ncT, actT'])⟩
  · have hjs : ¬ j < D.s := by simpa [Cnd.eval, hj, hG.s] using hc
    refine Hs.seqc (t1 := 1) (t2 := actCost D Λ - 3) (hs_copy C gZ gJ a (by decide)) (fun b hb => ?_)
      (by omega)
    subst hb
    refine Hs.seqc (t1 := 1) (t2 := actCost D Λ - 5) (hs_sub C gZ dS _ (by decide)
      (by vsimp [hj, hG.s]; omega)) (fun b hb => ?_) (by omega)
    subst hb
    have hG1 : GC D ((a.set gZ (a.env gJ)).set gZ ((a.set gZ (a.env gJ)).env gZ - (a.set gZ (a.env gJ)).env dS)) :=
      hG.of (Ext.of_eq rfl rfl rfl rfl) (T := [gZ]) (by fr_tac) (by decide)
    have hZ : ((a.set gZ (a.env gJ)).set gZ ((a.set gZ (a.env gJ)).env gZ - (a.set gZ (a.env gJ)).env dS)).env gZ =
        j - D.s := by vsimp [hj, hG.s]
    have hE0 : Ext a ((a.set gZ (a.env gJ)).set gZ ((a.set gZ (a.env gJ)).env gZ - (a.set gZ (a.env gJ)).env dS))
        [] := Ext.of_eq rfl rfl rfl rfl
    have hF0 : Fr a ((a.set gZ (a.env gJ)).set gZ ((a.set gZ (a.env gJ)).env gZ - (a.set gZ (a.env gJ)).env dS))
        actT' := by frx [actT']
    refine Hs.mono (t := actCost D Λ - 6) (Hs.ite (show gZ ≠ dTW by decide) (fun hc2 => ?_) (fun hc2 => ?_))
      (by omega) (fun b h => h)
    · have hlt : j - D.s < D.t * D.width := by
        have h := hc2; simp only [Cnd.eval, decide_eq_true_eq] at h; rwa [hZ, hG1.tw] at h
      refine Hs.mono (actHeadP_spec D Λ hOk hΛ _ hG1 q m (j - D.s) hq hm (by vsimp [hR]) hZ hlt)
        (by omega) ?_
      rintro b ⟨hb1, hb2⟩
      refine ⟨(hE0.trans hb1).congr (by simp [actT, hjs, show j < D.s + D.t * D.width by omega]), ?_⟩
      exact hF0.trans (Fr.weaken hb2 (by simp [actHeadBodyT, actT']))
    · have hge : ¬ j - D.s < D.t * D.width := by
        have h := hc2; simp only [Cnd.eval, decide_eq_false_iff_not] at h; rwa [hZ, hG1.tw] at h
      refine Hs.seqc (t1 := 1) (t2 := 12 * Λ + 120) (hs_sub C gZ dTW _ (by decide)
        (by rw [hZ, hG1.tw]; omega)) (fun b hb => ?_) (by omega)
      subst hb
      refine Hs.mono (actCellP_spec D Λ hOk hΛ _ (hG1.of (by exact Ext.of_eq rfl rfl rfl rfl) (T := [gZ])
        (by fr_tac) (by decide)) q m (j - D.s - D.t * D.width) hq hm (by vsimp [hR])
        (by rw [DS.set_env_self, hZ, hG1.tw]) (by omega)) le_rfl ?_
      rintro b ⟨hb1, hb2⟩
      refine ⟨((hE0.trans (by exact Ext.of_eq rfl rfl rfl rfl)).trans hb1).congr ?_, ?_⟩
      · simp only [actT, hjs, if_false, show ¬ j < D.s + D.t * D.width by omega, cellToks]
        cases D.td.wr q m ((j - D.s - D.t * D.width) / D.width) <;> rfl
      · exact (hF0.trans (by frx [actT'])).trans (Fr.weaken hb2 (by simp [actCellT, actT']))

end NearCubicGates.Adapters.Compile
