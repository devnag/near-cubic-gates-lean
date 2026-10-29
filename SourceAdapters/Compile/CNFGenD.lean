import SourceAdapters.Compile.CNFGenC

/-!
# Token generator, part D: selected values, transition bits, the round template

proof of `lem:multitape-refuter`: the next value of every window bit is selected from the finite table (`valT`, `transT`); one
round of the tableau is the vector of all window bits (`tmplT`, equal to `CNFRpn.roundToks` by
`CNFTokens.tmplT_eq` and `CNFCodeBits.ofBits_rep`). `tmplP` appends exactly `tmplT` of the table `GD.td`.
-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {C : Ctx}

/-- `gY := o2 + 2·gQ`. -/
def hlAddrP : St VV MM := .seq (.op (.mul gQ v2 gY)) (.op (.add gY dO2))

/-- The selected value of `(q, m)` for window bit `gJ` (record base in `gR`). -/
def valP : St VV MM :=
  .seq hlAddrP (.seq (lookP sCB gY gU) (.ite (.eq gU v1) (emitWir gJ) (.seq (lookP sCB gR gU)
    (.ite (.eq gU v1) (.seq fitsP (.seq actP (emitR kc4))) (emitR vZ)))))

def valT' : List (Fin VV) := [gE, gP, gK, gY, gU, gS, gV, gZ, gL, gB, gX, gT, gA]

def valCost (D : GD) (Λ : ℕ) : ℕ := fitsCost D Λ + actCost D Λ + 12 * Λ + 60

theorem valP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m j : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t) (hQ : a.env gQ = q)
    (hR : a.env gR = D.base q m) (hj : a.env gJ = j) (hjW : j < D.W) :
    Hs C valP a (valCost D Λ) (fun b => Ext a b (valT D.td D.t D.s D.width q m j) ∧ Fr a b valT') := by
  have hcb := hOk.cbΛ
  have hW := hOk.WΛ
  have hVC : valCost D Λ = fitsCost D Λ + actCost D Λ + 12 * Λ + 60 := rfl
  have hhl : D.o2 + 2 * q < D.cb.length := by
    have := D.rec_lt hq hm (j := 0) (by unfold GD.R; omega)
    unfold GD.base GD.o3 at this; rw [hOk.len]; unfold GD.o3; omega
  have hpr : D.base q m < D.cb.length := by
    have := D.rec_lt hq hm (j := 0) (by unfold GD.R; omega); rw [hOk.len]; omega
  have s1 : Hs C hlAddrP a 3 (fun b => b.env gY = D.o2 + 2 * q ∧ Ext a b [] ∧ Fr a b [gY]) := by
    apply hs_of_wpc
    simp only [hlAddrP, wpc, opwp]
    vsimp [hQ, hG.kc.two, hG.o2]
    and_split
    all_goals first | omega | exact Ext.of_eq rfl rfl rfl rfl | fr_tac | skip
  refine Hs.seqc (t1 := 3) (t2 := valCost D Λ - 4) s1 (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have hGb : GC D b := hG.of hb2 hb3 (by decide)
  refine Hs.seqc (t1 := 6 * (D.o2 + 2 * q) + 10) (t2 := valCost D Λ - 6 * (D.o2 + 2 * q) - 15)
    (lookP_at (C := C) sCB gY gU (by decide) (by decide) (by decide) b _ hb1 hGb.rcb (by rw [hGb.cb]; omega)
      (by omega)) (fun d hd => ?_) (by omega)
  obtain ⟨hd1, hd2, hd3⟩ := hd
  rw [hGb.cb] at hd1
  have hGd : GC D d := hGb.of hd2 hd3 (by decide)
  have dJ : d.env gJ = j := by rw [hd3 gJ (by decide), hb3 gJ (by decide), hj]
  have dR : d.env gR = D.base q m := by rw [hd3 gR (by decide), hb3 gR (by decide), hR]
  have hext : ∀ x toks, Ext d x toks → Ext a x toks := fun x toks hx => ((hb2.trans hd2).trans hx).congr (by simp)
  have hfr : ∀ x T, (∀ y ∈ T, y ∈ valT') → Fr d x T → Fr a x valT' := fun x T hT hx =>
    (Fr.weaken hb3 (by simp [valT'])).trans ((Fr.weaken hd3 (by simp [valT'])).trans (Fr.weaken hx hT))
  have hhlv : D.td.hl q = decide (D.cb.getD (D.o2 + 2 * q) 0 = 1) := rfl
  refine Hs.mono (t := (valCost D Λ - 6 * (D.o2 + 2 * q) - 16) + 1) (Hs.ite (c := .eq gU v1) (show gU ≠ v1 by decide)
    (fun hc => ?_) (fun hc => ?_)) (by omega) (fun b h => h)
  · have h1 : D.cb.getD (D.o2 + 2 * q) 0 = 1 := by
      simp only [Cnd.eval, decide_eq_true_eq, hd1, hGd.kc.one] at hc; exact hc
    refine Hs.mono (emitWir_spec gJ (by decide) (by decide) d hGd.tt hGd.kc (by rw [dJ]; omega)) (by omega) ?_
    rintro x ⟨hx1, hx2⟩
    refine ⟨hext _ _ (hx1.congr ?_), hfr _ _ (by simp [valT']) hx2⟩
    rw [dJ, valT, hhlv, if_pos (by simpa using h1)]
  · have h1 : ¬ D.cb.getD (D.o2 + 2 * q) 0 = 1 := by
      simp only [Cnd.eval, decide_eq_false_iff_not, hd1, hGd.kc.one] at hc; exact hc
    have hv : valT D.td D.t D.s D.width q m j = if D.td.pr q m then fitsT D.td D.t D.s D.width q m ++
        actT D.td D.t D.s D.width q m j ++ [.conj] else [.cst false] := by
      rw [valT, hhlv, if_neg (by simpa using h1)]
    refine Hs.seqc (t1 := 6 * D.base q m + 10) (t2 := fitsCost D Λ + actCost D Λ + 4)
      (lookP_at (C := C) sCB gR gU (by decide) (by decide) (by decide) d _ dR hGd.rcb (by rw [hGd.cb]; omega)
        (by omega)) (fun e he => ?_) (by omega)
    obtain ⟨he1, he2, he3⟩ := he
    rw [hGd.cb] at he1
    have hGe : GC D e := hGd.of he2 he3 (by decide)
    have eJ : e.env gJ = j := by rw [he3 gJ (by decide), dJ]
    have eR : e.env gR = D.base q m := by rw [he3 gR (by decide), dR]
    have hprv : D.td.pr q m = decide (D.cb.getD (D.base q m) 0 = 1) := rfl
    refine Hs.ite (show gU ≠ v1 by decide) (fun hc2 => ?_) (fun hc2 => ?_)
    · have h2 : D.cb.getD (D.base q m) 0 = 1 := by
        simp only [Cnd.eval, decide_eq_true_eq, he1, hGe.kc.one] at hc2; exact hc2
      refine Hs.seqc (t1 := fitsCost D Λ) (t2 := actCost D Λ + 2) (fitsP_spec D Λ hOk hΛ e hGe q m hq hm eR)
        (fun f hf => ?_) (by omega)
      obtain ⟨hf1, hf2⟩ := hf
      have hGf : GC D f := hGe.of hf1 hf2 (by decide)
      refine Hs.seqc (t1 := actCost D Λ) (t2 := 1) (actP_spec D Λ hOk hΛ f hGf q m j hq hm
        (by rw [hf2 gR (by decide), eR]) (by rw [hf2 gJ (by decide), eJ]) hjW) (fun g hg => ?_) (by omega)
      obtain ⟨hg1, hg2⟩ := hg
      have hGg : GC D g := hGf.of hg1 hg2 (by decide)
      refine Hs.mono (emitR_spec kc4 .conj g hGg.tt (by rw [hGg.kc.k4]; rfl)) le_rfl ?_
      rintro x ⟨hx1, hx2⟩
      refine ⟨hext _ _ ((he2.trans (hf1.trans (hg1.trans hx1))).congr ?_), ?_⟩
      · rw [hv, hprv, if_pos (by simpa using h2)]; simp
      · exact hfr _ valT' (fun y hy => hy) ((Fr.weaken he3 (by simp [valT'])).trans ((Fr.weaken hf2
          (by simp [fitsT', valT'])).trans ((Fr.weaken hg2 (by simp [actT', valT'])).trans (Fr.weaken hx2 (by simp)))))
    · have h2 : ¬ D.cb.getD (D.base q m) 0 = 1 := by
        simp only [Cnd.eval, decide_eq_false_iff_not, he1, hGe.kc.one] at hc2; exact hc2
      refine Hs.mono (emitR_spec vZ (.cst false) e hGe.tt (by rw [hGe.kc.z]; rfl)) (by omega) ?_
      rintro x ⟨hx1, hx2⟩
      refine ⟨hext _ _ ((he2.trans hx1).congr ?_), ?_⟩
      · rw [hv, hprv, if_neg (by simpa using h2)]; simp
      · exact hfr _ valT' (fun y hy => hy) ((Fr.weaken he3 (by simp [valT'])).trans (Fr.weaken hx2 (by simp)))

/-! ## One transition bit and the round -/

/-- `gR := o3 + (gQ·2^t + gM)·R`. -/
def baseP : St VV MM :=
  .seq (.op (.mul gQ dM gY)) (.seq (.op (.add gY gM)) (.seq (.op (.mul gY dR gR)) (.op (.add gR dO3))))

def transBodyP : St VV MM := .seq baseP (.seq rowP (.seq valP (emitR kc4)))

def transBodyT : List (Fin VV) := [gR, gE, gP, gK, gY, gU, gS, gV, gZ, gL, gB, gX, gT, gA]

def bodyCost (D : GD) (Λ : ℕ) : ℕ := 50 * Λ * Λ + 50 * Λ + valCost D Λ + 50

theorem transBodyP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m j : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t) (hQ : a.env gQ = q) (hM : a.env gM = m)
    (hj : a.env gJ = j) (hjW : j < D.W) :
    Hs C transBodyP a (bodyCost D Λ) (fun b => Ext a b (rowT D.t D.s D.width q m ++
      valT D.td D.t D.s D.width q m j ++ [.conj]) ∧ Fr a b transBodyT) := by
  have hcb := hOk.cbΛ
  have hBC : bodyCost D Λ = 50 * Λ * Λ + 50 * Λ + valCost D Λ + 50 := rfl
  have hb0 := D.rec_lt hq hm (j := 0) (by unfold GD.R; omega)
  rw [hOk.len] at hcb
  have hqm : (q * 2 ^ D.t + m) * D.R ≤ Λ := by unfold GD.base at hb0; omega
  have hq2 : q * 2 ^ D.t + m ≤ (q * 2 ^ D.t + m) * D.R := Nat.le_mul_of_pos_right _ (by unfold GD.R; omega)
  have hq1 : q * 2 ^ D.t ≤ q * 2 ^ D.t + m := Nat.le_add_right _ _
  have s1 : Hs C baseP a 7 (fun b => b.env gR = D.base q m ∧ Ext a b [] ∧ Fr a b [gY, gR]) := by
    apply hs_of_wpc
    simp only [baseP, wpc, opwp]
    vsimp [hQ, hM, hG.M, hG.R, hG.o3]
    and_split
    all_goals first | omega | exact Ext.of_eq rfl rfl rfl rfl | fr_tac | (unfold GD.base; ring) | skip
  refine Hs.seqc (t1 := 7) (t2 := bodyCost D Λ - 8) s1 (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have hGb : GC D b := hG.of hb2 hb3 (by decide)
  refine Hs.seqc (t1 := 50 * Λ * Λ + 50 * Λ + 30) (t2 := valCost D Λ + 2) (rowP_spec D Λ hOk hΛ b hGb q m
    (by rw [hb3 gQ (by decide), hQ]) (by rw [hb3 gM (by decide), hM]) hq) (fun d hd => ?_) (by omega)
  obtain ⟨hd1, hd2⟩ := hd
  have hGd : GC D d := hGb.of hd1 hd2 (by decide)
  refine Hs.seqc (t1 := valCost D Λ) (t2 := 1) (valP_spec D Λ hOk hΛ d hGd q m j hq hm
    (by rw [hd2 gQ (by decide), hb3 gQ (by decide), hQ]) (by rw [hd2 gR (by decide), hb1])
    (by rw [hd2 gJ (by decide), hb3 gJ (by decide), hj]) hjW) (fun e he => ?_) (by omega)
  obtain ⟨he1, he2⟩ := he
  have hGe : GC D e := hGd.of he1 he2 (by decide)
  refine Hs.mono (emitR_spec kc4 .conj e hGe.tt (by rw [hGe.kc.k4]; rfl)) le_rfl ?_
  rintro x ⟨hx1, hx2⟩
  refine ⟨(hb2.trans (hd1.trans (he1.trans hx1))).congr (by simp), ?_⟩
  exact (Fr.weaken hb3 (by simp [transBodyT])).trans ((Fr.weaken hd2 (by simp [rowT', transBodyT])).trans
    ((Fr.weaken he2 (by simp [valT', transBodyT])).trans (Fr.weaken hx2 (by simp))))

/-- The next value of window bit `gJ`. -/
def transP : St VV MM := anyP gQ dS (anyP gM dM transBodyP)

def transCost (D : GD) (Λ : ℕ) : ℕ :=
  D.s * ((2 ^ D.t * (bodyCost D Λ + 4) + 2 ^ D.t * 5 + 12) + 4) + D.s * 5 + 12

theorem transP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (j : ℕ) (hj : a.env gJ = j) (hjW : j < D.W) :
    Hs C transP a (transCost D Λ) (fun b => Ext a b (transT D.td D.t D.s D.width j) ∧
      Fr a b (gQ :: gM :: transBodyT)) := by
  have hsΛ := D.s_le Λ hOk
  have hMΛ := hOk.MΛ
  exact anyP_spec gQ dS (anyP gM dM transBodyP) (gM :: transBodyT) (by decide) (by decide)
    (fun b => GC D b ∧ b.env gJ = j) D.s _ _ (fun b hb => hb.1.s) (fun b hb => ⟨hb.1.tt, hb.1.kc⟩)
    (fun b d toks hb hE hF => ⟨hb.1.of hE hF (by decide), by rw [hF gJ (by decide), hb.2]⟩) (by omega)
    (fun q hq b hb hbQ => anyP_spec gM dM transBodyP transBodyT (by decide) (by decide)
      (fun d => (GC D d ∧ d.env gJ = j) ∧ d.env gQ = q) (2 ^ D.t) (bodyCost D Λ) _
      (fun d hd => hd.1.1.M) (fun d hd => ⟨hd.1.1.tt, hd.1.1.kc⟩)
      (fun d e toks hd hE hF => ⟨⟨hd.1.1.of hE hF (by decide), by rw [hF gJ (by decide), hd.1.2]⟩,
        by rw [hF gQ (by decide), hd.2]⟩) (by omega)
      (fun m hm d hd hdM => transBodyP_spec D Λ hOk hΛ d hd.1.1 q m j hq hm hd.2 hdM hd.1.2 hjW) b ⟨hb, hbQ⟩)
    a ⟨hG, hj⟩

/-- **One round of the tableau**: every window bit, saved, then swap (`tmplT`). -/
def tmplP : St VV MM := .seq (forP gJ dW (.seq transP (emitR kc6))) (emitR kc7)

def tmplT' : List (Fin VV) := gJ :: gQ :: gM :: transBodyT

def tmplCost (D : GD) (Λ : ℕ) : ℕ := D.W * ((transCost D Λ + 1 + 1) + 4) + 4 + 1 + 1

theorem tmplP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) :
    Hs C tmplP a (tmplCost D Λ) (fun b => Ext a b (tmplT D.td D.t D.s D.width) ∧ Fr a b tmplT') := by
  have hWΛ := hOk.WΛ
  refine Hs.seqc (t1 := D.W * ((transCost D Λ + 1 + 1) + 4) + 4) (t2 := 1)
    (forP_spec gJ dW (.seq transP (emitR kc6)) (gQ :: gM :: transBodyT) (by decide) (by decide) (GC D)
      D.W (transCost D Λ + 1 + 1) (fun j => transT D.td D.t D.s D.width j ++ [.save]) (fun b hb => hb.W)
      (fun b d toks hb hE hF => hb.of hE hF (by decide)) (by omega)
      (fun j hj b hb hbJ => Hs.seq (transP_spec D Λ hOk hΛ b hb j hbJ hj) (fun d ⟨hd1, hd2⟩ => by
        have hGd : GC D d := hb.of hd1 hd2 (by decide)
        refine Hs.mono (emitR_spec kc6 .save d hGd.tt (by rw [hGd.kc.k6]; rfl)) le_rfl ?_
        rintro e ⟨he1, he2⟩
        exact ⟨hd1.trans he1, hd2.trans (Fr.weaken he2 (by simp))⟩)) a hG) (fun b hb => ?_) (by unfold tmplCost; omega)
  obtain ⟨hb1, hb2⟩ := hb
  have hGb : GC D b := hG.of hb1 hb2 (by decide)
  refine Hs.mono (emitR_spec kc7 .swap b hGb.tt (by rw [hGb.kc.k7]; rfl)) le_rfl ?_
  rintro e ⟨he1, he2⟩
  exact ⟨(hb1.trans he1).congr (by simp [tmplT, GD.W]), hb2.trans (Fr.weaken he2 (by simp))⟩

end NearCubicGates.Adapters.Compile
