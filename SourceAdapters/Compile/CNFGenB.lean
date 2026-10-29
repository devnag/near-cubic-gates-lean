import SourceAdapters.Compile.CNFGenA

/-!
# Token generator, part B: fit tests and action values

proof of `lem:multitape-refuter`: a rule fires only when every head move stays in the window (`fitsT`), and then sets the next
control, the moved heads and the written cells (`actT`). These cell procedures append exactly `CNFTokens.fitsT` and
`CNFTokens.actT` of the table `GD.td` read from the stored code bits.
-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {C : Ctx}

theorem GD.t_le (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) : D.t ≤ Λ := by
  have h1 := hOk.MΛ
  have h2 : D.t < 2 ^ D.t := Nat.lt_two_pow_self
  omega

theorem GD.s_le (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) : D.s ≤ Λ := by
  have := hOk.WΛ; unfold GD.W windowBits at this; omega

theorem GD.width_le (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) : D.width ≤ Λ := by
  have := hOk.WΛ; unfold GD.W windowBits at this; nlinarith [hOk.width, hOk.t1]

theorem GD.head_lt (D : GD) {ta pos : ℕ} (ht : ta < D.t) (hp : pos < D.width) :
    D.width * ta + pos < D.t * D.width := by nlinarith

/-! ## Fit tests -/

/-- `gY := head(gA, gB)`, then `wir gY`. -/
def headWirP (ta po : Fin VV) : St VV MM :=
  .seq (.op (.mul dWd ta gY)) (.seq (.op (.add gY po)) (.seq (.op (.add gY dS)) (emitWir gY)))

theorem headWirP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (ta po : Fin VV)
    (hta : ta ∉ [gY, gX, dWd, dS]) (hpo : po ∉ [gY, gX, dWd, dS]) (a : DS VV MM) (hG : GC D a) (tv pv : ℕ)
    (htv : a.env ta = tv) (hpv : a.env po = pv) (ht : tv < D.t) (hp : pv < D.width) :
    Hs C (headWirP ta po) a 12 (fun b => Ext a b [.wir (headI D.s D.width tv pv)] ∧ Fr a b [gY, gX]) := by
  have hta' : ta ≠ gY ∧ ta ≠ gX ∧ ta ≠ dWd ∧ ta ≠ dS := by simpa using hta
  have hpo' : po ≠ gY ∧ po ≠ gX ∧ po ≠ dWd ∧ po ≠ dS := by simpa using hpo
  have hk := hG.kc
  have hT := hG.tt
  unfold TTend at hT
  have hWl : D.s + (D.t * D.width + D.t * D.width) ≤ Λ := hOk.WΛ
  have h1 := D.head_lt ht hp
  apply hs_of_wpc
  simp only [headWirP, emitWir, emitR, wpc, opwp]
  vsimp [hk.k8, hk.two, htv, hpv, hG.wd, hG.s, DS.put, putAt, hT, Ne.symm hta'.2.2.1, hta'.1, hpo'.1,
    Ne.symm hta'.1, Ne.symm hpo'.1]
  and_split
  all_goals try omega
  all_goals try fr_tac
  ext_tac [hT, headI]

/-- After `mvP`: `cst (gV < width)` (or `= gE` for the head target), then `conj`. -/
def cmpTailP (c : Cnd VV) : St VV MM := .seq (.ite c (emitR kc8) (emitR vZ)) (emitR kc4)

theorem cmpTailP_spec (c : Cnd VV) (hc : c.wf) (a : DS VV MM) (hT : TTend a) (hk : KC a) :
    Hs C (cmpTailP c) a 4 (fun b => Ext a b [.cst (c.eval a), .conj] ∧ Fr a b []) := by
  unfold TTend at hT
  apply hs_of_wpc
  simp only [cmpTailP, emitR, wpc, opwp]
  refine ⟨hc, fun he => ?_, fun he => ?_⟩
  · vsimp [hT, DS.put, putAt, hk.k8, hk.k4]
    refine ⟨?_, by fr_tac⟩
    ext_tac [hT, he]
  · vsimp [hT, DS.put, putAt, hk.z, hk.k4]
    refine ⟨?_, by fr_tac⟩
    ext_tac [hT, he]

def fitsBodyP : St VV MM := .seq (headWirP gA gB) (.seq (mvP gA gB) (cmpTailP (.lt gV dWd)))

def fitsBodyT : List (Fin VV) := [gY, gX, gU, gS, gV, gT]

theorem fitsBodyP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m ta pos : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t) (hR : a.env gR = D.base q m)
    (hta : a.env gA = ta) (hpos : a.env gB = pos) (ht : ta < D.t) (hp : pos < D.width) :
    Hs C fitsBodyP a (14 * Λ + 80) (fun b => Ext a b [.wir (headI D.s D.width ta pos),
      .cst (decide (D.td.mv q m ta pos < D.width)), .conj] ∧ Fr a b fitsBodyT) := by
  have hwΛ := D.width_le Λ hOk
  refine Hs.seqc (t1 := 12) (t2 := 14 * Λ + 66) (headWirP_spec D Λ hOk hΛ gA gB (by decide) (by decide) a hG
    ta pos hta hpos ht hp) (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hb2⟩ := hb
  have hGb : GC D b := hG.of hb1 hb2 (by decide)
  refine Hs.seqc (t1 := 14 * Λ + 60) (t2 := 5) (mvP_spec D Λ hOk hΛ gA gB (by decide) (by decide) (by decide) b
    hGb q m hq hm (by rw [hb2 gR (by decide), hR]) (by rw [hb2 gA (by decide), hta]; exact ht)
    (by rw [hb2 gB (by decide), hpos]; omega)) (fun d hd => ?_) (by omega)
  obtain ⟨hd1, hd2, hd3⟩ := hd
  have hGd : GC D d := hGb.of hd2 hd3 (by decide)
  refine Hs.mono (cmpTailP_spec (C := C) (.lt gV dWd) (show gV ≠ dWd by decide) d hGd.tt hGd.kc) (by omega) ?_
  rintro e ⟨he1, he2⟩
  have hbA : b.env gA = ta := by rw [hb2 gA (by decide), hta]
  have hbB : b.env gB = pos := by rw [hb2 gB (by decide), hpos]
  refine ⟨(hb1.trans (hd2.trans he1)).congr ?_, ?_⟩
  · simp [Cnd.eval, hd1, hbA, hbB, hGd.wd]
  · exact (Fr.weaken hb2 (by simp [fitsBodyT])).trans ((Fr.weaken hd3 (by simp [fitsBodyT, mvT])).trans
      (Fr.weaken he2 (by simp)))

/-- `fitsT` of `(q, m)` (record base in `gR`). -/
def fitsP : St VV MM := allP gA dT (anyP gB dWd fitsBodyP)

def fitsT' : List (Fin VV) := [gA, gB, gY, gX, gU, gS, gV, gT]

/-- The cost of `fitsP`. -/
def fitsCost (D : GD) (Λ : ℕ) : ℕ :=
  D.t * ((D.width * ((14 * Λ + 80) + 4) + D.width * 5 + 12) + 4) + D.t * 5 + 12

theorem fitsP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t) (hR : a.env gR = D.base q m) :
    Hs C fitsP a (fitsCost D Λ) (fun b => Ext a b (fitsT D.td D.t D.s D.width q m) ∧ Fr a b fitsT') := by
  have htΛ := D.t_le Λ hOk
  have hwΛ := D.width_le Λ hOk
  exact allP_spec gA dT (anyP gB dWd fitsBodyP) (gB :: fitsBodyT) (by decide) (by decide)
    (fun b => GC D b ∧ b.env gR = D.base q m) D.t _ _ (fun b hb => hb.1.t) (fun b hb => ⟨hb.1.tt, hb.1.kc⟩)
    (fun b d toks hb hE hF => ⟨hb.1.of hE hF (by decide), by rw [hF gR (by decide), hb.2]⟩) (by omega)
    (fun ta hta b hb hbA => anyP_spec gB dWd fitsBodyP fitsBodyT (by decide) (by decide)
      (fun d => (GC D d ∧ d.env gR = D.base q m) ∧ d.env gA = ta) D.width (14 * Λ + 80) _
      (fun d hd => hd.1.1.wd) (fun d hd => ⟨hd.1.1.tt, hd.1.1.kc⟩)
      (fun d e toks hd hE hF => ⟨⟨hd.1.1.of hE hF (by decide), by rw [hF gR (by decide), hd.1.2]⟩,
        by rw [hF gA (by decide), hd.2]⟩) (by omega)
      (fun pos hpos d hd hdB => fitsBodyP_spec D Λ hOk hΛ d hd.1.1 q m ta pos hq hm hd.1.2 hd.2 hdB hta hpos)
      b ⟨hb, hbA⟩) a ⟨hG, hR⟩

/-! ## Next control -/

/-- One bit of the next-control field: `gE += gP·bit(gR + 1 + gK)`, `gP := 2·gP`. -/
def ncBodyP : St VV MM :=
  .seq (.seq (.op (.copy gY gR)) (.seq (.op (.inc gY)) (.op (.add gY gK)))) (.seq (lookP sCB gY gU)
    (.seq (.op (.mul gU gP gV)) (.seq (.op (.add gE gV)) (.seq (.op (.shl gP)) (.op (.inc gK))))))

/-- `gE := nc(q, m)` (scratch `gP gK gY gU gS gV`). -/
def ncP : St VV MM := .seq (.op (.zero gE)) (.seq (.op (.copy gP v1)) (.seq (.op (.zero gK))
  (.loop (.lt gK dWb) ncBodyP)))

def ncT : List (Fin VV) := [gE, gP, gK, gY, gU, gS, gV]

theorem numAt_lt (f : ℕ → Bool) (p : ℕ) : ∀ w, numAt f p w < 2 ^ w := by
  intro w
  induction w with
  | zero => simp [numAt]
  | succ w ih => rw [numAt, pow_succ]; cases f (p + w) <;> simp <;> omega

theorem bitAt_toNat (cb : List ℕ) (p : ℕ) (h : cb.getD p 0 ≤ 1) : (bitAt cb p).toNat = cb.getD p 0 := by
  unfold bitAt
  rcases (by omega : cb.getD p 0 = 0 ∨ cb.getD p 0 = 1) with h0 | h0 <;> rw [h0] <;> rfl

theorem numAt_succ' (f : ℕ → Bool) (p w : ℕ) : numAt f p (w + 1) = numAt f p w + (f (p + w)).toNat * 2 ^ w := rfl

theorem ncP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t) (hR : a.env gR = D.base q m) :
    Hs C ncP a (Λ * (6 * Λ + 40) + 10) (fun b => b.env gE = D.td.nc q m ∧ Ext a b [] ∧ Fr a b ncT) := by
  have hwΛ : D.w < Λ := by
    have h1 := hOk.wΛ
    have h2 : D.w < 2 ^ D.w := Nat.lt_two_pow_self
    omega
  have hcb := hOk.cbΛ
  let I : ℕ → DS VV MM → Prop := fun k b => GC D b ∧ b.env gK = k ∧ b.env gP = 2 ^ k ∧
    b.env gE = numAt (bitAt D.cb) (D.base q m + 1) k ∧ b.env gR = D.base q m ∧ Ext a b [] ∧ Fr a b ncT
  have hloop := Hs.loopN (C := C) (c := .lt gK dWb) (s := ncBodyP) (show gK ≠ dWb by decide) I D.w (6 * Λ + 36)
    (fun k hk b hb => by
      obtain ⟨hGb, h1, h2, h3, h4, h5, h6⟩ := hb
      refine ⟨by simp [Cnd.eval, h1, hGb.wb, hk], ?_⟩
      have hpk : 2 ^ k < Λ := lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hk) hOk.wΛ
      have haddr : D.base q m + (1 + k) < D.cb.length := by
        rw [hOk.len]; exact D.rec_lt hq hm (by unfold GD.R; omega)
      refine Hs.seqc (t1 := 5) (t2 := 6 * Λ + 30) (hs_of_wpc (R := fun d => d.env gY = D.base q m + (1 + k) ∧
          Ext b d [] ∧ Fr b d [gY]) (by simp only [wpc, opwp]; vsimp [h4, h1]; and_split; wp_fin)) (fun d hd => ?_)
        (by omega)
      obtain ⟨hd1, hd2, hd3⟩ := hd
      have hGd : GC D d := hGb.of hd2 hd3 (by decide)
      refine Hs.seqc (t1 := 6 * (D.base q m + (1 + k)) + 10) (t2 := 7)
        (lookP_at (C := C) sCB gY gU (by decide) (by decide) (by decide) d _ hd1 hGd.rcb (by rw [hGd.cb]; omega)
          (by omega)) (fun e he => ?_) (by omega)
      obtain ⟨he1, he2, he3⟩ := he
      rw [hGd.cb] at he1
      have hGe : GC D e := hGd.of he2 he3 (by decide)
      have eK : e.env gK = k := by rw [he3 gK (by decide), hd3 gK (by decide), h1]
      have eP : e.env gP = 2 ^ k := by rw [he3 gP (by decide), hd3 gP (by decide), h2]
      have eE : e.env gE = numAt (bitAt D.cb) (D.base q m + 1) k := by
        rw [he3 gE (by decide), hd3 gE (by decide), h3]
      have eR : e.env gR = D.base q m := by rw [he3 gR (by decide), hd3 gR (by decide), h4]
      have hnum := numAt_lt (bitAt D.cb) (D.base q m + 1) k
      have h01 := hOk.cb01 (D.base q m + (1 + k))
      have hbit : (bitAt D.cb (D.base q m + 1 + k)).toNat = D.cb.getD (D.base q m + (1 + k)) 0 := by
        rw [show D.base q m + 1 + k = D.base q m + (1 + k) by ring]; exact bitAt_toNat _ _ h01
      have hfr : ∀ x, Fr e x ncT → Fr a x ncT := fun x hx =>
        h6.trans ((Fr.weaken hd3 (by simp [ncT])).trans ((Fr.weaken he3 (by simp [ncT])).trans hx))
      have hext : ∀ x, Ext e x [] → Ext a x [] := fun x hx => (h5.trans (hd2.trans (he2.trans hx))).congr (by simp)
      have hnext : numAt (bitAt D.cb) (D.base q m + 1) (k + 1) =
          numAt (bitAt D.cb) (D.base q m + 1) k + D.cb.getD (D.base q m + (1 + k)) 0 * 2 ^ k := by
        rw [numAt_succ', hbit]
      generalize D.cb.getD (D.base q m + (1 + k)) 0 = c at he1 hnext h01
      have hmul : c * 2 ^ k ≤ 2 ^ k := by nlinarith
      apply hs_of_wpc
      simp only [wpc, opwp, I]
      vsimp [he1, eK, eP, eE, eR, hnext, pow_succ]
      and_split
      all_goals first
        | omega
        | exact hGe.of (Ext.of_eq rfl rfl rfl rfl) (T := ncT) (by frx [ncT]) (by decide)
        | ring1
        | exact hext _ (Ext.of_eq rfl rfl rfl rfl)
        | exact hfr _ (by frx [ncT]))
    (fun b hb => by simp [Cnd.eval, hb.2.1, hb.1.wb])
  refine Hs.seqc (t1 := 1) (t2 := Λ * (6 * Λ + 40) + 8) (hs_zero C gE a) (fun b hb => ?_) (by omega)
  subst hb
  refine Hs.seqc (t1 := 1) (t2 := Λ * (6 * Λ + 40) + 6) (hs_copy C gP v1 _ (by decide)) (fun b hb => ?_) (by omega)
  subst hb
  refine Hs.seqc (t1 := 1) (t2 := Λ * (6 * Λ + 40) + 4) (hs_zero C gK _) (fun b hb => ?_) (by omega)
  subst hb
  refine Hs.mono (hloop _ ⟨hG.of (Ext.of_eq rfl rfl rfl rfl) (T := ncT) (by frx [ncT]) (by decide), by vsimp [],
    by vsimp [hG.kc.one], by vsimp [numAt], by vsimp [hR], Ext.of_eq rfl rfl rfl rfl, by frx [ncT]⟩)
    (by nlinarith) ?_
  rintro b ⟨_, _, _, h3, _, h5, h6⟩
  exact ⟨by rw [h3]; rfl, h5, h6⟩

end NearCubicGates.Adapters.Compile