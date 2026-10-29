import SourceAdapters.Compile.CNFWp

/-!
# Token generator, part A: context, head moves, scanned bits, row tests, fit tests

proof of `lem:multitape-refuter` (the transition circuit reads the finite transition table: the current state and scanned symbols
select a rule, whose head moves must stay in the window). These cell procedures append exactly the token lists
`CNFTokens.rowT` and `CNFTokens.fitsT` of the table `TD.ofBits` read from the stored code bits (store `sCB`).

`GC D Λ a` is the generator context: constants, token cursor at the end, the stored code/input bits with cursors
at `0`, and the data registers holding the request's dimensions `D`. `GD.Ok D Λ` bounds every address and value by
`Λ`, and `64·Λ + 64 ≤ 2^Wd` keeps every cell operation in range.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The dimensions and stored bits the generator reads. -/
structure GD where
  cb : List ℕ
  ib : List ℕ
  t : ℕ
  s : ℕ
  w : ℕ
  width : ℕ
  n : ℕ
  st : ℕ
  o2 : ℕ

def GD.o3 (D : GD) : ℕ := D.o2 + 2 * D.s
def GD.R (D : GD) : ℕ := 1 + D.w + 4 * D.t
def GD.W (D : GD) : ℕ := windowBits D.t D.s D.width
/-- The table read from the stored code bits. -/
def GD.td (D : GD) : TD := TD.ofBits D.cb D.t D.w D.o2 D.o3 D.R
/-- The record base of `(q, m)`. -/
def GD.base (D : GD) (q m : ℕ) : ℕ := D.o3 + (q * 2 ^ D.t + m) * D.R

/-- Size bounds: every address and value is at most `Λ`. -/
structure GD.Ok (D : GD) (Λ : ℕ) : Prop where
  len : D.cb.length = D.o3 + D.s * 2 ^ D.t * D.R
  width : 1 ≤ D.width
  t1 : 1 ≤ D.t
  cb01 : ∀ p, D.cb.getD p 0 ≤ 1
  cbΛ : D.cb.length ≤ Λ
  ibΛ : D.ib.length ≤ Λ
  WΛ : D.W ≤ Λ
  MΛ : 2 ^ D.t ≤ Λ
  wΛ : 2 ^ D.w ≤ Λ
  nΛ : D.n ≤ Λ
  stΛ : D.st ≤ Λ

/-- The generator context. -/
structure GC (D : GD) (a : DS VV MM) : Prop where
  kc : KC a
  tt : TTend a
  cb : a.ram sCB = D.cb
  ib : a.ram sIB = D.ib
  rcb : a.rc sCB = 0
  rib : a.rc sIB = 0
  t : a.env dT = D.t
  s : a.env dS = D.s
  wb : a.env dWb = D.w
  wd : a.env dWd = D.width
  tw : a.env dTW = D.t * D.width
  W : a.env dW = D.W
  M : a.env dM = 2 ^ D.t
  R : a.env dR = D.R
  o2 : a.env dO2 = D.o2
  o3 : a.env dO3 = D.o3
  n : a.env dN = D.n
  st : a.env dSt = D.st
  il : a.env dIL = D.ib.length

/-- The registers the context reads. -/
def gcRegs : List (Fin VV) :=
  [vZ, v1, v2, kc3, kc4, kc5, kc6, kc7, kc8, dT, dS, dWb, dWd, dTW, dW, dM, dR, dO2, dO3, dN, dSt, dIL]

theorem GC.of {D : GD} {a b : DS VV MM} {toks : List RTok} {T : List (Fin VV)} (h : GC D a) (hE : Ext a b toks)
    (hF : Fr a b T) (hT : ∀ y ∈ gcRegs, y ∉ T) : GC D b := by
  have e : ∀ y ∈ gcRegs, b.env y = a.env y := fun y hy => hF y (hT y hy)
  refine ⟨KC.of_fr h.kc hF (fun y hy => hT y (by simp [kcRegs] at hy; simp [gcRegs]; tauto)), h.tt.of_ext hE,
    by rw [hE.ram sCB (by decide), h.cb], by rw [hE.ram sIB (by decide), h.ib], by rw [hE.rcs sCB (by decide), h.rcb],
    by rw [hE.rcs sIB (by decide), h.rib], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e dT (by decide), h.t]
  · rw [e dS (by decide), h.s]
  · rw [e dWb (by decide), h.wb]
  · rw [e dWd (by decide), h.wd]
  · rw [e dTW (by decide), h.tw]
  · rw [e dW (by decide), h.W]
  · rw [e dM (by decide), h.M]
  · rw [e dR (by decide), h.R]
  · rw [e dO2 (by decide), h.o2]
  · rw [e dO3 (by decide), h.o3]
  · rw [e dN (by decide), h.n]
  · rw [e dSt (by decide), h.st]
  · rw [e dIL (by decide), h.il]

theorem GD.rec_lt (D : GD) {q m j : ℕ} (hq : q < D.s) (hm : m < 2 ^ D.t) (hj : j < D.R) :
    D.base q m + j < D.o3 + D.s * 2 ^ D.t * D.R := by
  unfold GD.base
  have h1 : q * 2 ^ D.t + m + 1 ≤ D.s * 2 ^ D.t := by nlinarith
  have h2 : (q * 2 ^ D.t + m + 1) * D.R ≤ D.s * 2 ^ D.t * D.R := Nat.mul_le_mul_right _ h1
  nlinarith

variable {C : Ctx}

/-! ## Head moves -/

/-- `gY := base + 1 + w + 4·ta + 3`, the address of the second move bit. -/
def mvAddr (ta : Fin VV) : St VV MM :=
  .seq (.op (.mul ta kc4 gY)) (.seq (.op (.add gY gR)) (.seq (.op (.add gY dWb)) (.op (.add gY kc4))))

/-- `gV := po + 1` if `gU = 1`, else `po` if `gT = 1`, else `po - 1` (truncated). -/
def mvCalc (po : Fin VV) : St VV MM :=
  .ite (.eq gU v1) (.seq (.op (.copy gV po)) (.op (.inc gV)))
    (.ite (.eq gT v1) (.op (.copy gV po))
      (.seq (.op (.copy gV po)) (.ite (.lt vZ gV) (.op (.sub gV v1)) (.op (.zero gU)))))

/-- `gV := mv(q, m, env ta, env po)` with `gR` the record base of `(q, m)` (scratch `gY gU gT gS`). -/
def mvP (ta po : Fin VV) : St VV MM :=
  .seq (mvAddr ta) (.seq (lookP sCB gY gU) (.seq (.op (.sub gY v1)) (.seq (lookP sCB gY gT) (mvCalc po))))

def mvT : List (Fin VV) := [gY, gU, gS, gV, gT]

theorem mvP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (ta po : Fin VV)
    (hta : ta ∉ mvT) (hpo : po ∉ mvT) (hta4 : ta ≠ kc4)
    (a : DS VV MM) (hG : GC D a) (q m : ℕ) (hq : q < D.s) (hm : m < 2 ^ D.t)
    (hR : a.env gR = D.base q m) (htv : a.env ta < D.t) (hpv : a.env po ≤ Λ) :
    Hs C (mvP ta po) a (14 * Λ + 60)
      (fun b => b.env gV = D.td.mv q m (a.env ta) (a.env po) ∧ Ext a b [] ∧ Fr a b mvT) := by
  have hta' : ta ≠ gY ∧ ta ≠ gU ∧ ta ≠ gS ∧ ta ≠ gV ∧ ta ≠ gT := by simpa [mvT] using hta
  have hpo' : po ≠ gY ∧ po ≠ gU ∧ po ≠ gS ∧ po ≠ gV ∧ po ≠ gT := by simpa [mvT] using hpo
  have hk := hG.kc
  set p3 := D.base q m + (1 + D.w + 4 * a.env ta + 3) with hp3
  have hlt3 : p3 < D.cb.length := by
    rw [hOk.len]; exact D.rec_lt hq hm (by unfold GD.R; omega)
  have hcb := hOk.cbΛ
  have s1 : Hs C (mvAddr ta) a 7 (fun b => b.env gY = p3 ∧ Ext a b [] ∧ Fr a b [gY]) := by
    apply hs_of_wpc
    simp only [mvAddr, wpc, opwp]
    vsimp [hk.k4, hR, hG.wb, hta'.1, Ne.symm hta'.1]
    and_split
    wp_fin
  refine Hs.seqc (t1 := 7) (t2 := 12 * Λ + 45) s1 (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have hGb : GC D b := hG.of hb2 hb3 (by decide)
  refine Hs.seqc (t1 := 6 * p3 + 10) (t2 := 6 * Λ + 25)
    (lookP_at (C := C) sCB gY gU (by decide) (by decide) (by decide) b p3 hb1 hGb.rcb (by rw [hGb.cb]; omega)
      (by omega)) (fun d hd => ?_) (by omega)
  obtain ⟨hd1, hd2, hd3⟩ := hd
  have hGd : GC D d := hGb.of hd2 hd3 (by decide)
  have hdY : d.env gY = p3 := by rw [hd3 gY (by decide), hb1]
  refine Hs.seqc (t1 := 1) (t2 := 6 * Λ + 23)
    (hs_sub C gY v1 d (by decide) (by rw [hdY, hGd.kc.one]; omega)) (fun e he => ?_) (by omega)
  subst he
  have hGe : GC D (d.set gY (d.env gY - d.env v1)) := hGd.of (Ext.of_eq rfl rfl rfl rfl)
    (Fr.set (T := [gY]) d _ (by simp)) (by decide)
  refine Hs.seqc (t1 := 6 * (p3 - 1) + 10) (t2 := 10)
    (lookP_at (C := C) sCB gY gT (by decide) (by decide) (by decide) _ (p3 - 1)
      (by vsimp [hdY, hGd.kc.one]) hGe.rcb (by rw [hGe.cb]; omega) (by omega)) (fun g hg => ?_) (by omega)
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hgpo : g.env po = a.env po := by
    rw [hg3 po (by simp [hpo'.2.2.1, hpo'.2.2.2.2]), DS.set_env_ne _ _ hpo'.1,
      hd3 po (by simp [hpo'.2.2.1, hpo'.2.1]), hb3 po (by simp [hpo'.1])]
  have hgU : g.env gU = D.cb.getD p3 0 := by
    rw [hg3 gU (by decide)]; vsimp [hd1, hGb.cb]
  rw [hGe.cb] at hg1
  have hg1' : g.env v1 = 1 := by rw [hg3 v1 (by decide)]; vsimp [hGd.kc.one]
  have hg0 : g.env vZ = 0 := by rw [hg3 vZ (by decide)]; vsimp [hGd.kc.z]
  have hval : D.td.mv q m (a.env ta) (a.env po) = if D.cb.getD p3 0 = 1 then a.env po + 1
      else if D.cb.getD (p3 - 1) 0 = 1 then a.env po else a.env po - 1 := by
    simp only [GD.td, TD.ofBits, bitAt, decide_eq_true_eq]
    rw [show D.o3 + (q * 2 ^ D.t + m) * D.R = D.base q m from rfl,
      show D.base q m + 1 + D.w + 4 * a.env ta + 3 = p3 by omega,
      show D.base q m + 1 + D.w + 4 * a.env ta + 2 = p3 - 1 by omega]
  have hde : Ext d (d.set gY (d.env gY - d.env v1)) [] := Ext.of_eq rfl rfl rfl rfl
  have hext : ∀ x, Ext g x [] → Ext a x [] := fun x hx =>
    ((hb2.trans hd2).trans (hde.trans (hg2.trans hx))).congr (by simp)
  have hfr : ∀ x, Fr g x mvT → Fr a x mvT := fun x hx =>
    ((Fr.weaken hb3 (by simp [mvT])).trans (Fr.weaken hd3 (by simp [mvT]))).trans
      ((Fr.set d _ (by simp [mvT])).trans ((Fr.weaken hg3 (by simp [mvT])).trans hx))
  have hVpo : gV ≠ po := Ne.symm hpo'.2.2.2.1
  generalize D.cb.getD p3 0 = c3 at hgU hval
  generalize D.cb.getD (p3 - 1) 0 = c2 at hg1 hval
  apply hs_of_wpc
  simp only [mvCalc, wpc, opwp, Cnd.eval, Cnd.wf]
  vsimp [hg1, hgU, hgpo, hg1', hg0, hval, hVpo]
  by_cases h3 : c3 = 1 <;> by_cases h2 : c2 = 1 <;> by_cases hp0 : a.env po = 0 <;>
    simp only [h3, h2, hp0, if_true, if_false, true_implies, not_true_eq_false, false_implies, not_false_eq_true,
      and_true, true_and, implies_true, Nat.lt_irrefl, Nat.pos_iff_ne_zero, ne_eq] <;> and_split <;>
    first | omega | exact hext _ (Ext.of_eq rfl rfl rfl rfl) | exact hfr _ (by frx [mvT]) | skip

/-! ## Scanned bits -/

/-- Body of `scannedT`: `wir head(ta,pos), wir cell(ta,pos), conj` (tape in `gA`, position in `gB`). -/
def scanBodyP : St VV MM :=
  .seq (.op (.mul dWd gA gY)) (.seq (.op (.add gY gB)) (.seq (.op (.add gY dS)) (.seq (emitWir gY)
    (.seq (.op (.add gY dTW)) (.seq (emitWir gY) (emitR kc4))))))

theorem scanBodyP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (ta pos : ℕ) (hta : a.env gA = ta) (hpos : a.env gB = pos) (ht : ta < D.t)
    (hp : pos < D.width) :
    Hs C scanBodyP a 25 (fun b => Ext a b [.wir (headI D.s D.width ta pos), .wir (cellI D.t D.s D.width ta pos),
      .conj] ∧ Fr a b [gY, gX]) := by
  have hk := hG.kc
  have hT := hG.tt
  unfold TTend at hT
  have hWl : D.s + (D.t * D.width + D.t * D.width) ≤ Λ := hOk.WΛ
  have h1 : D.width * ta + pos < D.t * D.width := by nlinarith
  apply hs_of_wpc
  simp only [scanBodyP, emitWir, emitR, wpc, opwp]
  vsimp [hk.k4, hk.k8, hk.two, hta, hpos, hG.wd, hG.s, hG.tw, DS.put, putAt, hT]
  and_split
  all_goals try omega
  all_goals try fr_tac
  ext_tac [hT, headI, cellI]

/-- `scannedT t s width ta` (tape in `gA`). -/
def scannedP : St VV MM := anyP gB dWd scanBodyP

def scannedT' : List (Fin VV) := [gB, gY, gX]

theorem scannedP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (ta : ℕ) (hta : a.env gA = ta) (ht : ta < D.t) :
    Hs C scannedP a (34 * Λ + 12) (fun b => Ext a b (scannedT D.t D.s D.width ta) ∧ Fr a b scannedT') := by
  have hwΛ : D.width ≤ Λ := by have := hOk.WΛ; unfold GD.W windowBits at this; nlinarith [hOk.width, hOk.t1]
  refine Hs.mono (anyP_spec gB dWd scanBodyP [gY, gX] (by decide) (by decide)
    (fun b => GC D b ∧ b.env gA = ta) D.width 25 _ (fun b hb => hb.1.wd) (fun b hb => ⟨hb.1.tt, hb.1.kc⟩)
    (fun b d toks hb hE hF => ⟨hb.1.of hE hF (by decide), by rw [hF gA (by decide), hb.2]⟩) (by omega)
    (fun i hi b hb hbi => scanBodyP_spec D Λ hOk hΛ b hb.1 ta i hb.2 hbi ht hi) a ⟨hG, hta⟩)
    (by nlinarith) (fun b h => h)

/-! ## Test bits -/

/-- `gV := (env x / 2 ^ env i) % 2` (scratch `gZ gK gU`). -/
def tbP (x i : Fin VV) : St VV MM :=
  .seq (.op (.copy gZ x)) (.seq (.op (.zero gK)) (.seq (.loop (.lt gK i) (.seq (.op (.half gZ)) (.op (.inc gK))))
    (.op (.dm gZ v2 gU gV))))

theorem tbP_spec (x i : Fin VV) (hx : x ∉ [gZ, gK, gU, gV]) (hi : i ∉ [gZ, gK, gU, gV]) (a : DS VV MM) (hk : KC a)
    (hW : a.env i + 4 < 2 ^ C.Wd) :
    Hs C (tbP x i) a (5 * a.env i + 10) (fun b => b.env gV = (a.env x / 2 ^ a.env i) % 2 ∧ Ext a b [] ∧
      Fr a b [gZ, gK, gU, gV]) := by
  have hx' : x ≠ gZ ∧ x ≠ gK ∧ x ≠ gU ∧ x ≠ gV := by simpa using hx
  have hi' : i ≠ gZ ∧ i ≠ gK ∧ i ≠ gU ∧ i ≠ gV := by simpa using hi
  set I0 := a.env i with hI0
  let I : ℕ → DS VV MM → Prop := fun k b => b.env gK = k ∧ b.env gZ = a.env x / 2 ^ k ∧ Ext a b [] ∧
    Fr a b [gZ, gK, gU, gV]
  have hloop := Hs.loopN (C := C) (c := .lt gK i) (s := .seq (.op (.half gZ)) (.op (.inc gK)))
    (show gK ≠ i from fun h => hi'.2.1 h.symm) I I0 3
    (fun k hk b hb => by
      obtain ⟨h1, h2, h3, h4⟩ := hb
      have hib : b.env i = I0 := h4 i hi
      refine ⟨by simp [Cnd.eval, h1, hib, hk], ?_⟩
      refine Hs.seqc (t1 := 1) (t2 := 1) (hs_half C gZ b) (fun d hd => ?_) (by omega)
      subst hd
      refine Hs.op (OpEx.inc gK _ (by vsimp [h1]; omega)) ⟨by vsimp [h1], by vsimp [h2, Nat.div_div_eq_div_mul,
        pow_succ], h3.trans (Ext.of_eq rfl rfl rfl rfl), ?_⟩
      intro y hy
      have hy' : y ≠ gZ ∧ y ≠ gK ∧ y ≠ gU ∧ y ≠ gV := by simpa using hy
      simp [DS.set, Function.update_apply, hy'.1, hy'.2.1, h4 y hy])
    (fun b hb => by
      obtain ⟨h1, _, _, h4⟩ := hb
      simp [Cnd.eval, h1, h4 i hi, hI0])
  refine Hs.seqc (t1 := 1) (t2 := 5 * I0 + 8) (hs_copy C gZ x a (Ne.symm hx'.1)) (fun b hb => ?_) (by omega)
  subst hb
  refine Hs.seqc (t1 := 1) (t2 := 5 * I0 + 6) (hs_zero C gK _) (fun d hd => ?_) (by omega)
  subst hd
  refine Hs.seqc (t1 := I0 * (3 + 2) + 2) (t2 := 1) (hloop _ ⟨by simp, by vsimp [Ne.symm hx'.1],
    Ext.of_eq rfl rfl rfl rfl, by fr_tac⟩) (fun e he => ?_) (by omega)
  obtain ⟨h1, h2, h3, h4⟩ := he
  have h2' : e.env v2 = 2 := by rw [h4 v2 (by decide)]; exact hk.two
  refine Hs.op (OpEx.dm gZ v2 gU gV e (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [h2']; norm_num) (by rw [h2']; omega)) ⟨by vsimp [h2, h2'], h3.trans (Ext.of_eq rfl rfl rfl rfl), ?_⟩
  intro y hy
  have hy' : y ≠ gZ ∧ y ≠ gK ∧ y ≠ gU ∧ y ≠ gV := by simpa using hy
  simp [DS.set, Function.update_apply, hy'.1, hy'.2.1, hy'.2.2.1, hy'.2.2.2, h4 y hy]

theorem testBit_eq_div (m i : ℕ) : m.testBit i = decide ((m / 2 ^ i) % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]

/-! ## Row tests -/

/-- Body of the scan pattern: the scanned bit of tape `gA`, negated when bit `gA` of the mask `gM` is clear. -/
def scanPatBodyP : St VV MM :=
  .seq scannedP (.seq (tbP gM gA) (.ite (.eq gV v1) (.op (.zero gU)) (emitR kc3)))

def scanPatT' : List (Fin VV) := [gB, gY, gX, gZ, gK, gU, gV]

theorem scanPatBodyP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (ta m : ℕ) (hta : a.env gA = ta) (hm : a.env gM = m) (ht : ta < D.t) :
    Hs C scanPatBodyP a (40 * Λ + 40) (fun b => Ext a b (scannedT D.t D.s D.width ta ++
      (if m.testBit ta then [] else [.neg])) ∧ Fr a b scanPatT') := by
  have htΛ : D.t ≤ Λ := by
    have h1 := hOk.MΛ
    have h2 : D.t < 2 ^ D.t := Nat.lt_two_pow_self
    omega
  refine Hs.seqc (t1 := 34 * Λ + 12) (t2 := 6 * Λ + 20) (scannedP_spec D Λ hOk hΛ a hG ta hta ht)
    (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hb2⟩ := hb
  have hGb : GC D b := hG.of hb1 hb2 (by decide)
  have hbA : b.env gA = ta := by rw [hb2 gA (by decide), hta]
  have hbM : b.env gM = m := by rw [hb2 gM (by decide), hm]
  refine Hs.seqc (t1 := 5 * ta + 10) (t2 := 3) (Hs.mono (tbP_spec (C := C) gM gA (by decide) (by decide) b hGb.kc
    (by rw [hbA]; omega)) (by rw [hbA]) (fun d hd => hd)) (fun d hd => ?_) (by omega)
  obtain ⟨hd1, hd2, hd3⟩ := hd
  have hGd : GC D d := hGb.of hd2 hd3 (by decide)
  rw [hbM, hbA] at hd1
  have hfr : ∀ e, Fr d e [gU] → Fr a e scanPatT' := fun e he =>
    (Fr.weaken hb2 (by simp [scannedT', scanPatT'])).trans ((Fr.weaken hd3 (by simp [scanPatT'])).trans
      (Fr.weaken he (by simp [scanPatT'])))
  have hone : d.env v1 = 1 := hGd.kc.one
  refine Hs.ite (show gV ≠ v1 by decide) (fun hc => ?_) (fun hc => ?_)
  · have hbit : m.testBit ta = true := by
      simp only [Cnd.eval, decide_eq_true_eq, hd1, hone] at hc
      rw [testBit_eq_div, hc]; rfl
    refine Hs.mono (hs_zero C gU d) (by omega) ?_
    rintro e rfl
    refine ⟨(hb1.trans (hd2.trans (Ext.of_eq (b := d.set gU 0) rfl rfl rfl rfl))).congr (by simp [hbit]),
      hfr _ (by fr_tac)⟩
  · have hbit : m.testBit ta = false := by
      simp only [Cnd.eval, decide_eq_false_iff_not, hd1, hone] at hc
      rw [testBit_eq_div]; simpa using hc
    refine Hs.mono (emitR_spec kc3 .neg d hGd.tt (by rw [hGd.kc.k3]; rfl)) (by omega) ?_
    rintro e ⟨he1, he2⟩
    refine ⟨(hb1.trans (hd2.trans he1)).congr (by simp [hbit]), hfr _ (Fr.weaken he2 (by simp))⟩

/-- `rowT t s width q m` (state in `gQ`, mask in `gM`). -/
def rowP : St VV MM := .seq (emitWir gQ) (.seq (allP gA dT scanPatBodyP) (emitR kc4))

def rowT' : List (Fin VV) := [gA, gB, gY, gX, gZ, gK, gU, gV]

theorem rowP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q m : ℕ) (hq : a.env gQ = q) (hm : a.env gM = m) (hqs : q < D.s) :
    Hs C rowP a (50 * Λ * Λ + 50 * Λ + 30) (fun b => Ext a b (rowT D.t D.s D.width q m) ∧ Fr a b rowT') := by
  have htΛ : D.t ≤ Λ := by
    have h1 := hOk.MΛ
    have h2 : D.t < 2 ^ D.t := Nat.lt_two_pow_self
    omega
  have hsΛ : D.s ≤ Λ := by have := hOk.WΛ; unfold GD.W windowBits at this; omega
  refine Hs.seqc (t1 := 5) (t2 := 50 * Λ * Λ + 50 * Λ + 24) (emitWir_spec gQ (by decide) (by decide) a hG.tt hG.kc
    (by rw [hq]; omega)) (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hb2⟩ := hb
  have hGb : GC D b := hG.of hb1 hb2 (by decide)
  refine Hs.seqc (t1 := D.t * (40 * Λ + 40 + 4) + D.t * 5 + 12) (t2 := 1)
    (allP_spec gA dT scanPatBodyP scanPatT' (by decide) (by decide) (fun d => GC D d ∧ d.env gM = m) D.t
      (40 * Λ + 40) _ (fun d hd => hd.1.t) (fun d hd => ⟨hd.1.tt, hd.1.kc⟩)
      (fun d e toks hd hE hF => ⟨hd.1.of hE hF (by decide), by rw [hF gM (by decide), hd.2]⟩) (by omega)
      (fun i hi d hd hdi => scanPatBodyP_spec D Λ hOk hΛ d hd.1 i m hdi hd.2 hi) b
      ⟨hGb, by rw [hb2 gM (by decide), hm]⟩) (fun d hd => ?_) (by nlinarith)
  obtain ⟨hd1, hd2⟩ := hd
  have hGd : GC D d := hGb.of hd1 hd2 (by decide)
  refine Hs.mono (emitR_spec kc4 .conj d hGd.tt (by rw [hGd.kc.k4]; rfl)) le_rfl ?_
  rintro e ⟨he1, he2⟩
  refine ⟨(hb1.trans (hd1.trans he1)).congr (by simp [rowT, hq]), ?_⟩
  exact (Fr.weaken hb2 (by simp [rowT'])).trans ((Fr.weaken hd2 (by simp [rowT', scanPatT'])).trans
    (Fr.weaken he2 (by simp)))

end NearCubicGates.Adapters.Compile
