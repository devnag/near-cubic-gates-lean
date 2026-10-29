import SourceAdapters.Compile.CNFGenD

/-!
# Token generator, part E: the initial vector and the acceptance test

proof of `lem:multitape-refuter` (the tableau starts from the native initial configuration: start control, heads at cell 0, the framed
actual input on tape 0 and the framed free witness on tape 1) and proof of `lem:multitape-refuter` (the circuit output tests acceptance
after the last round). `initP` appends exactly `CNFTokens.initT` and `accP` exactly `CNFTokens.accT` of the table read
from the stored code bits.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {C : Ctx}

/-! ## Acceptance -/

/-- `wir q`, `cst (halted q ∧ accepting q)`, `conj` (control index in `gQ`). -/
def accBodyP : St VV MM :=
  .seq (emitWir gQ) (.seq hlAddrP (.seq (lookP sCB gY gU) (.seq (.op (.inc gY)) (.seq (lookP sCB gY gT)
    (.seq (.ite (.eq gU v1) (cstP (.eq gT v1)) (emitR vZ)) (emitR kc4))))))

def accBodyT : List (Fin VV) := [gX, gY, gU, gS, gT]

theorem accBodyP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) (q : ℕ) (hq : q < D.s) (hQ : a.env gQ = q) :
    Hs C accBodyP a (12 * Λ + 60)
      (fun b => Ext a b [.wir q, .cst (D.td.hl q && D.td.ac q), .conj] ∧ Fr a b accBodyT) := by
  have hcb := hOk.cbΛ
  have hsΛ := D.s_le Λ hOk
  have hP : D.o2 + 2 * q + 1 < D.cb.length := by rw [hOk.len]; unfold GD.o3; omega
  refine Hs.seqc (t1 := 5) (t2 := 12 * Λ + 54) (emitWir_spec gQ (by decide) (by decide) a hG.tt hG.kc
    (by rw [hQ]; omega)) (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hb2⟩ := hb
  rw [hQ] at hb1
  have hGb : GC D b := hG.of hb1 hb2 (by decide)
  have bQ : b.env gQ = q := by rw [hb2 gQ (by decide), hQ]
  have s2 : Hs C hlAddrP b 3 (fun d => d.env gY = D.o2 + 2 * q ∧ Ext b d [] ∧ Fr b d [gY]) := by
    apply hs_of_wpc
    simp only [hlAddrP, wpc, opwp]
    vsimp [bQ, hGb.kc.two, hGb.o2]
    and_split
    all_goals first | omega | exact Ext.of_eq rfl rfl rfl rfl | fr_tac | skip
  refine Hs.seqc (t1 := 3) (t2 := 12 * Λ + 50) s2 (fun d hd => ?_) (by omega)
  obtain ⟨hd1, hd2, hd3⟩ := hd
  have hGd : GC D d := hGb.of hd2 hd3 (by decide)
  refine Hs.seqc (t1 := 6 * (D.o2 + 2 * q) + 10) (t2 := 6 * (D.o2 + 2 * q + 1) + 18)
    (lookP_at (C := C) sCB gY gU (by decide) (by decide) (by decide) d _ hd1 hGd.rcb (by rw [hGd.cb]; omega)
      (by omega)) (fun e he => ?_) (by omega)
  obtain ⟨he1, he2, he3⟩ := he
  rw [hGd.cb] at he1
  have hGe : GC D e := hGd.of he2 he3 (by decide)
  have eY : e.env gY = D.o2 + 2 * q := by rw [he3 gY (by decide), hd1]
  refine Hs.seqc (t1 := 1) (t2 := 6 * (D.o2 + 2 * q + 1) + 16) (hs_inc C gY e (by rw [eY]; omega))
    (fun f hf => ?_) (by omega)
  subst hf
  have hGf : GC D (e.set gY (e.env gY + 1)) :=
    hGe.of (Ext.of_eq rfl rfl rfl rfl) (Fr.set e _ (show gY ∈ [gY] by simp)) (by decide)
  refine Hs.seqc (t1 := 6 * (D.o2 + 2 * q + 1) + 10) (t2 := 5)
    (lookP_at (C := C) sCB gY gT (by decide) (by decide) (by decide) _ _ (by simp [eY]) hGf.rcb
      (by rw [hGf.cb]; omega) (by omega)) (fun g hg => ?_) (by omega)
  obtain ⟨hg1, hg2, hg3⟩ := hg
  rw [hGf.cb] at hg1
  have hGg : GC D g := hGf.of hg2 hg3 (by decide)
  have gU' : g.env gU = D.cb.getD (D.o2 + 2 * q) 0 := by
    rw [hg3 gU (by decide), DS.set_env_ne _ _ (show gU ≠ gY by decide), he1]
  have hval : (D.td.hl q && D.td.ac q) =
      (decide (D.cb.getD (D.o2 + 2 * q) 0 = 1) && decide (D.cb.getD (D.o2 + 2 * q + 1) 0 = 1)) := rfl
  have hext : ∀ x toks, Ext g x toks → Ext a x ([.wir q] ++ toks) := fun x toks hx =>
    ((hb1.trans (hd2.trans (he2.trans ((Ext.of_eq rfl rfl rfl rfl : Ext e (e.set gY (e.env gY + 1)) []).trans
      (hg2.trans hx))))).congr (by simp))
  have hfr : ∀ x T, (∀ y ∈ T, y ∈ accBodyT) → Fr g x T → Fr a x accBodyT := fun x T hT hx =>
    (Fr.weaken hb2 (by simp [accBodyT])).trans ((Fr.weaken hd3 (by simp [accBodyT])).trans
      ((Fr.weaken he3 (by simp [accBodyT])).trans ((Fr.set e _ (show gY ∈ accBodyT by simp [accBodyT])).trans
        ((Fr.weaken hg3 (by simp [accBodyT])).trans (Fr.weaken hx hT)))))
  refine Hs.seqc (t1 := 3) (t2 := 1) (R1 := fun x => Ext g x [.cst (D.td.hl q && D.td.ac q)] ∧ Fr g x [])
    (Hs.ite (show gU ≠ v1 by decide) (fun hc => ?_) (fun hc => ?_)) (fun x hx => ?_) (by omega)
  · have h1 : D.cb.getD (D.o2 + 2 * q) 0 = 1 := by simpa [Cnd.eval, gU', hGg.kc.one] using hc
    refine Hs.mono (cstP_spec (.eq gT v1) (show gT ≠ v1 by decide) g hGg.tt hGg.kc) (by omega) ?_
    rintro x ⟨hx1, hx2⟩
    refine ⟨hx1.congr ?_, hx2⟩
    rw [hval, h1]
    simp [Cnd.eval, hg1, hGg.kc.one]
  · have h1 : ¬ D.cb.getD (D.o2 + 2 * q) 0 = 1 := by simpa [Cnd.eval, gU', hGg.kc.one] using hc
    refine Hs.mono (emitR_spec vZ (.cst false) g hGg.tt (by rw [hGg.kc.z]; rfl)) (by omega) ?_
    rintro x ⟨hx1, hx2⟩
    refine ⟨hx1.congr ?_, hx2⟩
    rw [hval, show decide (D.cb.getD (D.o2 + 2 * q) 0 = 1) = false from decide_eq_false h1]
    rfl
  · obtain ⟨hx1, hx2⟩ := hx
    have hGx : GC D x := hGg.of hx1 hx2 (by decide)
    refine Hs.mono (emitR_spec kc4 .conj x hGx.tt (by rw [hGx.kc.k4]; rfl)) le_rfl ?_
    rintro y ⟨hy1, hy2⟩
    exact ⟨(hext _ _ (hx1.trans hy1)).congr (by simp), hfr _ [] (by simp) (hx2.trans hy2)⟩

/-- **The acceptance test** (`accT`). -/
def accP : St VV MM := anyP gQ dS accBodyP

def accCost (Λ : ℕ) : ℕ := Λ * (12 * Λ + 64) + Λ * 5 + 12

theorem accP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM)
    (hG : GC D a) :
    Hs C accP a (accCost Λ) (fun b => Ext a b (accT D.td D.s) ∧ Fr a b (gQ :: accBodyT)) := by
  have hsΛ := D.s_le Λ hOk
  have h := anyP_spec (C := C) gQ dS accBodyP accBodyT (by decide) (by decide) (GC D) D.s (12 * Λ + 60)
    (fun q => [.wir q, .cst (D.td.hl q && D.td.ac q), .conj]) (fun b hb => hb.s) (fun b hb => ⟨hb.tt, hb.kc⟩)
    (fun b d toks hb hE hF => hb.of hE hF (by decide)) (by omega)
    (fun q hq b hb hbQ => accBodyP_spec D Λ hOk hΛ b hb q hq hbQ) a hG
  refine Hs.mono h ?_ (fun b hb => ⟨hb.1.congr (by rfl), hb.2⟩)
  unfold accCost
  have h1 : D.s * (12 * Λ + 60 + 4) ≤ Λ * (12 * Λ + 64) := Nat.mul_le_mul_right _ hsΛ
  have h2 : D.s * 5 ≤ Λ * 5 := Nat.mul_le_mul_right _ hsΛ
  omega

/-! ## The initial vector -/

/-- `cst (frameBit input pos)` with `gE = pos / 2`, `gK = pos % 2`. -/
def frameBitP : St VV MM :=
  .ite (.eq gK vZ) (cstP (.lt gE dIL)) (.ite (.lt gE dIL) (.seq (lookP sIB gE gU) (cstP (.eq gU v1))) (emitR vZ))

/-- The witness frame bit with `gE = pos / 2`, `gK = pos % 2`. -/
def witBitP : St VV MM :=
  .ite (.eq gK vZ) (cstP (.lt gE dN)) (.ite (.lt gE dN) (emitInp gE) (emitR vZ))

/-- Tapes `0`, `1` and the rest: `gB` the tape, `gE gK` the halved position. -/
def tapeSelP : St VV MM := .ite (.eq gB vZ) frameBitP (.ite (.eq gB v1) witBitP (emitR vZ))

/-- Head bits: `gA = j - s < t·width`. -/
def headInitP : St VV MM := .seq (.op (.dm gA dWd gB gC)) (cstP (.eq gC vZ))

/-- Cell bits: `gA = j - s ≥ t·width`. -/
def tapeInitP : St VV MM :=
  .seq (.seq (.op (.sub gA dTW)) (.seq (.op (.dm gA dWd gB gC)) (.op (.dm gC v2 gE gK)))) tapeSelP

/-- The initial value of window bit `gJ`. -/
def initBodyP : St VV MM :=
  .ite (.lt gJ dS) (cstP (.eq dSt gJ))
    (.seq (.seq (.op (.copy gA gJ)) (.op (.sub gA dS))) (.ite (.lt gA dTW) headInitP tapeInitP))

def initBodyT : List (Fin VV) := [gA, gB, gC, gE, gK, gU, gS, gX]

theorem frameBit_of (input : List Bool) (pos : ℕ) :
    frameBit input pos = if pos % 2 = 0 then decide (pos / 2 < input.length)
      else if pos / 2 < input.length then decide ((input.map Bool.toNat).getD (pos / 2) 0 = 1) else false := by
  unfold frameBit
  split_ifs with h1 h2
  · rfl
  · rw [← bitAt_map]; rfl
  · rw [List.getD_eq_default _ _ (by omega)]

theorem frameBitP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (input : List Bool)
    (hib : D.ib = input.map Bool.toNat) (a : DS VV MM) (hG : GC D a) (pos : ℕ) (hE : a.env gE = pos / 2)
    (hK : a.env gK = pos % 2) :
    Hs C frameBitP a (6 * Λ + 20) (fun b => Ext a b [.cst (frameBit input pos)] ∧ Fr a b [gU, gS]) := by
  have hib' := hOk.ibΛ
  have hil : D.ib.length = input.length := by rw [hib]; simp
  refine Hs.ite (show gK ≠ vZ by decide) (fun hc => ?_) (fun hc => ?_)
  · have h1 : pos % 2 = 0 := by simpa [Cnd.eval, hK, hG.kc.z] using hc
    refine Hs.mono (cstP_spec (.lt gE dIL) (show gE ≠ dIL by decide) a hG.tt hG.kc) (by omega) ?_
    rintro b ⟨hb1, hb2⟩
    refine ⟨hb1.congr ?_, Fr.weaken hb2 (by simp)⟩
    rw [frameBit_of, if_pos h1]
    simp [Cnd.eval, hE, hG.il, hil]
  · have h1 : ¬ pos % 2 = 0 := by simpa [Cnd.eval, hK, hG.kc.z] using hc
    refine Hs.mono (t := 6 * Λ + 18) (Hs.ite (show gE ≠ dIL by decide) (fun hc2 => ?_) (fun hc2 => ?_)) (by omega)
      (fun b h => h)
    · have h2 : pos / 2 < input.length := by simpa [Cnd.eval, hE, hG.il, hil] using hc2
      refine Hs.seqc (t1 := 6 * (pos / 2) + 10) (t2 := 2) (lookP_at (C := C) sIB gE gU (by decide) (by decide)
        (by decide) a _ hE hG.rib (by rw [hG.ib, hil]; exact h2) (by omega)) (fun b hb => ?_) (by omega)
      obtain ⟨hb1, hb2, hb3⟩ := hb
      have hGb : GC D b := hG.of hb2 hb3 (by decide)
      refine Hs.mono (cstP_spec (.eq gU v1) (show gU ≠ v1 by decide) b hGb.tt hGb.kc) le_rfl ?_
      rintro d ⟨hd1, hd2⟩
      refine ⟨(hb2.trans hd1).congr ?_, Fr.weaken (hb3.trans (Fr.weaken hd2 (by simp))) (by simp)⟩
      rw [frameBit_of, if_neg h1, if_pos h2]
      simp [Cnd.eval, hb1, hG.ib, hib, hGb.kc.one]
    · have h2 : ¬ pos / 2 < input.length := by simpa [Cnd.eval, hE, hG.il, hil] using hc2
      refine Hs.mono (emitR_spec vZ (.cst false) a hG.tt (by rw [hG.kc.z]; rfl)) (by omega) ?_
      rintro b ⟨hb1, hb2⟩
      refine ⟨hb1.congr ?_, Fr.weaken hb2 (by simp)⟩
      rw [frameBit_of, if_neg h1, if_neg h2]

/-- The witness-tape tokens of `initJ` at position `pos`. -/
def witToks (n pos : ℕ) : List RTok :=
  if pos % 2 = 0 then [.cst (decide (pos / 2 < n))] else if pos / 2 < n then [.inp (pos / 2)] else [.cst false]

theorem witBitP_spec (D : GD) (Λ : ℕ) (_hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (a : DS VV MM) (hG : GC D a)
    (pos : ℕ) (hpos : pos ≤ Λ) (hE : a.env gE = pos / 2) (hK : a.env gK = pos % 2) :
    Hs C witBitP a 8 (fun b => Ext a b (witToks D.n pos) ∧ Fr a b [gX]) := by
  refine Hs.ite (show gK ≠ vZ by decide) (fun hc => ?_) (fun hc => ?_)
  · have h1 : pos % 2 = 0 := by simpa [Cnd.eval, hK, hG.kc.z] using hc
    refine Hs.mono (cstP_spec (.lt gE dN) (show gE ≠ dN by decide) a hG.tt hG.kc) (by omega) ?_
    rintro b ⟨hb1, hb2⟩
    refine ⟨hb1.congr ?_, Fr.weaken hb2 (by simp)⟩
    simp [witToks, h1, Cnd.eval, hE, hG.n]
  · have h1 : ¬ pos % 2 = 0 := by simpa [Cnd.eval, hK, hG.kc.z] using hc
    refine Hs.mono (t := 6) (Hs.ite (show gE ≠ dN by decide) (fun hc2 => ?_) (fun hc2 => ?_)) (by omega)
      (fun b h => h)
    · have h2 : pos / 2 < D.n := by simpa [Cnd.eval, hE, hG.n] using hc2
      refine Hs.mono (emitInp_spec gE (by decide) (by decide) a hG.tt hG.kc (by rw [hE]; omega)) (by omega) ?_
      rintro b ⟨hb1, hb2⟩
      exact ⟨hb1.congr (by simp [witToks, h1, h2, hE]), hb2⟩
    · have h2 : ¬ pos / 2 < D.n := by simpa [Cnd.eval, hE, hG.n] using hc2
      refine Hs.mono (emitR_spec vZ (.cst false) a hG.tt (by rw [hG.kc.z]; rfl)) (by omega) ?_
      rintro b ⟨hb1, hb2⟩
      exact ⟨hb1.congr (by simp [witToks, h1, h2]), Fr.weaken hb2 (by simp)⟩

theorem initJ_of (t s width n st : ℕ) (input : List Bool) (j : ℕ) :
    initJ t s width n st input j =
      if j < s then [.cst (decide (st = j))]
      else if j - s < t * width then [.cst (decide ((j - s) % width = 0))]
      else if (j - s - t * width) / width = 0 then [.cst (frameBit input ((j - s - t * width) % width))]
      else if (j - s - t * width) / width = 1 then witToks n ((j - s - t * width) % width)
      else [.cst false] := by
  unfold initJ witToks
  by_cases h1 : j < s
  · simp [h1]
  · have e : (j < s + t * width) ↔ (j - s < t * width) := by omega
    simp only [h1, if_false, e]

theorem initBodyP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (input : List Bool)
    (hib : D.ib = input.map Bool.toNat) (a : DS VV MM) (hG : GC D a) (j : ℕ) (hj : a.env gJ = j)
    (_hjW : j < D.W) :
    Hs C initBodyP a (6 * Λ + 40) (fun b => Ext a b (initJ D.t D.s D.width D.n D.st input j) ∧ Fr a b initBodyT) := by
  have hk := hG.kc
  have hwid := hOk.width
  have hWl := hOk.WΛ
  have hwΛ := D.width_le Λ hOk
  unfold GD.W windowBits at hWl
  rw [initJ_of]
  refine Hs.ite (show gJ ≠ dS by decide) (fun hc => ?_) (fun hc => ?_)
  · have h1 : j < D.s := by simpa [Cnd.eval, hj, hG.s] using hc
    refine Hs.mono (cstP_spec (.eq dSt gJ) (show dSt ≠ gJ by decide) a hG.tt hk) (by omega) ?_
    rintro b ⟨hb1, hb2⟩
    refine ⟨hb1.congr ?_, Fr.weaken hb2 (by simp)⟩
    simp [h1, Cnd.eval, hG.st, hj]
  · have h1 : ¬ j < D.s := by simpa [Cnd.eval, hj, hG.s] using hc
    rw [if_neg h1]
    have s1 : Hs C (.seq (.op (.copy gA gJ)) (.op (.sub gA dS))) a 3
        (fun b => b.env gA = j - D.s ∧ Ext a b [] ∧ Fr a b [gA]) := by
      apply hs_of_wpc
      simp only [wpc, opwp]
      vsimp [hj, hG.s]
      and_split
      all_goals first | omega | exact Ext.of_eq rfl rfl rfl rfl | fr_tac | skip
    refine Hs.seqc (t1 := 3) (t2 := 6 * Λ + 34) s1 (fun b hb => ?_) (by omega)
    obtain ⟨hb1, hb2, hb3⟩ := hb
    have hGb : GC D b := hG.of hb2 hb3 (by decide)
    have hext : ∀ x toks, Ext b x toks → Ext a x toks := fun x toks hx => (hb2.trans hx).congr (by simp)
    have hfr : ∀ x T, (∀ y ∈ T, y ∈ initBodyT) → Fr b x T → Fr a x initBodyT := fun x T hT hx =>
      (Fr.weaken hb3 (by simp [initBodyT])).trans (Fr.weaken hx hT)
    refine Hs.mono (t := 6 * Λ + 33) (Hs.ite (show gA ≠ dTW by decide) (fun hc2 => ?_) (fun hc2 => ?_)) (by omega)
      (fun x h => h)
    · have h2 : j - D.s < D.t * D.width := by simpa [Cnd.eval, hb1, hGb.tw] using hc2
      rw [if_pos h2]
      have s2 : Hs C headInitP b 5 (fun x => Ext b x [.cst (decide ((j - D.s) % D.width = 0))] ∧ Fr b x [gB, gC]) := by
        refine Hs.seqc (t1 := 1) (t2 := 3) (hs_dm C gA dWd gB gC b (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by rw [hGb.wd]; omega) (by rw [hGb.wd]; omega)) (fun x hx => ?_) (by omega)
        subst hx
        have hGx : GC D ((b.set gB (b.env gA / b.env dWd)).set gC (b.env gA % b.env dWd)) :=
          hGb.of (T := [gB, gC]) (Ext.of_eq rfl rfl rfl rfl) (by fr_tac) (by decide)
        refine Hs.mono (cstP_spec (.eq gC vZ) (show gC ≠ vZ by decide) _ hGx.tt hGx.kc) (by omega) ?_
        rintro y ⟨hy1, hy2⟩
        refine ⟨((Ext.of_eq rfl rfl rfl rfl : Ext b ((b.set gB (b.env gA / b.env dWd)).set gC (b.env gA % b.env dWd))
          []).trans hy1).congr ?_, (by fr_tac : Fr b ((b.set gB (b.env gA / b.env dWd)).set gC (b.env gA % b.env dWd))
          [gB, gC]).trans (Fr.weaken hy2 (by simp))⟩
        vsimp [Cnd.eval, hb1, hGb.wd, hGb.kc.z, Function.update_apply]
      refine Hs.mono s2 (by omega) ?_
      rintro x ⟨hx1, hx2⟩
      exact ⟨hext _ _ hx1, hfr _ _ (by simp [initBodyT]) hx2⟩
    · have h2 : ¬ j - D.s < D.t * D.width := by simpa [Cnd.eval, hb1, hGb.tw] using hc2
      rw [if_neg h2]
      obtain ⟨u, hu⟩ : ∃ u, u = j - D.s - D.t * D.width := ⟨_, rfl⟩
      rw [← hu]
      have s3 : Hs C (.seq (.op (.sub gA dTW)) (.seq (.op (.dm gA dWd gB gC)) (.op (.dm gC v2 gE gK)))) b 5
          (fun x => x.env gB = u / D.width ∧ x.env gE = u % D.width / 2 ∧ x.env gK = u % D.width % 2 ∧
            Ext b x [] ∧ Fr b x [gA, gB, gC, gE, gK]) := by
        apply hs_of_wpc
        simp only [wpc, opwp]
        vsimp [hb1, hGb.tw, hGb.wd, hGb.kc.two, hu]
        and_split
        all_goals first | omega | exact Ext.of_eq rfl rfl rfl rfl | fr_tac | skip
      refine Hs.seqc (t1 := 5) (t2 := 6 * Λ + 26) s3 (fun x hx => ?_) (by omega)
      obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
      have hGx : GC D x := hGb.of hx4 hx5 (by decide)
      have hext' : ∀ y toks, Ext x y toks → Ext a y toks := fun y toks hy => hext _ _ ((hx4.trans hy).congr (by simp))
      have hfr' : ∀ y T, (∀ z ∈ T, z ∈ initBodyT) → Fr x y T → Fr a y initBodyT := fun y T hT hy =>
        hfr _ initBodyT (fun z hz => hz) ((Fr.weaken hx5 (by simp [initBodyT])).trans (Fr.weaken hy hT))
      refine Hs.ite (show gB ≠ vZ by decide) (fun hc3 => ?_) (fun hc3 => ?_)
      · have h3 : u / D.width = 0 := by simpa [Cnd.eval, hx1, hk.z, hGx.kc.z] using hc3
        rw [if_pos h3]
        refine Hs.mono (frameBitP_spec D Λ hOk hΛ input hib x hGx (u % D.width) hx2 hx3) (by omega) ?_
        rintro y ⟨hy1, hy2⟩
        exact ⟨hext' _ _ hy1, hfr' _ _ (by simp [initBodyT]) hy2⟩
      · have h3 : ¬ u / D.width = 0 := by simpa [Cnd.eval, hx1, hk.z, hGx.kc.z] using hc3
        rw [if_neg h3]
        refine Hs.mono (t := 9) (Hs.ite (show gB ≠ v1 by decide) (fun hc4 => ?_) (fun hc4 => ?_)) (by omega)
          (fun y h => h)
        · have h4 : u / D.width = 1 := by simpa [Cnd.eval, hx1, hGx.kc.one] using hc4
          rw [if_pos h4]
          have hmod : u % D.width ≤ Λ := by have := Nat.mod_lt u (show 0 < D.width by omega); omega
          refine Hs.mono (witBitP_spec D Λ hOk hΛ x hGx (u % D.width) hmod hx2 hx3) (by omega) ?_
          rintro y ⟨hy1, hy2⟩
          exact ⟨hext' _ _ hy1, hfr' _ _ (by simp [initBodyT]) hy2⟩
        · have h4 : ¬ u / D.width = 1 := by simpa [Cnd.eval, hx1, hGx.kc.one] using hc4
          rw [if_neg h4]
          refine Hs.mono (emitR_spec vZ (.cst false) x hGx.tt (by rw [hGx.kc.z]; rfl)) (by omega) ?_
          rintro y ⟨hy1, hy2⟩
          exact ⟨hext' _ _ hy1, hfr' _ [] (by simp) hy2⟩

/-- **The initial vector** (`initT`): every window bit, saved, then swap. -/
def initP : St VV MM := .seq (forP gJ dW (.seq initBodyP (emitR kc6))) (emitR kc7)

def initT' : List (Fin VV) := gJ :: initBodyT

def initCost (Λ : ℕ) : ℕ := Λ * (6 * Λ + 46) + 6

theorem initP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (input : List Bool)
    (hib : D.ib = input.map Bool.toNat) (a : DS VV MM) (hG : GC D a) :
    Hs C initP a (initCost Λ) (fun b => Ext a b (initT D.t D.s D.width D.n D.st input) ∧ Fr a b initT') := by
  have hWΛ := hOk.WΛ
  refine Hs.seqc (t1 := D.W * ((6 * Λ + 40 + 1 + 1) + 4) + 4) (t2 := 1)
    (forP_spec gJ dW (.seq initBodyP (emitR kc6)) initBodyT (by decide) (by decide) (GC D)
      D.W (6 * Λ + 40 + 1 + 1) (fun j => initJ D.t D.s D.width D.n D.st input j ++ [.save]) (fun b hb => hb.W)
      (fun b d toks hb hE hF => hb.of hE hF (by decide)) (by omega)
      (fun j hj b hb hbJ => Hs.seq (t1 := 6 * Λ + 40) (t2 := 1) (initBodyP_spec D Λ hOk hΛ input hib b hb j hbJ hj) (fun d ⟨hd1, hd2⟩ => by
        have hGd : GC D d := hb.of hd1 hd2 (by decide)
        refine Hs.mono (emitR_spec kc6 .save d hGd.tt (by rw [hGd.kc.k6]; rfl)) le_rfl ?_
        rintro e ⟨he1, he2⟩
        exact ⟨hd1.trans he1, hd2.trans (Fr.weaken he2 (by simp))⟩)) a hG) (fun b hb => ?_)
    (by
      unfold initCost
      have := Nat.mul_le_mul_right (6 * Λ + 46) hWΛ
      nlinarith)
  obtain ⟨hb1, hb2⟩ := hb
  have hGb : GC D b := hG.of hb1 hb2 (by decide)
  refine Hs.mono (emitR_spec kc7 .swap b hGb.tt (by rw [hGb.kc.k7]; rfl)) le_rfl ?_
  rintro e ⟨he1, he2⟩
  exact ⟨(hb1.trans he1).congr (by simp [initT, GD.W]), hb2.trans (Fr.weaken he2 (by simp))⟩

end NearCubicGates.Adapters.Compile
