import Proof.Gates.Cells.FormsAll2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

/-- Run-wide: index in `sN` of the first parity entry, and the parity list length. -/
def gPar : Fin VV := ⟨124, by decide⟩
def gPL : Fin VV := ⟨125, by decide⟩

/-- The machine's running xor. -/
def opStep (zb : List ℕ) (acc x : ℕ) : ℕ := if acc + zb.getD x 0 = 2 then 0 else acc + zb.getD x 0

def opVal (zb par : List ℕ) : ℕ := par.foldl (opStep zb) 0

def opBody : St VV MM :=
  .seq (.op (.rdM sN t0)) (.seq (fetch sZb t0 t1) (.seq (.op (.add vOP t1))
    (.ite (.eq vOP v2) (.op (.zero vOP)) skipS)))

def opP : St VV MM := .seq (.op (.zero vOP)) (.seq (seekP sN gPar) (forS c5 gPL opBody))

def opT : List (Fin VV) := [vOP, c0, vJ, c5, t0, t1]

/-! ## Value level -/

theorem opStep_bit (zb : List ℕ) (hz : ∀ x ∈ zb, x ≤ 1) (acc x : ℕ) (b : Bool) (hb : acc = b.toNat) :
    opStep zb acc x = (xor b (decide (zb.getD x 0 = 1))).toNat := by
  have h : zb.getD x 0 ≤ 1 := by
    rw [List.getD_eq_getElem?_getD]
    cases hx : zb[x]? with
    | none => simp
    | some v => simp; exact hz v (List.mem_of_getElem? hx)
  unfold opStep
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · rw [h0]; cases b <;> simp_all
  · rw [h1]; cases b <;> simp_all

theorem opVal_foldl (zb : List ℕ) (hz : ∀ x ∈ zb, x ≤ 1) : ∀ (par : List ℕ) (b : Bool),
    par.foldl (opStep zb) b.toNat = (par.foldl (fun acc x => xor acc (decide (zb.getD x 0 = 1))) b).toNat
  | [], b => rfl
  | x :: par, b => by
    simp only [List.foldl_cons]
    rw [opStep_bit zb hz b.toNat x b rfl]
    exact opVal_foldl zb hz par _

theorem zbL_le_one {n : ℕ} (I : Finset (Fin n)) (i : ℕ) : ∀ x ∈ zbL I i, x ≤ 1 := by
  intro x hx
  simp only [zbL, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  split_ifs <;> omega

theorem outerParity_eq (c : Call) (wt : Wit c.n) (i : ℕ) :
    opVal (zbL wt.I i) c.parity = if outerParity c wt (cellOf wt.I i) then 1 else 0 := by
  have h := opVal_foldl (zbL wt.I i) (zbL_le_one wt.I i) c.parity false
  simp only [Bool.toNat_false] at h
  unfold opVal; rw [h]
  have hmap : (c.parity.map fun x => if h : x < c.n then
      (if hI : (⟨x, h⟩ : Fin c.n) ∈ wt.I then false else cellOf wt.I i ⟨⟨x, h⟩, hI⟩) else false) =
      c.parity.map fun x => decide ((zbL wt.I i).getD x 0 = 1) := by
    apply List.map_congr_left
    intro x _
    by_cases hx : x < c.n
    · rw [dif_pos hx]
      have := zbL_point wt.I i ⟨x, hx⟩
      unfold extend at this
      by_cases hI : (⟨x, hx⟩ : Fin c.n) ∈ wt.I
      · rw [dif_pos hI] at this ⊢; simpa [zeroPoint] using this
      · rw [dif_neg hI] at this ⊢; exact this
    · rw [dif_neg hx]
      have : (zbL wt.I i).getD x 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [zbL]; omega)]; rfl
      rw [List.getD_eq_getElem?_getD] at this
      simp [this]
  unfold outerParity
  rw [hmap, List.foldl_map]
  cases (c.parity.foldl (fun acc x => xor acc (decide ((zbL wt.I i).getD x 0 = 1))) false) <;> simp

theorem opStep_le (zb : List ℕ) (hz : ∀ x ∈ zb, x ≤ 1) (acc x : ℕ) (hacc : acc ≤ 1) : opStep zb acc x ≤ 1 := by
  have h : zb.getD x 0 ≤ 1 := by
    rw [List.getD_eq_getElem?_getD]
    cases hx : zb[x]? with
    | none => simp
    | some v => simp; exact hz v (List.mem_of_getElem? hx)
  unfold opStep; split_ifs <;> omega

theorem foldl_opStep_le (zb : List ℕ) (hz : ∀ x ∈ zb, x ≤ 1) : ∀ (l : List ℕ) (acc : ℕ), acc ≤ 1 →
    l.foldl (opStep zb) acc ≤ 1
  | [], _, h => h
  | x :: l, acc, h => foldl_opStep_le zb hz l _ (opStep_le zb hz acc x h)

theorem opP_spec (a : DS VV MM) (hc : Cst a) (zb par R : List ℕ) (hzb : a.ram sZb = zb) (hz : ∀ x ∈ zb, x ≤ 1)
    (hpar : ∀ x ∈ par, x < zb.length) (hPar : (a.ram sN).drop (a.env gPar) = par ++ R)
    (hParl : a.env gPar ≤ (a.ram sN).length) (hPL : a.env gPL = par.length) (hW : a.env gPar < 2 ^ C.Wd)
    (hPLW : par.length < 2 ^ C.Wd) (hzW : zb.length < 2 ^ C.Wd) (hW4 : 4 ≤ 2 ^ C.Wd)
    (hzr : a.rc sZb ≤ zb.length) :
    Hs C opP a (a.rc sN + 5 * a.env gPar + par.length * (6 * zb.length + 26 + 4) + 20) (fun b =>
      b.env vOP = opVal zb par ∧ b.ram = a.ram ∧ b.rc sN = a.env gPar + par.length ∧ b.rc sZb ≤ zb.length ∧
      Agr a b [sN, sZb] opT) := by
  have hNZ : sN ≠ sZb := by decide
  refine Hs.bseq (hs_zero C vOP a) (by omega) (fun e1 he1 => ?_)
  subst he1
  refine Hs.bseq (Hs.mono (seekP_spec sN gPar (by decide) (by decide) (a.set vOP 0) hParl hW)
    (show (a.set vOP 0).rc sN + 5 * (a.set vOP 0).env gPar + 6 ≤ a.rc sN + 5 * a.env gPar + 6 by
      simp only [DS.set_rc]; rw [DS.set_env_ne _ _ (by decide)]) (fun _ h => h)) (by omega)
    (fun e2 ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ?_)
  have ag2 : Agr a e2 [sN, sZb] opT := (Agr.set a _ _ (by simp [opT])).trans
    (Agr.of_seek (m := sN) (by simp) (by simp [opT]) ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩)
  have e2v : e2.env vOP = 0 := by rw [h8 vOP (by decide)]; simp
  have e2PL : e2.env gPL = par.length := by rw [ag2.fr gPL (by decide)]; exact hPL
  have e2P : e2.env gPar = a.env gPar := ag2.fr gPar (by decide)
  have hlenN : a.env gPar + par.length ≤ (a.ram sN).length := by
    have := congrArg List.length hPar; simp at this; omega
  let I : ℕ → DS VV MM → Prop := fun k e => e.env vOP = (par.take k).foldl (opStep zb) 0 ∧ e.ram = a.ram ∧
    e.rc sN = a.env gPar + k ∧ e.rc sZb ≤ zb.length ∧ Agr a e [sN, sZb] opT
  have hl := forS_spec' (C := C) c5 gPL (by decide) opBody e2 par.length hPLW I (6 * zb.length + 26)
    (fun k e v ⟨i1, i2, i3, i4, i5⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1, i2, i3, i4,
      i5.trans (Agr.set e _ _ (by simp [opT]))⟩)
    ⟨by rw [e2v]; simp, h1, by rw [h2, Function.update_self, DS.set_env_ne _ _ (by decide)]; rfl, by
      rw [h2, Function.update_of_ne hNZ.symm, DS.set_rc]; exact hzr, ag2⟩ e2PL ?_
  · refine Hs.mono hl (by omega) ?_
    rintro b ⟨⟨i1, i2, i3, i4, i5⟩, _, _⟩
    refine ⟨by rw [i1, List.take_of_length_le le_rfl]; rfl, i2, i3, i4, i5⟩
  · intro k hk e ⟨i1, i2, i3, i4, i5⟩ hek hem
    have ec : Cst e := Cst.of_fr hc i5.fr (by decide)
    have hacc : e.env vOP ≤ 1 := by rw [i1]; exact foldl_opStep_le zb hz _ 0 (by omega)
    have hdk : (a.ram sN).getD (a.env gPar + k) 0 = par[k] := by
      rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop, hPar, List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem hk]; rfl
    have hpk : par[k] < zb.length := hpar _ (List.getElem_mem hk)
    refine Hs.bseq (hs_rdM C sN t0 e (by rw [i3, i2]; omega)) (by omega) (fun e1 he1 => ?_)
    subst he1
    have f1v : ((e.set t0 ((e.ram sN).getD (e.rc sN) 0)).adv sN).env t0 = par[k] := by
      simp only [DS.adv]; rw [DS.set_env_self, i2, i3, hdk]
    refine Hs.bseq (Hs.mono (fetch_spec sZb t0 t1 (by decide) (by decide) _
      (by rw [f1v]; simp only [DS.adv, DS.set_ram]; rw [i2, hzb]; exact hpk) (by rw [f1v]; omega))
      (show ((e.set t0 ((e.ram sN).getD (e.rc sN) 0)).adv sN).rc sZb +
        5 * ((e.set t0 ((e.ram sN).getD (e.rc sN) 0)).adv sN).env t0 + 9 ≤ 6 * zb.length + 9 by
        rw [f1v]; simp only [DS.adv, DS.set_rc]; rw [Function.update_of_ne hNZ.symm]; omega) (fun _ h => h))
      (by omega) (fun e2 ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ => ?_)
    have e2acc : e2.env vOP = e.env vOP := by
      rw [g9 vOP (by decide)]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]
    have e2t1 : e2.env t1 = zb.getD par[k] 0 := by
      rw [g1, f1v]; simp only [DS.adv, DS.set_ram]; rw [i2, hzb]
    have hzk : zb.getD par[k] 0 ≤ 1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpk]; exact hz _ (List.getElem_mem hpk)
    refine Hs.bseq (hs_add C vOP t1 e2 (by decide) (by rw [e2acc, e2t1]; omega)) (by omega) (fun e3 he3 => ?_)
    subst he3
    have hfold : (par.take (k + 1)).foldl (opStep zb) 0 = opStep zb (e.env vOP) par[k] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append, ← i1]; rfl
    have e2Agr : Agr a ((e2.set vOP (e2.env vOP + e2.env t1))) [sN, sZb] opT := by
      refine i5.trans ⟨fun m hm => ?_, fun m hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
        simp only [DS.set_ram]; rw [g4]; simp [DS.adv, DS.set]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
        simp only [DS.set_rc]; rw [g5, Function.update_of_ne hm.2]; simp [DS.adv, DS.set, Function.update_of_ne hm.1]
      · simp only [DS.set_ip]; rw [g2]; rfl
      · simp only [DS.set_out]; rw [g3]; rfl
      · simp only [DS.set_kin]; rw [g6]; rfl
      · simp only [DS.set_kout]; rw [g7]; rfl
      · simp only [DS.set_kc]; rw [g8]; rfl
      · intro y hy
        simp only [opT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        rw [DS.set_env_ne _ _ hy.1, g9 y (by simp [hy.2.1, hy.2.2.1, hy.2.2.2.2.2])]
        simp only [DS.adv]; rw [DS.set_env_ne _ _ hy.2.2.2.2.1]
    have e3rest : (e2.set vOP (e2.env vOP + e2.env t1)).ram = a.ram ∧
        (e2.set vOP (e2.env vOP + e2.env t1)).rc sN = a.env gPar + (k + 1) ∧
        (e2.set vOP (e2.env vOP + e2.env t1)).rc sZb ≤ zb.length := by
      refine ⟨by simp only [DS.set_ram]; rw [g4]; simp [DS.adv, DS.set, i2], ?_, ?_⟩
      · simp only [DS.set_rc]; rw [g5, Function.update_of_ne hNZ]; simp [DS.adv, DS.set, i3]; ring
      · simp only [DS.set_rc]; rw [g5, Function.update_self]; rw [f1v]; omega
    have hc5 : ∀ (f : DS VV MM), Agr a f [sN, sZb] opT → f.env c5 = (e.env c5) → f.env c5 = k := by
      intro f _ h; rw [h, hek]
    refine Hs.mono (Hs.ite (t := 10) (c := .eq vOP v2) (show vOP ≠ v2 by decide) (fun ht => ?_) (fun ht => ?_))
      (by omega) (fun _ h => h)
    · simp only [Cnd.eval, decide_eq_true_eq] at ht
      refine Hs.mono (hs_zero C vOP _) (by omega) ?_
      rintro b rfl
      have hv2 : (e2.set vOP (e2.env vOP + e2.env t1)).env v2 = 2 := by
        rw [DS.set_env_ne _ _ (by decide), g9 v2 (by decide)]; simp only [DS.adv]
        rw [DS.set_env_ne _ _ (by decide)]; exact ec.two
      rw [hv2, DS.set_env_self] at ht
      refine ⟨⟨?_, e3rest.1, e3rest.2.1, e3rest.2.2, e2Agr.trans (Agr.set _ _ _ (by simp [opT]))⟩, ?_, ?_⟩
      · rw [DS.set_env_self, hfold]; unfold opStep; rw [e2acc, e2t1] at ht; rw [if_pos ht]
      · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), g9 c5 (by decide)]
        simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]; exact hek
      · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), g9 gPL (by decide)]
        simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]; exact hem
    · simp only [Cnd.eval, decide_eq_false_iff_not] at ht
      refine Hs.mono (skip_spec _) (by omega) ?_
      rintro b rfl
      have hv2 : (e2.set vOP (e2.env vOP + e2.env t1)).env v2 = 2 := by
        rw [DS.set_env_ne _ _ (by decide), g9 v2 (by decide)]; simp only [DS.adv]
        rw [DS.set_env_ne _ _ (by decide)]; exact ec.two
      rw [hv2, DS.set_env_self] at ht
      refine ⟨⟨?_, e3rest.1, e3rest.2.1, e3rest.2.2, e2Agr.trans (Agr.set _ _ _ (by simp [opT]))⟩, ?_, ?_⟩
      · rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, hfold]; unfold opStep; rw [e2acc, e2t1] at ht ⊢
        rw [if_neg ht]
      · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), g9 c5 (by decide)]
        simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]; exact hek
      · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), g9 gPL (by decide)]
        simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]; exact hem

end NearCubicGates.Close.Cells
