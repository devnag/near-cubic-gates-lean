import Proof.Gates.Cells.Gates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (gateN intN)

variable {C : Ctx}

/-- The length of the current linear form. -/
def fL : Fin VV := ⟨116, by decide⟩

/-- `gPos − gNeg += Σ_g a_g·b_g` over the next `n` coefficient fields of `sN` and the gate bits of `sB` (counter `c3`). -/
def linP : St VV MM :=
  forS c3 fL (.seq (.op (.rdM sN gS0)) (.seq (.op (.rdM sN gS1)) (.seq (.op (.rdM sB gZ))
    (.ite (.eq gZ v1) (.ite (.eq gS0 vZ) (.op (.add gPos gS1)) (.op (.add gNeg gS1))) skipS))))

def linT : List (Fin VV) := [c3, gS0, gS1, gZ, gPos, gNeg, vJ]

theorem linP_spec (a : DS VV MM) (hc : Cst a) (n : ℕ) (hn : a.env fL = n) (hnW : n < 2 ^ C.Wd)
    (ws : List ℤ) (hws : ws.length = n) (R : List ℕ) (hsN : (a.ram sN).drop (a.rc sN) = ws.flatMap intN ++ R)
    (zb Z : List ℕ) (hzb : a.ram sB = zb ++ Z) (hzl : zb.length = n) (hz0 : a.rc sB = 0)
    (hp0 : a.env gPos = 0) (hn0 : a.env gNeg = 0) (hB : (ws.map Int.natAbs).sum < 2 ^ C.Wd) :
    Hs C linP a (n * (1 + (1 + (1 + 4 + 1) + 1) + 1 + 4) + 4)
      (fun b => b.env gPos = posPart ws zb ∧ b.env gNeg = negPart ws zb ∧
        b.rc = Function.update (Function.update a.rc sN (a.rc sN + 2 * n)) sB n ∧
        b.ram = a.ram ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
        Fr a b linT) := by
  have hsd : sN ≠ sB := by decide
  set p0 := a.rc sN
  let I : ℕ → DS VV MM → Prop := fun k e => e.env gPos = posPart (ws.take k) (zb.take k) ∧
    e.env gNeg = negPart (ws.take k) (zb.take k) ∧
    e.rc = Function.update (Function.update a.rc sN (p0 + 2 * k)) sB k ∧
    e.ram = a.ram ∧ e.ip = a.ip ∧ e.out = a.out ∧ e.kin = a.kin ∧ e.kout = a.kout ∧ e.kc = a.kc ∧ Fr a e linT
  have hl := forS_spec' (C := C) c3 fL (by decide) (.seq (.op (.rdM sN gS0)) (.seq (.op (.rdM sN gS1))
    (.seq (.op (.rdM sB gZ)) (.ite (.eq gZ v1) (.ite (.eq gS0 vZ) (.op (.add gPos gS1)) (.op (.add gNeg gS1)))
      skipS)))) a n hnW I (1 + (1 + (1 + 4 + 1) + 1) + 1)
    (fun k e v ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1,
      by rw [DS.set_env_ne _ _ (by decide)]; exact i2, i3, i4, i5, i6, i7, i8, i9, Fr.trans i10 (Fr.set e v (by decide))⟩)
    ⟨by simp [hp0, posPart], by simp [hn0, negPart],
      by funext m; by_cases h1 : m = sB
         · subst h1; simp [hz0]
         · by_cases h2 : m = sN
           · subst h2; simp [Function.update_of_ne h1]; rfl
           · simp [Function.update_of_ne h1, Function.update_of_ne h2],
      rfl, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩ hn ?_
  · refine Hs.mono hl le_rfl ?_
    rintro e ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩, _, _⟩
    refine ⟨by rw [i1, List.take_of_length_le (by omega), List.take_of_length_le (by omega)],
      by rw [i2, List.take_of_length_le (by omega), List.take_of_length_le (by omega)], i3, i4, i5, i6, i7, i8, i9, i10⟩
  · intro k hk e ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ hek hem
    have hc' : Cst e := Cst.of_fr hc i10 (by decide)
    have hkw : k < ws.length := by omega
    have hkz : k < zb.length := by omega
    -- the two weight fields
    have hdrop : (a.ram sN).drop (p0 + 2 * k) = [if ws[k] < 0 then 1 else 0, ws[k].natAbs] ++
        ((ws.drop (k + 1)).flatMap intN ++ R) := by
      have hsp : ws = ws.take k ++ (ws[k] :: ws.drop (k + 1)) := by
        rw [← List.drop_eq_getElem_cons hkw, List.take_append_drop]
      have hfm : ws.flatMap intN = (ws.take k).flatMap intN ++ (intN ws[k] ++ (ws.drop (k + 1)).flatMap intN) := by
        have := congrArg (List.flatMap intN) hsp
        exact this.trans (by rw [List.flatMap_append, List.flatMap_cons])
      have hl2 : ((ws.take k).flatMap intN).length = 2 * k := by
        rw [CounterMachine.flatMap_intN_length]; simp; omega
      rw [← List.drop_drop, hsN, hfm, List.append_assoc, ← hl2, List.drop_left]
      simp [intN, List.append_assoc]
    have eN : e.ram sN = a.ram sN := by rw [i4]
    have eNc : e.rc sN = p0 + 2 * k := by rw [i3, Function.update_of_ne hsd]; simp
    have eZ : e.ram sB = zb ++ Z := by rw [i4, hzb]
    have eZc : e.rc sB = k := by rw [i3]; simp
    have hlenN : p0 + 2 * k + 1 < (a.ram sN).length := by
      have := congrArg List.length hdrop; simp at this; omega
    have g0 : (a.ram sN).getD (p0 + 2 * k) 0 = if ws[k] < 0 then 1 else 0 :=
      fld_of_drop (B := _) (by rw [hdrop]; rfl)
    have h' : (a.ram sN).drop (p0 + 2 * k) = [if ws[k] < 0 then 1 else 0] ++
        (ws[k].natAbs :: ((ws.drop (k + 1)).flatMap intN ++ R)) := by rw [hdrop]; rfl
    have g1 : (a.ram sN).getD (p0 + 2 * k + 1) 0 = ws[k].natAbs := fld_of_drop (B := _) (drop_split' h' 1 rfl)
    have hpt := posPart_take_succ ws zb k hkw hkz
    have hsum : posPart (ws.take (k + 1)) (zb.take (k + 1)) + negPart (ws.take (k + 1)) (zb.take (k + 1)) <
        2 ^ C.Wd :=
      lt_of_le_of_lt ((posPart_le _ _).trans (natAbs_sum_take ws (k + 1))) hB
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + (1 + 4 + 1) + 1) (hs_rdM C sN gS0 e (by rw [eNc, eN]; omega))
      (fun e1 he1 => ?_)) (by norm_num) (fun _ h => h)
    subst he1
    set e1 := (e.set gS0 ((e.ram sN).getD (e.rc sN) 0)).adv sN with he1
    have e1N : e1.ram sN = a.ram sN := by simp [he1, DS.adv, DS.set, eN]
    have e1Nc : e1.rc sN = p0 + 2 * k + 1 := by simp [he1, DS.adv, eNc]
    have e1s : e1.env gS0 = if ws[k] < 0 then 1 else 0 := by
      simp only [he1, DS.adv, DS.set_env_self, eN, eNc]; exact g0
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + 4 + 1) (hs_rdM C sN gS1 e1 (by rw [e1Nc, e1N]; omega))
      (fun e2 he2 => ?_)) (by norm_num) (fun _ h => h)
    subst he2
    set e2 := (e1.set gS1 ((e1.ram sN).getD (e1.rc sN) 0)).adv sN with he2
    have e2Z : e2.ram sB = zb ++ Z := by simp [he2, he1, DS.adv, DS.set, eZ]
    have e2Zc : e2.rc sB = k := by simp [he2, he1, DS.adv, DS.set, Function.update_of_ne (Ne.symm hsd), eZc]
    have e2m : e2.env gS1 = ws[k].natAbs := by
      simp only [he2, DS.adv, DS.set_env_self, e1N, e1Nc]; exact g1
    have e2s : e2.env gS0 = if ws[k] < 0 then 1 else 0 := by simp only [he2, DS.adv]; vsimp [e1s]
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 4) (hs_rdM C sB gZ e2 (by rw [e2Zc, e2Z]; simp; omega))
      (fun e3 he3 => ?_)) (by norm_num) (fun _ h => h)
    subst he3
    set e3 := (e2.set gZ ((e2.ram sB).getD (e2.rc sB) 0)).adv sB with he3
    have e3z : e3.env gZ = zb[k] := by
      simp only [he3, DS.adv, DS.set_env_self, e2Z, e2Zc]; rw [List.getD_append _ _ _ _ hkz, List.getD_eq_getElem _ _ hkz]
    have e3m : e3.env gS1 = ws[k].natAbs := by simp only [he3, DS.adv]; vsimp [e2m]
    have e3s : e3.env gS0 = if ws[k] < 0 then 1 else 0 := by simp only [he3, DS.adv]; vsimp [e2s]
    have e3p : e3.env gPos = posPart (ws.take k) (zb.take k) := by
      simp only [he3, he2, he1, DS.adv]; vsimp [i1]
    have e3n : e3.env gNeg = negPart (ws.take k) (zb.take k) := by
      simp only [he3, he2, he1, DS.adv]; vsimp [i2]
    have e3v1 : e3.env v1 = 1 := by simp only [he3, he2, he1, DS.adv]; vsimp [hc'.one]
    have e3vZ : e3.env vZ = 0 := by simp only [he3, he2, he1, DS.adv]; vsimp [hc'.z]
    have e3c : e3.env c3 = k := by simp only [he3, he2, he1, DS.adv]; vsimp [hek]
    have e3n' : e3.env fL = n := by simp only [he3, he2, he1, DS.adv]; vsimp [hem]
    have e3fr : Fr a e3 linT := by
      intro y hy
      simp only [linT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp only [he3, he2, he1, DS.adv, DS.set]
      rw [Function.update_of_ne hy.2.2.2.1, Function.update_of_ne hy.2.2.1, Function.update_of_ne hy.2.1]
      exact i10 y (by simp [linT]; tauto)
    have e3rc : e3.rc = Function.update (Function.update a.rc sN (p0 + 2 * (k + 1))) sB (k + 1) := by
      simp only [he3, he2, he1, DS.adv, DS.set]
      rw [i3]
      funext m; by_cases h1 : m = sB
      · subst h1; simp [Function.update_of_ne (Ne.symm hsd)]
      · by_cases h2 : m = sN
        · subst h2; simp [Function.update_of_ne hsd]; ring
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]
    have e3rest : e3.ram = a.ram ∧ e3.ip = a.ip ∧ e3.out = a.out ∧ e3.kin = a.kin ∧ e3.kout = a.kout ∧
        e3.kc = a.kc := by
      simp only [he3, he2, he1, DS.adv, DS.set]; exact ⟨i4, i5, i6, i7, i8, i9⟩
    have fin : ∀ (x : Fin VV) (v : ℕ), x ∈ [gPos, gNeg, vJ] →
        (e3.set x v).env gPos = posPart (ws.take (k + 1)) (zb.take (k + 1)) →
        (e3.set x v).env gNeg = negPart (ws.take (k + 1)) (zb.take (k + 1)) →
        I (k + 1) (e3.set x v) ∧ (e3.set x v).env c3 = k ∧ (e3.set x v).env fL = n := by
      intro x v hx q1 q2
      have hxc : c3 ≠ x := by intro h; rw [← h] at hx; revert hx; decide
      have hxn : fL ≠ x := by intro h; rw [← h] at hx; revert hx; decide
      refine ⟨⟨q1, q2, e3rc, e3rest.1, e3rest.2.1, e3rest.2.2.1, e3rest.2.2.2.1, e3rest.2.2.2.2.1,
        e3rest.2.2.2.2.2, Fr.trans e3fr (Fr.set e3 v (by simp [linT] at hx ⊢; tauto))⟩, ?_, ?_⟩
      · rw [DS.set_env_ne _ _ hxc, e3c]
      · rw [DS.set_env_ne _ _ hxn, e3n']
    refine Hs.ite (show gZ ≠ v1 by decide) (fun hz => ?_) (fun hz => ?_)
    · simp only [Cnd.eval, e3z, e3v1, decide_eq_true_eq] at hz
      refine Hs.ite (show gS0 ≠ vZ by decide) (fun hs => ?_) (fun hs => ?_)
      · simp only [Cnd.eval, e3s, e3vZ, decide_eq_true_eq] at hs
        have hw : ¬ ws[k] < 0 := by intro h; simp [h] at hs
        have hb : posPart (ws.take k) (zb.take k) + ws[k].natAbs < 2 ^ C.Wd := by
          have h1 := hsum; rw [hpt.1, hpt.2] at h1; simp only [hz, hw, true_and, false_and, if_true,
            if_false, not_false_eq_true] at h1; omega
        refine Hs.mono (hs_add C gPos gS1 e3 (by decide) (by rw [e3p, e3m]; exact hb)) (by norm_num) ?_
        rintro r rfl
        refine fin gPos _ (by simp) ?_ ?_
        · rw [DS.set_env_self, e3p, e3m, hpt.1]; simp [hz, hw]
        · rw [DS.set_env_ne _ _ (by decide), e3n, hpt.2]; simp [hz, hw]
      · simp only [Cnd.eval, e3s, e3vZ, decide_eq_false_iff_not] at hs
        have hw : ws[k] < 0 := by by_contra h; simp [h] at hs
        have hb : negPart (ws.take k) (zb.take k) + ws[k].natAbs < 2 ^ C.Wd := by
          have h1 := hsum; rw [hpt.1, hpt.2] at h1; simp only [hz, hw, true_and, if_true,
            not_true_eq_false, and_false, if_false] at h1; omega
        refine Hs.mono (hs_add C gNeg gS1 e3 (by decide) (by rw [e3n, e3m]; exact hb)) (by norm_num) ?_
        rintro r rfl
        refine fin gNeg _ (by simp) ?_ ?_
        · rw [DS.set_env_ne _ _ (by decide), e3p, hpt.1]; simp [hz, hw]
        · rw [DS.set_env_self, e3n, e3m, hpt.2]; simp [hz, hw]
    · simp only [Cnd.eval, e3z, e3v1, decide_eq_false_iff_not] at hz
      refine Hs.mono (skip_spec e3) (by norm_num) ?_
      rintro r rfl
      refine fin vJ 0 (by simp) ?_ ?_
      · rw [DS.set_env_ne _ _ (by decide), e3p, hpt.1]; simp [hz]
      · rw [DS.set_env_ne _ _ (by decide), e3n, hpt.2]; simp [hz]

/-! ## Value level -/

theorem gbit_eval {n : ℕ} (g : NormalizedThresholdGate n) (z : BitInput n) (zb : List ℕ)
    (hz : ∀ j : Fin n, z j = decide (zb.getD j.val 0 = 1)) (hl : zb.length = n) :
    gbit g zb = if g.eval z then 1 else 0 := by
  rw [eval_eq_wsum g z zb hz hl]; unfold gbit; by_cases h : g.threshold ≤ wsum (List.ofFn g.weight) zb <;> simp [h]

/-- **A linear form over the gates is the machine's signed sum over the gate bits.** -/
theorem linForm_eq {n : ℕ} (z : BitInput n) (zb : List ℕ) (hz : ∀ j : Fin n, z j = decide (zb.getD j.val 0 = 1))
    (hl : zb.length = n) : ∀ (gs : List (NormalizedThresholdGate n)) (cs : List ℤ),
    linForm gs cs z = wsum cs (gs.map (gbit · zb))
  | [], cs => by cases cs <;> simp [linForm, wsum]
  | g :: gs, [] => by simp [linForm, wsum]
  | g :: gs, c :: cs => by
    have ih := linForm_eq z zb hz hl gs cs
    simp only [linForm, List.zip_cons_cons, List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [ih, wsum, gbit_eval g z zb hz hl]
    by_cases h : g.eval z <;> simp [h, Function.comp_def]

/-- `z_y` in terms of the z-bits of the program. -/
theorem zbL_point {n : ℕ} (I : Finset (Fin n)) (i : ℕ) (j : Fin n) :
    extend I (cellOf I i) (zeroPoint I) j = decide ((zbL I i).getD j.val 0 = 1) := by
  rw [zpt_eq]
  simp only [zbL, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [List.length_ofFn, j.isLt, Option.getD_some, Fin.eta]
  split_ifs with h
  · simp
  · rw [Nat.testBit_eq_decide_div_mod_eq]; rfl

/-! ## Store helpers -/

/-- Writing `W` from cursor `c` over the list `L`. -/
def wr (L : List ℕ) (c : ℕ) (W : List ℕ) : List ℕ := L.take c ++ W ++ L.drop (c + W.length)

theorem putAt_wr (L : List ℕ) (c : ℕ) (W : List ℕ) (v : ℕ) (hc : c ≤ L.length) :
    putAt (wr L c W) (c + W.length) v = wr L c (W ++ [v]) := by
  have hl : (L.take c ++ W).length = c + W.length := by simp; omega
  have := putAt_split (L.take c ++ W) (L.drop (c + W.length)) v
  rw [hl] at this
  unfold wr; rw [this, List.drop_drop]; simp [List.append_assoc, Nat.add_comm, Nat.add_left_comm]; omega

theorem wr_nil (L : List ℕ) (c : ℕ) : wr L c [] = L := by simp [wr]

theorem wr_length_ge (L : List ℕ) (c : ℕ) (W : List ℕ) (hc : c ≤ L.length) : c + W.length ≤ (wr L c W).length := by
  simp [wr]; omega

/-- Advance the cursor of store `m` by `x` records. -/
def advP (m : Fin MM) (x : Fin VV) : St VV MM := forS c0 x (.op (.rdM m vJ))

theorem advP_spec (m : Fin MM) (x : Fin VV) (hx0 : x ≠ c0) (hxJ : x ≠ vJ) (a : DS VV MM)
    (hle : a.rc m + a.env x ≤ (a.ram m).length) (hW : a.env x < 2 ^ C.Wd) :
    Hs C (advP m x) a (a.env x * (1 + 4) + 4) (fun b => b.ram = a.ram ∧
      b.rc = Function.update a.rc m (a.rc m + a.env x) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, vJ]) := by
  set N := a.env x with hNdef
  let I : ℕ → DS VV MM → Prop := fun k e => e.ip = a.ip ∧ e.out = a.out ∧ e.ram = a.ram ∧
    e.rc = Function.update a.rc m (a.rc m + k) ∧ e.kin = a.kin ∧ e.kout = a.kout ∧ e.kc = a.kc ∧ Fr a e [c0, vJ]
  have hl := forS_spec' (C := C) c0 x (Ne.symm hx0) (.op (.rdM m vJ)) a N hW I 1
    (fun k e v ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h7,
      Fr.trans h8 (Fr.set e v (List.mem_cons_self ..))⟩)
    ⟨rfl, rfl, rfl, by simp, rfl, rfl, rfl, Fr.refl _ _⟩ rfl ?_
  · refine Hs.mono hl le_rfl ?_
    rintro e ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, _, _⟩
    exact ⟨h3, h4, h1, h2, h5, h6, h7, h8⟩
  · intro k hk e ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hek hem
    refine Hs.mono (hs_rdM C m vJ e (by rw [h4, h3]; simp; omega)) le_rfl ?_
    rintro f rfl
    refine ⟨⟨by simp [DS.adv, DS.set, h1], by simp [DS.adv, DS.set, h2], by simp [DS.adv, DS.set, h3],
      by simp [DS.adv, DS.set, h4]; ring, by simp [DS.adv, DS.set, h5], by simp [DS.adv, DS.set, h6],
      by simp [DS.adv, DS.set, h7], Fr.trans h8 (fun y hy => by
        simp only [DS.adv, DS.set]
        rw [Function.update_of_ne]; intro h; apply hy; rw [h]; simp)⟩, ?_, ?_⟩
    · simp only [DS.adv, DS.set]; rw [Function.update_of_ne (by decide)]; exact hek
    · simp only [DS.adv, DS.set]; rw [Function.update_of_ne hxJ]; exact hem

/-- Move the cursor of store `m` to index `x`. -/
def seekP (m : Fin MM) (x : Fin VV) : St VV MM := .seq (.op (.rwM m)) (advP m x)

theorem seekP_spec (m : Fin MM) (x : Fin VV) (hx0 : x ≠ c0) (hxJ : x ≠ vJ) (a : DS VV MM)
    (hle : a.env x ≤ (a.ram m).length) (hW : a.env x < 2 ^ C.Wd) :
    Hs C (seekP m x) a (a.rc m + 5 * a.env x + 6) (fun b => b.ram = a.ram ∧
      b.rc = Function.update a.rc m (a.env x) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, vJ]) := by
  refine Hs.mono (Hs.seq (hs_rwM C m a) (fun b hb => ?_)) (show a.rc m + 1 + (a.env x * (1 + 4) + 4) + 1 ≤ _
    by omega) (fun _ h => h)
  subst hb
  refine Hs.mono (advP_spec m x hx0 hxJ (a.rew m) (by simp [DS.rew]; exact hle) hW) le_rfl ?_
  rintro b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨h1, by rw [h2]; simp [DS.rew], h3, h4, h5, h6, h7, h8⟩

/-! ## One witness block -/

def fR : Fin VV := ⟨117, by decide⟩

/-- One witness block `[L] ++ coefficients`: if its role (the constant `κv`) is the current role `fR`, append the
form's `(pos, neg)` parts over the gate bits to `sG`; otherwise skip it. -/
def blockP (κv : Fin VV) : St VV MM :=
  .seq (.op (.rdM sN fL)) (.ite (.eq fR κv)
    (.seq (.op (.zero gPos)) (.seq (.op (.zero gNeg)) (.seq linP (.seq (.op (.rwM sB))
      (.seq (.op (.wrM sG gPos)) (.op (.wrM sG gNeg)))))))
    (.seq (advP sN fL) (advP sN fL)))

def bkT : List (Fin VV) := [fL, c0, c3, gS0, gS1, gZ, gPos, gNeg, vJ]

theorem blockP_spec (κv : Fin VV) (hκ : κv = vZ ∨ κv = v1) (a : DS VV MM) (hc : Cst a)
    (cs : List ℤ) (R : List ℕ) (hsN : (a.ram sN).drop (a.rc sN) = [cs.length] ++ (cs.flatMap intN ++ R))
    (vals Z : List ℕ) (hsB : a.ram sB = vals ++ Z) (hvl : a.env fR = a.env κv → vals.length = cs.length)
    (hB0 : a.rc sB = 0) (hG : a.rc sG ≤ (a.ram sG).length) (hLW : cs.length < 2 ^ C.Wd)
    (hW : (cs.map Int.natAbs).sum < 2 ^ C.Wd) :
    Hs C (blockP κv) a (15 * cs.length + 17) (fun b =>
      (a.env fR = a.env κv → b.ram = Function.update a.ram sG
          (putAt (putAt (a.ram sG) (a.rc sG) (posPart cs vals)) (a.rc sG + 1) (negPart cs vals)) ∧
        b.rc = Function.update (Function.update a.rc sN (a.rc sN + 1 + 2 * cs.length)) sG (a.rc sG + 2)) ∧
      (a.env fR ≠ a.env κv → b.ram = a.ram ∧ b.rc = Function.update a.rc sN (a.rc sN + 1 + 2 * cs.length)) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b bkT) := by
  set L := cs.length with hL
  set p0 := a.rc sN with hp0
  have hsb : sN ≠ sB := by decide
  have hsg : sN ≠ sG := by decide
  have hbg : sB ≠ sG := by decide
  have hlen : p0 + 1 + 2 * L ≤ (a.ram sN).length := by
    have := congrArg List.length hsN
    rw [List.length_drop, List.length_append, List.length_append, CounterMachine.flatMap_intN_length] at this
    simp at this; omega
  have f0 : (a.ram sN).getD p0 0 = L := fld_of_drop (B := _) hsN
  have f0' := f0
  rw [List.getD_eq_getElem?_getD] at f0'
  have hd1 : (a.ram sN).drop (p0 + 1) = cs.flatMap intN ++ R := drop_split' hsN 1 rfl
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 15 * L + 15) (hs_rdM C sN fL a (by omega)) (fun e1 he1 => ?_))
    (by omega) (fun _ h => h)
  subst he1
  set e1 := (a.set fL ((a.ram sN).getD p0 0)).adv sN with he1
  have e1L : e1.env fL = L := by simp only [he1, DS.adv]; vsimp [f0']
  have e1fr : Fr a e1 bkT := by
    intro y hy
    have hne : y ≠ fL := fun h => hy (by rw [h]; decide)
    simp only [he1, DS.adv, DS.set, Function.update_of_ne hne]
  have e1c : Cst e1 := Cst.of_fr hc e1fr (by decide)
  have e1ram : e1.ram = a.ram := rfl
  have e1rc : e1.rc = Function.update a.rc sN (p0 + 1) := rfl
  have e1R : e1.env fR = a.env fR := e1fr fR (by decide)
  have e1κ : e1.env κv = a.env κv := e1fr κv (by rcases hκ with h | h <;> subst h <;> decide)
  refine Hs.ite (show fR ≠ κv by rcases hκ with h | h <;> subst h <;> decide) (fun ht => ?_) (fun ht => ?_)
  · simp only [Cnd.eval, e1R, e1κ, decide_eq_true_eq] at ht
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 15 * L + 12) (hs_zero C gPos e1) (fun e2 he2 => ?_)) (by omega)
      (fun _ h => h)
    subst he2
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 15 * L + 10) (hs_zero C gNeg _) (fun e3 he3 => ?_)) (by omega)
      (fun _ h => h)
    subst he3
    set e3 := (e1.set gPos 0).set gNeg 0 with he3
    have e3rc : e3.rc = Function.update a.rc sN (p0 + 1) := rfl
    have e3fr : Fr e1 e3 bkT := Fr.trans (Fr.set e1 (x := gPos) 0 (by decide)) (Fr.set _ (x := gNeg) 0 (by decide))
    have e3c : Cst e3 := Cst.of_fr e1c e3fr (by decide)
    have q1 : e3.env fL = L := by simp only [he3]; vsimp [e1L]
    have q2 : (e3.ram sN).drop (e3.rc sN) = cs.flatMap intN ++ R := by
      simp only [he3, DS.set_ram, DS.set_rc]; rw [e1rc, e1ram]; simp; exact hd1
    have q3 : e3.rc sB = 0 := by
      simp only [he3, DS.set_rc]; rw [e1rc, Function.update_of_ne (Ne.symm hsb)]; exact hB0
    have q4 : e3.env gPos = 0 := by simp only [he3]; vsimp []
    have q5 : e3.env gNeg = 0 := by simp only [he3]; vsimp []
    have hlin := linP_spec e3 e3c L q1 hLW cs rfl R q2 vals Z hsB (hvl ht) q3 q4 q5 hW
    refine Hs.mono (Hs.seq (t1 := 14 * L + 4) (t2 := L + 5) (Hs.mono hlin (by ring_nf; omega) (fun _ h => h))
      (fun e4 he4 => ?_)) (by omega) (fun _ h => h)
    obtain ⟨h4p, h4n, h4rc, h4ram, h4ip, h4out, h4kin, h4kout, h4kc, h4fr⟩ := he4
    have e4B : e4.rc sB = L := by rw [h4rc]; simp
    refine Hs.mono (Hs.seq (t1 := L + 1) (t2 := 3) (Hs.mono (hs_rwM C sB e4) (by rw [e4B]) (fun _ h => h))
      (fun e5 he5 => ?_)) (by omega) (fun _ h => h)
    subst he5
    have e5G : (e4.rew sB).rc sG = a.rc sG := by
      simp only [DS.rew]; rw [Function.update_of_ne (Ne.symm hbg), h4rc, Function.update_of_ne (Ne.symm hbg),
        Function.update_of_ne (Ne.symm hsg)]; rfl
    have e5Gm : (e4.rew sB).ram sG = a.ram sG := by simp only [DS.rew]; rw [h4ram]; rfl
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_wrM C sG gPos _ (by rw [e5G, e5Gm]; exact hG)) (fun e6 he6 => ?_)
    subst he6
    refine Hs.mono (hs_wrM C sG gNeg _ (by
      simp only [DS.put, Function.update_self]; rw [e5G, e5Gm, putAt_length _ _ _ hG]; omega)) le_rfl ?_
    rintro b rfl
    have e5p : (e4.rew sB).env gPos = posPart cs vals := h4p
    have e5n : (e4.rew sB).env gNeg = negPart cs vals := h4n
    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd ht h, ?_⟩
    · simp only [DS.put, Function.update_self, Function.update_idem]
      rw [e5n, e5G, e5p, e5Gm]
      show Function.update e4.ram sG _ = _
      rw [h4ram]; rfl
    · simp only [DS.put, Function.update_self, Function.update_idem]
      rw [e5G]; simp only [DS.rew]; rw [h4rc]
      funext m; by_cases h1 : m = sG
      · subst h1; simp
      · by_cases h2 : m = sB
        · subst h2; simp [Function.update_of_ne h1, hB0, Function.update_of_ne (Ne.symm hsb)]
        · by_cases h3 : m = sN
          · subst h3; simp [Function.update_of_ne hsb, Function.update_of_ne hsg, e3rc]
          · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3, e3rc]
    · refine ⟨h4ip, h4out, h4kin, h4kout, h4kc, ?_⟩
      exact Fr.trans (Fr.trans e1fr e3fr) (Fr.weaken h4fr (by decide))
  · simp only [Cnd.eval, e1R, e1κ, decide_eq_false_iff_not] at ht
    have hx0 : fL ≠ c0 := by decide
    have hxJ : fL ≠ vJ := by decide
    have q1 : e1.rc sN + e1.env fL ≤ (e1.ram sN).length := by rw [e1L, e1rc, e1ram]; simp; omega
    have ha1 := advP_spec sN fL hx0 hxJ e1 q1 (by rw [e1L]; exact hLW)
    rw [e1L] at ha1
    refine Hs.mono (Hs.seq (t1 := L * (1 + 4) + 4) (t2 := L * (1 + 4) + 4) ha1
      (fun e2 ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ?_)) (by omega) (fun _ h => h)
    have e2L : e2.env fL = L := by rw [h8 fL (by decide)]; exact e1L
    have q2 : e2.rc sN + e2.env fL ≤ (e2.ram sN).length := by rw [e2L, h2, h1, e1rc, e1ram]; simp; omega
    have ha2 := advP_spec sN fL hx0 hxJ e2 q2 (by rw [e2L]; exact hLW)
    rw [e2L] at ha2
    refine Hs.mono ha2 le_rfl ?_
    rintro b ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩
    refine ⟨fun h => absurd h ht, fun _ => ⟨by rw [g1, h1]; rfl, ?_⟩, g3.trans h3, g4.trans h4, g5.trans h5,
      g6.trans h6, g7.trans h7, Fr.trans e1fr (Fr.trans (Fr.weaken h8 (by decide)) (Fr.weaken g8 (by decide)))⟩
    rw [g2, h2, e1rc]
    funext m; by_cases hm : m = sN
    · subst hm; simp; omega
    · simp [hm]

/-! ## One stage: the blocks of all roles -/

/-- The witness blocks of stage `s`. -/
def blocksOf (cf : ℕ → ℕ → List ℤ) (s rc : ℕ) : List ℕ :=
  (List.range rc).flatMap fun ρ => [(cf s ρ).length] ++ (cf s ρ).flatMap intN

def stageP : St VV MM := .seq (blockP vZ) (.ite (.eq gRC v2) (blockP v1) skipS)

theorem blocksOf_one (cf : ℕ → ℕ → List ℤ) (s : ℕ) :
    blocksOf cf s 1 = [(cf s 0).length] ++ ((cf s 0).flatMap intN ++ []) := by simp [blocksOf]

theorem blocksOf_two (cf : ℕ → ℕ → List ℤ) (s : ℕ) :
    blocksOf cf s 2 = [(cf s 0).length] ++ ((cf s 0).flatMap intN ++
      ([(cf s 1).length] ++ ((cf s 1).flatMap intN ++ []))) := by
  simp [blocksOf, List.range_succ, List.append_assoc]

/-- **One stage**: the blocks of every role of stage `s`; the block of the current role `r = fR` appends its form's
`(pos, neg)` parts to `sG`. -/
theorem stageP_spec (a : DS VV MM) (hc : Cst a) (rc r : ℕ) (hrc : rc = 1 ∨ rc = 2) (hr : r < rc)
    (hR : a.env fR = r) (hRC : a.env gRC = rc) (cf : ℕ → ℕ → List ℤ) (s : ℕ) (R : List ℕ)
    (hsN : (a.ram sN).drop (a.rc sN) = blocksOf cf s rc ++ R)
    (vals Z : List ℕ) (hsB : a.ram sB = vals ++ Z) (hvl : vals.length = (cf s r).length) (hB0 : a.rc sB = 0)
    (hG : a.rc sG ≤ (a.ram sG).length) (Gm : ℕ) (hGm : ∀ ρ < rc, (cf s ρ).length ≤ Gm)
    (hLW : Gm < 2 ^ C.Wd) (hW : ∀ ρ < rc, ((cf s ρ).map Int.natAbs).sum < 2 ^ C.Wd) :
    Hs C stageP a (30 * Gm + 40) (fun b =>
      b.ram = Function.update a.ram sG
          (putAt (putAt (a.ram sG) (a.rc sG) (posPart (cf s r) vals)) (a.rc sG + 1) (negPart (cf s r) vals)) ∧
      b.rc = Function.update (Function.update a.rc sN (a.rc sN + (blocksOf cf s rc).length)) sG (a.rc sG + 2) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b bkT) := by
  have hsg : sN ≠ sG := by decide
  have hsb : sN ≠ sB := by decide
  have hbg : sB ≠ sG := by decide
  have hG0 := hGm 0 (by omega)
  have hW0 := hW 0 (by omega)
  have hs0 : ∃ rest, (a.ram sN).drop (a.rc sN) = [(cf s 0).length] ++ ((cf s 0).flatMap intN ++ rest) := by
    rw [hsN]
    rcases hrc with h | h <;> subst h
    · exact ⟨R, by rw [blocksOf_one]; simp⟩
    · exact ⟨[(cf s 1).length] ++ ((cf s 1).flatMap intN ++ R), by rw [blocksOf_two]; simp⟩
  obtain ⟨rest, hs0⟩ := hs0
  refine Hs.mono (Hs.seq (t1 := 15 * (cf s 0).length + 17) (t2 := 15 * Gm + 18)
    (blockP_spec vZ (Or.inl rfl) a hc (cf s 0) rest hs0 vals Z hsB
      (fun h => by rw [hR, hc.z] at h; subst h; exact hvl) hB0 hG (by omega) hW0)
    (fun e1 he1 => ?_)) (by omega) (fun _ h => h)
  obtain ⟨hit1, miss1, i3, i4, i5, i6, i7, i8⟩ := he1
  have e1c : Cst e1 := Cst.of_fr hc i8 (by decide)
  have e1RC : e1.env gRC = rc := by rw [i8 gRC (by decide)]; exact hRC
  have e1R : e1.env fR = r := by rw [i8 fR (by decide)]; exact hR
  set L0 := (cf s 0).length with hL0
  set g0 := a.rc sG with hg0
  have hz0 : (a.env fR = a.env vZ) ↔ r = 0 := by rw [hR, hc.z]
  have e1N : e1.ram sN = a.ram sN := by
    by_cases h : a.env fR = a.env vZ
    · rw [(hit1 h).1, Function.update_of_ne hsg]
    · rw [(miss1 h).1]
  have e1Nc : e1.rc sN = a.rc sN + 1 + 2 * L0 := by
    by_cases h : a.env fR = a.env vZ
    · rw [(hit1 h).2, Function.update_of_ne hsg, Function.update_self]
    · rw [(miss1 h).2, Function.update_self]
  have e1B : e1.ram sB = a.ram sB := by
    by_cases h : a.env fR = a.env vZ
    · rw [(hit1 h).1, Function.update_of_ne hbg]
    · rw [(miss1 h).1]
  have e1Bc : e1.rc sB = 0 := by
    by_cases h : a.env fR = a.env vZ
    · rw [(hit1 h).2, Function.update_of_ne hbg, Function.update_of_ne (Ne.symm hsb)]; exact hB0
    · rw [(miss1 h).2, Function.update_of_ne (Ne.symm hsb)]; exact hB0
  have e1G : e1.rc sG ≤ (e1.ram sG).length := by
    by_cases h : a.env fR = a.env vZ
    · have hl1 := putAt_length (a.ram sG) g0 (posPart (cf s 0) vals) hG
      have hl2 := putAt_length (putAt (a.ram sG) g0 (posPart (cf s 0) vals)) (g0 + 1) (negPart (cf s 0) vals)
        (by rw [hl1]; omega)
      rw [(hit1 h).1, (hit1 h).2, Function.update_self, Function.update_self, hl2, hl1]; omega
    · rw [(miss1 h).1, (miss1 h).2, Function.update_of_ne (Ne.symm hsg)]; exact hG
  have e1Gm : a.env fR ≠ a.env vZ → e1.ram sG = a.ram sG ∧ e1.rc sG = g0 := by
    intro h; rw [(miss1 h).1, (miss1 h).2, Function.update_of_ne (Ne.symm hsg)]; exact ⟨rfl, rfl⟩
  refine Hs.ite (show gRC ≠ v2 by decide) (fun ht => ?_) (fun ht => ?_)
  · simp only [Cnd.eval, e1RC, e1c.two, decide_eq_true_eq] at ht
    subst ht
    set L1 := (cf s 1).length with hL1
    have hG1 := hGm 1 (by omega)
    have hblen : (blocksOf cf s 2).length = 1 + 2 * L0 + (1 + 2 * L1) := by
      rw [blocksOf_two]
      simp only [List.length_append, List.length_singleton, CounterMachine.flatMap_intN_length, List.length_nil]
      omega
    have hs1 : (e1.ram sN).drop (e1.rc sN) = [L1] ++ ((cf s 1).flatMap intN ++ R) := by
      rw [e1N, e1Nc]
      have h2 : (a.ram sN).drop (a.rc sN) = ([L0] ++ (cf s 0).flatMap intN) ++ ([L1] ++ ((cf s 1).flatMap intN ++ R)) := by
        rw [hsN, blocksOf_two]; simp [List.append_assoc, hL0, hL1]
      have h3 := drop_split h2
      have h4 : ([L0] ++ (cf s 0).flatMap intN).length = 1 + 2 * L0 := by
        simp only [List.length_append, List.length_singleton, CounterMachine.flatMap_intN_length]; omega
      rw [h4] at h3; rw [show a.rc sN + 1 + 2 * L0 = a.rc sN + (1 + 2 * L0) by omega]; exact h3
    refine Hs.mono (blockP_spec v1 (Or.inr rfl) e1 e1c (cf s 1) R hs1 vals Z (by rw [e1B]; exact hsB)
      (fun h => by rw [e1R, e1c.one] at h; subst h; exact hvl) e1Bc e1G (by omega) (hW 1 (by omega)))
      (by omega) ?_
    rintro b ⟨hit2, miss2, j3, j4, j5, j6, j7, j8⟩
    have hrest : b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b bkT :=
      ⟨j3.trans i3, j4.trans i4, j5.trans i5, j6.trans i6, j7.trans i7, Fr.trans i8 j8⟩
    by_cases hr0 : r = 0
    · subst hr0
      have h0 : a.env fR = a.env vZ := hz0.2 rfl
      have hn1 : e1.env fR ≠ e1.env v1 := by rw [e1R, e1c.one]; omega
      obtain ⟨b1, b2⟩ := miss2 hn1
      obtain ⟨k1, k2⟩ := hit1 h0
      refine ⟨by rw [b1, k1], ?_, hrest⟩
      rw [b2, e1Nc, k2, hblen]
      funext m; by_cases hm : m = sG
      · subst hm; simp [Function.update_of_ne (Ne.symm hsg)]
      · by_cases hn : m = sN
        · subst hn; simp [Function.update_of_ne hsg]; omega
        · simp [Function.update_of_ne hm, Function.update_of_ne hn]
    · have hr1 : r = 1 := by omega
      subst hr1
      have h0 : a.env fR ≠ a.env vZ := fun h => hr0 (hz0.1 h)
      have hh1 : e1.env fR = e1.env v1 := by rw [e1R, e1c.one]
      obtain ⟨b1, b2⟩ := hit2 hh1
      obtain ⟨k1, k2⟩ := miss1 h0
      obtain ⟨m1, m2⟩ := e1Gm h0
      refine ⟨by rw [b1, m1, m2, k1], ?_, hrest⟩
      rw [b2, e1Nc, m2, k2, hblen]
      funext m; by_cases hm : m = sG
      · subst hm; simp [Function.update_of_ne (Ne.symm hsg)]
      · by_cases hn : m = sN
        · subst hn; simp [Function.update_of_ne hsg]; omega
        · simp [Function.update_of_ne hm, Function.update_of_ne hn]
  · simp only [Cnd.eval, e1RC, e1c.two, decide_eq_false_iff_not] at ht
    have hrc1 : rc = 1 := by omega
    subst hrc1
    have hr0 : r = 0 := by omega
    subst hr0
    obtain ⟨k1, k2⟩ := hit1 (hz0.2 rfl)
    have hblen : (blocksOf cf s 1).length = 1 + 2 * L0 := by
      rw [blocksOf_one]
      simp only [List.length_append, List.length_singleton, CounterMachine.flatMap_intN_length, List.length_nil]
      omega
    refine Hs.mono (skip_spec e1) (by omega) ?_
    rintro b rfl
    refine ⟨by rw [DS.set_ram, k1], ?_, i3, i4, i5, i6, i7, Fr.trans i8 (Fr.set e1 0 (by decide))⟩
    rw [DS.set_rc, k2, hblen]
    congr 1; congr 1; omega

end NearCubicGates.Close.Cells
