import Proof.Gates.Cells.Zb

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

def gPos : Fin VV := ⟨110, by decide⟩
def gNeg : Fin VV := ⟨111, by decide⟩
def gS0 : Fin VV := ⟨112, by decide⟩
def gS1 : Fin VV := ⟨113, by decide⟩
def gZ : Fin VV := ⟨114, by decide⟩

/-! ## Value level -/

/-- The signed sum `Σ_j w_j·[z_j = 1]`. -/
def wsum : List ℤ → List ℕ → ℤ
  | w :: ws, z :: zs => (if z = 1 then w else 0) + wsum ws zs
  | _, _ => 0

/-- Positive and negative parts accumulated by the machine. -/
def posPart : List ℤ → List ℕ → ℕ
  | w :: ws, z :: zs => (if z = 1 ∧ ¬ w < 0 then w.natAbs else 0) + posPart ws zs
  | _, _ => 0

def negPart : List ℤ → List ℕ → ℕ
  | w :: ws, z :: zs => (if z = 1 ∧ w < 0 then w.natAbs else 0) + negPart ws zs
  | _, _ => 0

theorem wsum_parts : ∀ (ws : List ℤ) (zs : List ℕ), wsum ws zs = (posPart ws zs : ℤ) - negPart ws zs
  | w :: ws, z :: zs => by
    simp only [wsum, posPart, negPart, wsum_parts ws zs]
    by_cases hz : z = 1 <;> by_cases hw : w < 0 <;>
      simp only [hz, hw, true_and, and_true, not_false_eq_true, not_true_eq_false, and_false, false_and, if_true,
        if_false, Nat.cast_add, Nat.cast_zero] <;> omega
  | [], _ => by simp [wsum, posPart, negPart]
  | _ :: _, [] => by simp [wsum, posPart, negPart]

theorem sum_eq_wsum : ∀ (n : ℕ) (w : Fin n → ℤ) (zb : List ℕ), zb.length = n →
    (∑ i, w i * (if zb.getD i.val 0 = 1 then 1 else 0)) = wsum (List.ofFn w) zb
  | 0, w, zb, h => by simp [wsum]
  | n + 1, w, zb, h => by
    cases zb with
    | nil => simp at h
    | cons z zb =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [Fin.sum_univ_succ, List.ofFn_succ, wsum]
      have ih := sum_eq_wsum n (fun i => w i.succ) zb h
      simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ] at ih ⊢
      rw [ih]
      split_ifs <;> simp

theorem eval_eq_wsum {n : ℕ} (g : NormalizedThresholdGate n) (z : BitInput n) (zb : List ℕ)
    (hz : ∀ j : Fin n, z j = decide (zb.getD j.val 0 = 1)) (hlen : zb.length = n) :
    g.eval z = decide (g.threshold ≤ wsum (List.ofFn g.weight) zb) := by
  unfold NormalizedThresholdGate.eval
  rw [← sum_eq_wsum n g.weight zb hlen]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [hz i]
  by_cases h : zb.getD i.val 0 = 1 <;> simp [h]

theorem posPart_take_succ (ws : List ℤ) (zs : List ℕ) (k : ℕ) (hk : k < ws.length) (hz : k < zs.length) :
    posPart (ws.take (k + 1)) (zs.take (k + 1)) = posPart (ws.take k) (zs.take k) +
      (if zs[k] = 1 ∧ ¬ ws[k] < 0 then ws[k].natAbs else 0) ∧
    negPart (ws.take (k + 1)) (zs.take (k + 1)) = negPart (ws.take k) (zs.take k) +
      (if zs[k] = 1 ∧ ws[k] < 0 then ws[k].natAbs else 0) := by
  induction ws generalizing zs k with
  | nil => simp at hk
  | cons w ws ih =>
    cases zs with
    | nil => simp at hz
    | cons z zs =>
      cases k with
      | zero => simp [posPart, negPart]
      | succ k =>
        simp only [List.take_succ_cons, posPart, negPart, List.getElem_cons_succ]
        have := ih zs k (by simpa using hk) (by simpa using hz)
        omega

theorem posPart_le : ∀ (ws : List ℤ) (zs : List ℕ), posPart ws zs + negPart ws zs ≤ (ws.map Int.natAbs).sum
  | w :: ws, z :: zs => by
    simp only [posPart, negPart, List.map_cons, List.sum_cons]
    have := posPart_le ws zs
    split_ifs <;> omega
  | [], _ => by simp [posPart, negPart]
  | _ :: _, [] => by simp [posPart, negPart]

theorem natAbs_sum_take (ws : List ℤ) (k : ℕ) : ((ws.take k).map Int.natAbs).sum ≤ (ws.map Int.natAbs).sum := by
  rw [List.map_take]
  exact (List.take_sublist _ _).sum_le_sum (fun _ _ => Nat.zero_le _)

/-- `gPos − gNeg += Σ_j w_j·z_j` over the next `n` weight fields of `sN` and the z-bits of `sZb` (counter `c3`). -/
def wsumP : St VV MM :=
  forS c3 gN (.seq (.op (.rdM sN gS0)) (.seq (.op (.rdM sN gS1)) (.seq (.op (.rdM sZb gZ))
    (.ite (.eq gZ v1) (.ite (.eq gS0 vZ) (.op (.add gPos gS1)) (.op (.add gNeg gS1))) skipS))))

def wsumT : List (Fin VV) := [c3, gS0, gS1, gZ, gPos, gNeg, vJ]

theorem wsumP_spec (a : DS VV MM) (hc : Cst a) (n : ℕ) (hn : a.env gN = n) (hnW : n < 2 ^ C.Wd)
    (ws : List ℤ) (hws : ws.length = n) (R : List ℕ) (hsN : (a.ram sN).drop (a.rc sN) = ws.flatMap intN ++ R)
    (zb : List ℕ) (hzb : a.ram sZb = zb) (hzl : zb.length = n) (hz0 : a.rc sZb = 0)
    (hp0 : a.env gPos = 0) (hn0 : a.env gNeg = 0) (hB : (ws.map Int.natAbs).sum < 2 ^ C.Wd) :
    Hs C wsumP a (n * (1 + (1 + (1 + 4 + 1) + 1) + 1 + 4) + 4)
      (fun b => b.env gPos = posPart ws zb ∧ b.env gNeg = negPart ws zb ∧
        b.rc = Function.update (Function.update a.rc sN (a.rc sN + 2 * n)) sZb n ∧
        b.ram = a.ram ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
        Fr a b wsumT) := by
  have hsd : sN ≠ sZb := by decide
  set p0 := a.rc sN
  let I : ℕ → DS VV MM → Prop := fun k e => e.env gPos = posPart (ws.take k) (zb.take k) ∧
    e.env gNeg = negPart (ws.take k) (zb.take k) ∧
    e.rc = Function.update (Function.update a.rc sN (p0 + 2 * k)) sZb k ∧
    e.ram = a.ram ∧ e.ip = a.ip ∧ e.out = a.out ∧ e.kin = a.kin ∧ e.kout = a.kout ∧ e.kc = a.kc ∧ Fr a e wsumT
  have hl := forS_spec' (C := C) c3 gN (by decide) (.seq (.op (.rdM sN gS0)) (.seq (.op (.rdM sN gS1))
    (.seq (.op (.rdM sZb gZ)) (.ite (.eq gZ v1) (.ite (.eq gS0 vZ) (.op (.add gPos gS1)) (.op (.add gNeg gS1)))
      skipS)))) a n hnW I (1 + (1 + (1 + 4 + 1) + 1) + 1)
    (fun k e v ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1,
      by rw [DS.set_env_ne _ _ (by decide)]; exact i2, i3, i4, i5, i6, i7, i8, i9, Fr.trans i10 (Fr.set e v (by decide))⟩)
    ⟨by simp [hp0, posPart], by simp [hn0, negPart],
      by funext m; by_cases h1 : m = sZb
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
    have eZ : e.ram sZb = zb := by rw [i4, hzb]
    have eZc : e.rc sZb = k := by rw [i3]; simp
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
    have e2Z : e2.ram sZb = zb := by simp [he2, he1, DS.adv, DS.set, eZ]
    have e2Zc : e2.rc sZb = k := by simp [he2, he1, DS.adv, DS.set, Function.update_of_ne (Ne.symm hsd), eZc]
    have e2m : e2.env gS1 = ws[k].natAbs := by
      simp only [he2, DS.adv, DS.set_env_self, e1N, e1Nc]; exact g1
    have e2s : e2.env gS0 = if ws[k] < 0 then 1 else 0 := by simp only [he2, DS.adv]; vsimp [e1s]
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 4) (hs_rdM C sZb gZ e2 (by rw [e2Zc, e2Z]; omega))
      (fun e3 he3 => ?_)) (by norm_num) (fun _ h => h)
    subst he3
    set e3 := (e2.set gZ ((e2.ram sZb).getD (e2.rc sZb) 0)).adv sZb with he3
    have e3z : e3.env gZ = zb[k] := by
      simp only [he3, DS.adv, DS.set_env_self, e2Z, e2Zc]; rw [List.getD_eq_getElem _ _ hkz]
    have e3m : e3.env gS1 = ws[k].natAbs := by simp only [he3, DS.adv]; vsimp [e2m]
    have e3s : e3.env gS0 = if ws[k] < 0 then 1 else 0 := by simp only [he3, DS.adv]; vsimp [e2s]
    have e3p : e3.env gPos = posPart (ws.take k) (zb.take k) := by
      simp only [he3, he2, he1, DS.adv]; vsimp [i1]
    have e3n : e3.env gNeg = negPart (ws.take k) (zb.take k) := by
      simp only [he3, he2, he1, DS.adv]; vsimp [i2]
    have e3v1 : e3.env v1 = 1 := by simp only [he3, he2, he1, DS.adv]; vsimp [hc'.one]
    have e3vZ : e3.env vZ = 0 := by simp only [he3, he2, he1, DS.adv]; vsimp [hc'.z]
    have e3c : e3.env c3 = k := by simp only [he3, he2, he1, DS.adv]; vsimp [hek]
    have e3n' : e3.env gN = n := by simp only [he3, he2, he1, DS.adv]; vsimp [hem]
    have e3fr : Fr a e3 wsumT := by
      intro y hy
      simp only [wsumT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp only [he3, he2, he1, DS.adv, DS.set]
      rw [Function.update_of_ne hy.2.2.2.1, Function.update_of_ne hy.2.2.1, Function.update_of_ne hy.2.1]
      exact i10 y (by simp [wsumT]; tauto)
    have e3rc : e3.rc = Function.update (Function.update a.rc sN (p0 + 2 * (k + 1))) sZb (k + 1) := by
      simp only [he3, he2, he1, DS.adv, DS.set]
      rw [i3]
      funext m; by_cases h1 : m = sZb
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
        I (k + 1) (e3.set x v) ∧ (e3.set x v).env c3 = k ∧ (e3.set x v).env gN = n := by
      intro x v hx q1 q2
      have hxc : c3 ≠ x := by intro h; rw [← h] at hx; revert hx; decide
      have hxn : gN ≠ x := by intro h; rw [← h] at hx; revert hx; decide
      refine ⟨⟨q1, q2, e3rc, e3rest.1, e3rest.2.1, e3rest.2.2.1, e3rest.2.2.2.1, e3rest.2.2.2.2.1,
        e3rest.2.2.2.2.2, Fr.trans e3fr (Fr.set e3 v (by simp [wsumT] at hx ⊢; tauto))⟩, ?_, ?_⟩
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

/-! ## One gate -/

/-- The value of a gate at the z-bits `zb`, as `0/1`. -/
def gbit {n : ℕ} (g : NormalizedThresholdGate n) (zb : List ℕ) : ℕ :=
  if g.threshold ≤ wsum (List.ofFn g.weight) zb then 1 else 0

/-- One gate: skip its arity field, sum its weights over `sZb`, compare with the threshold, append the bit to `sB`. -/
def gateBody : St VV MM :=
  .seq (.op (.rdM sN gS0)) (.seq (.op (.zero gPos)) (.seq (.op (.zero gNeg)) (.seq wsumP
    (.seq (.op (.rdM sN gS0)) (.seq (.op (.rdM sN gS1)) (.seq
      (.ite (.eq gS0 vZ) (.seq (.op (.add gS1 gNeg)) (.ite (.lt gPos gS1) (.op (.zero gZ)) (.op (.copy gZ v1))))
        (.seq (.op (.add gS1 gPos)) (.ite (.lt gS1 gNeg) (.op (.zero gZ)) (.op (.copy gZ v1)))))
      (.seq (.op (.wrM sB gZ)) (.op (.rwM sZb)))))))))

theorem gbit_cmp {n : ℕ} (g : NormalizedThresholdGate n) (zb : List ℕ) :
    gbit g zb = if g.threshold < 0 then (if posPart (List.ofFn g.weight) zb + g.threshold.natAbs <
        negPart (List.ofFn g.weight) zb then 0 else 1)
      else (if posPart (List.ofFn g.weight) zb < g.threshold.natAbs + negPart (List.ofFn g.weight) zb then 0
        else 1) := by
  unfold gbit
  rw [wsum_parts]
  split_ifs <;> omega

theorem gateBody_spec {n : ℕ} (e : DS VV MM) (hc : Cst e) (g : NormalizedThresholdGate n) (hn : e.env gN = n)
    (hnW : n < 2 ^ C.Wd) (R : List ℕ) (hsN : (e.ram sN).drop (e.rc sN) = gateN g ++ R)
    (zb : List ℕ) (hzb : e.ram sZb = zb) (hzl : zb.length = n) (hz0 : e.rc sZb = 0)
    (hsB : e.rc sB ≤ (e.ram sB).length)
    (hW : ((List.ofFn g.weight).map Int.natAbs).sum + g.threshold.natAbs < 2 ^ C.Wd) :
    Hs C gateBody e (15 * n + 24)
      (fun d => d.ram = Function.update e.ram sB (putAt (e.ram sB) (e.rc sB) (gbit g zb)) ∧
        d.rc = Function.update (Function.update e.rc sN (e.rc sN + (2 * n + 3))) sB (e.rc sB + 1) ∧
        d.ip = e.ip ∧ d.out = e.out ∧ d.kin = e.kin ∧ d.kout = e.kout ∧ d.kc = e.kc ∧ Fr e d wsumT) := by
  set ws := List.ofFn g.weight with hws
  have hwl : ws.length = n := by simp [hws]
  have hsd : sN ≠ sZb := by decide
  have hsb : sN ≠ sB := by decide
  have hzbB : sZb ≠ sB := by decide
  set p0 := e.rc sN with hp0
  have hg : gateN g = [n] ++ (ws.flatMap intN ++ intN g.threshold) := by
    simp [gateN, hws, List.append_assoc]
  rw [hg, List.append_assoc] at hsN
  have hlen : p0 < (e.ram sN).length := by
    have := congrArg List.length hsN; simp at this; omega
  have hd1 : (e.ram sN).drop (p0 + 1) = ws.flatMap intN ++ (intN g.threshold ++ R) := by
    rw [drop_split' hsN 1 rfl, List.append_assoc]
  have hd2 : (e.ram sN).drop (p0 + 1 + 2 * n) = [if g.threshold < 0 then 1 else 0] ++
      (g.threshold.natAbs :: R) := by
    rw [drop_split' hd1 (2 * n) (by rw [CounterMachine.flatMap_intN_length, hwl])]; rfl
  have hlen2 : p0 + 1 + 2 * n + 1 < (e.ram sN).length := by
    have := congrArg List.length hd2; simp at this; omega
  have f0 : (e.ram sN).getD p0 0 = n := fld_of_drop (B := _) (by rw [hsN]; rfl)
  have f1 : (e.ram sN).getD (p0 + 1 + 2 * n) 0 = if g.threshold < 0 then 1 else 0 := fld_of_drop (B := _) hd2
  have f2 : (e.ram sN).getD (p0 + 1 + 2 * n + 1) 0 = g.threshold.natAbs :=
    fld_of_drop (B := _) (drop_split' hd2 1 rfl)
  have f1' := f1; have f2' := f2
  rw [List.getD_eq_getElem?_getD] at f1' f2'
  -- arity field
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 15 * n + 22) (hs_rdM C sN gS0 e (by omega)) (fun e1 he1 => ?_))
    (by omega) (fun _ h => h)
  subst he1
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 15 * n + 20) (hs_zero C gPos _) (fun e2 he2 => ?_))
    (by omega) (fun _ h => h)
  subst he2
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 15 * n + 18) (hs_zero C gNeg _) (fun e3 he3 => ?_))
    (by omega) (fun _ h => h)
  subst he3
  set e3 := ((((e.set gS0 ((e.ram sN).getD p0 0)).adv sN).set gPos 0).set gNeg 0) with he3
  have e3fr : Fr e e3 wsumT := by
    intro y hy; simp only [wsumT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [he3, DS.adv]; vsimp [Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2.2.2.1,
      Function.update_of_ne hy.2.2.2.2.2.1]
  have e3c : Cst e3 := Cst.of_fr hc e3fr (by decide)
  have e3ram : e3.ram = e.ram := rfl
  have e3rc : e3.rc = Function.update e.rc sN (p0 + 1) := by simp only [he3, DS.adv, DS.set]; rfl
  have e3N : (e3.ram sN).drop (e3.rc sN) = ws.flatMap intN ++ (intN g.threshold ++ R) := by
    rw [e3ram, e3rc]; simp; exact hd1
  have e3gN : e3.env gN = n := by rw [e3fr gN (by decide)]; exact hn
  have e3z : e3.ram sZb = zb := hzb
  have e3z0 : e3.rc sZb = 0 := by rw [e3rc, Function.update_of_ne (Ne.symm hsd)]; exact hz0
  have e3p : e3.env gPos = 0 := by simp only [he3]; vsimp []
  have e3n : e3.env gNeg = 0 := by simp only [he3]; vsimp []
  have hBw : (ws.map Int.natAbs).sum < 2 ^ C.Wd := by omega
  refine Hs.mono (Hs.seq (t1 := 14 * n + 4) (t2 := n + 13) (Hs.mono (wsumP_spec e3 e3c n e3gN hnW ws hwl
    (intN g.threshold ++ R) e3N zb e3z hzl e3z0 e3p e3n hBw) (by ring_nf; omega) (fun _ h => h))
    (fun e4 he4 => ?_)) (by omega) (fun _ h => h)
  obtain ⟨h4p, h4n, h4rc, h4ram, h4ip, h4out, h4kin, h4kout, h4kc, h4fr⟩ := he4
  have e4c : Cst e4 := Cst.of_fr e3c h4fr (by decide)
  have e4N : e4.ram sN = e.ram sN := by rw [h4ram]; rfl
  have e4Nc : e4.rc sN = p0 + 1 + 2 * n := by
    rw [h4rc, Function.update_of_ne hsd]; simp [e3rc]
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := n + 11) (hs_rdM C sN gS0 e4 (by rw [e4Nc, e4N]; omega))
    (fun e5 he5 => ?_)) (by omega) (fun _ h => h)
  subst he5
  set e5 := (e4.set gS0 ((e4.ram sN).getD (e4.rc sN) 0)).adv sN with he5
  have e5Nc : e5.rc sN = p0 + 1 + 2 * n + 1 := by simp [he5, DS.adv, e4Nc]
  have e5N : e5.ram sN = e.ram sN := by simp [he5, DS.adv, DS.set, e4N]
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := n + 9) (hs_rdM C sN gS1 e5 (by rw [e5Nc, e5N]; omega))
    (fun e6 he6 => ?_)) (by omega) (fun _ h => h)
  subst he6
  set e6 := (e5.set gS1 ((e5.ram sN).getD (e5.rc sN) 0)).adv sN with he6
  have e6s : e6.env gS0 = if g.threshold < 0 then 1 else 0 := by
    simp only [he6, he5, DS.adv]; vsimp [e4N, e4Nc, f1']
  have e6m : e6.env gS1 = g.threshold.natAbs := by
    simp only [he6, DS.adv]; vsimp [e5N, e5Nc, f2']
  have e6p : e6.env gPos = posPart ws zb := by simp only [he6, he5, DS.adv]; vsimp [h4p]
  have e6n : e6.env gNeg = negPart ws zb := by simp only [he6, he5, DS.adv]; vsimp [h4n]
  have e6z : e6.env vZ = 0 := by simp only [he6, he5, DS.adv]; vsimp [e4c.z]
  have e6one : e6.env v1 = 1 := by simp only [he6, he5, DS.adv]; vsimp [e4c.one]
  have hPN : posPart ws zb + negPart ws zb ≤ (ws.map Int.natAbs).sum := posPart_le ws zb
  have hcmp := gbit_cmp g zb
  rw [← hws] at hcmp

  have hite : Hs C (.ite (.eq gS0 vZ) (.seq (.op (.add gS1 gNeg)) (.ite (.lt gPos gS1) (.op (.zero gZ))
        (.op (.copy gZ v1)))) (.seq (.op (.add gS1 gPos)) (.ite (.lt gS1 gNeg) (.op (.zero gZ))
        (.op (.copy gZ v1))))) e6 5
      (fun d => d.env gZ = gbit g zb ∧ Same e6 d ∧ Fr e6 d [gS1, gZ]) := by
    refine Hs.ite (show gS0 ≠ vZ by decide) (fun hs => ?_) (fun hs => ?_)
    · simp only [Cnd.eval, e6s, e6z, decide_eq_true_eq] at hs
      have ht : ¬ g.threshold < 0 := by intro h; simp [h] at hs
      refine Hs.seq (t1 := 1) (t2 := 2) (hs_add C gS1 gNeg e6 (by decide) (by rw [e6m, e6n]; omega))
        (fun f hf => ?_)
      subst hf
      refine Hs.ite (show gPos ≠ gS1 by decide) (fun hl => ?_) (fun hl => ?_)
      · simp only [Cnd.eval, decide_eq_true_eq] at hl
        vsimp [e6p, e6m, e6n] at hl
        refine Hs.mono (hs_zero C gZ _) le_rfl ?_
        rintro d rfl
        refine ⟨by vsimp [hcmp, ht, hl], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
        exact Fr.trans (Fr.set e6 _ (by simp)) (Fr.set _ _ (by simp))
      · simp only [Cnd.eval, decide_eq_false_iff_not] at hl
        vsimp [e6p, e6m, e6n] at hl
        refine Hs.mono (hs_copy C gZ v1 _ (by decide)) le_rfl ?_
        rintro d rfl
        refine ⟨by vsimp [hcmp, ht, hl, e6one], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
        exact Fr.trans (Fr.set e6 _ (by simp)) (Fr.set _ _ (by simp))
    · simp only [Cnd.eval, e6s, e6z, decide_eq_false_iff_not] at hs
      have ht : g.threshold < 0 := by by_contra h; simp [h] at hs
      refine Hs.seq (t1 := 1) (t2 := 2) (hs_add C gS1 gPos e6 (by decide) (by rw [e6m, e6p]; omega))
        (fun f hf => ?_)
      subst hf
      refine Hs.ite (show gS1 ≠ gNeg by decide) (fun hl => ?_) (fun hl => ?_)
      · simp only [Cnd.eval, decide_eq_true_eq] at hl
        vsimp [e6p, e6m, e6n] at hl
        refine Hs.mono (hs_zero C gZ _) le_rfl ?_
        rintro d rfl
        refine ⟨by vsimp [hcmp, ht]; omega, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
        exact Fr.trans (Fr.set e6 _ (by simp)) (Fr.set _ _ (by simp))
      · simp only [Cnd.eval, decide_eq_false_iff_not] at hl
        vsimp [e6p, e6m, e6n] at hl
        refine Hs.mono (hs_copy C gZ v1 _ (by decide)) le_rfl ?_
        rintro d rfl
        refine ⟨by vsimp [hcmp, ht, e6one]; omega, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
        exact Fr.trans (Fr.set e6 _ (by simp)) (Fr.set _ _ (by simp))
  have e6ram : e6.ram = e.ram := h4ram
  have e6rc : e6.rc = Function.update (Function.update e.rc sN (p0 + (2 * n + 3))) sZb n := by
    show Function.update (Function.update e4.rc sN (e4.rc sN + 1)) sN
      (Function.update e4.rc sN (e4.rc sN + 1) sN + 1) = _
    rw [h4rc, e3rc]
    funext m; by_cases h1 : m = sZb
    · subst h1; simp [Function.update_of_ne (Ne.symm hsd)]
    · by_cases h2 : m = sN
      · subst h2; simp [Function.update_of_ne hsd]; ring
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  have e6o : e6.ip = e.ip ∧ e6.out = e.out ∧ e6.kin = e.kin ∧ e6.kout = e.kout ∧ e6.kc = e.kc :=
    ⟨h4ip, h4out, h4kin, h4kout, h4kc⟩
  have e6B : e6.rc sB = e.rc sB := by
    rw [e6rc, Function.update_of_ne (Ne.symm hzbB), Function.update_of_ne (Ne.symm hsb)]
  refine Hs.mono (Hs.seq (t1 := 5) (t2 := n + 3) hite (fun e7 ⟨h7z, h7s, h7fr⟩ => ?_)) (by omega) (fun _ h => h)
  have e7B : e7.rc sB = e.rc sB := by rw [h7s.rc, e6B]
  have e7Bm : e7.ram sB = e.ram sB := by rw [h7s.ram, e6ram]
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := n + 1) (hs_wrM C sB gZ e7 (by rw [e7B, e7Bm]; exact hsB))
    (fun e8 he8 => ?_)) (by omega) (fun _ h => h)
  subst he8
  have e8Z : (e7.put sB (e7.env gZ)).rc sZb = n := by
    show Function.update e7.rc sB (e7.rc sB + 1) sZb = n
    rw [Function.update_of_ne hzbB, h7s.rc, e6rc]; simp
  refine Hs.mono (hs_rwM C sZb _) (by rw [e8Z]) ?_
  rintro d rfl
  refine ⟨?_, ?_, ?_⟩
  · show Function.update e7.ram sB (putAt (e7.ram sB) (e7.rc sB) (e7.env gZ)) = _
    rw [h7s.ram, e7B, e6ram, h7z]
  · show Function.update (Function.update e7.rc sB (e7.rc sB + 1)) sZb 0 = _
    rw [e7B, h7s.rc, e6rc]
    funext m; by_cases h1 : m = sZb
    · subst h1; simp [Function.update_of_ne (Ne.symm hsd), Function.update_of_ne hzbB, hz0]
    · by_cases h2 : m = sB
      · subst h2; simp [Function.update_of_ne (Ne.symm hzbB)]
      · by_cases h3 : m = sN
        · subst h3; simp [Function.update_of_ne hsd, Function.update_of_ne hsb]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show e7.ip = e.ip; rw [h7s.ip]; exact e6o.1
    · show e7.out = e.out; rw [h7s.out]; exact e6o.2.1
    · show e7.kin = e.kin; rw [h7s.kin]; exact e6o.2.2.1
    · show e7.kout = e.kout; rw [h7s.kout]; exact e6o.2.2.2.1
    · show e7.kc = e.kc; rw [h7s.kc]; exact e6o.2.2.2.2
    · have f67 : Fr e6 e7 wsumT := Fr.weaken h7fr (by decide)
      have f46 : Fr e4 e6 wsumT := by
        intro y hy; simp only [wsumT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp only [he6, he5, DS.adv]; vsimp [Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2.1]
      exact Fr.trans (Fr.trans (Fr.trans e3fr h4fr) f46) (fun y hy => f67 y hy)

/-! ## Generic list facts -/

theorem drop_flatMap_get {α : Type} (f : α → List ℕ) (sz : ℕ) (hf : ∀ x, (f x).length = sz) (L : List α) (k : ℕ)
    (hk : k < L.length) (X R : List ℕ) (p0 : ℕ) (h : X.drop p0 = L.flatMap f ++ R) :
    X.drop (p0 + k * sz) = f L[k] ++ ((L.drop (k + 1)).flatMap f ++ R) := by
  have hsp : L = L.take k ++ (L[k] :: L.drop (k + 1)) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hfm : L.flatMap f = (L.take k).flatMap f ++ (f L[k] ++ (L.drop (k + 1)).flatMap f) := by
    have := congrArg (List.flatMap f) hsp
    exact this.trans (by rw [List.flatMap_append, List.flatMap_cons])
  have hl : ((L.take k).flatMap f).length = k * sz := by
    rw [List.length_flatMap]
    have : ((L.take k).map fun x => (f x).length) = List.replicate (L.take k).length sz := by
      rw [List.eq_replicate_iff]; simp [hf]
    rw [this, List.sum_replicate, List.length_take, min_eq_left (le_of_lt hk), smul_eq_mul]
  rw [← List.drop_drop, h, hfm, List.append_assoc, ← hl, List.drop_left]
  simp [List.append_assoc]

theorem putAt_take (vals old : List ℕ) (k : ℕ) (hk : k < vals.length) :
    putAt (vals.take k ++ old.drop k) k vals[k] = vals.take (k + 1) ++ old.drop (k + 1) := by
  have hl : (vals.take k).length = k := by simp; omega
  have := putAt_split (vals.take k) (old.drop k) vals[k]
  rw [hl] at this
  rw [this, List.take_succ_eq_append_getElem hk, List.drop_drop, List.append_assoc]
  simp [Nat.add_comm]

theorem take_drop_length (vals old : List ℕ) (k : ℕ) (hk : k ≤ vals.length) :
    k ≤ (vals.take k ++ old.drop k).length := by simp; omega

/-! ## All gates of a role -/

/-- The gate count of the current role. -/
def gG : Fin VV := ⟨115, by decide⟩

/-- The gate bits of a role into `sB` (cursor `c4`). -/
def gatesP : St VV MM := forS c4 gG gateBody

def gatesT : List (Fin VV) := [c4, c3, gS0, gS1, gZ, gPos, gNeg, vJ]

theorem gatesP_spec {n : ℕ} (a : DS VV MM) (hc : Cst a) (hn : a.env gN = n) (hnW : n < 2 ^ C.Wd)
    (gs : List (NormalizedThresholdGate n)) (hG : a.env gG = gs.length) (hGW : gs.length < 2 ^ C.Wd)
    (R : List ℕ) (hsN : (a.ram sN).drop (a.rc sN) = gs.flatMap gateN ++ R)
    (zb : List ℕ) (hzb : a.ram sZb = zb) (hzl : zb.length = n) (hz0 : a.rc sZb = 0) (hB0 : a.rc sB = 0)
    (hW : ∀ g ∈ gs, ((List.ofFn g.weight).map Int.natAbs).sum + g.threshold.natAbs < 2 ^ C.Wd) :
    Hs C gatesP a (gs.length * (15 * n + 24 + 4) + 4)
      (fun b => b.ram = Function.update a.ram sB (gs.map (gbit · zb) ++ (a.ram sB).drop gs.length) ∧
        b.rc = Function.update (Function.update a.rc sN (a.rc sN + gs.length * (2 * n + 3))) sB gs.length ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b gatesT) := by
  have hsd : sN ≠ sZb := by decide
  have hsb : sN ≠ sB := by decide
  have hzbB : sZb ≠ sB := by decide
  set p0 := a.rc sN with hp0
  set vals := gs.map (gbit · zb) with hvals
  set old := a.ram sB with hold
  have hvl : vals.length = gs.length := by simp [hvals]
  let I : ℕ → DS VV MM → Prop := fun k e =>
    e.ram = Function.update a.ram sB (vals.take k ++ old.drop k) ∧
    e.rc = Function.update (Function.update a.rc sN (p0 + k * (2 * n + 3))) sB k ∧
    e.ip = a.ip ∧ e.out = a.out ∧ e.kin = a.kin ∧ e.kout = a.kout ∧ e.kc = a.kc ∧ Fr a e gatesT
  have hl := forS_spec' (C := C) c4 gG (by decide) gateBody a gs.length hGW I (15 * n + 24)
    (fun k e v ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ => ⟨i1, i2, i3, i4, i5, i6, i7, Fr.trans i8 (Fr.set e v (by decide))⟩)
    ⟨by simp; rfl, by
        funext m; by_cases h1 : m = sB
        · subst h1; simp [hB0]
        · by_cases h2 : m = sN
          · subst h2; simp [Function.update_of_ne h1]; rfl
          · simp [Function.update_of_ne h1, Function.update_of_ne h2],
      rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩ hG ?_
  · refine Hs.mono hl le_rfl ?_
    rintro e ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8⟩, _, _⟩
    refine ⟨by rw [i1, ← hvl, List.take_length, hvl], i2, i3, i4, i5, i6, i7, i8⟩
  · intro k hk e ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ hek hem
    have hc' : Cst e := Cst.of_fr hc i8 (by decide)
    have hkv : k < vals.length := by omega
    have eN : e.ram sN = a.ram sN := by rw [i1, Function.update_of_ne hsb]
    have eNc : e.rc sN = p0 + k * (2 * n + 3) := by
      rw [i2, Function.update_of_ne hsb]; simp
    have hdrop := drop_flatMap_get gateN (2 * n + 3) CounterMachine.gateN_length gs k hk (a.ram sN) R p0 hsN
    refine Hs.mono (gateBody_spec e hc' gs[k] (by rw [i8 gN (by decide)]; exact hn) hnW
      ((gs.drop (k + 1)).flatMap gateN ++ R) (by rw [eN, eNc]; exact hdrop) zb
      (by rw [i1, Function.update_of_ne hzbB]; exact hzb) hzl
      (by rw [i2, Function.update_of_ne hzbB, Function.update_of_ne (Ne.symm hsd)]; exact hz0)
      (by rw [i2, i1]; simp only [Function.update_self]; exact take_drop_length vals old k (by omega))
      (hW gs[k] (List.getElem_mem hk))) le_rfl ?_
    rintro d ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩
    have eB : e.rc sB = k := by rw [i2]; simp
    have eBm : e.ram sB = vals.take k ++ old.drop k := by rw [i1]; simp
    have hv : vals[k] = gbit gs[k] zb := by simp [hvals]
    refine ⟨⟨?_, ?_, d3.trans i3, d4.trans i4, d5.trans i5, d6.trans i6, d7.trans i7,
      Fr.trans i8 (Fr.weaken d8 (by decide))⟩, ?_, ?_⟩
    · rw [d1, eB, eBm, i1, ← hv, putAt_take vals old k hkv, Function.update_idem]
    · rw [d2, eB, eNc, i2]
      funext m; by_cases h1 : m = sB
      · subst h1; simp
      · by_cases h2 : m = sN
        · subst h2; simp [Function.update_of_ne hsb]; ring
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]
    · rw [d8 c4 (by decide)]; exact hek
    · rw [d8 gG (by decide)]; exact hem

end NearCubicGates.Close.Cells
