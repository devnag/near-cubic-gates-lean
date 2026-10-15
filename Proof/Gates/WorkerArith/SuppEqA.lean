import Proof.Gates.WorkerArith.SuppEqDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

variable {ns nr : ℕ}

/-! ## Blanking -/

theorem blankLoop (cap : ℕ) (o : Fin (ns + 1)) (C T2 : Fin nr) (hCT : C ≠ T2) (l : List Bool) (hc : l.length ≤ cap) :
    ∀ k j (σ : WState ns nr), j + k = l.length → σ.st o = List.replicate j false ++ l.drop j → σ.sh o = j →
      σ.val C = k → σ.val T2 = j →
      WExec cap (.whr C (.seq (.dec C) (.seq (.wr o false) (.seq (.fwd o) (.inc T2))))) σ
        ((((σ.sets o (List.replicate l.length false)).seth o l.length).setv C 0).setv T2 l.length) (k * 11 + 1)
  | 0, j, σ, hjk, hst, hsh, hC, hT => by
    have hj : j = l.length := by omega
    subst hj
    have e : (((σ.sets o (List.replicate l.length false)).seth o l.length).setv C 0).setv T2 l.length = σ := by
      apply WState.eq
      · funext i; by_cases hi : i = o
        · subst hi; simp [hsh]
        · simp [Function.update_of_ne hi]
      · funext i; by_cases hi : i = o
        · subst hi; simp [hst]
        · simp [Function.update_of_ne hi]
      · funext r; by_cases hr : r = T2
        · subst hr; simp [hT]
        · by_cases hr2 : r = C
          · subst hr2; simp [hr, hC]
          · simp [Function.update_of_ne hr, Function.update_of_ne hr2]
      · rfl
    rw [e]; exact WExec.whrF hC
  | k + 1, j, σ, hjk, hst, hsh, hC, hT => by
    have e1 := WExec.dec (cap := cap) C σ (by omega)
    set σ1 := σ.setv C (σ.val C - 1) with hσ1
    have e2 := WExec.wr (cap := cap) o false σ1
    have hw : writeTapeBit (σ1.st o) (σ1.sh o) false = List.replicate (j + 1) false ++ l.drop (j + 1) := by
      simp only [hσ1, WState.setv_st, WState.setv_sh, hst, hsh]; exact write_clear j l
    rw [hw] at e2
    set σ2 := σ1.sets o (List.replicate (j + 1) false ++ l.drop (j + 1)) with hσ2
    have e3 := WExec.fwd (cap := cap) o σ2
    set σ3 := σ2.seth o (σ2.sh o + 1) with hσ3
    have e4 := WExec.inc (cap := cap) T2 σ3 (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hCT.symm, hT]; omega)
    set σ4 := σ3.setv T2 (σ3.val T2 + 1) with hσ4
    have ih := blankLoop cap o C T2 hCT l hc k (j + 1) σ4 (by omega) (by simp [hσ4, hσ3, hσ2])
      (by simp [hσ4, hσ3, hσ2, hσ1, hsh]) (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hCT, hC])
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hCT.symm, hT])
    refine WExec.mono (WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ih) ?_
      le_rfl) (by nlinarith)
    apply WState.eq
    · funext i; by_cases hi : i = o
      · subst hi; simp [hσ4, hσ3, hσ2, hσ1]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hi]
    · funext i; by_cases hi : i = o
      · subst hi; simp [hσ4, hσ3, hσ2, hσ1]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hi]
    · funext r; by_cases hr : r = T2
      · subst hr; simp [hσ4, hσ3, hσ2, hσ1]
      · by_cases hr2 : r = C
        · subst hr2; simp [hσ4, hσ3, hσ2, hσ1, hr]
        · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr, Function.update_of_ne hr2]
    · rfl

theorem blankM (cap : ℕ) (o : Fin (ns + 1)) (C T2 : Fin nr) (hCT : C ≠ T2) (σ : WState ns nr) (l : List Bool)
    (hl : σ.st o = l) (ho : σ.sh o = 0) (hC : σ.val C = l.length) (hT : σ.val T2 = 0) (hc : l.length ≤ cap) :
    WExec cap (blankW o C T2) σ ((σ.sets o (List.replicate l.length false)).setv C 0) (20 * l.length + 3) := by
  have e1 := blankLoop cap o C T2 hCT l hc l.length 0 σ (by omega) (by simp [hl]) ho hC hT
  set τ := (((σ.sets o (List.replicate l.length false)).seth o l.length).setv C 0).setv T2 l.length with hτ
  have e2 := wrewind_spec (cap := cap) o T2 l.length τ (by simp [hτ]) (by simp [hτ]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by nlinarith)
  apply WState.eq
  · funext i; by_cases hi : i = o
    · subst hi; simp [hτ, ho]
    · simp [hτ, Function.update_of_ne hi]
  · rfl
  · funext r; by_cases hr : r = T2
    · subst hr; simp [hτ, hT, Function.update_of_ne hCT.symm]
    · by_cases hr2 : r = C
      · subst hr2; simp [hτ, hr]
      · simp [hτ, Function.update_of_ne hr, Function.update_of_ne hr2]
  · rfl

/-! ## Comparing two marked words -/

theorem marks_even (l : List Bool) (k : ℕ) : readTapeBit (marks l) (2 * k) = decide (k < l.length) := by
  induction l generalizing k with
  | nil => simp [marks, readTapeBit]
  | cons b l ih =>
    cases k with
    | zero => simp [marks, readTapeBit]
    | succ k =>
      have := ih k
      simp only [marks, List.flatMap_cons, readTapeBit, List.cons_append, List.nil_append] at this ⊢
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ, this]
      simp

theorem marks_odd (l : List Bool) (k : ℕ) : readTapeBit (marks l) (2 * k + 1) = l.getD k false := by
  induction l generalizing k with
  | nil => simp [marks, readTapeBit]
  | cons b l ih =>
    cases k with
    | zero => simp [marks, readTapeBit]
    | succ k =>
      have := ih k
      simp only [marks, List.flatMap_cons, readTapeBit, List.cons_append, List.nil_append] at this ⊢
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ, this]
      simp

/-- The mismatch flag after `k` compared cells. -/
def mm (la lb : List Bool) (k : ℕ) : Bool := decide (la.take k ≠ lb.take k)

theorem mm_zero (la lb : List Bool) : mm la lb 0 = false := by simp [mm]

theorem mm_succ (la lb : List Bool) (k : ℕ) (hk : k < la.length) :
    mm la lb (k + 1) = (mm la lb k || !decide (k < lb.length) || (la.getD k false != lb.getD k false)) := by
  unfold mm
  have ha : la.take (k + 1) = la.take k ++ [la[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  have hga : la.getD k false = la[k] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  by_cases hb : k < lb.length
  · have hbb : lb.take (k + 1) = lb.take k ++ [lb[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hb]; rfl
    have hgb : lb.getD k false = lb[k] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]; rfl
    have key : (la.take k ++ [la[k]] = lb.take k ++ [lb[k]]) ↔ (la.take k = lb.take k ∧ la[k] = lb[k]) :=
      ⟨fun h => by
        have := List.append_inj h (by simp; omega)
        exact ⟨this.1, by simpa using this.2⟩, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
    rw [ha, hbb, hga, hgb, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne, ne_eq]
    rw [key]
    tauto
  · have hbb : lb.take (k + 1) = lb.take k := by
      rw [List.take_add_one, List.getElem?_eq_none (by omega)]; simp
    rw [hbb]
    have hne : la.take (k + 1) ≠ lb.take k := by
      intro h; have := congrArg List.length h; simp [List.length_take] at this; omega
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne]
    constructor
    · intro _; left; right; exact hb
    · intro _; exact hne

theorem mm_final (la lb : List Bool) : (mm la lb la.length || decide (la.length < lb.length)) = decide (la ≠ lb) := by
  unfold mm
  rw [List.take_length]
  by_cases h : la.length < lb.length
  · have : la ≠ lb := fun e => by rw [e] at h; omega
    simp [h, this]
  · have hl : lb.take la.length = lb := List.take_of_length_le (by omega)
    simp [h, hl]

/-! ## The comparison loop -/

section Cmp
variable (cap : ℕ) (A B : Fin (ns + 1)) (NEQ CNT : Fin nr)

theorem setIfNot (σ : WState ns nr) (m c : Bool) (hN : σ.val NEQ = m.toNat) (hw : wbit σ B = c) (hc : 1 ≤ cap) :
    WExec cap (.ifs B .skip (WM.setF NEQ)) σ (σ.setv NEQ (m || !c).toNat) 5 := by
  cases c
  · have e := wsetF_spec (cap := cap) NEQ σ (by rw [hN]; cases m <;> simp) hc
    simpa using (WExec.ifsF (P := .skip) hw e).mono (by omega)
  · have e : σ.setv NEQ (m || !true).toNat = σ := by simp only [Bool.not_true, Bool.or_false]; rw [← hN, wsetv_same]
    rw [e]; exact (WExec.ifsT (Q := WM.setF NEQ) hw (WExec.skip σ)).mono (by omega)

theorem setIf (σ : WState ns nr) (m c : Bool) (hN : σ.val NEQ = m.toNat) (hw : wbit σ B = c) (hc : 1 ≤ cap) :
    WExec cap (.ifs B (WM.setF NEQ) .skip) σ (σ.setv NEQ (m || c).toNat) 5 := by
  cases c
  · have e : σ.setv NEQ (m || false).toNat = σ := by simp only [Bool.or_false]; rw [← hN, wsetv_same]
    rw [e]; exact (WExec.ifsF (P := WM.setF NEQ) hw (WExec.skip σ)).mono (by omega)
  · have e := wsetF_spec (cap := cap) NEQ σ (by rw [hN]; cases m <;> simp) hc
    simpa using (WExec.ifsT (Q := .skip) hw e).mono (by omega)

theorem setIfNe (σ : WState ns nr) (m a b : Bool) (hN : σ.val NEQ = m.toNat) (ha : wbit σ A = a) (hb : wbit σ B = b)
    (hc : 1 ≤ cap) :
    WExec cap (.ifs A (.ifs B .skip (WM.setF NEQ)) (.ifs B (WM.setF NEQ) .skip)) σ
      (σ.setv NEQ (m || (a != b)).toNat) 6 := by
  cases a
  · have e := setIf cap B NEQ σ m b hN hb hc
    have : (m || (false != b)) = (m || b) := by cases b <;> rfl
    rw [this]; exact (WExec.ifsF ha e).mono (by omega)
  · have e := setIfNot cap B NEQ σ m b hN hb hc
    have : (m || (true != b)) = (m || !b) := by cases b <;> rfl
    rw [this]; exact (WExec.ifsT ha e).mono (by omega)

variable (hAB : A ≠ B) (hNC : NEQ ≠ CNT)
include hAB hNC

/-- The loop state after `k` compared cells. -/
def cmpSt (σ : WState ns nr) (la lb : List Bool) (k : ℕ) : WState ns nr :=
  (((σ.seth A (2 * k)).seth B (2 * k)).setv NEQ (mm la lb k).toNat).setv CNT k

theorem cmpBodyM (σ : WState ns nr) (la lb : List Bool) (hA : σ.st A = marks la) (hB : σ.st B = marks lb)
    (k : ℕ) (hk : k < la.length) (hc : la.length + 1 ≤ cap) :
    WExec cap (cmpBody A B NEQ CNT) (cmpSt A B NEQ CNT σ la lb k) (cmpSt A B NEQ CNT σ la lb (k + 1)) 25 := by
  set τ := cmpSt A B NEQ CNT σ la lb k with hτ
  have hτA : τ.st A = marks la := by simp [hτ, cmpSt, hA]
  have hτB : τ.st B = marks lb := by simp [hτ, cmpSt, hB]
  have hτN : τ.val NEQ = (mm la lb k).toNat := by simp [hτ, cmpSt, Function.update_of_ne hNC]
  have w1 : wbit τ B = decide (k < lb.length) := by
    simp only [wbit, hτB]; rw [show τ.sh B = 2 * k by simp [hτ, cmpSt]]; exact marks_even lb k
  have e1 := setIfNot cap B NEQ τ (mm la lb k) _ hτN w1 (by omega)
  set m1 := (mm la lb k || !decide (k < lb.length)) with hm1
  set τ1 := τ.setv NEQ m1.toNat with hτ1
  have e2 := WExec.fwd (cap := cap) A τ1
  have e3 := WExec.fwd (cap := cap) B (τ1.seth A (τ1.sh A + 1))
  set τ3 := (τ1.seth A (τ1.sh A + 1)).seth B ((τ1.seth A (τ1.sh A + 1)).sh B + 1) with hτ3
  have hshA3 : τ3.sh A = 2 * k + 1 := by simp [hτ3, hτ1, hτ, cmpSt, Function.update_of_ne hAB]
  have hshB3 : τ3.sh B = 2 * k + 1 := by simp [hτ3, hτ1, hτ, cmpSt, Function.update_of_ne hAB.symm]
  have wa : wbit τ3 A = la.getD k false := by
    simp only [wbit, hshA3]; rw [show τ3.st A = marks la by simp [hτ3, hτ1, hτA]]; exact marks_odd la k
  have wb : wbit τ3 B = lb.getD k false := by
    simp only [wbit, hshB3]; rw [show τ3.st B = marks lb by simp [hτ3, hτ1, hτB]]; exact marks_odd lb k
  have e4 := setIfNe cap A B NEQ τ3 m1 _ _ (by simp [hτ3, hτ1]) wa wb (by omega)
  set τ4 := τ3.setv NEQ (m1 || (la.getD k false != lb.getD k false)).toNat with hτ4
  have e5 := WExec.fwd (cap := cap) A τ4
  have e6 := WExec.fwd (cap := cap) B (τ4.seth A (τ4.sh A + 1))
  set τ6 := (τ4.seth A (τ4.sh A + 1)).seth B ((τ4.seth A (τ4.sh A + 1)).sh B + 1) with hτ6
  have e7 := WExec.inc (cap := cap) CNT τ6 (by simp [hτ6, hτ4, hτ3, hτ1, hτ, cmpSt, Function.update_of_ne hNC.symm]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_ (by omega)
  have hmm := mm_succ la lb k hk
  apply WState.eq
  · funext i; by_cases hi : i = A
    · subst hi; simp [hτ6, hτ4, hτ3, hτ1, hτ, cmpSt, Function.update_of_ne hAB]; ring
    · by_cases hi2 : i = B
      · subst hi2; simp [hτ6, hτ4, hτ3, hτ1, hτ, cmpSt, Function.update_of_ne hi]; ring
      · simp [hτ6, hτ4, hτ3, hτ1, hτ, cmpSt, Function.update_of_ne hi, Function.update_of_ne hi2]
  · rfl
  · funext r; by_cases hr : r = CNT
    · subst hr; simp [hτ6, hτ4, hτ3, hτ1, hτ, cmpSt, Function.update_of_ne hNC.symm]
    · by_cases hr2 : r = NEQ
      · subst hr2; simp [hτ6, hτ4, hτ3, hτ1, hτ, cmpSt, hr, hmm, hm1, Bool.or_assoc]
      · simp [hτ6, hτ4, hτ3, hτ1, hτ, cmpSt, Function.update_of_ne hr, Function.update_of_ne hr2]
  · rfl

theorem cmpLoopM (σ : WState ns nr) (la lb : List Bool) (hA : σ.st A = marks la) (hB : σ.st B = marks lb)
    (hc : la.length + 1 ≤ cap) : ∀ m k, k + m = la.length →
      WExec cap (.whs A (cmpBody A B NEQ CNT)) (cmpSt A B NEQ CNT σ la lb k) (cmpSt A B NEQ CNT σ la lb la.length)
        (m * 27 + 1)
  | 0, k, hk => by
    rw [Nat.add_zero] at hk; subst hk
    refine WExec.whsF ?_
    simp only [wbit]; rw [show (cmpSt A B NEQ CNT σ la lb la.length).st A = marks la by simp [cmpSt, hA],
      show (cmpSt A B NEQ CNT σ la lb la.length).sh A = 2 * la.length by
        simp [cmpSt, Function.update_of_ne hAB]]
    rw [marks_even]; simp
  | m + 1, k, hk => by
    have hw : wbit (cmpSt A B NEQ CNT σ la lb k) A = true := by
      simp only [wbit]; rw [show (cmpSt A B NEQ CNT σ la lb k).st A = marks la by simp [cmpSt, hA],
        show (cmpSt A B NEQ CNT σ la lb k).sh A = 2 * k by simp [cmpSt, Function.update_of_ne hAB]]
      rw [marks_even]; simp; omega
    have e := cmpBodyM cap A B NEQ CNT hAB hNC σ la lb hA hB k (by omega) hc
    have ih := cmpLoopM σ la lb hA hB hc m (k + 1) (by omega)
    exact (WExec.whsT hw e ih).mono (by ring_nf; omega)

theorem rewind2 (σ : WState ns nr) : ∀ k : ℕ, σ.val CNT = k → σ.sh A = 2 * k → σ.sh B = 2 * k → k ≤ cap →
    WExec cap (.whr CNT (.seq (.dec CNT) (.seq (.bwd A) (.seq (.bwd A) (.seq (.bwd B) (.bwd B)))))) σ
      (((σ.seth A 0).seth B 0).setv CNT 0) (k * 11 + 1)
  | 0, hk, hA, hB, _ => by
    have e : ((σ.seth A 0).seth B 0).setv CNT 0 = σ := by
      apply WState.eq
      · funext i; by_cases hi : i = A
        · subst hi; simp [Function.update_of_ne hAB, hA]
        · by_cases hi2 : i = B
          · subst hi2; simp [hB]
          · simp [Function.update_of_ne hi, Function.update_of_ne hi2]
      · rfl
      · simp only [WState.setv_val, WState.seth_val]; rw [← hk]; exact Function.update_eq_self CNT σ.val
      · rfl
    rw [e]; exact WExec.whrF hk
  | k + 1, hk, hA, hB, hc => by
    have e1 := WExec.dec (cap := cap) CNT σ (by omega)
    set σ1 := σ.setv CNT (σ.val CNT - 1) with hσ1
    have e2 := WExec.bwd (cap := cap) A σ1
    have e3 := WExec.bwd (cap := cap) A (σ1.seth A (σ1.sh A - 1))
    have e4 := WExec.bwd (cap := cap) B ((σ1.seth A (σ1.sh A - 1)).seth A ((σ1.seth A (σ1.sh A - 1)).sh A - 1))
    set σ4 := (((σ1.seth A (σ1.sh A - 1)).seth A ((σ1.seth A (σ1.sh A - 1)).sh A - 1)).seth B
      (((σ1.seth A (σ1.sh A - 1)).seth A ((σ1.seth A (σ1.sh A - 1)).sh A - 1)).sh B - 1)) with hσ4
    have e5 := WExec.bwd (cap := cap) B σ4
    have ih := rewind2 (σ4.seth B (σ4.sh B - 1)) k (by simp [hσ4, hσ1, hk])
      (by simp [hσ4, hσ1, Function.update_of_ne hAB, hA]; omega) (by simp [hσ4, hσ1, Function.update_of_ne hAB.symm, hB]; omega) (by omega)
    refine (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ih).cast cap ?_
      (le_of_eq (by ring))
    apply WState.eq
    · funext i; by_cases hi : i = A
      · subst hi; simp [Function.update_of_ne hAB]
      · by_cases hi2 : i = B
        · subst hi2; simp
        · simp [hσ4, hσ1, Function.update_of_ne hi, Function.update_of_ne hi2]
    · rfl
    · funext r; by_cases hr : r = CNT
      · subst hr; simp
      · simp [hσ4, hσ1, Function.update_of_ne hr]
    · rfl

/-- **Compare two marked words**: `NEQ := [la ≠ lb]`, heads back at `0`, `CNT` back at `0`. -/
theorem cmpM (σ : WState ns nr) (la lb : List Bool) (hA : σ.st A = marks la) (hB : σ.st B = marks lb)
    (hAh : σ.sh A = 0) (hBh : σ.sh B = 0) (hN : σ.val NEQ = 0) (hC : σ.val CNT = 0) (hc : la.length + 1 ≤ cap) :
    WExec cap (cmpW A B NEQ CNT) σ (σ.setv NEQ (decide (la ≠ lb)).toNat) (40 * la.length + 15) := by
  have st0 : cmpSt A B NEQ CNT σ la lb 0 = σ := by
    apply WState.eq
    · funext i; by_cases hi : i = A
      · subst hi; simp [cmpSt, Function.update_of_ne hAB, hAh]
      · by_cases hi2 : i = B
        · subst hi2; simp [cmpSt, hBh]
        · simp [cmpSt, Function.update_of_ne hi, Function.update_of_ne hi2]
    · rfl
    · funext r; by_cases hr : r = CNT
      · subst hr; simp [cmpSt, hC]
      · by_cases hr2 : r = NEQ
        · subst hr2; simp [cmpSt, hr, mm_zero, hN]
        · simp [cmpSt, Function.update_of_ne hr, Function.update_of_ne hr2]
    · rfl
  have e1 := cmpLoopM cap A B NEQ CNT hAB hNC σ la lb hA hB hc la.length 0 (by omega)
  rw [st0] at e1
  set τ := cmpSt A B NEQ CNT σ la lb la.length with hτ
  have wB : wbit τ B = decide (la.length < lb.length) := by
    simp only [wbit]; rw [show τ.st B = marks lb by simp [hτ, cmpSt, hB],
      show τ.sh B = 2 * la.length by simp [hτ, cmpSt]]
    exact marks_even lb la.length
  have e2 := setIf cap B NEQ τ (mm la lb la.length) _ (by simp [hτ, cmpSt, Function.update_of_ne hNC]) wB (by omega)
  rw [mm_final] at e2
  set τ2 := τ.setv NEQ (decide (la ≠ lb)).toNat with hτ2
  have e3 := rewind2 cap A B NEQ CNT hAB hNC τ2 la.length (by simp [hτ2, hτ, cmpSt, Function.update_of_ne hNC.symm])
    (by simp [hτ2, hτ, cmpSt, Function.update_of_ne hAB]) (by simp [hτ2, hτ, cmpSt]) (by omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by nlinarith)
  apply WState.eq
  · funext i; by_cases hi : i = A
    · subst hi; simp [hτ2, hτ, cmpSt, Function.update_of_ne hAB, hAh]
    · by_cases hi2 : i = B
      · subst hi2; simp [hτ2, hτ, cmpSt, hBh]
      · simp [hτ2, hτ, cmpSt, Function.update_of_ne hi, Function.update_of_ne hi2]
  · rfl
  · funext r; by_cases hr : r = CNT
    · subst hr; simp [hτ2, hτ, cmpSt, Function.update_of_ne hNC.symm, hC]
    · by_cases hr2 : r = NEQ
      · subst hr2; simp [hτ2, hτ, cmpSt, hr]
      · simp [hτ2, hτ, cmpSt, Function.update_of_ne hr, Function.update_of_ne hr2]
  · rfl

end Cmp

end NearCubicGates.Close.WorkerArith
