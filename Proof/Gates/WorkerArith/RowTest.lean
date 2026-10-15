import Proof.Gates.WorkerArith.Entries
import Proof.Gates.WorkerArith.Classes

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces (listWord)

variable {ns nr : ℕ}

theorem marks_getD_odd : ∀ (w : List Bool) (k : ℕ), k < w.length → (marks w).getD (2 * k + 1) false = w.getD k false
  | [], k, hk => by simp at hk
  | b :: w, 0, _ => by simp [marks]
  | b :: w, k + 1, hk => by
    have := marks_getD_odd w k (by simpa using hk)
    simp only [marks, List.flatMap_cons] at this ⊢
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring]
    simp only [List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_succ]
    simpa using this

/-- `n ≠ 0` iff bit `1` or bit `2` of `natWord n` is set. -/
theorem natWord_test (n : ℕ) : ((natWord n).getD 1 false || (natWord n).getD 2 false) = decide (n ≠ 0) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> rfl
  · have hl : 2 ≤ natBitLength n := by
      unfold natBitLength
      have := Nat.log_pos (b := 2) (by norm_num) h
      omega
    have h1 : (natWord n).getD 1 false = true := by
      simp only [natWord, WilliamsPublishedForm.framedNatBits]
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      rw [if_pos (by omega)]; rfl
    rw [h1]; simp; omega

/-- **The row test.** Registers: `Rg 14 = r` (kept), `Rg 9 … Rg 11`, `Rg 0 … Rg 6` scratch, `LS` the record bound,
`NE` the result flag. -/
def rowNonemptyW (S : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr) (LS NE : Fin nr) : WM ns nr :=
  .seq (Codec.rewindCW S LS (Rg 11) (Rg 10))
  (.seq (Codec.dupR (Rg 14) (Rg 9) (Rg 10))
  (.seq (Codec.seekRows S Rg)
  (.seq (.seq (.fwd S) (.seq (.fwd S) (.fwd S))) (.seq (.ifs S (.inc NE) .skip)
  (.seq (.seq (.fwd S) (.fwd S)) (.seq (.ifs S (WM.setF NE) .skip)
  (Codec.rewindCW S LS (Rg 11) (Rg 10))))))))

theorem rowNonemptyW_spec (cap : ℕ) (S : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr) (LS NE : Fin nr)
    (hLS : ∀ k, LS ≠ Rg k) (hNE : ∀ k, NE ≠ Rg k) (hNL : NE ≠ LS) (rows : ℕ → List ℕ) (R r : ℕ) (hr : r < R)
    (rb : ℕ) (hrb : ∀ j < R, Codec.rowCost (rows j) ≤ rb)
    (hfit : ∀ j < R, 2 ^ (natBitLength (rows j).length + 1) ≤ cap ∧ (rows j).length ≤ cap ∧
      ∀ x ∈ rows j, natBitLength x + 1 ≤ cap)
    (Lb : ℕ) (hLc : Lb + r + 1 ≤ cap) (rest : List Bool) (τ : WState ns nr)
    (hst : τ.st S = Codec.rowPrefix rows R ++ rest) (hshL : τ.sh S ≤ Lb) (hLR : (Codec.rowPrefix rows R).length ≤ Lb)
    (hz : ∀ k : Fin 16, k ≠ 7 → k ≠ 12 → k ≠ 13 → k ≠ 14 → k ≠ 15 → τ.val (Rg k) = 0) (hR : τ.val (Rg 14) = r)
    (hLv : τ.val LS = Lb) (hN0 : τ.val NE = 0) :
    WExec cap (rowNonemptyW S Rg LS NE) τ ((τ.seth S 0).setv NE (decide (rows r ≠ [])).toNat)
      (60 * (Lb + 1) + (r + 1) * (rb + 30)) := by
  have hz' : ∀ k : Fin 16, k.val ≤ 11 → k ≠ 7 → τ.val (Rg k) = 0 := fun k hk h7 =>
    hz k h7 (fun h => by subst h; simp at hk) (fun h => by subst h; simp at hk)
      (fun h => by subst h; simp at hk) (fun h => by subst h; simp at hk)
  have hRne : ∀ {a b : Fin 16}, a ≠ b → Rg a ≠ Rg b := fun h => Rg.injective.ne h
  -- rewind
  have e1 := Codec.rewindCW_spec cap S LS (Rg 11) (Rg 10) (hLS 11) (hLS 10) (hRne (by decide)) τ
    (hz' 11 (by decide) (by decide)) (hz' 10 (by decide) (by decide)) (by rw [hLv]; exact hshL) (by omega)
  rw [hLv] at e1
  set τ1 := τ.seth S 0 with hτ1
  -- `Rg 9 := r`
  have e2 := Codec.dupR_spec cap (Rg 14) (Rg 9) (Rg 10) (hRne (by decide)) (hRne (by decide)) (hRne (by decide)) τ1
    (by simp [hτ1]; exact hz' 10 (by decide) (by decide))
    (by simp [hτ1, hR, hz' 9 (by decide) (by decide)]; omega)
  have hI0 : τ1.val (Rg 9) = 0 := by simp [hτ1]; exact hz' 9 (by decide) (by decide)
  have hR1 : τ1.val (Rg 14) = r := by simp [hτ1, hR]
  rw [hI0, hR1, Nat.zero_add] at e2
  set τ2 := τ1.setv (Rg 9) r with hτ2
  -- seek
  have e3 := Codec.seekRows_spec cap S Rg rows R r hr.le rb hrb hfit (by omega) rest τ2 (by simp [hτ2, hτ1, hst])
    (by simp [hτ2, hτ1])
    (fun k hk => by
      have h9 : Rg k ≠ Rg 9 := hRne (fun h => by subst h; simp at hk)
      simp [hτ2, hτ1, Function.update_of_ne h9]; exact hz' k (by omega) (fun h => by subst h; simp at hk))
    (by simp [hτ2])
  set h0 := (Codec.rowPrefix rows r).length with hh0
  set τ3 := (τ2.seth S h0).setv (Rg 9) 0 with hτ3
  have v3 : τ3.val = Function.update τ.val (Rg 9) 0 := by simp [hτ3, hτ2, hτ1]
  -- the stream around row `r`
  have hsplit := Codec.rowPrefix_split rows hr
  set w := listWord natWord (rows r) with hw
  have hwl : 3 ≤ w.length := by
    simp only [hw, listWord, List.length_append]
    have := natWord_len_c (rows r).length; have : 1 ≤ natBitLength (rows r).length := one_le_nbl _; omega
  have hst3 : τ3.st S = Codec.rowPrefix rows r ++ marks w ++
      ((Codec.rowPrefix rows R).drop (Codec.rowPrefix rows (r + 1)).length ++ rest) := by
    simp [hτ3, hτ2, hτ1, hst]; conv_lhs => rw [hsplit]
    simp [List.append_assoc]
  have hbit : ∀ k, k < w.length → readTapeBit (τ3.st S) (h0 + (2 * k + 1)) = w.getD k false := by
    intro k hk
    rw [hst3, readTapeBit, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
    rw [show h0 + (2 * k + 1) - (Codec.rowPrefix rows r).length = 2 * k + 1 by omega]
    rw [List.getD_append _ _ _ _ (by rw [Codec.marks_length]; omega)]
    exact marks_getD_odd w k hk
  have hw1 : w.getD 1 false = (natWord (rows r).length).getD 1 false := by
    simp only [hw, listWord]; rw [List.getD_append _ _ _ _ (by rw [natWord_len_c]; have := one_le_nbl (rows r).length; omega)]
  have hw2 : w.getD 2 false = (natWord (rows r).length).getD 2 false := by
    simp only [hw, listWord]; rw [List.getD_append _ _ _ _ (by rw [natWord_len_c]; have := one_le_nbl (rows r).length; omega)]
  -- three steps forward, test, two forward, test
  have f1 := WExec.fwd (cap := cap) S τ3
  have f2 := WExec.fwd (cap := cap) S (τ3.seth S (τ3.sh S + 1))
  have f3 := WExec.fwd (cap := cap) S ((τ3.seth S (τ3.sh S + 1)).seth S ((τ3.seth S (τ3.sh S + 1)).sh S + 1))
  set τ4 := τ3.seth S (h0 + 3) with hτ4
  have e4 : WExec cap (.seq (.fwd S) (.seq (.fwd S) (.fwd S))) τ3 τ4 5 := by
    refine WExec.cast cap (WExec.seq f1 (WExec.seq f2 f3)) ?_ (by omega)
    rw [hτ4]; apply WState.eq
    · funext j; by_cases hj : j = S
      · subst hj; simp [hτ3]; try omega
      · simp [Function.update_of_ne hj]
    · rfl
    · rfl
    · rfl
  set b1 := w.getD 1 false with hb1
  have t1 : wbit τ4 S = b1 := by
    have := hbit 1 (by omega); simp only [wbit, hτ4, WState.seth_st, WState.seth_sh, Function.update_self]
    rw [show h0 + 3 = h0 + (2 * 1 + 1) by ring]; exact this
  set τ5 := τ4.setv NE b1.toNat with hτ5
  have e5 : WExec cap (.ifs S (.inc NE) .skip) τ4 τ5 4 := by
    have hNτ4 : τ4.val NE = 0 := by
      rw [hτ4, WState.seth_val, v3, Function.update_of_ne (hNE 9), hN0]
    cases hb : b1
    · rw [hτ5, hb]
      have e := WExec.ifsF (cap := cap) (Q := .skip) (P := .inc NE) (by rw [t1, hb]) (WExec.skip τ4)
      refine WExec.cast cap e ?_ (by omega)
      simp only [Bool.toNat_false]; rw [← hNτ4, wsetv_same]
    · rw [hτ5, hb]
      have e := WExec.ifsT (cap := cap) (P := .inc NE) (Q := .skip) (by rw [t1, hb]) (WExec.inc (cap := cap) NE τ4 (by rw [hNτ4]; omega))
      refine WExec.cast cap e ?_ (by omega)
      rw [hNτ4]; rfl
  have g1 := WExec.fwd (cap := cap) S τ5
  have g2 := WExec.fwd (cap := cap) S (τ5.seth S (τ5.sh S + 1))
  set τ6 := τ5.seth S (h0 + 5) with hτ6
  have e6 : WExec cap (.seq (.fwd S) (.fwd S)) τ5 τ6 3 := by
    refine WExec.cast cap (WExec.seq g1 g2) ?_ (by omega)
    rw [hτ6]; apply WState.eq
    · funext j; by_cases hj : j = S
      · subst hj; simp [hτ5, hτ4]; try omega
      · simp [Function.update_of_ne hj]
    · rfl
    · rfl
    · rfl
  set b2 := w.getD 2 false with hb2
  have t2 : wbit τ6 S = b2 := by
    have := hbit 2 (by omega); simp only [wbit, hτ6, hτ5, hτ4, WState.seth_st, WState.setv_st, WState.seth_sh,
      WState.setv_sh, Function.update_self]
    rw [show h0 + 5 = h0 + (2 * 2 + 1) by ring]; exact this
  set τ7 := τ6.setv NE (b1 || b2).toNat with hτ7
  have e7 : WExec cap (.ifs S (WM.setF NE) .skip) τ6 τ7 5 := by
    have hN6 : τ6.val NE = b1.toNat := by simp [hτ6, hτ5]
    cases hb : b2
    · have e := WExec.ifsF (cap := cap) (P := WM.setF NE) (Q := .skip) (by rw [t2, hb]) (WExec.skip τ6)
      refine WExec.cast cap e ?_ (by omega)
      rw [hτ7, hb, Bool.or_false, ← hN6, wsetv_same]
    · have e := WExec.ifsT (cap := cap) (P := WM.setF NE) (Q := .skip) (by rw [t2, hb])
        (wsetF_spec (cap := cap) NE τ6 (by rw [hN6]; cases b1 <;> simp) (by omega))
      refine WExec.cast cap e ?_ (by omega)
      rw [hτ7, hb, Bool.or_true]; rfl
  -- rewind again
  have hrow : h0 + 6 ≤ Lb := by
    have h1 : (Codec.rowPrefix rows (r + 1)).length = h0 + 2 * w.length := by
      rw [Codec.rowPrefix_succ, List.length_append, Codec.marks_length, ← hw]
    have h2 : (Codec.rowPrefix rows (r + 1)).length ≤ (Codec.rowPrefix rows R).length := by
      have e1 := congrArg List.length hsplit
      have e2 := congrArg List.length (Codec.rowPrefix_succ rows r)
      rw [← hw] at e2
      simp only [List.length_append] at e1 e2
      omega
    omega
  have v7 : τ7.val = Function.update (Function.update τ.val (Rg 9) 0) NE (b1 || b2).toNat := by
    rw [hτ7, WState.setv_val, hτ6, WState.seth_val, hτ5, WState.setv_val, hτ4, WState.seth_val, v3,
      Function.update_idem]
  have hL7 : τ7.val LS = Lb := by
    rw [v7, Function.update_of_ne (Ne.symm hNL), Function.update_of_ne (hLS 9), hLv]
  have h11 : τ7.val (Rg 11) = 0 := by
    rw [v7, Function.update_of_ne (hNE 11).symm, Function.update_of_ne (hRne (show (11 : Fin 16) ≠ 9 by decide))]
    exact hz' 11 (by decide) (by decide)
  have h10 : τ7.val (Rg 10) = 0 := by
    rw [v7, Function.update_of_ne (hNE 10).symm, Function.update_of_ne (hRne (show (10 : Fin 16) ≠ 9 by decide))]
    exact hz' 10 (by decide) (by decide)
  have hS7 : τ7.sh S = h0 + 5 := by simp [hτ7, hτ6]
  have e8 := Codec.rewindCW_spec cap S LS (Rg 11) (Rg 10) (hLS 11) (hLS 10) (hRne (by decide)) τ7 h11 h10
    (by rw [hS7, hL7]; omega) (by rw [hL7]; omega)
  rw [hL7] at e8
  have hfin : (b1 || b2) = decide (rows r ≠ []) := by
    rw [hw1, hw2, natWord_test]; simp
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_ ?_
  · rw [← hfin]
    apply WState.eq
    · funext j; by_cases hj : j = S
      · subst hj; simp [hτ1]
      · simp [hτ7, hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, Function.update_of_ne hj]
    · rfl
    · funext k
      by_cases hk : k = NE
      · subst hk; simp [hτ7, hτ6, hτ5, hτ4, hτ3, hτ2, hτ1]
      · by_cases hk9 : k = Rg 9
        · subst hk9; simp [hτ7, hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, Function.update_of_ne hk]
          exact (hz' 9 (by decide) (by decide)).symm
        · simp [hτ7, hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, Function.update_of_ne hk, Function.update_of_ne hk9]
    · rfl
  · have := Nat.mul_le_mul_left (r + 1) (show 0 ≤ rb by omega)
    nlinarith

end NearCubicGates.Close.WorkerArith
