import Proof.Wire_3_5.ListMachineRowPopInst
import Proof.Wire_3_5.ListMachinePrintCost

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord)
open NearCubicWires.RepairOrdinary (frame frame_length)
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

theorem outerPassGCost_le (labs : List ℕ) {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk : k < (Interp.goods L d).length) :
    outerPassGCost (recSpecL labs) E d k ≤ 2 ^ d * (E.cost + 8 * L + 14) + 2 * labCost L labs + 8 * L ^ 2 + 76 * L + 60 := by
  have hl := xsAt_length L d k
  have hp : 2 ^ Interp.pop (xsAt L d k) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (xsAt_pop L d hd k hk)
  have hm : 2 ^ Interp.pop (xsAt L d k) * (innerPassCost E L + 2) ≤ 2 ^ d * (E.cost + 8 * L + 14) := by
    apply Nat.mul_le_mul hp
    simp [innerPassCost, innerRestCost]; omega
  have hr : (recSpecL labs).cost (xsAt L d k) = 2 * labCost L labs + 2 := by
    show 2 * recInnerLCost (xsAt L d k) labs + 2 = _
    rw [recInnerLCost_len, hl]
  simp only [outerPassGCost, outerRestGCost, hl, hr]
  nlinarith

/-- **The labelled printer's cost.** -/
theorem printGCost_le (labs : List ℕ) {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d : ℕ) (hd : 1 ≤ d) :
    printGCost (recSpecL labs) E d ≤ (L + 1) ^ d * 2 ^ d * (E.cost + 2 * labCost L labs + 100 * (L + 1) ^ 2) + 3 := by
  have hb : ∀ x ∈ (List.range (Interp.goods L d).length).map (fun k => outerPassGCost (recSpecL labs) E d k + 2),
      x ≤ 2 ^ d * (E.cost + 2 * labCost L labs + 100 * (L + 1) ^ 2) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have h1 := outerPassGCost_le labs E d hd k (List.mem_range.mp hk)
    have h2 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    nlinarith
  have hs := List.sum_le_card_nsmul _ _ hb
  simp only [List.length_map, List.length_range, smul_eq_mul] at hs
  have hg := goods_length_le L d
  unfold printGCost
  calc _ ≤ (Interp.goods L d).length * (2 ^ d * (E.cost + 2 * labCost L labs + 100 * (L + 1) ^ 2)) + 3 := by omega
    _ ≤ (L + 1) ^ d * (2 ^ d * (E.cost + 2 * labCost L labs + 100 * (L + 1) ^ 2)) + 3 := by
      have := Nat.mul_le_mul_right (2 ^ d * (E.cost + 2 * labCost L labs + 100 * (L + 1) ^ 2)) hg
      omega
    _ = (L + 1) ^ d * 2 ^ d * (E.cost + 2 * labCost L labs + 100 * (L + 1) ^ 2) + 3 := by ring

/-! ## The POP row's cost -/

theorem sum_range_le (n B : ℕ) (f : ℕ → ℕ) (h : ∀ j < n, f j ≤ B) : ((List.range n).map f).sum ≤ n * B := by
  have := List.sum_le_card_nsmul ((List.range n).map f) B (by
    intro x hx; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx; exact h j (List.mem_range.mp hj))
  simpa using this

theorem storeCost_le {F : EvalFam} (xs : List (FSpec F)) (R : ℕ) (hR : ∀ x ∈ xs, x.cost + 1 ≤ R) :
    storeCost xs R ≤ xs.length * (4 * R + 9) + 1 := by
  unfold storeCost
  have := sum_range_le xs.length (4 * R + 9) (fun j => storePass xs R j + 2) (by
    intro j hj
    have h := hR xs[j] (List.getElem_mem hj)
    simp only [storePass, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some, sfCost]
    omega)
  omega

theorem termCost_le (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (cap : ℕ)
    (h1 : 2 * (coefWord c).length + 1 ≤ cap) (h2 : ((List.range ps.length).map fun j => selPass ps j + 2).sum + 1 ≤ cap) :
    termCost c ps ≤ 4 * cap + 8 := by
  unfold termCost
  simp only [coefWord, frame_length] at h1
  omega

theorem rowPass_le (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (cap : ℕ)
    (h1 : 2 * (coefWord c).length + 1 ≤ cap) (h2 : ((List.range ps.length).map fun j => selPass ps j + 2).sum + 1 ≤ cap)
    (j : ℕ) : rowPass t θ c ps j ≤ 12 * t + 4 * cap + 25 := by
  have := termCost_le c ps cap h1 h2
  unfold rowPass
  split_ifs <;> omega

theorem rowsCost_le (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (cap : ℕ)
    (h1 : 2 * (coefWord c).length + 1 ≤ cap) (h2 : ((List.range ps.length).map fun j => selPass ps j + 2).sum + 1 ≤ cap) :
    rowsCost t θ c ps ≤ 2 ^ t * (12 * t + 4 * cap + 27) + 1 := by
  unfold rowsCost
  have := sum_range_le (2 ^ t) (12 * t + 4 * cap + 27) (fun j => rowPass t θ c ps j + 2)
    (fun j _ => by have := rowPass_le t θ c ps cap h1 h2 j; omega)
  omega

theorem stateCost_le {F : EvalFam} (n θ : ℕ) (R cap : ℕ) (st : SSpec F) (hok : StateOk n R cap st) :
    stateCost n θ st.1 st.2 R ≤ st.2.length * (8 * R + 18) + 2 ^ n * (12 * n + 4 * cap + 27) + 2 * cap + 20 := by
  obtain ⟨hlen, hR, _, h4, _, h6⟩ := hok
  have hps : (statePairs st.2).length = n := by
    unfold statePairs; rw [length_pairsOf n _ (by simp [hlen])]
  have hs := storeCost_le st.2 R hR
  have hr := rowsCost_le n θ st.1 (statePairs st.2) cap h4 (by rw [hps]; exact h6)
  unfold stateCost
  have : 2 * storeCost st.2 R ≤ st.2.length * (8 * R + 18) + 2 := by nlinarith
  omega

theorem statesCost_le {F : EvalFam} (n θ : ℕ) (sts : List (SSpec F)) (R cap Fm : ℕ)
    (hok : ∀ st ∈ sts, StateOk n R cap st) (hFm : ∀ st ∈ sts, st.2.length ≤ Fm) :
    statesCost n θ sts R ≤ sts.length * (Fm * (8 * R + 18) + 2 ^ n * (12 * n + 4 * cap + 27) + 2 * cap + 22) + 1 := by
  unfold statesCost
  have := sum_range_le sts.length (Fm * (8 * R + 18) + 2 ^ n * (12 * n + 4 * cap + 27) + 2 * cap + 22)
    (fun j => statePass n θ sts R j + 2) (by
      intro j hj
      have h := stateCost_le n θ R cap sts[j] (hok _ (List.getElem_mem hj))
      have hf := hFm _ (List.getElem_mem hj)
      have hm : sts[j].2.length * (8 * R + 18) ≤ Fm * (8 * R + 18) := Nat.mul_le_mul_right _ hf
      simp only [statePass, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
      omega)
  omega

theorem loadCost_le (ws : List (List Bool)) : loadCost ws ≤ 2 * (fieldsWord ws).length := by
  induction ws with
  | nil => simp [loadCost]
  | cons w ws ih => simp only [loadCost, fieldsWord_cons, List.length_append, frame_length]; omega

theorem setupFields_eq (u n θ R L cap : ℕ) : setupFields u n θ R L cap =
    [List.replicate R true, List.replicate L false, frame (binary n 0), frame (List.replicate n false),
      List.replicate θ true ++ [false], [false], [false], [], List.replicate cap false] := by
  simp only [setupFields, targetsQ, List.map_cons, List.map_nil, setupF_driver, setupF_log, setupF_e]
  rfl

theorem setupFields_len (u n θ R L cap : ℕ) :
    R ≤ (fieldsWord (setupFields u n θ R L cap)).length ∧ cap ≤ (fieldsWord (setupFields u n θ R L cap)).length ∧
      n ≤ (fieldsWord (setupFields u n θ R L cap)).length := by
  rw [setupFields_eq]
  simp only [fieldsWord, List.flatMap_cons, List.flatMap_nil, List.length_append, frame_length, List.length_replicate,
    List.length_nil]
  omega

theorem popRec_len {F : EvalFam} (oneW : List Bool) (sts : List (SSpec F)) :
    oneW.length ≤ (popRec oneW sts).length ∧ sts.length ≤ (popRec oneW sts).length ∧
      ∀ st ∈ sts, st.2.length ≤ (popRec oneW sts).length := by
  have hsrec : ∀ st : SSpec F, st.2.length + 1 ≤ (srec st).length := by
    intro st
    have : st.2.length ≤ (storeRec st.2).length := by
      unfold storeRec
      have h : ∀ l : List (FSpec F), l.length ≤ (l.flatMap fun x => true :: x.block).length := by
        intro l; induction l with
        | nil => simp
        | cons x l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega
      have := h st.2
      simp only [List.length_append]; omega
    simp only [srec, stateRec, List.length_cons, List.length_append]; omega
  have hflat : ∀ l : List (SSpec F), l.length ≤ (l.flatMap srec).length ∧
      ∀ st ∈ l, st.2.length ≤ (l.flatMap srec).length := by
    intro l
    induction l with
    | nil => simp
    | cons st l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.mem_cons]
      have := hsrec st
      refine ⟨by omega, ?_⟩
      rintro st' (rfl | h)
      · omega
      · have := ih.2 st' h; omega
  obtain ⟨h1, h2⟩ := hflat sts
  simp only [popRec, List.length_append, frame_length, List.length_cons, List.length_nil]
  refine ⟨by omega, by omega, fun st h => by have := h2 st h; omega⟩

/-- **The POP row's cost**: at most `2^t · 128 · (|record| + 1)^3` — the `2^t` truth-table rows of each state, every
other part polynomial in the row record (whose capacity fields carry the factor prints' costs). -/
theorem popRowCost_le {F : EvalFam} (n θ R Lg cap : ℕ) (oneW : List Bool) (sts : List (SSpec F))
    (hok : ∀ st ∈ sts, StateOk n R cap st) :
    popRowCost n θ R Lg cap oneW sts ≤ 2 ^ n * (128 * ((popRowRec n θ R Lg cap oneW sts).length + 1) ^ 3) := by
  set S := (popRowRec n θ R Lg cap oneW sts).length with hS
  obtain ⟨hR, hcap, hn⟩ := setupFields_len F.t n θ R Lg cap
  obtain ⟨h1, h2, h3⟩ := popRec_len oneW sts
  have hlenS : (fieldsWord (setupFields F.t n θ R Lg cap)).length + (popRec oneW sts).length = S := by
    rw [hS, popRowRec, List.length_append]
  have hRS : R ≤ S := by omega
  have hcS : cap ≤ S := by omega
  have hnS : n ≤ S := by omega
  have hoS : oneW.length ≤ S := by omega
  have hsS : sts.length ≤ S := by omega
  have hst := statesCost_le n θ sts R cap S hok (fun st h => by have := h3 st h; omega)
  have hld := loadCost_le (setupFields F.t n θ R Lg cap)
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hb1 : sts.length * (S * (8 * R + 18) + 2 ^ n * (12 * n + 4 * cap + 27) + 2 * cap + 22) ≤
      S * (S * (8 * S + 18) + 2 ^ n * (16 * S + 27) + 2 * S + 22) := by
    apply Nat.mul_le_mul hsS
    have e1 : S * (8 * R + 18) ≤ S * (8 * S + 18) := Nat.mul_le_mul_left _ (by omega)
    have e2 : 2 ^ n * (12 * n + 4 * cap + 27) ≤ 2 ^ n * (16 * S + 27) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hb2 : S * (S * (8 * S + 18) + 2 ^ n * (16 * S + 27) + 2 * S + 22) ≤ 2 ^ n * (S * (8 * S * S + 36 * S + 49)) := by
    have hA : S * (8 * S + 18) + 2 * S + 22 ≤ 2 ^ n * (8 * S * S + 20 * S + 22) := by
      have h := Nat.mul_le_mul_right (8 * S * S + 20 * S + 22) hp
      rw [one_mul] at h
      have e : S * (8 * S + 18) + 2 * S + 22 = 8 * S * S + 20 * S + 22 := by ring
      omega
    calc S * (S * (8 * S + 18) + 2 ^ n * (16 * S + 27) + 2 * S + 22)
        ≤ S * (2 ^ n * (8 * S * S + 20 * S + 22) + 2 ^ n * (16 * S + 27)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ n * (S * (8 * S * S + 36 * S + 49)) := by ring
  unfold popRowCost popCost
  have hfin : 2 ^ n * (S * (8 * S * S + 36 * S + 49)) + 13 * S + 30 ≤ 2 ^ n * (128 * (S + 1) ^ 3) := by
    have h13 := Nat.mul_le_mul_right (13 * S + 30) hp
    rw [one_mul] at h13
    have hpoly : S * (8 * S * S + 36 * S + 49) + (13 * S + 30) ≤ 128 * (S + 1) ^ 3 := by nlinarith
    have := Nat.mul_le_mul_left (2 ^ n) hpoly
    rw [Nat.mul_add] at this
    omega
  omega

end NearCubicWires.WireExponent3_5.ListMachine.Row
