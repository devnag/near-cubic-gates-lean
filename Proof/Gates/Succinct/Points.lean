import Proof.Gates.Succinct.Count

/-!
# 𝒱_G, part 5: the point counter

Paper: lem:succinct-verifier (app:multitape), stage (3): "For `i = 0, 1, …, N−1` … it evaluates `B` at
`bin_ν(i)0^{a−ν}`". The point stream holds `pList i`, the little-endian bits of `i` (`bitsValue (pList i) = i`), so
cell `j` reads `i.testBit j` (`read_pList`) — for `i < 2^ν` this is the point `(bin_ν(i), 0, …)`. `incP` turns
`pList i` into `pList (i+1)` (**`incP_spec`**).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- Little-endian increment. -/
def incList : List Bool → List Bool
  | [] => [true]
  | true :: l => false :: incList l
  | false :: l => true :: l

/-- The bits of `i` as kept by the point counter. -/
def pList : ℕ → List Bool
  | 0 => []
  | i + 1 => incList (pList i)

theorem bitsValue_incList : ∀ l : List Bool, CanonicalBinary.bitsValue (incList l) = CanonicalBinary.bitsValue l + 1
  | [] => by simp [incList, CanonicalBinary.bitsValue]
  | true :: l => by simp [incList, CanonicalBinary.bitsValue, bitsValue_incList l]; ring
  | false :: l => by simp [incList, CanonicalBinary.bitsValue]; ring

theorem bitsValue_pList : ∀ i, CanonicalBinary.bitsValue (pList i) = i
  | 0 => rfl
  | i + 1 => by rw [pList, bitsValue_incList, bitsValue_pList i]

theorem testBit_bitsValue : ∀ (l : List Bool) (j : ℕ), (CanonicalBinary.bitsValue l).testBit j = l.getD j false
  | [], j => by simp [CanonicalBinary.bitsValue]
  | b :: l, 0 => by
    simp only [CanonicalBinary.bitsValue, List.getD_cons_zero]
    rw [Nat.testBit_zero]
    cases b <;> simp [Nat.add_mul_mod_self_left]
  | b :: l, j + 1 => by
    simp only [CanonicalBinary.bitsValue, List.getD_cons_succ]
    rw [Nat.testBit_succ, ← testBit_bitsValue l j]
    congr 1
    cases b <;> simp <;> omega

/-- **The point** (paper lem:succinct-verifier, stage (3)): cell `j` of `pList i` reads bit `j` of `i`. -/
theorem read_pList (i j : ℕ) : readTapeBit (pList i) j = i.testBit j := by
  unfold readTapeBit
  rw [← testBit_bitsValue, bitsValue_pList]

theorem incList_eq : ∀ l : List Bool, incList l = List.replicate (onesL l) false ++ true :: l.drop (onesL l + 1)
  | [] => rfl
  | true :: l => by simp [incList, onesL, incList_eq l, List.replicate_succ]
  | false :: l => by simp [incList, onesL]

/-- `P := incList P` from head `0` (head returns; `C` scratch). -/
def incP (P : Fin (ns + 1)) (C : Fin nr) : WM ns nr :=
  .seq (.whs P (.seq (.wr P false) (WM.fwdC P C))) (.seq (.wr P true) (WM.rewind P C))

theorem incLoop (cap : ℕ) (P : Fin (ns + 1)) (C : Fin nr) (l : List Bool) (σ : WState ns nr)
    (hcap : l.length + 1 ≤ cap) :
    ∀ m k, k + m = onesL l →
      WExec cap (.whs P (.seq (.wr P false) (WM.fwdC P C)))
        (((σ.sets P (List.replicate k false ++ l.drop k)).seth P k).setv C k)
        (((σ.sets P (List.replicate (onesL l) false ++ l.drop (onesL l))).seth P (onesL l)).setv C (onesL l))
        (m * 9 + 1) := by
  have hL := onesL_le l
  intro m
  induction m with
  | zero =>
    intro k hk
    rw [Nat.add_zero] at hk; subst hk
    refine WExec.whsF ?_
    simp only [wbit, WState.setv_st, WState.setv_sh, WState.seth_st, WState.seth_sh, WState.sets_st,
      Function.update_self]
    unfold readTapeBit
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_replicate, Nat.sub_self,
      List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero, ← List.getD_eq_getElem?_getD]
    exact onesL_false l
  | succ m ih =>
    intro k hk
    have hkL : k < onesL l := by omega
    have hkl : k < l.length := by omega
    have htrue : l.getD k false = true := onesL_true l k hkL
    have hdrop : l.drop k = true :: l.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hkl]; congr; rw [List.getD_eq_getElem _ _ hkl] at htrue; exact htrue
    set τ := ((σ.sets P (List.replicate k false ++ l.drop k)).seth P k).setv C k with hτ
    have hb : wbit τ P = true := by
      simp only [wbit, τ, WState.setv_st, WState.setv_sh, WState.seth_st, WState.seth_sh, WState.sets_st,
        Function.update_self]
      unfold readTapeBit
      rw [List.getD_append_right _ _ _ _ (by simp), List.length_replicate, Nat.sub_self, hdrop]
      rfl
    have e1 := WExec.wr (cap := cap) P false τ
    have e2 := wfwdC_spec cap P C (τ.sets P (writeTapeBit (τ.st P) (τ.sh P) false))
      (by simp only [τ, WState.sets_val, WState.setv_val, WState.seth_val, Function.update_self]; omega)
    have hw : writeTapeBit (List.replicate k false ++ l.drop k) k false =
        List.replicate (k + 1) false ++ l.drop (k + 1) := by
      rw [writeTapeBit_set' _ _ _ (by simp; omega), hdrop, List.set_append_right _ _ (by simp),
        List.length_replicate, Nat.sub_self, List.set_cons_zero, List.replicate_succ', List.append_assoc]
      rfl
    have ih' := ih (k + 1) (by omega)
    refine WExec.mono (WExec.whsT hb (WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl) ih') (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; by_cases hx : x = P
      · subst hx; simp [τ]
      · simp [τ, Function.update_of_ne hx]
    · funext x; by_cases hx : x = P
      · subst hx; simp [τ, hw]
      · simp [τ, Function.update_of_ne hx]
    · funext q; by_cases hq : q = C
      · subst hq; simp [τ]
      · simp [τ, Function.update_of_ne hq]

/-- **The point counter's step** (paper lem:succinct-verifier, stage (3)): `P := incList P`. -/
theorem incP_spec (cap : ℕ) (P : Fin (ns + 1)) (C : Fin nr) (σ : WState ns nr) (l : List Bool)
    (hP : σ.st P = l) (hPh : σ.sh P = 0) (hC : σ.val C = 0) (hcap : l.length + 1 ≤ cap) :
    WExec cap (incP P C) σ (σ.sets P (incList l)) (14 * l.length + 5) := by
  have hL := onesL_le l
  have h0 : ((σ.sets P (List.replicate 0 false ++ l.drop 0)).seth P 0).setv C 0 = σ := by
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; by_cases hx : x = P
      · subst hx; simp [hPh]
      · simp [Function.update_of_ne hx]
    · funext x; by_cases hx : x = P
      · subst hx; simp [hP]
      · simp [Function.update_of_ne hx]
    · funext q; by_cases hq : q = C
      · subst hq; simp [hC]
      · simp [Function.update_of_ne hq]
  have e1 := incLoop cap P C l σ hcap (onesL l) 0 (by omega)
  rw [h0] at e1
  set L := onesL l with hLdef
  set τ := ((σ.sets P (List.replicate L false ++ l.drop L)).seth P L).setv C L with hτ
  have e2 := WExec.wr (cap := cap) P true τ
  have hw : writeTapeBit (List.replicate L false ++ l.drop L) L true = incList l := by
    rw [incList_eq, ← hLdef]
    rcases Nat.lt_or_ge L l.length with hl | hl
    · have hf : l.getD L false = false := onesL_false l
      have hdrop : l.drop L = false :: l.drop (L + 1) := by
        rw [List.drop_eq_getElem_cons hl]; congr; rw [List.getD_eq_getElem _ _ hl] at hf; exact hf
      rw [writeTapeBit_set' _ _ _ (by simp; omega), hdrop, List.set_append_right _ _ (by simp)]
      simp
    · have hLl : L = l.length := by omega
      have hd : l.drop L = [] := List.drop_of_length_le hl
      have hd1 : l.drop (L + 1) = [] := List.drop_of_length_le (by omega)
      rw [hd, hd1, List.append_nil]
      have := FinalPass.Tm.writeTapeBit_end' (List.replicate L false) true
      simpa using this
  have e3 := wrewind_spec cap P C L (τ.sets P (writeTapeBit (τ.st P) (τ.sh P) true)) (by simp [τ])
    (by simp only [τ, WState.sets_val, WState.setv_val, WState.seth_val, Function.update_self]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by have h1 : L ≤ l.length := hLdef ▸ onesL_le l; omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext x; by_cases hx : x = P
    · subst hx; simp [τ, hPh]
    · simp [τ, Function.update_of_ne hx]
  · funext x; by_cases hx : x = P
    · subst hx; simp [τ, hw]
    · simp [τ, Function.update_of_ne hx]
  · funext q; by_cases hq : q = C
    · subst hq; simp [τ, hC]
    · simp [τ, Function.update_of_ne hq]

theorem pList_length_le : ∀ i, (pList i).length ≤ i
  | 0 => le_rfl
  | i + 1 => by
    rw [pList]
    have h := pList_length_le i
    have : (incList (pList i)).length ≤ (pList i).length + 1 := by
      clear h
      generalize pList i = l
      induction l with
      | nil => simp [incList]
      | cons b l ih => cases b <;> simp [incList] <;> omega
    omega

end NearCubicGates.Close.Succinct
