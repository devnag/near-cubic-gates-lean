import Proof.Gates.Succinct.IntegerRootW

/-!
# 𝒱_G, part 4: reading the input and the binary point counter

Paper: lem:succinct-verifier (app:multitape), stages (1)–(3). `countW`: from `frame u` on the input stream, the length
`n = |u|` into `NN` and `u` itself, raw, onto the description stream `D` (**`countW_spec`**). `incP`: the point
stream holds the little-endian bits of `i` (`pList i`); `incP` advances it to `i + 1` (**`incP_spec`**), and the
point it presents to the evaluator reads `i.testBit j` at cell `j` (`read_pList`).
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

/-! ## Framed words -/

theorem frame_even (bits : List Bool) (j : ℕ) :
    readTapeBit (RepairOrdinary.frame bits) (2 * j) = decide (j < bits.length) := by
  unfold readTapeBit
  induction bits generalizing j with
  | nil => cases j <;> simp [RepairOrdinary.frame]
  | cons b bs ih =>
    cases j with
    | zero => simp [RepairOrdinary.frame]
    | succ j =>
      have := ih j
      show (true :: b :: RepairOrdinary.frame bs).getD (2 * j + 1 + 1) false = decide (j + 1 < bs.length + 1)
      rw [List.getD_cons_succ, List.getD_cons_succ, this]
      simp

theorem frame_odd (bits : List Bool) (j : ℕ) (hj : j < bits.length) :
    readTapeBit (RepairOrdinary.frame bits) (2 * j + 1) = bits.getD j false := by
  unfold readTapeBit
  induction bits generalizing j with
  | nil => simp at hj
  | cons b bs ih =>
    cases j with
    | zero => simp [RepairOrdinary.frame]
    | succ j =>
      have := ih j (by simpa using hj)
      show (true :: b :: RepairOrdinary.frame bs).getD (2 * j + 1 + 1 + 1) false = (b :: bs).getD (j + 1) false
      rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, this]

theorem take_succ_getD (u : List Bool) (j : ℕ) (hj : j < u.length) :
    u.take (j + 1) = u.take j ++ [u.getD j false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]; rfl

/-! ## Counting and copying the input -/

def countW (IN D : Fin (ns + 1)) (E : VReg → Fin nr) : WM ns nr :=
  .seq (.whs IN (.seq (WM.fwdC IN (E .c)) (.seq (.ifs IN (.wr D true) (.wr D false))
      (.seq (WM.fwdC IN (E .c)) (.seq (WM.fwdC D (E .k2)) (.inc (E .nn)))))))
    (.seq (WM.rewind IN (E .c)) (WM.rewind D (E .k2)))

/-- The state after copying `j` cells. -/
def cntSt (IN D : Fin (ns + 1)) (E : VReg → Fin nr) (σ : WState ns nr) (u : List Bool) (j : ℕ) : WState ns nr :=
  (((((σ.seth IN (2 * j)).sets D (u.take j)).seth D j).setv (E .c) (2 * j)).setv (E .k2) j).setv (E .nn) j

theorem countLoop (cap : ℕ) (IN D : Fin (ns + 1)) (hID : IN ≠ D) (E : VReg → Fin nr) (hE : Function.Injective E)
    (σ : WState ns nr) (u : List Bool) (hIN : σ.st IN = RepairOrdinary.frame u) (hcap : 2 * u.length + 1 ≤ cap) :
    ∀ m j, j + m = u.length →
      WExec cap (.whs IN (.seq (WM.fwdC IN (E .c)) (.seq (.ifs IN (.wr D true) (.wr D false))
        (.seq (WM.fwdC IN (E .c)) (.seq (WM.fwdC D (E .k2)) (.inc (E .nn)))))))
        (cntSt IN D E σ u j) (cntSt IN D E σ u u.length) (m * 26 + 1) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    rw [Nat.add_zero] at hj; subst hj
    refine WExec.whsF ?_
    simp [wbit, cntSt, Function.update_apply, hID, Ne.symm hID, hIN, frame_even]
  | succ m ih =>
    intro j hj
    have hjl : j < u.length := by omega
    set τ := cntSt IN D E σ u j with hτ
    have hbit0 : wbit τ IN = true := by
      simp [wbit, τ, cntSt, Function.update_apply, hID, Ne.symm hID, hIN, frame_even, hjl]
    have e1 := wfwdC_spec cap IN (E .c) τ (by simp [τ, cntSt, Function.update_apply, hE.eq_iff]; omega)
    set τ1 := (τ.seth IN (τ.sh IN + 1)).setv (E .c) (τ.val (E .c) + 1) with hτ1
    have hb1 : wbit τ1 IN = u.getD j false := by
      have := frame_odd u j hjl
      simpa [wbit, τ1, τ, cntSt, Function.update_apply, hID, Ne.symm hID, hIN] using this
    have e2 : WExec cap (.ifs IN (.wr D true) (.wr D false)) τ1
        (τ1.sets D (writeTapeBit (τ1.st D) (τ1.sh D) (u.getD j false))) 2 := by
      cases hb : u.getD j false
      · exact WExec.mono (WExec.ifsF (by rw [hb1, hb]) (WExec.wr D false τ1)) (by omega)
      · exact WExec.mono (WExec.ifsT (by rw [hb1, hb]) (WExec.wr D true τ1)) (by omega)
    set τ2 := τ1.sets D (writeTapeBit (τ1.st D) (τ1.sh D) (u.getD j false)) with hτ2
    have e3 := wfwdC_spec cap IN (E .c) τ2 (by simp [τ2, τ1, τ, cntSt, Function.update_apply, hE.eq_iff]; omega)
    set τ3 := (τ2.seth IN (τ2.sh IN + 1)).setv (E .c) (τ2.val (E .c) + 1) with hτ3
    have e4 := wfwdC_spec cap D (E .k2) τ3
      (by simp [τ3, τ2, τ1, τ, cntSt, Function.update_apply, hE.eq_iff, hID, Ne.symm hID]; omega)
    set τ4 := (τ3.seth D (τ3.sh D + 1)).setv (E .k2) (τ3.val (E .k2) + 1) with hτ4
    have e5 := WExec.inc (cap := cap) (E .nn) τ4
      (by simp [τ4, τ3, τ2, τ1, τ, cntSt, Function.update_apply, hE.eq_iff, hID, Ne.symm hID]; omega)
    have ih' := ih (j + 1) (by omega)
    have hlen : (u.take j).length = j := by simp; omega
    have hw : writeTapeBit (u.take j) j (u.getD j false) = u.take (j + 1) := by
      have := FinalPass.Tm.writeTapeBit_end' (u.take j) (u.getD j false)
      rw [hlen] at this; rw [take_succ_getD u j hjl]; exact this
    have hw' : writeTapeBit (u.take j) j (u[j]?.getD false) = u.take (j + 1) := by
      rw [← List.getD_eq_getElem?_getD]; exact hw
    have hbody : WExec cap (.seq (WM.fwdC IN (E .c)) (.seq (.ifs IN (.wr D true) (.wr D false))
        (.seq (WM.fwdC IN (E .c)) (.seq (WM.fwdC D (E .k2)) (.inc (E .nn)))))) τ (cntSt IN D E σ u (j + 1)) 24 := by
      refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by omega)
      refine WState.eq ?_ ?_ ?_ rfl
      · funext x
        by_cases hx : x = IN
        · subst hx; simp [τ4, τ3, τ2, τ1, τ, cntSt, Function.update_apply, hID]; omega
        · by_cases hxD : x = D
          · subst hxD; simp [τ4, τ3, τ2, τ1, τ, cntSt, Function.update_apply, hx]
          · simp [τ4, τ3, τ2, τ1, τ, cntSt, Function.update_apply, hx, hxD]
      · funext x
        by_cases hxD : x = D
        · subst hxD
          simp [τ4, τ3, τ2, τ1, τ, cntSt, Function.update_apply, hID, Ne.symm hID, hw, hw']
        · simp [τ4, τ3, τ2, τ1, τ, cntSt, Function.update_apply, hxD]
      · funext q
        simp only [τ4, τ3, τ2, τ1, τ, cntSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
        by_cases hn : q = E .nn
        · subst hn; simp [hE.eq_iff]
        · by_cases hk : q = E .k2
          · subst hk; simp [hE.eq_iff]
          · by_cases hc : q = E .c
            · subst hc; simp [hE.eq_iff]; omega
            · simp [hn, hk, hc]
    exact WExec.mono (WExec.whsT hbit0 hbody ih') (by omega)

/-- **Reading the input** (paper lem:succinct-verifier, stage (1)): `NN := |u|`, `D := u`. -/
theorem countW_spec (cap : ℕ) (IN D : Fin (ns + 1)) (hID : IN ≠ D) (E : VReg → Fin nr) (hE : Function.Injective E)
    (σ : WState ns nr) (u : List Bool) (hIN : σ.st IN = RepairOrdinary.frame u) (hINh : σ.sh IN = 0)
    (hD : σ.st D = []) (hDh : σ.sh D = 0) (hc : σ.val (E .c) = 0) (hk : σ.val (E .k2) = 0) (hn : σ.val (E .nn) = 0)
    (hcap : 2 * u.length + 1 ≤ cap) :
    WExec cap (countW IN D E) σ ((σ.sets D u).setv (E .nn) u.length) (45 * u.length + 5) := by
  have h0 : cntSt IN D E σ u 0 = σ := by
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x
      by_cases hx : x = IN
      · subst hx; simp [cntSt, Function.update_apply, hID, hINh]
      · by_cases hxD : x = D
        · subst hxD; simp [cntSt, hDh]
        · simp [cntSt, Function.update_apply, hx, hxD]
    · funext x; by_cases hxD : x = D
      · subst hxD; simp [cntSt, hD]
      · simp [cntSt, Function.update_apply, hxD]
    · funext q; simp only [cntSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      by_cases h1 : q = E .nn
      · subst h1; simp [hn]
      · by_cases h2 : q = E .k2
        · subst h2; simp [h1, hk]
        · by_cases h3 : q = E .c
          · subst h3; simp [h1, h2, hc]
          · simp [h1, h2, h3]
  have e1 := countLoop cap IN D hID E hE σ u hIN hcap u.length 0 (by omega)
  rw [h0] at e1
  set τ := cntSt IN D E σ u u.length with hτ
  have e2 := wrewind_spec cap IN (E .c) (2 * u.length) τ (by simp [τ, cntSt, Function.update_apply, hE.eq_iff])
    (by simp [τ, cntSt, Function.update_apply, hE.eq_iff]; omega)
  have e3 := wrewind_spec cap D (E .k2) u.length (((τ.setv (E .c) 0).seth IN (τ.sh IN - 2 * u.length)))
    (by simp [τ, cntSt, Function.update_apply, hE.eq_iff]) (by simp [τ, cntSt, Function.update_apply, hE.eq_iff]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext x
    by_cases hx : x = IN
    · subst hx; simp [τ, cntSt, Function.update_apply, hID, hINh]
    · by_cases hxD : x = D
      · subst hxD; simp [τ, cntSt, Function.update_apply, hx, hDh]
      · simp [τ, cntSt, Function.update_apply, hx, hxD]
  · funext x; by_cases hxD : x = D
    · subst hxD; simp [τ, cntSt]
    · simp [τ, cntSt, Function.update_apply, hxD]
  · funext q; simp only [τ, cntSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    by_cases h1 : q = E .k2
    · subst h1; simp [hE.eq_iff, hk]
    · by_cases h2 : q = E .c
      · subst h2; simp [h1, hE.eq_iff, hc]
      · by_cases h3 : q = E .nn
        · subst h3; simp [h1, h2]
        · simp [h1, h2, h3]

end NearCubicGates.Close.Succinct
