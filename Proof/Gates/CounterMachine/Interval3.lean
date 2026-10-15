import Proof.Gates.CounterMachine.Interval2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairRepresentation (natWord)

variable {ns nr : ℕ}

section Rat
variable (P : Fin 12 ↪ Fin (ns + 1)) (Q : Fin 20 ↪ Fin nr)

/-- The first ten registers (the shared printer registers; `Q 2` holds the width). -/
def q10 : Fin 10 ↪ Fin nr := (Fin.castLEEmb (by norm_num : 10 ≤ 20)).trans Q

theorem q10_apply (r : Fin 10) : q10 Q r = Q (Fin.castLE (by norm_num) r) := rfl

/-- `D := 2^{e}` by doubling (`Q 17` counted down). -/
def ivlPowP : WMX ns nr :=
  .seq (BinW.one (P 3) (P 7) (Q 15) (Q 16)) (.whr (Q 17) (.seq (WMX.dec (Q 17)) (BinW.shl (P 3) (P 7) (Q 15) (Q 16))))

def powCost (W e : ℕ) : ℕ := 41 * W + 7 + 1 + (e * (41 * W + 8 + 1 + 1 + 2) + 1)

theorem ivlPowP_spec (cap W e : ℕ) (σ : WState ns nr) (d c : ℕ) (hW : 1 ≤ W) (he : e < W)
    (hD : NumOn σ (P 3) W d) (hS : NumOn σ (P 7) W c) (h15 : σ.val (Q 15) = 0) (h16 : σ.val (Q 16) = 0)
    (h17 : σ.val (Q 17) = e) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (ivlPowP P Q) σ ((σ.sets (P 3) (frame (binary W (2 ^ e)))).setv (Q 17) 0) (powCost W e) := by
  have hDS : P 3 ≠ P 7 := P.injective.ne (by decide)
  have hFR : Q 15 ≠ Q 16 := Q.injective.ne (by decide)
  have e1 := BinW.one_spec cap W hDS hFR σ d c hD hS h15 h16 hW hcap
  set σ1 := σ.sets (P 3) (frame (binary W 1)) with hσ1
  let st : ℕ → WState ns nr := fun m => (σ.sets (P 3) (frame (binary W (2 ^ (e - m))))).setv (Q 17) m
  have hst : ∀ m ≤ e, (st m).val (Q 17) = m := fun m _ => by simp [st]
  have hl := Runs.whr (cap := cap) (r := Q 17) (P := .seq (WMX.dec (Q 17)) (BinW.shl (P 3) (P 7) (Q 15) (Q 16)))
    (fun m τ => m ≤ e ∧ τ = st m) (41 * W + 8 + 1 + 1)
    (fun τ => τ = (σ.sets (P 3) (frame (binary W (2 ^ e)))).setv (Q 17) 0)
    (fun τ ⟨_, h⟩ => by subst h; exact ⟨by simp [st], by simp [st]⟩)
    (by
      rintro m τ ⟨hm, rfl⟩
      refine ⟨by rw [hst (m + 1) hm]; omega, ?_⟩
      have d1 := WXExec.dec cap (Q 17) (st (m + 1)) (by rw [hst (m + 1) hm]; omega)
      rw [hst (m + 1) hm] at d1
      have hD' : NumOn ((st (m + 1)).setv (Q 17) (m + 1 - 1)) (P 3) W (2 ^ (e - (m + 1))) :=
        ⟨by simp [st], by simp [st, hD.2]⟩
      have hS' : NumOn ((st (m + 1)).setv (Q 17) (m + 1 - 1)) (P 7) W c :=
        ⟨by simp [st, Function.update_of_ne hDS.symm, hS.1], by simp [st, hS.2]⟩
      have s1 := BinW.shl_spec cap W hDS hFR ((st (m + 1)).setv (Q 17) (m + 1 - 1)) _ c hD' hS'
        (by simp [st, Function.update_of_ne (Q.injective.ne (show (15 : Fin 20) ≠ 17 by decide)), h15])
        (by simp [st, Function.update_of_ne (Q.injective.ne (show (16 : Fin 20) ≠ 17 by decide)), h16]) hcap
      refine Runs.of (WXExec.mono (WXExec.seq d1 s1) (by omega)) ⟨by omega, ?_⟩
      apply WState.eq
      · simp [st]
      · funext j; by_cases hj : j = P 3
        · subst hj; simp [st]
          congr 2
          rw [show e - m = (e - (m + 1)) + 1 by omega, pow_succ]; ring
        · simp [st, Function.update_of_ne hj]
      · simp [st]
      · simp [st])
    e (st e) ⟨le_rfl, rfl⟩
  have e0 : st e = σ1.setv (Q 17) e := by
    apply WState.eq
    · simp [st, hσ1]
    · simp [st, hσ1]
    · funext r; by_cases hr : r = Q 17
      · subst hr; simp [st, hσ1]
      · simp [st, hσ1, Function.update_of_ne hr]
    · simp [st, hσ1]
  have e0' : σ1.setv (Q 17) e = σ1 := by rw [← h17]; exact wsetv_same (σ.sets (P 3) (frame (binary W 1))) (Q 17)
  rw [e0, e0'] at hl
  obtain ⟨τ, el, rfl⟩ := hl
  exact WXExec.cast cap (WXExec.seq e1 el) rfl (by unfold powCost; omega)

/-- Print `natWord 0 ++ natWord x ++ natWord (2^{e'})` from the word `P X` and the exponent `Q 17`. -/
def ratP (X : Fin 12) : WMX ns nr :=
  .seq (emitL (P 0) [true, false, false]) (.seq (printL P (q10 Q) X) (.seq (addR (Q 13) (Q 12) (Q 14))
  (.seq (.wm (WM.rewind (P X) (Q 12))) (.seq (ivlPowP P Q) (.seq (printL P (q10 Q) 3) (.seq (addR (Q 13) (Q 12) (Q 14))
  (.seq (.wm (WM.rewind (P 3) (Q 12))) (BinW.zero (P 3) (P 7) (Q 15) (Q 16)))))))))

def ratCost (W e : ℕ) : ℕ :=
  4 * 3 + 1 + (NearCubicWires.WireExponent3_5.FinalPass.Out.P5.pnCost W + 1 + (18 * (2 * W + 1) + 3 + 1 +
    (5 * (2 * W + 1) + 1 + 1 + (powCost W e + 1 + (NearCubicWires.WireExponent3_5.FinalPass.Out.P5.pnCost W + 1 +
    (18 * (2 * W + 1) + 3 + 1 + (5 * (2 * W + 1) + 1 + 1 + (41 * W + 3))))))))

/-- The printer registers at rest: all `0` but the width. -/
def PrRegs (W : ℕ) (σ : WState ns nr) : Prop := σ.val (q10 Q 2) = W ∧ ∀ r : Fin 10, r ≠ 2 → σ.val (q10 Q r) = 0

theorem ratP_spec (cap W x e : ℕ) (X : Fin 12) (hX0 : X ≠ 0) (hX3 : X ≠ 3) (hX7 : X ≠ 7) (σ : WState ns nr)
    (d c : ℕ) (hW : 1 ≤ W) (hx : x < 2 ^ W) (he : e < W)
    (hO : σ.sh (P 0) = (σ.st (P 0)).length) (hXw : NumOn σ (P X) W x) (hD : NumOn σ (P 3) W d)
    (hS : NumOn σ (P 7) W c) (hpr : PrRegs Q W σ) (h12 : σ.val (Q 12) = 0) (h13 : σ.val (Q 13) = 2 * W + 1)
    (h14 : σ.val (Q 14) = 0) (h15 : σ.val (Q 15) = 0) (h16 : σ.val (Q 16) = 0) (h17 : σ.val (Q 17) = e)
    (hcap : 8 * W + 8 ≤ cap) :
    WXExec cap (ratP P Q X) σ ((((σ.sets (P 0) (σ.st (P 0) ++ (natWord 0 ++ natWord x ++ natWord (2 ^ e)))).seth (P 0)
      ((σ.st (P 0)).length + (natWord 0 ++ natWord x ++ natWord (2 ^ e)).length)).sets (P 3)
      (frame (binary W 0))).setv (Q 17) 0) (ratCost W e) := by
  have pne : ∀ {a b : Fin 12}, a ≠ b → P a ≠ P b := fun h => P.injective.ne h
  have qne : ∀ {a b : Fin 20}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have hqc : ∀ r : Fin 10, q10 Q r = Q (Fin.castLE (by norm_num) r) := fun r => rfl
  have hLx := NearCubicWires.WireExponent3_5.CompilerMachine.Pool.natBitLength_le x W hW hx
  have h2e : 2 ^ e < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) he
  have hL2 := NearCubicWires.WireExponent3_5.CompilerMachine.Pool.natBitLength_le (2 ^ e) W hW h2e
  -- (1) natWord 0
  have e1 := emitL_spec cap (P 0) [true, false, false] σ hO
  set σ1 := (σ.sets (P 0) (σ.st (P 0) ++ [true, false, false])).seth (P 0) ((σ.st (P 0)).length + 3) with hσ1
  -- (2) natWord x
  have e2 := printL_spec P (q10 Q) cap W x X hX0 σ1 hW hx (by simp [hσ1, Function.update_of_ne (pne hX0), hXw.1])
    (by simp [hσ1, Function.update_of_ne (pne hX0), hXw.2]) (by simp [hσ1])
    (by simp [hσ1]; exact hpr.1) (fun r hr => by simp [hσ1]; exact hpr.2 r hr) hcap
  set σ2 := ((σ1.sets (P 0) (σ1.st (P 0) ++ natWord x)).seth (P 0) ((σ1.st (P 0)).length + (natWord x).length)).seth
    (P X) (2 * natBitLength x + 1) with hσ2
  -- (3) rewind the word
  have e3 := addR_spec cap (A := Q 13) (B := Q 12) (T := Q 14) (qne (by decide)) (qne (by decide)) (qne (by decide))
    σ2 (by simp [hσ2, hσ1, h14]) (by simp [hσ2, hσ1, h12, h13]; omega)
  have v2 : σ2.val = σ.val := by simp [hσ2, hσ1]
  rw [v2, h12, h13, Nat.zero_add] at e3
  have e4 := wrewind_spec (cap := cap) (P X) (Q 12) (2 * W + 1) (σ2.setv (Q 12) (2 * W + 1)) (by simp) (by simp; omega)
  set σ4 := ((σ2.setv (Q 12) (2 * W + 1)).setv (Q 12) 0).seth (P X) ((σ2.setv (Q 12) (2 * W + 1)).sh (P X) - (2 * W + 1))
    with hσ4
  have v4 : σ4.val = σ.val := by
    funext r; by_cases hr : r = Q 12
    · subst hr; simp [hσ4, v2, h12]
    · simp [hσ4, Function.update_of_ne hr, v2]
  -- (4) `2^e`
  have e5 := ivlPowP_spec P Q cap W e σ4 d c hW he
    ⟨by simp [hσ4, hσ2, hσ1, Function.update_of_ne (pne (show (3 : Fin 12) ≠ 0 by decide)), hD.1],
      by simp [hσ4, hσ2, hσ1, Function.update_of_ne (pne (Ne.symm hX3)),
        Function.update_of_ne (pne (show (3 : Fin 12) ≠ 0 by decide)), hD.2]⟩
    ⟨by simp [hσ4, hσ2, hσ1, Function.update_of_ne (pne (show (7 : Fin 12) ≠ 0 by decide)), hS.1],
      by simp [hσ4, hσ2, hσ1, Function.update_of_ne (pne (Ne.symm hX7)),
        Function.update_of_ne (pne (show (7 : Fin 12) ≠ 0 by decide)), hS.2]⟩
    (by rw [v4]; exact h15) (by rw [v4]; exact h16) (by rw [v4]; exact h17) (by omega)
  set σ5 := (σ4.sets (P 3) (frame (binary W (2 ^ e)))).setv (Q 17) 0 with hσ5
  -- (5) natWord (2^e)
  have e6 := printL_spec P (q10 Q) cap W (2 ^ e) 3 (by decide) σ5 hW h2e (by simp [hσ5])
    (by simp [hσ5, hσ4, hσ2, hσ1, Function.update_of_ne (pne (Ne.symm hX3)),
      Function.update_of_ne (pne (show (3 : Fin 12) ≠ 0 by decide)), hD.2])
    (by simp [hσ5, hσ4, hσ2, hσ1, Function.update_of_ne (pne (show (0 : Fin 12) ≠ 3 by decide)),
      Function.update_of_ne (pne (Ne.symm hX0))]; omega)
    (by rw [hqc]; simp [hσ5, Function.update_of_ne (qne (show (Fin.castLE (by norm_num) (2 : Fin 10) : Fin 20) ≠ 17 by decide)), v4]
        exact hpr.1)
    (fun r hr => by
      have hr17 : q10 Q r ≠ Q 17 := by rw [hqc]; exact qne (by revert r; decide)
      simp [hσ5, Function.update_of_ne hr17, v4]; exact hpr.2 r hr) hcap
  set σ6 := ((σ5.sets (P 0) (σ5.st (P 0) ++ natWord (2 ^ e))).seth (P 0)
    ((σ5.st (P 0)).length + (natWord (2 ^ e)).length)).seth (P 3) (2 * natBitLength (2 ^ e) + 1) with hσ6
  have v6 : σ6.val = (σ.setv (Q 17) 0).val := by
    funext r; by_cases hr : r = Q 17
    · subst hr; simp [hσ6, hσ5]
    · simp [hσ6, hσ5, Function.update_of_ne hr, v4]
  -- (6) rewind `D`, zero it
  have e7 := addR_spec cap (A := Q 13) (B := Q 12) (T := Q 14) (qne (by decide)) (qne (by decide)) (qne (by decide))
    σ6 (by rw [v6]; simp [Function.update_of_ne (qne (show (14 : Fin 20) ≠ 17 by decide)), h14])
    (by rw [v6]; simp [Function.update_of_ne (qne (show (12 : Fin 20) ≠ 17 by decide)),
      Function.update_of_ne (qne (show (13 : Fin 20) ≠ 17 by decide)), h12, h13]; omega)
  rw [v6] at e7
  simp only [WState.setv_val, Function.update_of_ne (qne (show (12 : Fin 20) ≠ 17 by decide)),
    Function.update_of_ne (qne (show (13 : Fin 20) ≠ 17 by decide)), h12, h13, Nat.zero_add] at e7
  have e8 := wrewind_spec (cap := cap) (P 3) (Q 12) (2 * W + 1) (σ6.setv (Q 12) (2 * W + 1)) (by simp) (by simp; omega)
  set σ8 := ((σ6.setv (Q 12) (2 * W + 1)).setv (Q 12) 0).seth (P 3) ((σ6.setv (Q 12) (2 * W + 1)).sh (P 3) - (2 * W + 1))
    with hσ8
  have hD8 : NumOn σ8 (P 3) W (2 ^ e) := ⟨by simp [hσ8, hσ6, Function.update_of_ne (pne (show (3 : Fin 12) ≠ 0 by decide)),
    hσ5], by simp [hσ8, hσ6]; omega⟩
  have hS8 : NumOn σ8 (P 7) W c := ⟨by simp [hσ8, hσ6, hσ5, hσ4, hσ2, hσ1,
      Function.update_of_ne (pne (show (7 : Fin 12) ≠ 0 by decide)), Function.update_of_ne (pne (show (7 : Fin 12) ≠ 3 by decide)),
      hS.1],
    by simp [hσ8, hσ6, hσ5, hσ4, hσ2, hσ1, Function.update_of_ne (pne (show (7 : Fin 12) ≠ 0 by decide)),
      Function.update_of_ne (pne (show (7 : Fin 12) ≠ 3 by decide)), Function.update_of_ne (pne (Ne.symm hX7)), hS.2]⟩
  have v8 : σ8.val = (σ.setv (Q 17) 0).val := by
    funext r; by_cases hr : r = Q 12
    · subst hr; simp [hσ8, Function.update_of_ne (qne (show (12 : Fin 20) ≠ 17 by decide)), h12]
    · simp [hσ8, Function.update_of_ne hr, v6]
  have e9 := BinW.zero_spec cap W (pne (show (3 : Fin 12) ≠ 7 by decide)) (qne (show (15 : Fin 20) ≠ 16 by decide)) σ8
    (2 ^ e) c hD8 hS8 (by rw [v8]; simp [Function.update_of_ne (qne (show (15 : Fin 20) ≠ 17 by decide)), h15])
    (by rw [v8]; simp [Function.update_of_ne (qne (show (16 : Fin 20) ≠ 17 by decide)), h16]) (by omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq (WXExec.wm e4)
    (WXExec.seq e5 (WXExec.seq e6 (WXExec.seq e7 (WXExec.seq (WXExec.wm e8) e9)))))))) ?_ le_rfl
  have hP03 : P 0 ≠ P 3 := pne (by decide)
  have hP0X : P 0 ≠ P X := pne (Ne.symm hX0)
  have hP3X : P 3 ≠ P X := pne (Ne.symm hX3)
  apply WState.eq
  · funext j
    by_cases j0 : j = P 0
    · subst j0
      simp [hσ8, hσ6, hσ5, hσ4, hσ2, hσ1, hP03, hP0X, Function.update_of_ne hP03, Function.update_of_ne hP0X,
        natWord_zero]
      omega
    · by_cases j3 : j = P 3
      · subst j3
        simp [hσ8, hD.2]
        simp [hσ6]
        have := hL2
        omega
      · by_cases jX : j = P X
        · subst jX
          simp [hσ8, hσ6, hσ5, hσ4, hσ2, Function.update_of_ne hP3X.symm, Function.update_of_ne hP0X.symm, hXw.2]
          have := hLx
          omega
        · simp [hσ8, hσ6, hσ5, hσ4, hσ2, hσ1, Function.update_of_ne j0, Function.update_of_ne j3,
            Function.update_of_ne jX]
  · funext j
    by_cases j0 : j = P 0
    · subst j0
      simp [hσ8, hσ6, hσ5, hσ4, hσ2, hσ1, Function.update_of_ne hP03, natWord_zero]
    · by_cases j3 : j = P 3
      · subst j3; simp
      · simp [hσ8, hσ6, hσ5, hσ4, hσ2, hσ1, Function.update_of_ne j0, Function.update_of_ne j3]
  · simp only [WState.sets_val]; rw [v8]; simp
  · simp [hσ8, hσ6, hσ5, hσ4, hσ2, hσ1]
