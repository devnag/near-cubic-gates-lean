import Proof.Gates.WorkerArith.CtrCallA

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

variable {ns nr : ℕ}

/-! ## Step 3: the output word, natWord by natWord -/

theorem copyKM (cap : ℕ) (O VI : Fin (ns + 1)) (hOV : O ≠ VI) (R : Fin 8 ↪ Fin nr) :
    ∀ (xs : List ℕ) (σ : WState ns nr) (pre rest : List Bool), σ.st O = pre ++ xs.flatMap natWord ++ rest →
      σ.sh O = pre.length → σ.sh VI = (σ.st VI).length → σ.val (R 1) = 0 → σ.val (R 2) = 0 →
      σ.val (R 7) + 2 * (xs.flatMap natWord).length + 2 ≤ cap →
      WExec cap (copyK O VI R xs.length) σ
        ((appendO σ VI (R 7) (marks (xs.flatMap natWord))).seth O (pre.length + (xs.flatMap natWord).length))
        (121 * (xs.flatMap natWord).length)
  | [], σ, pre, rest, _, hsh, hv, _, _, _ => by
    have e : (appendO σ VI (R 7) (marks (([] : List ℕ).flatMap natWord))).seth O
        (pre.length + (([] : List ℕ).flatMap natWord).length) = σ := by
      simp only [List.flatMap_nil, List.length_nil, Nat.add_zero]
      rw [show marks ([] : List Bool) = [] by simp [marks], Codec.appendO_nil σ VI (R 7) hv, ← hsh]
      exact WState.eq (by simp) rfl rfl rfl
    rw [e]; exact WExec.mono (WExec.skip σ) (Nat.zero_le _)
  | x :: xs, σ, pre, rest, hst, hsh, hv, h1, h2, hc => by
    simp only [List.flatMap_cons, List.length_append] at hc
    have e1 := Codec.copyNat_spec cap false O VI hOV R x pre (xs.flatMap natWord ++ rest) σ
      (by rw [hst]; simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc, List.append_assoc]) hsh hv h1 h2
      (by omega)
    set σ1 := (appendO σ VI (R 7) (marks (natWord x))).seth O
      (pre.length + NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp false * (natWord x).length) with hσ1
    have hs0 : NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp false = 1 := rfl
    have hs1 : NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp false * (natWord x).length = (natWord x).length := by
      rw [hs0, one_mul]
    have e2 := copyKM cap O VI hOV R xs σ1 (pre ++ natWord x) rest
      (by simp [hσ1, appendO, Function.update_of_ne hOV, hst, List.append_assoc])
      (by simp [hσ1, hs0])
      (by simp [hσ1, appendO, Function.update_of_ne hOV.symm, hv])
      (by simp [hσ1, appendO, Codec.Rne R (show (1 : Fin 8) ≠ 7 by decide), h1])
      (by simp [hσ1, appendO, Codec.Rne R (show (2 : Fin 8) ≠ 7 by decide), h2])
      (by
        have : σ1.val (R 7) = σ.val (R 7) + 2 * (natWord x).length := by
          simp only [hσ1, appendO, WState.seth_val, WState.setv_val, Function.update_self, Codec.marks_length]
        omega)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ ?_
    · rw [hσ1, hs1]
      apply WState.eq
      · funext i; by_cases hi : i = O
        · subst hi; simp [appendO, Function.update_of_ne hOV, List.append_assoc]; ring
        · by_cases hi2 : i = VI
          · subst hi2; simp [appendO, Function.update_of_ne hi, Codec.marksApp]; ring
          · simp [appendO, Function.update_of_ne hi, Function.update_of_ne hi2]
      · funext i; by_cases hi : i = VI
        · subst hi; simp [appendO, Function.update_of_ne hOV.symm, Codec.marksApp, List.append_assoc]
        · simp [appendO, Function.update_of_ne hi]
      · funext r; by_cases hr : r = R 7
        · subst hr; simp [appendO, Codec.marksApp, Codec.marks_length]; ring
        · simp [appendO, Function.update_of_ne hr]
      · rfl
    · simp only [List.flatMap_cons, List.length_append]
      have : 1 ≤ (natWord x).length := by
        simp [natWord, WilliamsPublishedForm.framedNatBits, WilliamsPublishedForm.fixedWidthNatBits]; omega
      nlinarith

/-! ## A register-driven rewind (WMX form) -/

theorem rewX (cap : ℕ) (G : Fin (ns + 1)) (R : Fin nr) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val R = k → k ≤ cap →
      WXExec cap (.whr R (.seq (WMX.bwd G) (WMX.dec R))) σ ((σ.seth G (σ.sh G - k)).setv R 0) (k * 5 + 1)
  | 0, σ, h0, _ => by
    have e : (σ.seth G (σ.sh G - 0)).setv R 0 = σ := by
      apply WState.eq
      · funext i; by_cases hi : i = G
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      · rfl
      · simp only [WState.setv_val]; rw [← h0]; exact Function.update_eq_self R σ.val
      · rfl
    rw [e]; exact WXExec.whrF h0
  | k + 1, σ, hk, hc => by
    have e1 := WXExec.bwd cap G σ
    have e2 := WXExec.dec cap R (σ.seth G (σ.sh G - 1)) (by simp; omega)
    have e3 := rewX cap G R k ((σ.seth G (σ.sh G - 1)).setv R ((σ.seth G (σ.sh G - 1)).val R - 1)) (by simp; omega)
      (by omega)
    refine (WXExec.whrT (by omega) (WXExec.seq e1 e2) e3).cast cap ?_ (by ring_nf; omega)
    apply WState.eq
    · funext i; by_cases hi : i = G
      · subst hi; simp; omega
      · simp [Function.update_of_ne hi]
    · rfl
    · funext r; by_cases hr : r = R
      · subst hr; simp
      · simp [Function.update_of_ne hr]
    · rfl

/-! ## Step 4: the tally -/

theorem tallyM (cap : ℕ) (TL G : Fin (ns + 1)) (hTG : TL ≠ G) (RG RT : Fin nr) (hR : RG ≠ RT) (σ : WState ns nr)
    (a s : ℕ) (hG : σ.st G = List.replicate a true) (hGh : σ.sh G = a) (hRG : σ.val RG = a)
    (hTL : σ.st TL = List.replicate s true) (hTLh : σ.sh TL = 0) (hRT : σ.val RT = 0) (hc : a + s ≤ cap) :
    WXExec cap (tallyP TL G RG RT) σ (((σ.sets G (List.replicate (a + s) true)).seth G 0).setv RG 0)
      (25 * (a + s) + 10) := by
  let st : ℕ → WState ns nr := fun j =>
    ((((σ.sets G (List.replicate (a + j) true)).seth G (a + j)).setv RG (a + j)).seth TL j).setv RT j
  have hloop := Runs.whs (cap := cap) (i := TL)
    (P := .seq (WMX.wr G true) (.seq (WMX.fwd G) (.seq (WMX.inc RG) (.seq (WMX.fwd TL) (WMX.inc RT)))))
    (fun k τ => k ≤ s ∧ τ = st (s - k)) 13 (fun τ => τ = st s)
    (by
      rintro τ ⟨-, rfl⟩
      refine ⟨?_, by simp⟩
      simp only [wbit, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        Function.update_of_ne hTG, Function.update_self, hTL, Nat.sub_zero]
      unfold readTapeBit; rw [List.getD_eq_default _ _ (by simp)])
    (by
      rintro k τ ⟨hk, rfl⟩
      set j := s - (k + 1) with hj
      refine ⟨?_, ?_⟩
      · simp only [wbit, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          Function.update_of_ne hTG, Function.update_self, hTL]
        unfold readTapeBit; rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
      · have e1 := WXExec.wr cap G true (st j)
        have hw : writeTapeBit ((st j).st G) ((st j).sh G) true = List.replicate (a + (j + 1)) true := by
          simp only [st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
            Function.update_self, Function.update_of_ne hTG.symm]
          have := writeTapeBit_end' (List.replicate (a + j) true) true
          rw [List.length_replicate] at this
          rw [this, ← List.replicate_succ']; rfl
        rw [hw] at e1
        set τ1 := (st j).sets G (List.replicate (a + (j + 1)) true) with hτ1
        have e2 := WXExec.fwd cap G τ1
        set τ2 := τ1.seth G (τ1.sh G + 1) with hτ2
        have e3 := WXExec.inc cap RG τ2 (by simp [hτ2, hτ1, st, Function.update_of_ne hR]; omega)
        set τ3 := τ2.setv RG (τ2.val RG + 1) with hτ3
        have e4 := WXExec.fwd cap TL τ3
        set τ4 := τ3.seth TL (τ3.sh TL + 1) with hτ4
        have e5 := WXExec.inc cap RT τ4 (by simp [hτ4, hτ3, hτ2, hτ1, st, Function.update_of_ne hR.symm]; omega)
        refine ⟨_, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5))), by omega, ?_⟩
        rw [show s - k = j + 1 by omega]
        apply WState.eq
        · funext i; by_cases hi : i = G
          · subst hi; simp [hτ4, hτ3, hτ2, hτ1, st, Function.update_of_ne hTG.symm]; omega
          · by_cases hi2 : i = TL
            · subst hi2; simp [hτ4, hτ3, hτ2, hτ1, st, Function.update_of_ne hi]
            · simp [hτ4, hτ3, hτ2, hτ1, st, Function.update_of_ne hi, Function.update_of_ne hi2]
        · funext i; by_cases hi : i = G
          · subst hi; simp [hτ4, hτ3, hτ2, hτ1, st]
          · simp [hτ4, hτ3, hτ2, hτ1, st, Function.update_of_ne hi]
        · funext r; by_cases hr1 : r = RG
          · subst hr1; simp [hτ4, hτ3, hτ2, hτ1, st, Function.update_of_ne hR]; omega
          · by_cases hr2 : r = RT
            · subst hr2; simp [hτ4, hτ3, hτ2, hτ1, st, Function.update_of_ne hr1]
            · simp [hτ4, hτ3, hτ2, hτ1, st, Function.update_of_ne hr1, Function.update_of_ne hr2]
        · rfl)
    s (st 0) ⟨le_rfl, by simp⟩
  obtain ⟨τ, e1, rfl⟩ := hloop
  have st0 : st 0 = σ := by
    apply WState.eq
    · funext i; by_cases hi : i = G
      · subst hi; simp [st, Function.update_of_ne hTG.symm, hGh]
      · by_cases hi2 : i = TL
        · subst hi2; simp [st, Function.update_of_ne hi, hTLh]
        · simp [st, Function.update_of_ne hi, Function.update_of_ne hi2]
    · funext i; by_cases hi : i = G
      · subst hi; simp [st, hG]
      · simp [st, Function.update_of_ne hi]
    · funext r; by_cases hr1 : r = RG
      · subst hr1; simp [st, Function.update_of_ne hR, hRG]
      · by_cases hr2 : r = RT
        · subst hr2; simp [st, Function.update_of_ne hr1, hRT]
        · simp [st, Function.update_of_ne hr1, Function.update_of_ne hr2]
    · rfl
  rw [st0] at e1
  have e2 := wrewind_spec (cap := cap) TL RT s (st s) (by simp [st]) (by simp [st]; omega)
  set τ2 := ((st s).setv RT 0).seth TL ((st s).sh TL - s) with hτ2
  have e3 := wrewind_spec (cap := cap) G RG (a + s) τ2 (by simp [hτ2, st, Function.update_of_ne hR])
    (by simp [hτ2, st, Function.update_of_ne hR]; omega)
  refine (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.wm e3))).cast cap ?_ (by nlinarith)
  apply WState.eq
  · funext i; by_cases hi : i = G
    · subst hi; simp [hτ2, st, Function.update_of_ne hTG.symm]
    · by_cases hi2 : i = TL
      · subst hi2; simp [hτ2, st, Function.update_of_ne hi, hTLh]
      · simp [hτ2, st, Function.update_of_ne hi, Function.update_of_ne hi2]
  · funext i; by_cases hi : i = G
    · subst hi; simp [hτ2, st]
    · simp [hτ2, st, Function.update_of_ne hi]
  · funext r; by_cases hr1 : r = RG
    · subst hr1; simp [hτ2, st]
    · by_cases hr2 : r = RT
      · subst hr2; simp [hτ2, st, Function.update_of_ne hr1, hRT]
      · simp [hτ2, st, Function.update_of_ne hr1, Function.update_of_ne hr2]
  · rfl

/-! ## Step 5a: clear the output tape backwards -/

theorem clearBackM (cap : ℕ) (O G : Fin (ns + 1)) (hOG : O ≠ G) (R : Fin nr) (σ : WState ns nr) (m p : ℕ)
    (hG : σ.st G = List.replicate m true) (hGh : σ.sh G = 0) (hR : σ.val R = 0) (hOh : σ.sh O = p)
    (hfar : ∀ q, p < q → readTapeBit (σ.st O) q = false) (hpm : p + 1 ≤ m) (hc : m ≤ cap) :
    ∃ l, WXExec cap (clearBackP O G R) σ ((σ.sets O l).seth O 0) (20 * m + 5) ∧ Worker.Blank l := by
  let st : ℕ → List Bool → WState ns nr := fun i l =>
    (((σ.sets O l).seth O (p - i)).seth G i).setv R i
  have hloop := Runs.whs (cap := cap) (i := G)
    (P := .seq (WMX.wr O false) (.seq (WMX.bwd O) (.seq (WMX.fwd G) (WMX.inc R))))
    (fun k τ => k ≤ m ∧ ∃ l, τ = st (m - k) l ∧ ∀ q, p < q + (m - k) → readTapeBit l q = false) 9
    (fun τ => ∃ l, τ = st m l ∧ Worker.Blank l)
    (by
      rintro τ ⟨-, l, rfl, hl⟩
      refine ⟨?_, l, by simp, fun q => hl q (by omega)⟩
      simp only [wbit, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        Function.update_of_ne hOG.symm, Function.update_self, hG, Nat.sub_zero]
      unfold readTapeBit; rw [List.getD_eq_default _ _ (by simp)])
    (by
      rintro k τ ⟨hk, l, rfl, hl⟩
      set i := m - (k + 1) with hi
      refine ⟨?_, ?_⟩
      · simp only [wbit, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          Function.update_of_ne hOG.symm, Function.update_self, hG]
        unfold readTapeBit; rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
      · have e1 := WXExec.wr cap O false (st i l)
        set l' := writeTapeBit ((st i l).st O) ((st i l).sh O) false with hl'
        have e2 := WXExec.bwd cap O ((st i l).sets O l')
        have e3 := WXExec.fwd cap G (((st i l).sets O l').seth O (((st i l).sets O l').sh O - 1))
        have e4 := WXExec.inc cap R ((((st i l).sets O l').seth O (((st i l).sets O l').sh O - 1)).seth G
          ((((st i l).sets O l').seth O (((st i l).sets O l').sh O - 1)).sh G + 1))
          (by simp [st]; omega)
        refine ⟨_, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4)), by omega, l', ?_, ?_⟩
        · rw [show m - k = i + 1 by omega]
          apply WState.eq
          · funext j; by_cases hj : j = O
            · subst hj; simp [st, Function.update_of_ne hOG]; omega
            · by_cases hj2 : j = G
              · subst hj2; simp [st, Function.update_of_ne hj]
              · simp [st, Function.update_of_ne hj, Function.update_of_ne hj2]
          · funext j; by_cases hj : j = O
            · subst hj; simp [st]
            · simp [st, Function.update_of_ne hj]
          · funext r; by_cases hr : r = R
            · subst hr; simp [st]
            · simp [st, Function.update_of_ne hr]
          · rfl
        · intro q hq
          have hsO : (st i l).sh O = p - i := by simp [st, Function.update_of_ne hOG]
          have hstO : (st i l).st O = l := by simp [st]
          rw [hl', hsO, hstO, readTapeBit_write]
          split_ifs with hq'
          · rfl
          · exact hl q (by omega))
    m (st 0 (σ.st O)) ⟨le_rfl, σ.st O, by simp, fun q hq => hfar q (by omega)⟩
  obtain ⟨τ, e1, l, rfl, hlb⟩ := hloop
  have st0 : st 0 (σ.st O) = σ := by
    apply WState.eq
    · funext j; by_cases hj : j = O
      · subst hj; simp [st, Function.update_of_ne hOG, hOh]
      · by_cases hj2 : j = G
        · subst hj2; simp [st, Function.update_of_ne hj, hGh]
        · simp [st, Function.update_of_ne hj, Function.update_of_ne hj2]
    · funext j; by_cases hj : j = O
      · subst hj; simp [st]
      · simp [st, Function.update_of_ne hj]
    · funext r; by_cases hr : r = R
      · subst hr; simp [st, hR]
      · simp [st, Function.update_of_ne hr]
    · rfl
  rw [st0] at e1
  have e2 := rewX cap G R m (st m l) (by simp [st]) hc
  refine ⟨l, (WXExec.seq e1 e2).cast cap ?_ (by nlinarith), hlb⟩
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp [st, Function.update_of_ne hOG]; omega
    · by_cases hj2 : j = G
      · subst hj2; simp [st, Function.update_of_ne hj, hGh]
      · simp [st, Function.update_of_ne hj, Function.update_of_ne hj2]
  · rfl
  · funext r; by_cases hr : r = R
    · subst hr; simp [st, hR]
    · simp [st, Function.update_of_ne hr]
  · rfl

/-! ## Step 5b: `clearOne` on a list of streams -/

theorem clearAllM (cap : ℕ) (G : Fin (ns + 1)) (R : Fin nr) (m : ℕ) (hc : m ≤ cap) :
    ∀ (Xs : List (Fin (ns + 1))) (σ : WState ns nr), Xs.Nodup → (∀ X ∈ Xs, X ≠ G) →
      σ.st G = List.replicate m true → σ.sh G = 0 → σ.val R = 0 → (∀ X ∈ Xs, σ.sh X = 0) →
      WXExec cap (clearAll G R Xs) σ ⟨σ.sh, fun i => if i ∈ Xs then clearPrefix m (σ.st i) else σ.st i, σ.val,
        σ.cell⟩ (Xs.length * (18 * m + 4))
  | [], σ, _, _, _, _, _, _ => by
    have e : (⟨σ.sh, fun i => if i ∈ ([] : List (Fin (ns + 1))) then clearPrefix m (σ.st i) else σ.st i, σ.val,
        σ.cell⟩ : WState ns nr) = σ := WState.eq rfl (by funext i; simp) rfl rfl
    rw [e]; simpa [clearAll] using WXExec.skip cap σ
  | X :: Xs, σ, hnd, hXG, hG, hGh, hR, hX0 => by
    have hX : X ≠ G := hXG X (by simp)
    have e1 := clearOne_exec X G R hX m hc σ hG hGh (hX0 X (by simp)) hR
    have hnX : X ∉ Xs := (List.nodup_cons.1 hnd).1
    have e2 := clearAllM cap G R m hc Xs (σ.sets X (clearPrefix m (σ.st X))) (List.nodup_cons.1 hnd).2
      (fun Y hY => hXG Y (by simp [hY])) (by simp [Function.update_of_ne hX.symm, hG]) (by simp [hGh]) (by simp [hR])
      (fun Y hY => by simp [hX0 Y (by simp [hY])])
    refine (WXExec.seq e1 e2).cast cap ?_ (by simp only [List.length_cons]; nlinarith)
    apply WState.eq
    · rfl
    · funext i
      by_cases hi : i = X
      · subst hi; simp [hnX]
      · by_cases hi2 : i ∈ Xs
        · simp [hi2, Function.update_of_ne hi]
        · simp [hi2, hi, Function.update_of_ne hi]
    · rfl
    · rfl

/-! ## Step 5d: blank the guard -/

theorem clearSelfM (cap : ℕ) (G : Fin (ns + 1)) (R : Fin nr) (σ : WState ns nr) (m : ℕ)
    (hG : σ.st G = List.replicate m true) (hGh : σ.sh G = 0) (hR : σ.val R = 0) (hc : m ≤ cap) :
    WXExec cap (clearSelfP G R) σ (σ.sets G (List.replicate m false)) (20 * m + 5) := by
  let st : ℕ → WState ns nr := fun i =>
    ((σ.sets G (List.replicate i false ++ List.replicate (m - i) true)).seth G i).setv R i
  have hloop := Runs.whs (cap := cap) (i := G)
    (P := .seq (WMX.wr G false) (.seq (WMX.fwd G) (WMX.inc R)))
    (fun k τ => k ≤ m ∧ τ = st (m - k)) 7 (fun τ => τ = st m)
    (by
      rintro τ ⟨-, rfl⟩
      refine ⟨?_, by simp⟩
      simp only [wbit, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        Function.update_self, Nat.sub_zero, Nat.sub_self, List.replicate_zero, List.append_nil]
      unfold readTapeBit; rw [List.getD_eq_default _ _ (by simp)])
    (by
      rintro k τ ⟨hk, rfl⟩
      set i := m - (k + 1) with hi
      have hl : List.replicate i false ++ List.replicate (m - i) true =
          List.replicate i false ++ (true :: List.replicate k true) := by
        rw [show m - i = k + 1 by omega]; rfl
      refine ⟨?_, ?_⟩
      · simp only [wbit, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          Function.update_self, hl]
        unfold readTapeBit
        rw [List.getD_append_right _ _ _ _ (by simp)]; simp
      · have e1 := WXExec.wr cap G false (st i)
        have hw : writeTapeBit ((st i).st G) ((st i).sh G) false =
            List.replicate (i + 1) false ++ List.replicate (m - (i + 1)) true := by
          simp only [st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
            Function.update_self, hl]
          have := wtb_mid (List.replicate i false) (true :: List.replicate k true) false
          rw [List.length_replicate] at this
          rw [this, show m - (i + 1) = k by omega]
          simp only [List.drop_succ_cons, List.drop_zero, List.replicate_succ', List.append_assoc,
            List.singleton_append]
        rw [hw] at e1
        have e2 := WXExec.fwd cap G ((st i).sets G (List.replicate (i + 1) false ++ List.replicate (m - (i + 1)) true))
        have e3 := WXExec.inc cap R (((st i).sets G (List.replicate (i + 1) false ++
          List.replicate (m - (i + 1)) true)).seth G (((st i).sets G (List.replicate (i + 1) false ++
          List.replicate (m - (i + 1)) true)).sh G + 1)) (by simp [st]; omega)
        refine ⟨_, WXExec.seq e1 (WXExec.seq e2 e3), by omega, ?_⟩
        rw [show m - k = i + 1 by omega]
        apply WState.eq
        · funext j; by_cases hj : j = G
          · subst hj; simp [st]
          · simp [st, Function.update_of_ne hj]
        · funext j; by_cases hj : j = G
          · subst hj; simp [st]
          · simp [st, Function.update_of_ne hj]
        · funext r; by_cases hr : r = R
          · subst hr; simp [st]
          · simp [st, Function.update_of_ne hr]
        · rfl)
    m (st 0) ⟨le_rfl, by simp⟩
  obtain ⟨τ, e1, rfl⟩ := hloop
  have st0 : st 0 = σ := by
    apply WState.eq
    · funext j; by_cases hj : j = G
      · subst hj; simp [st, hGh]
      · simp [st, Function.update_of_ne hj]
    · funext j; by_cases hj : j = G
      · subst hj; simp [st, hG]
      · simp [st, Function.update_of_ne hj]
    · funext r; by_cases hr : r = R
      · subst hr; simp [st, hR]
      · simp [st, Function.update_of_ne hr]
    · rfl
  rw [st0] at e1
  have e2 := rewX cap G R m (st m) (by simp [st]) hc
  refine (WXExec.seq e1 e2).cast cap ?_ (by nlinarith)
  apply WState.eq
  · funext j; by_cases hj : j = G
    · subst hj; simp [st, hGh]
    · simp [st, Function.update_of_ne hj]
  · funext j; by_cases hj : j = G
    · subst hj; simp [st]
    · simp [st, Function.update_of_ne hj]
  · funext r; by_cases hr : r = R
    · subst hr; simp [st, hR]
    · simp [st, Function.update_of_ne hr]
  · rfl

end NearCubicGates.Close.WorkerArith
