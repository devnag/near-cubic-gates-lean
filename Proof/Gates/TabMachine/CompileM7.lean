import Proof.Gates.TabMachine.CompileM6

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

section Scan
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- Zero the three statistics, then one pass over the weights. -/
def stats : WMX ns nr :=
  .seq (BinW.zero (S 8) (S 20) (R 2) (R 3))
  (.seq (BinW.zero (S 9) (S 20) (R 2) (R 3))
  (.seq (BinW.zero (S 10) (S 20) (R 2) (R 3))
  (recLoop (S 0) (S 3) (R 0) (R 1) (statBody S R))))

/-- The scan's invariant. -/
def SInv (W : ℕ) (σ0 : WState ns nr) (ws : List ℤ) (k : ℕ) (τ : WState ns nr) : Prop :=
  NumOn τ (S 8) (W + 1) (negN (ws.take k)) ∧ NumOn τ (S 9) (W + 1) (totalL (ws.take k)) ∧
    NumOn τ (S 10) (W + 1) (maxL (ws.take k)) ∧ (∃ v, NumOn τ (S 4) (W + 1) v) ∧ τ.sh (S 3) = 0 ∧
    (τ.st (S 3)).length ≤ 2 * (W + 1) + 1 ∧
    SameExcept σ0 τ [S 0, S 3, S 4, S 8, S 9, S 10] [R 0, R 1]

theorem negN_le (l : List ℤ) : negN l ≤ totalL l := by
  unfold negN totalL
  induction l with
  | nil => simp
  | cons z l ih => simp only [List.map_cons, List.sum_cons]; split <;> omega

theorem maxL_le (l : List ℤ) : maxL l ≤ totalL l := by
  induction l with
  | nil => simp [maxL, totalL]
  | cons z l ih => simp only [maxL, totalL, List.map_cons, List.foldr_cons, List.sum_cons] at ih ⊢; omega

theorem totalL_take_le (l : List ℤ) (k : ℕ) : totalL (l.take k) ≤ totalL l := by
  conv_rhs => rw [← List.take_append_drop k l]
  unfold totalL; rw [List.map_append, List.sum_append]; omega

theorem stats_spec (cap W : ℕ) (σ : WState ns nr) (ws : List ℤ) (junk : List Bool)
    (hWS : σ.st (S 0) = recStream (ws.map fun z => binary (W + 1) (encS z)) ++ junk) (hWSh : σ.sh (S 0) = 0)
    (hCI : σ.val (R 0) = 0) (hCW : σ.val (R 1) = 0) (hWkh : σ.sh (S 3) = 0)
    (hWkl : (σ.st (S 3)).length ≤ 2 * (W + 1) + 1) (hM : ∃ v, NumOn σ (S 4) (W + 1) v)
    (hNM : ∃ v, NumOn σ (S 8) (W + 1) v) (hTM : ∃ v, NumOn σ (S 9) (W + 1) v) (hMX : ∃ v, NumOn σ (S 10) (W + 1) v)
    (hZR : NumOn σ (S 20) (W + 1) 0) (hSg : σ.val (R 4) = 0) (hF : σ.val (R 2) = 0) (hR : σ.val (R 3) = 0)
    (hw : ∀ z ∈ ws, z.natAbs < 2 ^ W) (htot : totalL ws < 2 ^ W)
    (hcap : ws.length * (2 * (W + 1) + 1) + 2 * (W + 1) + 2 ≤ cap) :
    Runs cap (stats S R) σ (3 * (41 * (W + 1) + 4) + ws.length * (450 * W + 600 + (50 * (W + 1) + 30)) + 3)
      (fun τ => NumOn τ (S 8) (W + 1) (negN ws) ∧ NumOn τ (S 9) (W + 1) (totalL ws) ∧
        NumOn τ (S 10) (W + 1) (maxL ws) ∧ (∃ v, NumOn τ (S 4) (W + 1) v) ∧ τ.sh (S 3) = 0 ∧
        (τ.st (S 3)).length ≤ 2 * (W + 1) + 1 ∧ SameExcept σ τ [S 3, S 4, S 8, S 9, S 10] []) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  have hW1 : 2 ^ W ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc1 : 2 * (W + 1) + 1 ≤ cap := by nlinarith
  obtain ⟨nm0, hnm0⟩ := hNM
  obtain ⟨tm0, htm0⟩ := hTM
  obtain ⟨mx0, hmx0⟩ := hMX
  have z1 := BinW.zero_spec (A := S 8) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ nm0 0 hnm0 hZR hF hR hc1
  set σ1 := σ.sets (S 8) (frame (binary (W + 1) 0)) with hσ1
  have z2 := BinW.zero_spec (A := S 9) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ1 tm0 0 (BinW.numOn_sets_ne htm0 (hne (by decide)) _)
    (BinW.numOn_sets_ne hZR (hne (by decide)) _) (by simp [hσ1, hF]) (by simp [hσ1, hR]) hc1
  set σ2 := σ1.sets (S 9) (frame (binary (W + 1) 0)) with hσ2
  have z3 := BinW.zero_spec (A := S 10) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ2 mx0 0 (BinW.numOn_sets_ne (BinW.numOn_sets_ne hmx0 (hne (by decide)) _) (hne (by decide)) _)
    (BinW.numOn_sets_ne (BinW.numOn_sets_ne hZR (hne (by decide)) _) (hne (by decide)) _) (by simp [hσ2, hσ1, hF])
    (by simp [hσ2, hσ1, hR]) hc1
  set σ3 := σ2.sets (S 10) (frame (binary (W + 1) 0)) with hσ3
  have hfr3 : SameExcept σ σ3 [S 8, S 9, S 10] [] := ⟨fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hσ3, hσ2, hσ1, Function.update_of_ne hy.1, Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2],
    fun r _ => by simp [hσ3, hσ2, hσ1], rfl⟩
  have h0 : SInv S R W σ3 ws 0 σ3 := ⟨⟨by simp [hσ3, hσ2, hσ1, emb_eq_iff, negN], by
      simp [hσ3, hσ2, hσ1, hnm0.2]⟩, ⟨by simp [hσ3, hσ2, emb_eq_iff, totalL], by simp [hσ3, hσ2, hσ1, htm0.2]⟩,
    ⟨by simp [hσ3, maxL], by simp [hσ3, hσ2, hσ1, hmx0.2]⟩,
    hM.elim fun v h => ⟨v, hfr3.numOn (by simp [emb_eq_iff]) h⟩, by rw [hfr3.sh (by simp [emb_eq_iff]), hWkh],
    by rw [hfr3.st (by simp [emb_eq_iff])]; exact hWkl, SameExcept.refl _ _ _⟩
  have hwl : ∀ w ∈ ws.map (fun z => binary (W + 1) (encS z)), w.length = W + 1 := by
    intro w hw'; obtain ⟨z, _, rfl⟩ := List.mem_map.mp hw'; simp
  have hb : BodySpecJ cap (W + 1) (I := S 0) (Wk := S 3) (CI := R 0) (CW := R 1) (statBody S R)
      (ws.map fun z => binary (W + 1) (encS z)) (SInv S R W σ3 ws) (fun _ => 450 * W + 600) junk := by
    intro k hk τ hInv hst hsh hci hcw hwh hwl'
    simp only [List.length_map] at hk
    obtain ⟨hNMk, hTMk, hMXk, ⟨mv, hmv⟩, -, -, hfrk⟩ := hInv
    have hwk : (ws.map fun z => binary (W + 1) (encS z))[k] = binary (W + 1) (encS ws[k]) := List.getElem_map _
    rw [hwk]
    set τ1 := atRec (S 0) (S 3) (R 0) τ (binary (W + 1) (encS ws[k])) ((k + 1) * (2 * (W + 1) + 1)) with hτ1
    have hl : ∀ (j : Fin 24) (v : ℕ), j ≠ 0 → j ≠ 3 → NumOn τ (S j) (W + 1) v → NumOn τ1 (S j) (W + 1) v :=
      fun j v h0 h3 h => ⟨by simp [hτ1, atRec, Function.update_of_ne (hne h3), h.1], by
        simp [hτ1, atRec, Function.update_of_ne (hne h0), h.2]⟩
    have hRk : ∀ j : Fin 24, j ≠ 0 → j ≠ 1 → τ1.val (R j) = σ.val (R j) := fun j h0 h1 => by
      simp only [hτ1, atRec, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_of_ne (hner h0)]
      rw [hfrk.val (by simp [emb_eq_iff, h0, h1]), hfr3.val (by simp)]
    have hzk : ws[k].natAbs < 2 ^ W := hw _ (List.getElem_mem hk)
    have htk : totalL (ws.take k) + ws[k].natAbs ≤ totalL ws := by
      have := totalL_take_le ws (k + 1)
      rw [List.take_add_one, List.getElem?_eq_getElem hk] at this
      have e : (ws.take k ++ (some ws[k]).toList) = ws.take k ++ [ws[k]] := rfl
      rw [e, totalL_snoc] at this; exact this
    have hb := statBody_spec S R cap W τ1 ws[k] (negN (ws.take k)) (totalL (ws.take k)) (maxL (ws.take k)) mv
      ⟨by simp [hτ1, atRec], by simp [hτ1, atRec, emb_eq_iff, hwh]⟩ (hl _ _ (by decide) (by decide) hmv)
      (hl _ _ (by decide) (by decide) hNMk) (hl _ _ (by decide) (by decide) hTMk) (hl _ _ (by decide) (by decide) hMXk)
      (by rw [hRk 4 (by decide) (by decide)]; exact hSg) (by rw [hRk 2 (by decide) (by decide)]; exact hF)
      (by rw [hRk 3 (by decide) (by decide)]; exact hR) hzk
      (by have := maxL_le (ws.take k); omega) (by have := negN_le (ws.take k); omega) (by omega) hc1
    obtain ⟨τ2, e2, hNM2, hTM2, hMX2, hM2, hfr2⟩ := hb
    have htake : ws.take (k + 1) = ws.take k ++ [ws[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
    refine ⟨τ2, e2, ⟨by rw [htake, negN_snoc]; exact hNM2, by rw [htake, totalL_snoc]; exact hTM2,
      by rw [htake, maxL_snoc]; exact hMX2, hM2, by rw [hfr2.sh (by simp [emb_eq_iff])]; simp [hτ1, atRec, emb_eq_iff, hwh],
      by rw [hfr2.st (by simp [emb_eq_iff])]; simp [hτ1, atRec, frame_length], ?_⟩, ?_⟩
    · have hfr1 : SameExcept τ τ1 [S 0, S 3] [R 0] := ⟨fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [hτ1, atRec, Function.update_of_ne hy.1, Function.update_of_ne hy.2], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp [hτ1, atRec, Function.update_of_ne hr], rfl⟩
      exact (hfrk.trans (hfr1.weaken (by simp) (by simp))).trans (hfr2.weaken (by simp) (by simp))
    · have b1 : τ2.st (S 0) = τ1.st (S 0) := hfr2.st (by simp [emb_eq_iff])
      have b2 : τ2.sh (S 0) = τ1.sh (S 0) := hfr2.sh (by simp [emb_eq_iff])
      have b3 : τ2.val (R 0) = τ1.val (R 0) := hfr2.val (by simp)
      have b4 : τ2.val (R 1) = τ1.val (R 1) := hfr2.val (by simp)
      have b5 : τ2.sh (S 3) = 0 := by rw [hfr2.sh (by simp [emb_eq_iff])]; simp [hτ1, atRec, emb_eq_iff, hwh]
      have b6 : (τ2.st (S 3)).length ≤ 2 * (W + 1) + 1 := by
        rw [hfr2.st (by simp [emb_eq_iff])]; simp [hτ1, atRec, frame_length]
      exact ⟨b1, b2, b3, b4, b5, b6⟩
  obtain ⟨τ, hInv, hτI, hτCW, hloop⟩ := recLoopJ_spec (cap := cap) (L := W + 1) (I := S 0) (Wk := S 3) (CI := R 0)
    (CW := R 1) (body := statBody S R) (hne (by decide)) (hner (by decide)) hwl (by omega)
    (by simp only [List.length_map]; omega) hb σ3 h0
    (by rw [hfr3.st (by simp [emb_eq_iff]), hWS]) (by rw [hfr3.sh (by simp [emb_eq_iff]), hWSh])
    (by rw [hfr3.val (by simp)]; exact hCI) (by rw [hfr3.val (by simp)]; exact hCW)
    (by rw [hfr3.sh (by simp [emb_eq_iff]), hWkh]) (by rw [hfr3.st (by simp [emb_eq_iff])]; exact hWkl)
  simp only [List.length_map, List.take_length] at hInv hloop
  obtain ⟨hNMf, hTMf, hMXf, hMf, hWkhf, hWklf, hfrf⟩ := hInv
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hloop
  refine ⟨_, WXExec.mono (WXExec.seq z1 (WXExec.seq z2 (WXExec.seq z3 hloop))) (by omega), ?_⟩
  refine ⟨⟨by simp [hNMf.1], by simp [emb_eq_iff, hNMf.2]⟩, ⟨by simp [hTMf.1], by simp [emb_eq_iff, hTMf.2]⟩,
    ⟨by simp [hMXf.1], by simp [emb_eq_iff, hMXf.2]⟩, hMf.elim fun v h => ⟨v, by simp [h.1], by simp [emb_eq_iff, h.2]⟩,
    by simp [emb_eq_iff, hWkhf], by simpa using hWklf, ?_⟩
  refine ⟨fun y hy => ?_, fun r _ => ?_, by simp [hfrf.cell, hfr3.cell]⟩
  · by_cases hy0 : y = S 0
    · rw [hy0]; simp [hτI, hWS, hWSh]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      have h1 := hfrf.1 y (by simp [hy0, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2])
      have h2 := hfr3.1 y (by simp [hy.2.2.2.1, hy.2.2.2.2, hy.2.2.1])
      simp [Function.update_of_ne hy0, h1.1, h1.2, h2.1, h2.2]
  · by_cases r0 : r = R 0
    · rw [r0]; simp [hCI]
    · by_cases r1 : r = R 1
      · rw [r1]; simp [Function.update_of_ne (hner (show (1 : Fin 24) ≠ 0 by decide)), hτCW, hCW]
      · simp only [WState.setv_val, WState.seth_val, Function.update_of_ne r0]
        rw [hfrf.val (r := r) (by simp [r0, r1]), hfr3.val (r := r) (by simp)]

end Scan

end NearCubicGates.Close.TabMachine
