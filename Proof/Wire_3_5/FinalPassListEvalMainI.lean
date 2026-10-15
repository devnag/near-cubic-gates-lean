import Proof.Wire_3_5.FinalPassListEvalMain

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- Clear the cell and add the indicator `[X = 0]` to `C`. -/
def outputI : LProg := .seq (.setc false) (.ifr rX .skip (.inc rC))

/-- The repair, the comparison, the indicator. -/
def finalPartI : LProg := .seq leqFlag (.seq (.ifr rF (RM.clear rS) .skip) (.seq compare (.seq outputI cleanup)))

/-- **The stage-5 program with the indicator in `C`.** -/
def mainI : LProg := .seq (RM.readU 1 rTP rMR) (.seq (.whs 1 body) finalPartI)

/-- The blank state with cell `false` and `C = k`. -/
def blankI (k : ℕ) : LState := ⟨fun _ => 0, fun r => if r = rC then k else 0, false⟩

variable (inp : Fin 3 → List Bool) (cap : ℕ)

theorem finalPartI_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) (acc : Option ℕ × ℕ)
    (σ : LState) (hinv : Inv M J W row Z [] acc σ) (hs : s ≤ M) :
    RExec (streams M J W row Z s) (capOf M J W row Z.length) finalPartI σ
      (blankI (if repOf M acc.1 = s then 1 else 0)) (finalCost (capOf M J W row Z.length)) := by
  rcases acc with ⟨o, cp⟩
  obtain ⟨hd, hTP, hs0, hs2, hMR, hP, hPL, hF1, hSB, hsome, hnone, hC, hW, hV, hU, hT, hR, hSP, hX, hT1, hT2⟩ := hinv
  simp only at hP hPL hsome hnone ⊢
  generalize hinp : streams M J W row Z s = inp
  generalize hcapv : capOf M J W row Z.length = cap
  have hin1 : inp 1 = levelWord M J W row := by rw [← hinp]; rfl
  have hin2 : inp 2 = unary s := by rw [← hinp]; rfl
  have hcapB : cap = 4 * (wordLen M J W row + Z.length + 1) := by rw [← hcapv]; rfl
  have hM1 := word_M_le M J W row
  have hlen := drop_len_le hd (by simp)
  have hsh1 : σ.sh 1 ≤ wordLen M J W row := by unfold wordLen; simp at hlen; omega
  -- 1. the flag for `s_0 > M`
  have f1 := leqFlag_spec inp cap σ ⟨hT, hT1, hT2⟩ (by omega) (by omega) hF1 (by omega)
  obtain ⟨σa, hσa⟩ : ∃ τ : LState, τ = σ.setv rF (if σ.val rMR < σ.val rS then 1 else σ.val rF) := ⟨_, rfl⟩
  rw [← hσa] at f1
  -- 2. the repaired report into `S`
  have f2 : RExec inp cap (.ifr rF (RM.clear rS) .skip) σa (σa.setv rS (repOf M o)) (3 * cap + 2) := by
    cases o with
    | none =>
      have hF := hnone rfl
      have hFa : σa.val rF = 1 := by rw [hσa]; simp [hF]
      have c1 := clear_spec inp cap rS (σa.val rS) σa rfl (by rw [hσa]; simp; omega)
      exact RExec.mono (RExec.ifrT (by omega) c1) (by rw [hσa]; simp; omega)
    | some v =>
      obtain ⟨hF0, hS0⟩ := hsome v rfl
      by_cases hMv : M < v
      · have hFa : σa.val rF = 1 := by rw [hσa]; simp [hMR, hS0, hMv]
        have c1 := clear_spec inp cap rS (σa.val rS) σa rfl (by rw [hσa]; simp; omega)
        have hr : repOf M (some v) = 0 := by simp [repOf]; omega
        rw [hr]
        exact RExec.mono (RExec.ifrT (by omega) c1) (by rw [hσa]; simp; omega)
      · have hFa : σa.val rF = 0 := by rw [hσa]; simp [hMR, hS0, hMv, hF0]
        have hr : repOf M (some v) = v := by simp [repOf]; omega
        have e : σa.setv rS (repOf M (some v)) = σa := by
          rw [hr]; rw [hσa]; rs_eq [hS0]
        rw [e]
        exact RExec.mono (RExec.ifrF hFa (RExec.skip σa)) (by omega)
  obtain ⟨σb, hσb⟩ : ∃ τ : LState, τ = σa.setv rS (repOf M o) := ⟨_, rfl⟩
  rw [← hσb] at f2
  have hrepM : repOf M o ≤ M := by unfold repOf; split <;> [split <;> omega; omega]
  -- 3. the comparison with `s`
  have hd2 : (inp 2).drop (σb.sh 2) = List.replicate s true ++ false :: [] := by
    rw [hσb, hσa]; simp [hs2, hin2, unary]
  have f3a := cmpLoop_spec inp cap [] (by omega) s σb hd2 (by rw [hσb, hσa]; simp [hSP]; omega)
    (by rw [hσb]; simp; omega) (by rw [hσb, hσa]; simp [hX])
  obtain ⟨σc, hσc⟩ : ∃ τ : LState, τ = (((σb.seth 2 (σb.sh 2 + s)).setv rSP (σb.val rSP + s)).setv rS
      (σb.val rS - s)).setv rX (if σb.val rS < s then 1 else σb.val rX) := ⟨_, rfl⟩
  rw [← hσc] at f3a
  have hcS : σc.val rS = repOf M o - s := by rw [hσc, hσb]; simp
  have hcX : σc.val rX = if repOf M o < s then 1 else 0 := by rw [hσc, hσb, hσa]; simp [hX]
  have f3b : RExec inp cap (.ifr rS (RM.setF rX) .skip) σc (σc.setv rX (if repOf M o = s then 0 else 1)) 5 := by
    by_cases hz : σc.val rS = 0
    · have e : σc.setv rX (if repOf M o = s then 0 else 1) = σc := by
        have : σc.val rX = if repOf M o = s then 0 else 1 := by
          rw [hcX]; rw [hcS] at hz; split_ifs <;> omega
        rw [← this]; exact setv_same σc rX
      rw [e]
      exact RExec.mono (RExec.ifrF hz (RExec.skip σc)) (by omega)
    · have e : (if repOf M o = s then 0 else 1) = 1 := by rw [hcS] at hz; split_ifs <;> omega
      rw [e]
      exact RExec.mono (RExec.ifrT hz (setF_spec inp cap rX σc (by rw [hcX]; split_ifs <;> omega) (by omega)))
        (by omega)
  -- 4. the indicator into `C`
  have hcC : σc.val rC = 0 := by rw [hσc, hσb, hσa]; simp [hC]
  have f4 : RExec inp cap outputI (σc.setv rX (if repOf M o = s then 0 else 1))
      (((σc.setv rX (if repOf M o = s then 0 else 1)).setc false).setv rC (if repOf M o = s then 1 else 0)) 6 := by
    unfold outputI
    have h1 := RExec.setc (inp := inp) (cap := cap) false (σc.setv rX (if repOf M o = s then 0 else 1))
    by_cases he : repOf M o = s
    · have h2 := RExec.inc (inp := inp) (cap := cap) rC ((σc.setv rX (if repOf M o = s then 0 else 1)).setc false)
        (by simp [hcC]; omega)
      have h2' := RExec.ifrF (r := rX) (P := RM.skip) (by simp [he]) h2
      refine RExec.cast inp cap (RExec.seq h1 h2') ?_ (by omega)
      simp [hcC, he]
    · have h2 := RExec.skip (inp := inp) (cap := cap) ((σc.setv rX (if repOf M o = s then 0 else 1)).setc false)
      have h2' := RExec.ifrT (r := rX) (Q := RM.inc rC) (by simp [he]) h2
      refine RExec.cast inp cap (RExec.seq h1 h2') ?_ (by omega)
      rw [if_neg he]
      rs_eq [hcC]
  obtain ⟨σd, hσd⟩ : ∃ τ : LState, τ = ((σc.setv rX (if repOf M o = s then 0 else 1)).setc false).setv rC
      (if repOf M o = s then 1 else 0) := ⟨_, rfl⟩
  rw [← hσd] at f4
  -- 5. cleanup
  have hdS : σd.val rS = repOf M o - s := by rw [hσd]; simp [hcS]
  have hdX : σd.val rX ≤ 1 := by rw [hσd]; simp; split_ifs <;> omega
  have hdF : σd.val rF ≤ 1 := by rw [hσd, hσc, hσb, hσa]; simp; split_ifs <;> omega
  have hdP : σd.val rP = cp := by rw [hσd, hσc, hσb, hσa]; simp [hP]
  have hdM : σd.val rMR = M := by rw [hσd, hσc, hσb, hσa]; simp [hMR]
  have hdSP : σd.val rSP = s := by rw [hσd, hσc, hσb, hσa]; simp [hSP]
  have hdTP : σd.val rTP = σ.sh 1 := by rw [hσd, hσc, hσb, hσa]; simp [hTP]
  have g1 := clear_spec inp cap rS (σd.val rS) σd rfl (by rw [hdS]; omega)
  have g2 := clear_spec inp cap rX (σd.val rX) (σd.setv rS 0) (by simp) (by simp; omega)
  have g3 := clear_spec inp cap rF (σd.val rF) ((σd.setv rS 0).setv rX 0) (by simp) (by simp; omega)
  have g4 := clear_spec inp cap rP cp (((σd.setv rS 0).setv rX 0).setv rF 0) (by simp [hdP]) (by simp [hdP]; omega)
  have g5 := clear_spec inp cap rMR M ((((σd.setv rS 0).setv rX 0).setv rF 0).setv rP 0) (by simp [hdM])
    (by simp [hdM]; omega)
  have g6 := rewind_spec inp cap 2 rSP s (((((σd.setv rS 0).setv rX 0).setv rF 0).setv rP 0).setv rMR 0)
    (by simp [hdSP]) (by simp [hdSP]; omega)
  have g7 := rewind_spec inp cap 1 rTP (σ.sh 1) ((((((σd.setv rS 0).setv rX 0).setv rF 0).setv rP 0).setv rMR 0).setv
    rSP 0 |>.seth 2 ((((((σd.setv rS 0).setv rX 0).setv rF 0).setv rP 0).setv rMR 0).sh 2 - s)) (by simp [hdTP])
    (by simp [hdTP]; omega)
  refine RExec.cast inp cap (RExec.seq f1 (RExec.seq f2 (RExec.seq (RExec.seq f3a f3b) (RExec.seq f4
    (RExec.seq g1 (RExec.seq g2 (RExec.seq g3 (RExec.seq g4 (RExec.seq g5 (RExec.seq g6 g7)))))))))) ?_ ?_
  · rw [hσd, hσc, hσb, hσa]
    rs_eq [blankI, hs0, hs2, hTP, hC, hW, hV, hU, hT, hR, hSP, hX, hT1, hT2]
  · unfold finalCost
    rw [hdS]
    omega

theorem mainI_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) (b : Bool)
    (hrows : ∀ j ≤ J, (row j).length = Z.length) (hs : s ≤ M) :
    RExec (streams M J W row Z s) (capOf M J W row Z.length) mainI (blank b)
      (blankI (if reportRef M J W row Z = s then 1 else 0)) (mainCost (capOf M J W row Z.length)) := by
  generalize hcapv : capOf M J W row Z.length = cap
  have hcapB : cap = 4 * (wordLen M J W row + Z.length + 1) := by rw [← hcapv]; rfl
  have hM1 := word_M_le M J W row
  have hJ1 := word_levels_le M J W row
  have hword : levelWord M J W row = List.replicate M true ++ false :: ((levels J).flatMap (record J W row) ++ [false]) :=
    by simp [levelWord, unary]
  have hd0 : (streams M J W row Z s 1).drop ((blank b).sh 1) =
      List.replicate M true ++ false :: ((levels J).flatMap (record J W row) ++ [false]) := by
    rw [streams_one, hword]; rfl
  obtain ⟨ho, he⟩ := ones_of_drop hd0
  have r1 := readU_spec (streams M J W row Z s) cap 1 rTP rMR (by decide) M (blank b) ho he (by simp [blank]; omega)
    (by simp [blank]; omega)
  obtain ⟨σ1, hσ1⟩ : ∃ τ : LState, τ = (((blank b).seth 1 ((blank b).sh 1 + M + 1)).setv rTP
      ((blank b).val rTP + M + 1)).setv rMR ((blank b).val rMR + M) := ⟨_, rfl⟩
  rw [← hσ1] at r1
  have hinv1 : Inv M J W row Z (levels J) (some 0, 0) σ1 := by
    rw [hσ1]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have key : (levelWord M J W row).drop (0 + (List.replicate M true ++ [false]).length) =
          (levels J).flatMap (record J W row) ++ [false] :=
        drop_add_of_append (by rw [List.drop_zero, hword]; simp)
      simp only [List.length_append, List.length_replicate, List.length_singleton, Nat.zero_add] at key
      simpa [blank] using key
    all_goals simp [blank]
  have r2 := loop_spec M J W row Z s (levels J) (some 0, 0) σ1
    (fun j hj => hrows j (by simp [levels] at hj; omega)) hinv1
  rw [hcapv] at r2
  obtain ⟨σ2, r2, hinv2⟩ := r2
  have r3 := finalPartI_spec M J W row Z s _ σ2 hinv2 hs
  rw [hcapv] at r3
  rw [reportRef_eq_rep]
  refine RExec.mono (RExec.seq r1 (RExec.seq r2 r3)) ?_
  unfold finalCost mainCost bodyCost
  rw [levels_length]
  have hcc : (J + 1) * (40 * (cap + 1) * (cap + 1) + 2) ≤ cap * (40 * (cap + 1) * (cap + 1) + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have hc8 : 8 ≤ cap := by omega
  have hMc : M ≤ cap := by omega
  have hsq : 8 * cap ≤ cap * cap := Nat.mul_le_mul_right _ hc8
  have hcube : 0 ≤ cap * cap * cap := Nat.zero_le _
  linarith [hcc, hc8, hMc, hsq, hcube]

end NearCubicWires.WireExponent3_5.FinalPass.ListEval
