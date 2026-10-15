import Proof.Gates.WorkerArith.TermDefs

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
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord ratWord NCircuit)

variable {ns nr : ℕ}

theorem R_ne (E : TermEnv ns nr) {a b : Fin 40} (h : a ≠ b) : E.R a ≠ E.R b := fun e => h (E.R.injective e)

theorem rwC_apply (R : Fin 40 ↪ Fin nr) (k : Fin 16) : rwC R k = R (cIdx k) := rfl
theorem rwS_apply (R : Fin 40 ↪ Fin nr) (k : Fin 16) : rwS R k = R (sIdx k) := rfl
theorem qS_apply (R : Fin 40 ↪ Fin nr) (k : Fin 12) : qS R k = R (qIdx k) := rfl
theorem gT_apply (R : Fin 40 ↪ Fin nr) (k : Fin 8) : gT R k = R (gIdx k) := rfl
theorem pT_apply (R : Fin 40 ↪ Fin nr) (f : Fin 40) (hf : f = 0 ∨ f = 39) (k : Fin 8) : pT R f hf k = R (pIdx f k) :=
  rfl

theorem seth_self (σ : WState ns nr) (i : Fin (ns + 1)) (v : ℕ) (h : σ.sh i = v) : σ.seth i v = σ := by
  subst h; cases σ; simp [WState.seth]

theorem setv_self (σ : WState ns nr) (r : Fin nr) (v : ℕ) (h : σ.val r = v) : σ.setv r v = σ := by
  subst h; cases σ; simp [WState.setv]

/-! ## Recognizing the ideal end state -/

open Classical in
theorem termIdeal_simW {t : ℕ} (σ ρ : WState ns nr) (tmap : Fin t → Fin (ns + 1)) (E : TermEnv ns nr) (hW : ℕ)
    (entry : List Bool)
    (hVsp : ¬ ((∃ j, tmap j = E.VI) ∨ E.VI = E.TL ∨ E.VI = E.G ∨ E.VI = E.S1 ∨ E.VI = E.S2)) (hVW : E.VI ≠ E.WT)
    (hsh : ∀ i, i ≠ E.VI → ρ.sh i = if (∃ j, tmap j = i) ∨ i = E.TL ∨ i = E.G ∨ i = E.S1 ∨ i = E.S2 then 0 else
        if i = E.WT then hW else σ.sh i)
    (hshV : ρ.sh E.VI = σ.sh E.VI + (marks entry).length)
    (hst : ∀ i, i ≠ E.VI → ¬ ((∃ j, tmap j = i) ∨ i = E.TL ∨ i = E.G ∨ i = E.S1 ∨ i = E.S2) → ρ.st i = σ.st i)
    (hstB : ∀ i, ((∃ j, tmap j = i) ∨ i = E.TL ∨ i = E.G ∨ i = E.S1 ∨ i = E.S2) → Worker.Blank (ρ.st i))
    (hstV : ρ.st E.VI = σ.st E.VI ++ marks entry)
    (hval : ρ.val = Function.update σ.val (E.R 9) (σ.val (E.R 9) + (marks entry).length))
    (hcell : ρ.cell = σ.cell) : SimW (termIdeal σ tmap E hW entry) ρ := by
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · funext i
    simp only [termIdeal, appendO, WState.setv, WState.seth, WState.sets]
    by_cases hi : i = E.VI
    · subst hi; rw [Function.update_self, if_neg hVsp, if_neg hVW, hshV]
    · rw [Function.update_of_ne hi]; exact hsh i hi
  · simp only [termIdeal, appendO, WState.setv, WState.seth, WState.sets]; exact hval
  · simp only [termIdeal, appendO, WState.setv, WState.seth, WState.sets]; exact hcell
  · simp only [termIdeal, appendO, WState.setv, WState.seth, WState.sets]
    by_cases hi : i = E.VI
    · subst hi; rw [Function.update_self, if_neg hVsp, hstV]; exact RdEq.refl _
    · rw [Function.update_of_ne hi]
      by_cases hs : (∃ j, tmap j = i) ∨ i = E.TL ∨ i = E.G ∨ i = E.S1 ∨ i = E.S2
      · rw [if_pos hs]; exact (blank_nil (hstB i hs)).symm
      · rw [if_neg hs, hst i hi hs]; exact RdEq.refl _

/-! ## Consuming one witness field -/

theorem skipField_ideal (cap : ℕ) (E : TermEnv ns nr) (w pre rest : List Bool) (σ : WState ns nr)
    (h2G : E.S2 ≠ E.G) (hW2 : E.WT ≠ E.S2) (hWG : E.WT ≠ E.G)
    (hb2 : Worker.Blank (σ.st E.S2)) (h2 : σ.sh E.S2 = 0) (hbG : Worker.Blank (σ.st E.G)) (hG : σ.sh E.G = 0)
    (hwt : σ.st E.WT = pre ++ (Worker.Format.countWord w.length ++ w) ++ rest) (hwth : σ.sh E.WT = pre.length)
    (hz : ∀ i : Fin 40, 26 ≤ i.val → i.val ≤ 31 → σ.val (E.R i) = 0) (hc : 2 * w.length + 2 ≤ cap) :
    ∃ τ, WXExec cap (skipFieldW E) σ τ (300 * (w.length + 1)) ∧
      SimW (((σ.seth E.WT (pre.length + w.length + 1 + w.length)).sets E.S2 []).sets E.G []) τ := by
  have hfw := frame_len' w
  set σ0 := σ.sets E.S2 [] with hσ0
  have f1 := Codec.fieldFrameW_spec cap E.WT E.S2 hW2 (E.R 26) (E.R 27) (R_ne E (by decide)) pre w rest σ0
    (by simp [hσ0, Function.update_of_ne hW2, hwt]) (by simp [hσ0, hwth]) (by simp [hσ0, h2])
    (by simp [hσ0]; exact hz 27 (by decide) (by decide)) (by simp [hσ0]; rw [hz 26 (by decide) (by decide)]; omega)
    (by omega)
  set σ1 := appendO (σ0.seth E.WT (pre.length + w.length + 1 + w.length)) E.S2 (E.R 26) (frame w) with hσ1
  have v1 : σ1.val (E.R 26) = (frame w).length := by
    simp [hσ1, appendO, hσ0, hz 26 (by decide) (by decide)]
  have f2 := wrewind_spec (cap := cap) E.S2 (E.R 26) (frame w).length σ1 v1 (by rw [v1, hfw]; omega)
  set σ2 := (σ1.setv (E.R 26) 0).seth E.S2 (σ1.sh E.S2 - (frame w).length) with hσ2
  obtain ⟨τ, e3, s3⟩ := clearFrame_ideal cap E.S2 E.G (E.R 28) (E.R 29) (E.R 30) (E.R 31) w σ2 h2G
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
        exact ⟨⟨R_ne E (by decide), R_ne E (by decide), R_ne E (by decide)⟩, ⟨R_ne E (by decide), R_ne E (by decide)⟩,
          R_ne E (by decide), fun h => h⟩)
    (by simp [hσ2, hσ1, appendO, hσ0])
    (by simp [hσ2, hσ1, appendO, hσ0, Function.update_of_ne (Ne.symm hW2), h2])
    (by simp [hσ2, hσ1, appendO, hσ0, Function.update_of_ne (Ne.symm h2G)]; exact hbG)
    (by simp [hσ2, hσ1, appendO, hσ0, Function.update_of_ne (Ne.symm h2G), Function.update_of_ne (Ne.symm hWG), hG])
    (by simp [hσ2, hσ1, appendO, hσ0, Function.update_of_ne (R_ne E (show (28 : Fin 40) ≠ 26 by decide))]
        exact hz 28 (by decide) (by decide))
    (by simp [hσ2, hσ1, appendO, hσ0, Function.update_of_ne (R_ne E (show (29 : Fin 40) ≠ 26 by decide))]
        exact hz 29 (by decide) (by decide))
    (by simp [hσ2, hσ1, appendO, hσ0, Function.update_of_ne (R_ne E (show (30 : Fin 40) ≠ 26 by decide))]
        exact hz 30 (by decide) (by decide))
    (by simp [hσ2, hσ1, appendO, hσ0, Function.update_of_ne (R_ne E (show (31 : Fin 40) ≠ 26 by decide))]
        exact hz 31 (by decide) (by decide))
    (by omega)
  have e : WXExec cap (skipFieldW E) σ0 τ (300 * (w.length + 1)) :=
    WXExec.mono (WXExec.seq (WXExec.wm (WExec.seq f1 f2)) e3) (by rw [hfw]; omega)
  have hs0 : SimW σ0 σ := CheckedPCPP.SimW.symm (Worker.simW_sets σ E.S2 [] (blank_nil hb2))
  obtain ⟨τ', e', s'⟩ := wxexec_sim e σ hs0
  refine ⟨τ', e', CheckedPCPP.SimW.trans ?_ (CheckedPCPP.SimW.trans s3 s')⟩
  have hv : ∀ r, (σ2.val r) = σ.val r := fun r => by
    by_cases hr : r = E.R 26
    · subst hr; simp [hσ2, hz 26 (by decide) (by decide)]
    · simp [hσ2, Function.update_of_ne hr, hσ1, appendO, hσ0]
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · funext i
    simp only [WState.sets]
    by_cases hi : i = E.S2
    · subst hi
      simp [hσ2, hσ1, appendO, hσ0, Function.update_of_ne (Ne.symm hW2), h2]
    · simp [hσ2, Function.update_of_ne hi, hσ1, appendO, hσ0]
  · funext r; simp only [WState.sets]; rw [hv r]; rfl
  · simp [hσ2, hσ1, appendO, hσ0]
  · simp only [WState.sets]
    by_cases hG' : i = E.G
    · subst hG'; simp; exact RdEq.refl _
    · by_cases hi : i = E.S2
      · subst hi; simp [Function.update_of_ne h2G]; exact RdEq.refl _
      · simp [Function.update_of_ne hG', Function.update_of_ne hi, hσ2, hσ1, appendO, hσ0]; exact RdEq.refl _

end NearCubicGates.Close.WorkerArith
