import Proof.Gates.WorkerArith.TermG

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
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord ratWord NCircuit circuitWord listWord)
open NearCubicGates.Close.Codec (oneCallOf pairCallOf cwPrefix rowPrefix emptyCW)
open NearCubicGates.Close.Worker (Opd model1 model2)

variable {ns nr : ℕ}

theorem decide_toNat_ne (b : Bool) : decide (b.toNat ≠ 0) = b := by cases b <;> rfl

section Sys
variable {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ}
  {rows : ℕ → List ℕ} {Rn : ℕ} {ω : ℚ} {w pre rest : List Bool} {Z B V : ℕ} {σ : WState ns nr}

/-- The witness field skipped, in ideal form, from a term base. -/
theorem skipField_base (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ)
    (hFit : TermFit cap Cs N rows Rn ω w Z B V) :
    ∃ τ, WXExec cap (skipFieldW E) σ τ (300 * (w.length + 1)) ∧
      SimW (((σ.seth E.WT (pre.length + w.length + 1 + w.length)).sets E.S2 []).sets E.G []) τ := by
  obtain ⟨-, -, -, ⟨h2T, h2G, h2L, h2V, h2W⟩, -, ⟨hGL, hGV, hGW⟩, -, -⟩ := hB.dis
  have := hFit.wZ; have := hFit.capV; have := hFit.VZ
  exact skipField_ideal cap E w pre rest σ h2G (Ne.symm h2W) (Ne.symm hGW) hB.b2 hB.h2 hB.bG hB.hG hB.wt hB.wth
    (fun i a b => hB.z i (by omega) (by omega)) (by omega)

/-- The skipped-field state's values and the record. -/
theorem skip_facts (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hW : ℕ) :
    let ι := ((σ.seth E.WT hW).sets E.S2 []).sets E.G []
    ι.val = σ.val ∧ ι.st E.SUP = σ.st E.SUP ∧ ι.sh E.SUP = σ.sh E.SUP ∧ ι.sh E.VI = σ.sh E.VI ∧
      ι.st E.VI = σ.st E.VI ∧ ι.cell = σ.cell := by
  obtain ⟨-, ⟨s1, s2, sT, sG, sL, sV, sW⟩, -, ⟨h2T, h2G, h2L, h2V, h2W⟩, -, ⟨hGL, hGV, hGW⟩, -, hVW⟩ := hB.dis
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl⟩
  · simp [Function.update_of_ne sG, Function.update_of_ne s2]
  · simp [Function.update_of_ne sW]
  · simp [Function.update_of_ne hVW]
  · simp [Function.update_of_ne (Ne.symm hGV), Function.update_of_ne (Ne.symm h2V)]

/-- **The one-operand systematic term** (exact). -/
theorem sys1_ideal (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ)
    (hFit : TermFit cap Cs N rows Rn ω w Z B V) (hu : σ.val (E.R 2) < q + Rn) (huZ : σ.val (E.R 2) ≤ Z)
    (h8 : σ.val (E.R 8) ≤ Z) (hOP : σ.val (E.R 9) + 1000 * (Z + 1) ≤ cap) :
    ∃ τ, WXExec cap (.seq (skipFieldW E) (.seq (.wm (sysFlagW E (E.R 2)))
        (.seq (exactEntryW E.VI (E.R 9) (E.R 0) (E.R 37)) (.wm (WM.clear (E.R 37)))))) σ τ
        (1000000 * (Z + 1) ^ 2 * (B + 1)) ∧
      SimW (termIdeal σ tmap E (pre.length + w.length + 1 + w.length)
        (bitWord (decide (σ.val (E.R 0) ≠ 0)) ++
          outputWord (halfIf (decide (sysList q rows (σ.val (E.R 2)) ≠ [])), 0))) τ := by
  set hW := pre.length + w.length + 1 + w.length with hWd
  obtain ⟨τ1, e1, s1⟩ := skipField_base cap hB hFit
  set ι1 := ((σ.seth E.WT hW).sets E.S2 []).sets E.G [] with hι1
  obtain ⟨fv, fsup, fsuph, fvih, fvis, -⟩ := skip_facts hB hW (E := E)
  obtain ⟨restS, hrs⟩ := hB.sup
  have hcV := hFit.capV
  have hqZ := hFit.qZ
  set u := σ.val (E.R 2) with hud
  set f := (decide (sysList q rows u ≠ [])).toNat with hf
  have e2 := sysFlagW_spec cap E 2 (Or.inl rfl) rows Rn B restS ι1 (by rw [fsup, hrs]) (by rw [fsuph, hB.suph])
    (by rw [fv]; exact hB.supL) (by rw [fv, hB.hq]) (fun i a b => by rw [fv]; exact hB.z i a b) (by rw [fv]; exact hu)
    hFit.rowB hFit.rowfit (by rw [fv]; omega)
  rw [fv] at e2
  have e3 := exactEntryW_spec cap E.VI (E.R 9) (E.R 0) (E.R 37) (R_ne E (by decide)) (ι1.setv (E.R 37) f)
    (by simp only [WState.setv]; rw [fvih, fvis]; exact hB.vi)
    (by rw [WState.setv_val, Function.update_of_ne (R_ne E (show (9 : Fin 40) ≠ 37 by decide)), fv]; omega)
  have hv0 : (ι1.setv (E.R 37) f).val (E.R 0) = σ.val (E.R 0) := by
    rw [WState.setv_val, Function.update_of_ne (R_ne E (show (0 : Fin 40) ≠ 37 by decide)), fv]
  have hv37 : (ι1.setv (E.R 37) f).val (E.R 37) = f := by simp
  rw [hv0, hv37, hf, decide_toNat_ne] at e3
  set m := marks (bitWord (decide (σ.val (E.R 0) ≠ 0)) ++
    outputWord (halfIf (decide (sysList q rows u ≠ [])), 0)) with hm
  have e4 := wclear_spec (cap := cap) (E.R 37) f (appendO (ι1.setv (E.R 37) f) E.VI (E.R 9) m)
    (by simp [Function.update_of_ne (R_ne E (show (37 : Fin 40) ≠ 9 by decide))])
    (by simp [Function.update_of_ne (R_ne E (show (37 : Fin 40) ≠ 9 by decide))]; rw [hf]; cases decide (sysList q rows u ≠ []) <;> simp <;> omega)
  have hend : (appendO (ι1.setv (E.R 37) f) E.VI (E.R 9) m).setv (E.R 37) 0 = exactEnd E σ hW
      (bitWord (decide (σ.val (E.R 0) ≠ 0)) ++ outputWord (halfIf (decide (sysList q rows u ≠ [])), 0)) := by
    refine WState.eq rfl rfl ?_ rfl
    funext r
    simp only [exactEnd, appendO, WState.setv_val, WState.seth_val, WState.sets_val, ← hm]
    by_cases r37 : r = E.R 37
    · subst r37
      rw [Function.update_self, Function.update_of_ne (R_ne E (by decide))]
      exact (hB.z 37 (by decide) (by decide)).symm
    rw [Function.update_of_ne r37]
    by_cases r9 : r = E.R 9
    · subst r9; rw [Function.update_self, Function.update_self, Function.update_of_ne (R_ne E (by decide))]
      rw [hι1]; rfl
    rw [Function.update_of_ne r9, Function.update_of_ne r9, Function.update_of_ne r37]; rw [hι1]; rfl
  rw [hend] at e4
  obtain ⟨τ, e, s⟩ := Worker.seq_sim e1 s1 ⟨_, WXExec.seq (WXExec.wm e2) (WXExec.seq e3 (WXExec.wm e4)), SimW.refl _⟩
  refine ⟨τ, WXExec.mono e ?_, CheckedPCPP.SimW.trans (exactEnd_simW hB hW _) s⟩
  have hf1 : f ≤ 1 := by rw [hf]; cases decide (sysList q rows u ≠ []) <;> simp
  have hwZ := hFit.wZ
  unfold sysFlagCost
  have h1 : (u + 1) * (B + 30) ≤ 30 * ((Z + 1) ^ 2 * (B + 1)) := by
    have a : u + 1 ≤ (Z + 1) ^ 2 := by nlinarith
    have b : B + 30 ≤ 30 * (B + 1) := by omega
    calc (u + 1) * (B + 30) ≤ (Z + 1) ^ 2 * (30 * (B + 1)) := Nat.mul_le_mul a b
      _ = 30 * ((Z + 1) ^ 2 * (B + 1)) := by ring
  have h2 : Z + 1 ≤ (Z + 1) ^ 2 * (B + 1) := by nlinarith
  have eq : 1000000 * (Z + 1) ^ 2 * (B + 1) = 1000000 * ((Z + 1) ^ 2 * (B + 1)) := by ring
  rw [eq]
  try rw [← hud]
  omega

end Sys

theorem termW1_ideal {B1 B2 : ℕ} (ctr : Counter B1 B2) (E : TermEnv ns nr)
    (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1)) {q : ℕ} (Cs : ℕ → NCircuit q) (N : ℕ)
    (rows : ℕ → List ℕ) (Rn : ℕ) (ω : ℚ) (w pre rest : List Bool) (cap Z B V : ℕ) (σ : WState ns nr) :
    TermW1Ideal ctr E tmap Cs N rows Rn ω w pre rest cap Z B V σ := by
  intro hP hFit hsys haux h7 h8 hiZ hcap
  have hB := hP.toTermBase
  have hcV := hFit.capV
  have hVZ := hFit.VZ
  have hwZ := hFit.wZ
  by_cases hY : σ.val (E.R 1) = 0
  · -- a circuit operand: one single call
    have hj := haux hY
    set j := σ.val (E.R 2) with hjd
    have ew := oneAux_exec cap hB hFit 2 (Or.inl rfl) hj hiZ h7
    have hcl := callWord_one_le Cs j [] ω Z hFit.qZ (hFit.cwZ j hj) (by rw [listWord_nil_len]; omega) hFit.ωZ
    have hfl : (frame (callWord (oneCallOf Cs j [] ω))).length ≤ 30 * Z + 100 := by rw [frame_len']; omega
    have hF := finPre_of hB (oneCallOf Cs j [] ω) Z j 0 (cwPrefix Cs (j + 1)).length 0
      ((Codec.cwPrefix_length_mono Cs (show j + 1 ≤ N by omega)).trans hB.cwL) (by omega) hiZ (by omega)
    have hbud : bud1 ctr Cs ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) = ctr.budget (oneCallOf Cs j [] ω) w := by
      simp [bud1, opdAt, hY, hjd]
    rw [hbud] at hcap ⊢
    obtain ⟨τ, e, s⟩ := callBranch_ideal ctr E tmap 0 (Or.inl rfl) cap Z _ (oneAuxW E (E.R 2) ω) (writerCost Z B) hB ew hF
      h7 h8 (by omega) (by omega)
    refine ⟨τ, WXExec.mono (WXExec.ifrF hY e) ?_, ?_⟩
    · have := call_cost_le ctr.program.program.tapeCount Z B (callWord (oneCallOf Cs j [] ω)).length w.length
        (ctr.budget (oneCallOf Cs j [] ω) w) (frame (callWord (oneCallOf Cs j [] ω))).length hcl hwZ hfl
      omega
    · have hm : entryWord (model1 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2))) =
          bitWord (decide (σ.val (E.R 0) ≠ 0)) ++ outputWord (ctr.value (oneCallOf Cs j [] ω) w) := by
        simp [entryWord, model1, opdAt, hY, hjd]
      rw [hm]; exact s
  · -- a systematic operand: exact
    have hbud : bud1 ctr Cs ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) = 0 := by simp [bud1, opdAt, hY]
    rw [hbud] at hcap ⊢
    obtain ⟨τ, e, s⟩ := sys1_ideal cap hB hFit (hsys hY) hiZ h8 ((Nat.le_add_right _ _).trans hcap)
    refine ⟨τ, WXExec.mono (WXExec.ifrT hY e) ?_, ?_⟩
    · exact exact_cost_le _ Z B (1000000 * (Z + 1) ^ 2 * (B + 1) + 1) (by
        have : 1 ≤ (Z + 1) ^ 2 * (B + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have eq : 1000000 * (Z + 1) ^ 2 * (B + 1) = 1000000 * ((Z + 1) ^ 2 * (B + 1)) := by ring
        have eq2 : 2000000 * (Z + 1) ^ 2 * (B + 1) = 2000000 * ((Z + 1) ^ 2 * (B + 1)) := by ring
        omega)
    · have hm : entryWord (model1 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2))) =
          bitWord (decide (σ.val (E.R 0) ≠ 0)) ++
            outputWord (halfIf (decide (sysList q rows (σ.val (E.R 2)) ≠ [])), 0) := by
        simp [entryWord, model1, opdAt, hY]
      rw [hm]; exact s

end NearCubicGates.Close.WorkerArith
