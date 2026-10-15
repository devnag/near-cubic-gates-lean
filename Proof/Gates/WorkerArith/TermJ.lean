import Proof.Gates.WorkerArith.TermI

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

theorem ff_eq_cost (a b wl Z B : ℕ) (ha : a ≤ Z) (hb : b ≤ Z) (hw : wl ≤ Z) :
    18 * a + 3 + 1 + (18 * b + 3 + 1 + (8 * b + 1)) + 1 + (300 * (wl + 1) + 1 + 400 + 1 + 1) + 100 ≤
      2000000 * ((Z + 1) ^ 2 * (B + 1)) := by
  have h2 : Z + 1 ≤ (Z + 1) ^ 2 * (B + 1) := by nlinarith
  omega

section Calls
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) {E : TermEnv ns nr} {tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1)}
  {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ} {rows : ℕ → List ℕ} {Rn : ℕ} {ω : ℚ} {w pre rest : List Bool} {Z B V : ℕ}
  {σ : WState ns nr}

/-- **`[sys u, aux j]` / `[aux j, sys u]`**: one call with the parity list `sysList q rows u`. -/
theorem sysAuxCall_ideal (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ)
    (hFit : TermFit cap Cs N rows Rn ω w Z B V) (xs xa : Fin 40) (hx : (xs = 2 ∧ xa = 5) ∨ (xs = 5 ∧ xa = 2))
    (hu : σ.val (E.R xs) < q + Rn) (hj : σ.val (E.R xa) < N) (huZ : σ.val (E.R xs) ≤ Z) (hjZ : σ.val (E.R xa) ≤ Z)
    (h7 : σ.val (E.R 7) ≤ Z) (h8 : σ.val (E.R 8) ≤ Z)
    (hcap : σ.val (E.R 9) + 1000 * (Z + 1) +
      8 * ctr.budget (oneCallOf Cs (σ.val (E.R xa)) (sysList q rows (σ.val (E.R xs))) ω) w ≤ cap) :
    ∃ τ c, WXExec cap (.seq (.wm (sysAuxW E (E.R xs) (E.R xa) ω)) (callFinW E ctr tmap 39 (Or.inr rfl))) σ τ c ∧
      c + 100 ≤ termCost ctr.program.program.tapeCount Z B
        (ctr.budget (oneCallOf Cs (σ.val (E.R xa)) (sysList q rows (σ.val (E.R xs))) ω) w) ∧
      SimW (termIdeal σ tmap E (pre.length + w.length + 1 + w.length)
        (bitWord (decide (σ.val (E.R 39) ≠ 0)) ++
          outputWord (ctr.value (oneCallOf Cs (σ.val (E.R xa)) (sysList q rows (σ.val (E.R xs))) ω) w))) τ := by
  set u := σ.val (E.R xs) with hud
  set j := σ.val (E.R xa) with hjd
  have hcV := hFit.capV
  have hVZ := hFit.VZ
  have hwZ := hFit.wZ
  obtain ⟨b, hs, ew, hb, hhs⟩ := sysAux_exec cap hB hFit xs xa hx hu hj huZ hjZ h7 h8
  have hps : (listWord natWord (sysList q rows u)).length ≤ 2 * Z + 10 := by
    unfold sysList; split_ifs with h
    · exact listWord_single_le u Z huZ
    · have := hFit.rowZ (u - q) (by omega); omega
  have hcl := callWord_one_le Cs j (sysList q rows u) ω Z hFit.qZ (hFit.cwZ j hj) hps hFit.ωZ
  have hfl : (frame (callWord (oneCallOf Cs j (sysList q rows u) ω))).length ≤ 30 * Z + 100 := by
    rw [frame_len']; omega
  have hF := finPre_of hB (oneCallOf Cs j (sysList q rows u) ω) Z j b (cwPrefix Cs (j + 1)).length hs
    ((Codec.cwPrefix_length_mono Cs (show j + 1 ≤ N by omega)).trans hB.cwL) hhs hjZ hb
  obtain ⟨τ, e, s⟩ := callBranch_ideal ctr E tmap 39 (Or.inr rfl) cap Z _ (sysAuxW E (E.R xs) (E.R xa) ω)
    (writerCost Z B) hB ew hF h7 h8 (by omega) (by omega)
  refine ⟨τ, _, e, ?_, s⟩
  have := call_cost_le ctr.program.program.tapeCount Z B (callWord (oneCallOf Cs j (sysList q rows u) ω)).length
    w.length (ctr.budget (oneCallOf Cs j (sysList q rows u) ω) w)
    (frame (callWord (oneCallOf Cs j (sysList q rows u) ω))).length hcl hwZ hfl
  omega

/-- **`[aux i, aux j]`**: the pair call, or the exact `(0, 0)` when `i = j`. -/
theorem ff_ideal (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ)
    (hFit : TermFit cap Cs N rows Rn ω w Z B V) (hi : σ.val (E.R 2) < N) (hj : σ.val (E.R 5) < N)
    (hiZ : σ.val (E.R 2) ≤ Z) (hjZ : σ.val (E.R 5) ≤ Z) (h7 : σ.val (E.R 7) ≤ Z) (h8 : σ.val (E.R 8) ≤ Z)
    (hcap : σ.val (E.R 9) + 1000 * (Z + 1) + 8 * (if σ.val (E.R 2) = σ.val (E.R 5) then 0 else
      ctr.budget (pairCallOf Cs (σ.val (E.R 2)) (σ.val (E.R 5)) ω) w) ≤ cap) :
    ∃ τ c, WXExec cap (.seq (.wm (Worker.ltSubW (E.R 2) (E.R 5) (E.R 34) (E.R 35) (E.R 36) (E.R 38)))
        (.ifr (E.R 34)
          (.seq (.wm (.seq (WM.clear (E.R 34)) (WM.clear (E.R 35))))
            (.seq (.wm (pairW E ω)) (callFinW E ctr tmap 39 (Or.inr rfl))))
          (.ifr (E.R 35)
            (.seq (.wm (.seq (WM.clear (E.R 34)) (WM.clear (E.R 35))))
              (.seq (.wm (pairW E ω)) (callFinW E ctr tmap 39 (Or.inr rfl))))
            (.seq (skipFieldW E) (exactEntryW E.VI (E.R 9) (E.R 39) (E.R 37)))))) σ τ c ∧
      c + 100 ≤ termCost ctr.program.program.tapeCount Z B (if σ.val (E.R 2) = σ.val (E.R 5) then 0 else
        ctr.budget (pairCallOf Cs (σ.val (E.R 2)) (σ.val (E.R 5)) ω) w) ∧
      SimW (termIdeal σ tmap E (pre.length + w.length + 1 + w.length)
        (bitWord (decide (σ.val (E.R 39) ≠ 0)) ++ outputWord (if σ.val (E.R 2) = σ.val (E.R 5) then ((0 : ℚ), (0 : ℚ))
          else ctr.value (pairCallOf Cs (σ.val (E.R 2)) (σ.val (E.R 5)) ω) w))) τ := by
  set i := σ.val (E.R 2) with hid
  set j := σ.val (E.R 5) with hjd
  have hcV := hFit.capV
  have hVZ := hFit.VZ
  have hwZ := hFit.wZ
  have e0 := Worker.ltSubW_spec (cap := cap) (E.R 2) (E.R 5) (E.R 34) (E.R 35) (E.R 36) (E.R 38)
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
        exact ⟨⟨R_ne E (by decide), R_ne E (by decide), R_ne E (by decide), R_ne E (by decide), R_ne E (by decide)⟩,
          ⟨R_ne E (by decide), R_ne E (by decide), R_ne E (by decide), R_ne E (by decide)⟩,
          ⟨R_ne E (by decide), R_ne E (by decide), R_ne E (by decide)⟩, ⟨R_ne E (by decide), R_ne E (by decide)⟩,
          R_ne E (by decide), fun h => h⟩)
    σ (hB.z 34 (by decide) (by decide)) (hB.z 35 (by decide) (by decide)) (hB.z 36 (by decide) (by decide))
    (hB.z 38 (by decide) (by decide)) (by omega)
  have hback : ((((σ.setv (E.R 34) (i - j)).setv (E.R 35) (j - i)).setv (E.R 34) 0).setv (E.R 35) 0) = σ := by
    refine WState.eq rfl rfl ?_ rfl
    funext r
    by_cases r35 : r = E.R 35
    · subst r35; simp [hB.z 35 (by decide) (by decide)]
    by_cases r34 : r = E.R 34
    · subst r34; simp [Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 35 by decide)), hB.z 34 (by decide) (by decide)]
    simp [Function.update_of_ne r34, Function.update_of_ne r35]
  by_cases hij : i = j
  · -- the exact `(0, 0)`
    have hσ' : (σ.setv (E.R 34) (i - j)).setv (E.R 35) (j - i) = σ := by
      rw [show i - j = 0 by omega, show j - i = 0 by omega, setv_self _ _ _ (hB.z 34 (by decide) (by decide)),
        setv_self _ _ _ (hB.z 35 (by decide) (by decide))]
    rw [hσ'] at e0
    obtain ⟨τ1, e1, s1⟩ := skipField_base cap hB hFit
    obtain ⟨fv, -, -, fvih, fvis, -⟩ := skip_facts hB (pre.length + w.length + 1 + w.length) (E := E)
    have e2 := exactEntryW_spec cap E.VI (E.R 9) (E.R 39) (E.R 37) (R_ne E (by decide))
      (((σ.seth E.WT (pre.length + w.length + 1 + w.length)).sets E.S2 []).sets E.G [])
      (by rw [fvih, fvis]; exact hB.vi) (by rw [fv]; omega)
    rw [fv, hB.z 37 (by decide) (by decide)] at e2
    obtain ⟨τ, e, s⟩ := Worker.seq_sim e1 s1 ⟨_, e2, SimW.refl _⟩
    refine ⟨τ, _, WXExec.seq (WXExec.wm e0) (WXExec.ifrF (by rw [hB.z 34 (by decide) (by decide)])
      (WXExec.ifrF (by rw [hB.z 35 (by decide) (by decide)]) e)), ?_, ?_⟩
    · rw [if_pos hij]
      have := hFit.wZ
      refine exact_cost_le _ Z B _ ?_
      have h2 : Z + 1 ≤ (Z + 1) ^ 2 * (B + 1) := by nlinarith
      have eq : 2000000 * (Z + 1) ^ 2 * (B + 1) = 2000000 * ((Z + 1) ^ 2 * (B + 1)) := by ring
      rw [eq]; exact ff_eq_cost _ _ _ Z B hiZ hjZ hwZ
    · rw [if_pos hij]
      have hh : halfIf (decide ((0 : ℕ) ≠ 0)) = 0 := by simp [halfIf]
      rw [hh] at s
      exact CheckedPCPP.SimW.trans (exactEnd_simW hB _ _) s
  · -- the pair call
    have ew := pair_exec cap hB hFit hi hj hiZ hjZ h7 (ω := ω)
    have hcl := callWord_pair_le Cs i j ω Z hFit.qZ (hFit.cwZ i hi) (hFit.cwZ j hj) hFit.ωZ
    have hfl : (frame (callWord (pairCallOf Cs i j ω))).length ≤ 30 * Z + 100 := by rw [frame_len']; omega
    have hF := finPre_of hB (pairCallOf Cs i j ω) Z i j (cwPrefix Cs (j + 1)).length 0
      ((Codec.cwPrefix_length_mono Cs (show j + 1 ≤ N by omega)).trans hB.cwL) (by omega) hiZ hjZ
    rw [if_neg hij] at hcap ⊢
    rw [if_neg hij]
    obtain ⟨τ, e, s⟩ := callBranch_ideal ctr E tmap 39 (Or.inr rfl) cap Z _ (pairW E ω) (writerCost Z B) hB ew hF
      h7 h8 (by omega) (by omega)
    have c1 := wclear_spec (cap := cap) (E.R 34) (i - j) ((σ.setv (E.R 34) (i - j)).setv (E.R 35) (j - i))
      (by simp [Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 35 by decide))])
      (by simp [Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 35 by decide))]; omega)
    have c2 := wclear_spec (cap := cap) (E.R 35) (j - i) (((σ.setv (E.R 34) (i - j)).setv (E.R 35) (j - i)).setv (E.R 34) 0)
      (by simp [Function.update_of_ne (R_ne E (show (35 : Fin 40) ≠ 34 by decide))])
      (by simp [Function.update_of_ne (R_ne E (show (35 : Fin 40) ≠ 34 by decide))]; omega)
    rw [hback] at c2
    have ec := WXExec.seq (WXExec.wm (WExec.seq c1 c2)) e
    have hcost := call_cost_le ctr.program.program.tapeCount Z B (callWord (pairCallOf Cs i j ω)).length w.length
      (ctr.budget (pairCallOf Cs i j ω) w) (frame (callWord (pairCallOf Cs i j ω))).length hcl hwZ hfl
    by_cases hlt : j < i
    · refine ⟨τ, _, WXExec.seq (WXExec.wm e0) (WXExec.ifrT (by simp; omega) ec), ?_, s⟩
      omega
    · refine ⟨τ, _, WXExec.seq (WXExec.wm e0) (WXExec.ifrF (by simp; omega)
        (WXExec.ifrT (by simp [Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 35 by decide))]; omega) ec)), ?_, s⟩
      omega

end Calls

end NearCubicGates.Close.WorkerArith
