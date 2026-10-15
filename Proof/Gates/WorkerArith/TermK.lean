import Proof.Gates.WorkerArith.TermJ

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

theorem termIdeal_setv39 {t : ℕ} (σ : WState ns nr) (tmap : Fin t → Fin (ns + 1)) (E : TermEnv ns nr) (hW : ℕ)
    (entry : List Bool) (x : ℕ) (h39 : σ.val (E.R 39) = 0) :
    (termIdeal (σ.setv (E.R 39) x) tmap E hW entry).setv (E.R 39) 0 = termIdeal σ tmap E hW entry := by
  refine WState.eq rfl rfl ?_ rfl
  funext r
  simp only [termIdeal, appendO, WState.setv, WState.seth, WState.sets]
  by_cases r39 : r = E.R 39
  · subst r39; rw [Function.update_self, Function.update_of_ne (R_ne E (by decide)), h39]
  rw [Function.update_of_ne r39]
  by_cases r9 : r = E.R 9
  · subst r9; rw [Function.update_self, Function.update_self, Function.update_of_ne (R_ne E (by decide))]
  rw [Function.update_of_ne r9, Function.update_of_ne r9, Function.update_of_ne r39]

theorem termW2_ideal {B1 B2 : ℕ} (ctr : Counter B1 B2) (E : TermEnv ns nr)
    (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1)) {q : ℕ} (Cs : ℕ → NCircuit q) (N : ℕ)
    (rows : ℕ → List ℕ) (Rn : ℕ) (ω : ℚ) (w pre rest : List Bool) (cap Z B V : ℕ) (σ : WState ns nr) :
    TermW2Ideal ctr E tmap Cs N rows Rn ω w pre rest cap Z B V σ := by
  intro hP hFit hs1 ha1 hs2 ha2 h7 h8 hiZ hjZ hcap
  have hB := hP.toTermBase
  have hcV := hFit.capV
  set hW := pre.length + w.length + 1 + w.length with hWd
  set x := (xor (decide (σ.val (E.R 0) ≠ 0)) (decide (σ.val (E.R 3) ≠ 0))).toNat with hxd
  have hx1 : x ≤ 1 := by rw [hxd]; cases xor (decide (σ.val (E.R 0) ≠ 0)) (decide (σ.val (E.R 3) ≠ 0)) <;> simp
  have ex := xorW_spec cap (E.R 0) (E.R 3) (E.R 39) σ hP.z39 (by omega)
  set σx := σ.setv (E.R 39) x with hσx
  have hBx := hB.set39 x
  have vx : ∀ k : Fin 40, k ≠ 39 → σx.val (E.R k) = σ.val (E.R k) := fun k hk => by
    simp [hσx, Function.update_of_ne (R_ne E hk)]
  have v39 : decide (σx.val (E.R 39) ≠ 0) = xor (decide (σ.val (E.R 0) ≠ 0)) (decide (σ.val (E.R 3) ≠ 0)) := by
    simp only [hσx, WState.setv_val, Function.update_self, hxd, decide_toNat_ne]
  -- the branch, in ideal form from `σx`
  have hbr : ∃ τb c, WXExec cap (.ifr (E.R 1)
      (.ifr (E.R 4)
        (.seq (skipFieldW E) (.seq (.wm (suppEqW E.SUP E.S1 E.S2 (rwS E.R) (qS E.R)))
          (.seq (exactEntryNW E.VI (E.R 9) (E.R 39) (E.R 26)) (.wm (WM.clear (E.R 26))))))
        (.seq (.wm (sysAuxW E (E.R 2) (E.R 5) ω)) (callFinW E ctr tmap 39 (Or.inr rfl))))
      (.ifr (E.R 4)
        (.seq (.wm (sysAuxW E (E.R 5) (E.R 2) ω)) (callFinW E ctr tmap 39 (Or.inr rfl)))
        (.seq (.wm (Worker.ltSubW (E.R 2) (E.R 5) (E.R 34) (E.R 35) (E.R 36) (E.R 38)))
          (.ifr (E.R 34)
            (.seq (.wm (.seq (WM.clear (E.R 34)) (WM.clear (E.R 35))))
              (.seq (.wm (pairW E ω)) (callFinW E ctr tmap 39 (Or.inr rfl))))
            (.ifr (E.R 35)
              (.seq (.wm (.seq (WM.clear (E.R 34)) (WM.clear (E.R 35))))
                (.seq (.wm (pairW E ω)) (callFinW E ctr tmap 39 (Or.inr rfl))))
              (.seq (skipFieldW E) (exactEntryW E.VI (E.R 9) (E.R 39) (E.R 37)))))))) σx τb c ∧
      c + 98 ≤ termCost ctr.program.program.tapeCount Z B
        (bud2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5))) ∧
      SimW (termIdeal σx tmap E hW
        (entryWord (model2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5))))) τb := by
    have h1x : σx.val (E.R 1) = σ.val (E.R 1) := vx 1 (by decide)
    have h4x : σx.val (E.R 4) = σ.val (E.R 4) := vx 4 (by decide)
    have h2x : σx.val (E.R 2) = σ.val (E.R 2) := vx 2 (by decide)
    have h5x : σx.val (E.R 5) = σ.val (E.R 5) := vx 5 (by decide)
    have h7x : σx.val (E.R 7) = σ.val (E.R 7) := vx 7 (by decide)
    have h8x : σx.val (E.R 8) = σ.val (E.R 8) := vx 8 (by decide)
    have h9x : σx.val (E.R 9) = σ.val (E.R 9) := vx 9 (by decide)
    by_cases hY1 : σ.val (E.R 1) = 0 <;> by_cases hY4 : σ.val (E.R 4) = 0
    · -- `[aux i, aux j]`
      have hbud : bud2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5)) =
          if σ.val (E.R 2) = σ.val (E.R 5) then 0 else ctr.budget (pairCallOf Cs (σ.val (E.R 2)) (σ.val (E.R 5)) ω) w := by
        simp [bud2, opdAt, hY1, hY4]
      rw [hbud] at hcap ⊢
      obtain ⟨τ, c, e, hc, s⟩ := ff_ideal ctr cap hBx hFit (by rw [h2x]; exact ha1 hY1) (by rw [h5x]; exact ha2 hY4)
        (by rw [h2x]; exact hiZ) (by rw [h5x]; exact hjZ) (by rw [h7x]; exact h7) (by rw [h8x]; exact h8)
        (by rw [h9x, h2x, h5x]; exact hcap)
      rw [h2x, h5x] at hc s
      refine ⟨τ, _, WXExec.ifrF (by rw [h1x]; exact hY1) (WXExec.ifrF (by rw [h4x]; exact hY4) e), by omega, ?_⟩
      have hm : entryWord (model2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5))) =
          bitWord (decide (σx.val (E.R 39) ≠ 0)) ++ outputWord (if σ.val (E.R 2) = σ.val (E.R 5) then ((0 : ℚ), (0 : ℚ))
            else ctr.value (pairCallOf Cs (σ.val (E.R 2)) (σ.val (E.R 5)) ω) w) := by
        rw [v39]; simp [entryWord, model2, opdAt, hY1, hY4]
      rw [hm]; exact s
    · -- `[aux j, sys u]`
      have hbud : bud2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5)) =
          ctr.budget (oneCallOf Cs (σ.val (E.R 2)) (sysList q rows (σ.val (E.R 5))) ω) w := by
        simp [bud2, opdAt, hY1, hY4]
      rw [hbud] at hcap ⊢
      obtain ⟨τ, c, e, hc, s⟩ := sysAuxCall_ideal ctr cap hBx hFit 5 2 (Or.inr ⟨rfl, rfl⟩)
        (by rw [h5x]; exact hs2 hY4) (by rw [h2x]; exact ha1 hY1) (by rw [h5x]; exact hjZ) (by rw [h2x]; exact hiZ)
        (by rw [h7x]; exact h7) (by rw [h8x]; exact h8) (by rw [h9x, h2x, h5x]; exact hcap)
      rw [h2x, h5x] at hc s
      refine ⟨τ, _, WXExec.ifrF (by rw [h1x]; exact hY1) (WXExec.ifrT (by rw [h4x]; exact hY4) e), by omega, ?_⟩
      have hm : entryWord (model2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5))) =
          bitWord (decide (σx.val (E.R 39) ≠ 0)) ++
            outputWord (ctr.value (oneCallOf Cs (σ.val (E.R 2)) (sysList q rows (σ.val (E.R 5))) ω) w) := by
        rw [v39]; simp [entryWord, model2, opdAt, hY1, hY4]
      rw [hm]; exact s
    · -- `[sys u, aux j]`
      have hbud : bud2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5)) =
          ctr.budget (oneCallOf Cs (σ.val (E.R 5)) (sysList q rows (σ.val (E.R 2))) ω) w := by
        simp [bud2, opdAt, hY1, hY4]
      rw [hbud] at hcap ⊢
      obtain ⟨τ, c, e, hc, s⟩ := sysAuxCall_ideal ctr cap hBx hFit 2 5 (Or.inl ⟨rfl, rfl⟩)
        (by rw [h2x]; exact hs1 hY1) (by rw [h5x]; exact ha2 hY4) (by rw [h2x]; exact hiZ) (by rw [h5x]; exact hjZ)
        (by rw [h7x]; exact h7) (by rw [h8x]; exact h8) (by rw [h9x, h2x, h5x]; exact hcap)
      rw [h2x, h5x] at hc s
      refine ⟨τ, _, WXExec.ifrT (by rw [h1x]; exact hY1) (WXExec.ifrF (by rw [h4x]; exact hY4) e), by omega, ?_⟩
      have hm : entryWord (model2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5))) =
          bitWord (decide (σx.val (E.R 39) ≠ 0)) ++
            outputWord (ctr.value (oneCallOf Cs (σ.val (E.R 5)) (sysList q rows (σ.val (E.R 2))) ω) w) := by
        rw [v39]; simp [entryWord, model2, opdAt, hY1, hY4]
      rw [hm]; exact s
    · -- `[sys u, sys v]`
      have hbud : bud2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5)) = 0 := by
        simp [bud2, opdAt, hY1, hY4]
      rw [hbud] at hcap ⊢
      obtain ⟨τ, e, s⟩ := tt_ideal cap hBx hFit (by rw [h2x]; exact hs1 hY1) (by rw [h5x]; exact hs2 hY4)
        (by rw [h2x]; exact hiZ) (by rw [h5x]; exact hjZ) (by rw [h8x]; exact h8)
        (by rw [h9x]; exact (Nat.le_add_right _ _).trans hcap)
      rw [h2x, h5x] at s
      refine ⟨τ, _, WXExec.ifrT (by rw [h1x]; exact hY1) (WXExec.ifrT (by rw [h4x]; exact hY4) e), ?_, ?_⟩
      · refine exact_cost_le _ Z B _ ?_
        have h2 : 1 ≤ (Z + 1) ^ 2 * (B + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have eq : 2000000 * (Z + 1) ^ 2 * (B + 1) = 2000000 * ((Z + 1) ^ 2 * (B + 1)) := by ring
        have eq2 : 1000000 * (Z + 1) ^ 2 * (B + 1) = 1000000 * ((Z + 1) ^ 2 * (B + 1)) := by ring
        rw [eq, eq2]; omega
      · have hm : entryWord (model2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5))) =
            bitWord (decide (σx.val (E.R 39) ≠ 0)) ++
              outputWord (halfIf (decide (sysList q rows (σ.val (E.R 2)) ≠ sysList q rows (σ.val (E.R 5)))), 0) := by
          rw [v39]; simp [entryWord, model2, opdAt, hY1, hY4]
        rw [hm]; exact s
  obtain ⟨τb, c, eb, hc, sb⟩ := hbr
  have ec := wclear_spec (cap := cap) (E.R 39) x (termIdeal σx tmap E hW
      (entryWord (model2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5)))))
    (by simp [termIdeal, appendO, Function.update_of_ne (R_ne E (show (39 : Fin 40) ≠ 9 by decide)), hσx])
    (by simp [termIdeal, appendO, Function.update_of_ne (R_ne E (show (39 : Fin 40) ≠ 9 by decide)), hσx]; omega)
  rw [hσx, termIdeal_setv39 σ tmap E hW _ x hP.z39] at ec
  obtain ⟨τ, e, s⟩ := Worker.seq_sim (WXExec.wm ex) (SimW.refl _) (Worker.seq_sim eb sb ⟨_, WXExec.wm ec, SimW.refl _⟩)
  exact ⟨τ, WXExec.mono e (by omega), s⟩

end NearCubicGates.Close.WorkerArith
