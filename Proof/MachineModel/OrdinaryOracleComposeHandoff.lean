import Proof.MachineModel.OrdinaryOracleComposeLayout

/-! The two physical handoffs. A framed copy writes an exact fresh output
through its delimiter. Clearing the shared query uses the executed first
phase's retained unary clock; it does not truncate or replace a tape. -/
namespace NearCubicWires.RepairSource.OrdinaryOracleCompose
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem install_first {t : ℕ} (slot : Fin 3 → Fin t) (hi : Function.Injective slot)
    (ambient : Fin t → List Bool) (out log : List Bool) :
    install slot ambient ![ambient (slot 0), out, log] =
      Function.update (Function.update ambient (slot 1) out) (slot 2) log := by
  classical
  have h01 : slot 0 ≠ slot 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hi h)
  have h02 : slot 0 ≠ slot 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hi h)
  have h12 : slot 1 ≠ slot 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hi h)
  funext i
  by_cases h0 : i = slot 0
  · subst i; simp [install_slot slot hi, h01, h02]
  by_cases h1 : i = slot 1
  · subst i; simp [install_slot slot hi, h12]
  by_cases h2 : i = slot 2
  · subst i; simp [install_slot slot hi]
  rw [install_other slot ambient _ i (by intro j; fin_cases j <;> exact Ne.symm (by assumption))]
  simp [Function.update, h1, h2]

private theorem install_second {t : ℕ} (slot : Fin 3 → Fin t) (hi : Function.Injective slot)
    (ambient : Fin t → List Bool) (out log : List Bool) :
    install slot ambient ![out, ambient (slot 1), log] =
      Function.update (Function.update ambient (slot 0) out) (slot 2) log := by
  classical
  have h01 : slot 0 ≠ slot 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hi h)
  have h02 : slot 0 ≠ slot 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hi h)
  have h12 : slot 1 ≠ slot 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hi h)
  funext i
  by_cases h0 : i = slot 0
  · subst i; simp [install_slot slot hi, h02]
  by_cases h1 : i = slot 1
  · subst i; simp [install_slot slot hi, h01.symm, h12]
  by_cases h2 : i = slot 2
  · subst i; simp [install_slot slot hi]
  rw [install_other slot ambient _ i (by intro j; fin_cases j <;> exact Ne.symm (by assumption))]
  simp [Function.update, h0, h2]

theorem copy_ready {t : ℕ} (slot : Fin 3 → Fin t) (hi : Function.Injective slot)
    (ambient : Fin t → List Bool) (bits padding : List Bool)
    (hs : ambient (slot 0) = frame bits ++ padding)
    (ho : ambient (slot 1) = []) (hl : ambient (slot 2) = []) :
    ReadyRun (RecoveryFocus.machine slot PCPFieldMoves.readyMachine) (4 * bits.length + 4) ambient
      (Function.update (Function.update ambient (slot 1) (frame bits)) (slot 2)
        (List.replicate (2 * bits.length + 1) false)) := by
  classical
  have h := (PCPFieldMoves.ready_run bits padding 0 0).focus slot hi ambient (by
    intro j; fin_cases j <;> simpa using (by assumption))
  have he : PCPFieldMoves.output [] bits padding 0 0 =
      ![ambient (slot 0), frame bits, List.replicate (2 * bits.length + 1) false] := by
    funext j
    fin_cases j <;> simp [PCPFieldMoves.output, hs]
  rw [he, install_first slot hi] at h
  exact h

theorem clear_ready {t : ℕ} (slot : Fin 3 → Fin t) (hi : Function.Injective slot)
    (ambient : Fin t → List Bool) (n : ℕ)
    (hs : (ambient (slot 0)).length ≤ n)
    (hd : ambient (slot 1) = List.replicate n true) (hl : ambient (slot 2) = []) :
    ReadyRun (RecoveryFocus.machine slot (RecoveryScratchErase.resetMachine 1)) (2 * n + 4) ambient
      (Function.update (Function.update ambient (slot 0) (List.replicate n false)) (slot 2)
        (List.replicate (n + 1) false)) := by
  classical
  have h := RecoveryScratchErase.erase_ready n 0 (fun _ : Fin 1 => ambient (slot 0)) (by intro i; exact hs)
  have hin : (Fin.addCases (m := 2) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool) (fun _ : Fin 1 => ambient (slot 0))
      (fun _ : Fin 1 => List.replicate n true)) (fun _ : Fin 1 => List.replicate 0 false)) =
      ![ambient (slot 0), ambient (slot 1), ambient (slot 2)] := by
    funext j; fin_cases j <;> simp [hd, hl] <;> rfl
  have hout : (Fin.addCases (m := 2) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool) (fun _ : Fin 1 => List.replicate n false)
      (fun _ : Fin 1 => List.replicate n true)) (fun _ : Fin 1 => List.replicate (max 0 (n + 1)) false)) =
      ![List.replicate n false, ambient (slot 1), List.replicate (n + 1) false] := by
    funext j; fin_cases j <;> simp [hd] <;> rfl
  rw [hin, hout] at h
  have hf := h.focus slot hi ambient (by intro j; fin_cases j <;> rfl)
  rw [install_second slot hi] at hf
  exact hf

end NearCubicWires.RepairSource.OrdinaryOracleCompose
