import Proof.MachineModel.OrdinaryZeroPadding

/-! Reverse simulation for blank suffixes. A successful execution on padded
tapes also executes on the actual shorter tapes with the same transitions.
Only cells actually written are allocated; occupied storage never increases
when initially absent blank suffixes are removed. -/
namespace NearCubicWires.RepairOrdinary.ZeroPadding
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cells_le_config {t s : ℕ} (capacity : Fin t → ℕ) (c : Configuration t s) :
    c.tapeCells ≤ (config capacity c).tapeCells := by
  unfold Configuration.tapeCells
  apply Finset.sum_le_sum
  intro i _
  change (c.tapes i).length ≤ (pad (capacity i) (c.tapes i)).length
  rw [pad_length]
  exact Nat.le_max_right _ _

theorem step_config_eq {t s : ℕ} (p : Machine t s) (capacity : Fin t → ℕ)
    (c : Configuration t s) :
    step p (config capacity c) = (step p c).map (config capacity) := by
  change (p.rule c.control (config capacity c).scanned).map _ = _
  rw [scanned_config]
  simp only [step, Option.map_map, Function.comp_def]
  congr 1
  funext a
  exact apply_config capacity c a

theorem run_unpad {t s : ℕ} (p : Machine t s) (capacity : Fin t → ℕ)
    (fuel : ℕ) (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel (config capacity c) = some source) :
    ∃ r : ExecutionReceipt t s, runFrom p fuel c = some r ∧
      config capacity r.final = source.final ∧ r.steps = source.steps ∧
      r.peakTapeCells ≤ source.peakTapeCells := by
  induction fuel generalizing c source with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · next hc =>
      cases hr
      refine ⟨⟨c, 0, c.tapeCells⟩, ?_, rfl, rfl, cells_le_config capacity c⟩
      exact runFrom_zero_of_halted p c hc
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · next hc =>
      cases hr
      refine ⟨⟨c, 0, c.tapeCells⟩, ?_, rfl, rfl, cells_le_config capacity c⟩
      simp only [runFrom, show p.halted c.control = true from hc, ↓reduceIte]
    · next hc =>
      cases hs : step p c with
      | none => simp [step_config_eq, hs] at hr
      | some d =>
        have hstep := step_config p capacity c d hs
        cases ht : runFrom p fuel (config capacity d) with
        | none => simp [hstep, ht] at hr
        | some tail =>
          simp only [hstep, ht, Option.some.injEq] at hr
          subst source
          obtain ⟨suffix, hsuffix, hf, hsteps, hpeak⟩ := ih d tail ht
          have hnot : p.halted c.control = false := by simpa [config] using hc
          have hj := runFrom_step p c d suffix hnot hs hsuffix
          refine ⟨⟨suffix.final, suffix.steps + 1, max c.tapeCells suffix.peakTapeCells⟩,
            hj, hf, ?_, ?_⟩
          · dsimp only
            omega
          · exact max_le_max (cells_le_config capacity c) hpeak

end NearCubicWires.RepairOrdinary.ZeroPadding
