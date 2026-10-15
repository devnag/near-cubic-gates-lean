import Proof.Foundations.OrdinaryTapeEmbedding

/-! Compile a fixed renaming of physical tapes into the finite transition
table. This moves no data: the program's read/write/head labels are renamed.
It preserves the exact execution count and peak occupied tape cells. -/
namespace NearCubicWires.RepairOrdinary.TapeRenaming
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {t u s : ℕ} (e : Fin t ≃ Fin u) (c : Configuration t s) : Configuration u s :=
  ⟨c.control, c.heads ∘ e.symm, c.tapes ∘ e.symm⟩

def action {t u s : ℕ} (e : Fin t ≃ Fin u) (a : Action t s) : Action u s :=
  ⟨a.nextControl, a.write ∘ e.symm, a.move ∘ e.symm⟩

def machine {t u s : ℕ} (e : Fin t ≃ Fin u) (p : Machine t s) : Machine u s where
  descriptionBits := 0
  start := p.start
  halted := p.halted
  rule := fun state scanned => (p.rule state (scanned ∘ e)).map (action e)

@[simp] theorem config_cells {t u s : ℕ} (e : Fin t ≃ Fin u) (c : Configuration t s) :
    (config e c).tapeCells = c.tapeCells := by
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

theorem config_scanned {t u s : ℕ} (e : Fin t ≃ Fin u) (c : Configuration t s) :
    (config e c).scanned ∘ e = c.scanned := by
  funext i
  simp [config, Configuration.scanned]

theorem apply_action {t u s : ℕ} (e : Fin t ≃ Fin u) (c : Configuration t s)
    (a : Action t s) : applyAction (config e c) (action e a) = config e (applyAction c a) := rfl

theorem step_rename {t u s : ℕ} (e : Fin t ≃ Fin u) (p : Machine t s)
    (c : Configuration t s) :
    step (machine e p) (config e c) = (step p c).map (config e) := by
  change ((p.rule c.control ((config e c).scanned ∘ e)).map (action e)).map
    (applyAction (config e c)) = ((p.rule c.control c.scanned).map (applyAction c)).map (config e)
  rw [config_scanned]
  simp only [Option.map_map, Function.comp_def, apply_action]

def receipt {t u s : ℕ} (e : Fin t ≃ Fin u) (r : ExecutionReceipt t s) : ExecutionReceipt u s :=
  ⟨config e r.final, r.steps, r.peakTapeCells⟩

theorem run_rename {t u s : ℕ} (e : Fin t ≃ Fin u) (p : Machine t s)
    (fuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s)
    (hrun : runFrom p fuel c = some r) :
    runFrom (machine e p) fuel (config e c) = some (receipt e r) := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hrun
    split at hrun
    · next h =>
        cases hrun
        have hh : (machine e p).halted (config e c).control = true := h
        simpa [receipt] using runFrom_zero_of_halted (machine e p) (config e c) hh
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hrun
    split at hrun
    · next h =>
        cases hrun
        have hh : (machine e p).halted (config e c).control = true := h
        simp [runFrom, hh, receipt]
    · next h =>
        split at hrun
        · contradiction
        · next next hs =>
            split at hrun
            · contradiction
            · next suffix htail =>
                cases hrun
                have hi := ih next suffix htail
                have hstep : step (machine e p) (config e c) = some (config e next) := by
                  rw [step_rename, hs]
                  rfl
                simpa [receipt] using runFrom_step (machine e p) (config e c)
                  (config e next) (receipt e suffix)
                  (by simpa [machine, config] using h) hstep hi

end NearCubicWires.RepairOrdinary.TapeRenaming
