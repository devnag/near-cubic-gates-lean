import Proof.Foundations.OrdinaryMachine

/-! Extend a finite local machine by unused physical tapes. The extra tapes
are not cleared, ignored in the space bound, or reinitialized at a handoff.
This permits a source machine to run beside a loader's retained data. -/
namespace NearCubicWires.RepairOrdinary.TapeEmbedding
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {t e s : ℕ} (heads : Fin e → ℕ) (tapes : Fin e → List Bool)
    (c : Configuration t s) : Configuration (t + e) s where
  control := c.control
  heads := Fin.addCases c.heads heads
  tapes := Fin.addCases c.tapes tapes

def action {t s : ℕ} (e : ℕ) (a : Action t s) : Action (t + e) s where
  nextControl := a.nextControl
  write := Fin.addCases a.write (fun _ => none)
  move := Fin.addCases a.move (fun _ => .stay)

def machine {t s : ℕ} (e : ℕ) (p : Machine t s) : Machine (t + e) s where
  descriptionBits := 0
  start := p.start
  halted := p.halted
  rule := fun state scanned =>
    (p.rule state (fun i => scanned (i.castAdd e))).map (action e)

def extraCells {e : ℕ} (tapes : Fin e → List Bool) : ℕ :=
  ∑ i, (tapes i).length

@[simp] theorem config_cells {t e s : ℕ} (heads : Fin e → ℕ)
    (tapes : Fin e → List Bool) (c : Configuration t s) :
    (config heads tapes c).tapeCells = c.tapeCells + extraCells tapes := by
  simp [Configuration.tapeCells, config, extraCells, Fin.sum_univ_add]

theorem config_scanned {t e s : ℕ} (heads : Fin e → ℕ)
    (tapes : Fin e → List Bool) (c : Configuration t s) :
    (fun i : Fin t => (config heads tapes c).scanned (i.castAdd e)) = c.scanned := by
  funext i
  simp [Configuration.scanned, config]

theorem apply_action {t e s : ℕ} (heads : Fin e → ℕ)
    (tapes : Fin e → List Bool) (c : Configuration t s) (a : Action t s) :
    applyAction (config heads tapes c) (action e a) = config heads tapes (applyAction c a) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [applyAction, action, config]
    · simp [applyAction, action, config, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [applyAction, action, config]
    · simp [applyAction, action, config]

theorem step_embed {t e s : ℕ} (p : Machine t s) (heads : Fin e → ℕ)
    (tapes : Fin e → List Bool) (c : Configuration t s) :
    step (machine e p) (config heads tapes c) = (step p c).map (config heads tapes) := by
  change ((p.rule c.control (fun i => (config heads tapes c).scanned (i.castAdd e))).map
    (action e)).map (applyAction (config heads tapes c)) =
      ((p.rule c.control c.scanned).map (applyAction c)).map (config heads tapes)
  rw [config_scanned]
  simp only [Option.map_map, Function.comp_def, apply_action]

def receipt {t e s : ℕ} (heads : Fin e → ℕ) (tapes : Fin e → List Bool)
    (r : ExecutionReceipt t s) : ExecutionReceipt (t + e) s :=
  ⟨config heads tapes r.final, r.steps, r.peakTapeCells + extraCells tapes⟩

theorem run_embed {t e s : ℕ} (p : Machine t s) (heads : Fin e → ℕ)
    (tapes : Fin e → List Bool) (fuel : ℕ) (c : Configuration t s)
    (r : ExecutionReceipt t s) (hrun : runFrom p fuel c = some r) :
    runFrom (machine e p) fuel (config heads tapes c) = some (receipt heads tapes r) := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hrun
    split at hrun
    · next h =>
        cases hrun
        simp [runFrom, machine, config, receipt, Configuration.tapeCells,
          extraCells, Fin.sum_univ_add, h]
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hrun
    split at hrun
    · next h =>
        cases hrun
        simp [runFrom, machine, config, receipt, Configuration.tapeCells,
          extraCells, Fin.sum_univ_add, h]
    · next h =>
        split at hrun
        · contradiction
        · next next hs =>
            split at hrun
            · contradiction
            · next suffix htail =>
                cases hrun
                have hi := ih next suffix htail
                have hstep : step (machine e p) (config heads tapes c) =
                    some (config heads tapes next) := by
                  rw [step_embed, hs]
                  rfl
                have hfirst := runFrom_step (machine e p) (config heads tapes c)
                  (config heads tapes next) (receipt heads tapes suffix)
                  (by simpa [machine, config] using h) hstep hi
                have hpeak : max (c.tapeCells + extraCells tapes)
                    (suffix.peakTapeCells + extraCells tapes) =
                    max c.tapeCells suffix.peakTapeCells + extraCells tapes := by omega
                simpa only [receipt, config_cells, hpeak] using hfirst

end NearCubicWires.RepairOrdinary.TapeEmbedding
