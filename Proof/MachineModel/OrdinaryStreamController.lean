import Proof.MachineModel.OrdinaryCellLoad

/-! Run an actual fixed body until a designated stream tape reaches its
terminator. Entry, return and termination are executed transitions; stopping
does not append an unwanted delimiter to the raw matrix-output tape. -/
namespace NearCubicWires.RepairOrdinary.StreamController
open LocalBitMultitape
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def jump {t s : ℕ} (state : Fin s) : Action t s := ⟨state, fun _ => none, fun _ => .stay⟩
def mapped {t s : ℕ} (a : Action t s) : Action t (s + 2) := ⟨code a.nextControl, a.write, a.move⟩
def machine {t s : ℕ} (p : Machine t s) (sourceTape : Fin t) : Machine t (s + 2) where
  descriptionBits := 0
  start := test s
  halted := Fin.addCases (fun _ => false) (fun k => k.val == 1)
  rule := Fin.addCases
    (fun state scanned => if p.halted state then some (jump (test s)) else (p.rule state scanned).map mapped)
    (fun state scanned => if state.val = 0 then
      some (if scanned sourceTape then jump (code p.start) else jump (stop s)) else none)

@[simp] theorem body_halted {t s : ℕ} (p : Machine t s) (tape : Fin t) (state : Fin s) :
    (machine p tape).halted (code state) = false := by simp [machine, code]
@[simp] theorem test_halted {t s : ℕ} (p : Machine t s) (tape : Fin t) :
    (machine p tape).halted (test s) = false := by simp [machine, test]
@[simp] theorem stop_halted {t s : ℕ} (p : Machine t s) (tape : Fin t) :
    (machine p tape).halted (stop s) = true := by simp [machine, stop]

theorem body_step {t s : ℕ} (p : Machine t s) (tape : Fin t) (c : Configuration t s)
    (hn : p.halted c.control = false) :
    step (machine p tape) (controlConfig code c) = (step p c).map (controlConfig code) := by
  simp only [step, machine, controlConfig, code, Fin.addCases_left, hn, Bool.false_eq_true,
    ↓reduceIte, Option.map_map]
  rfl

theorem body_prefix {t s : ℕ} (p : Machine t s) (tape : Fin t) (fuel : ℕ) (c : Configuration t s)
    (r : ExecutionReceipt t s) (hr : runFrom p fuel c = some r) :
    Prefix (machine p tape) r.peakTapeCells r.steps (controlConfig code c) (controlConfig code r.final) ∧
      p.halted r.final.control = true := by
  obtain ⟨hp, hh⟩ := prefix_of_run p fuel c r hr
  refine ⟨hp.mapControl code (fun c _ => body_halted p tape c.control) ?_, hh⟩
  intro c d hn hs
  rw [body_step p tape c hn, hs]
  rfl

theorem enter_step {t s : ℕ} (p : Machine t s) (tape : Fin t) (c : Configuration t s)
    (hr : c.scanned tape = true) :
    step (machine p tape) (controlConfig (fun _ => test s) c) =
      some (controlConfig code (Composition.restart c p.start)) := by
  change readTapeBit (c.tapes tape) (c.heads tape) = true at hr
  simp [step, machine, test, controlConfig, Configuration.scanned, hr]
  rfl

theorem return_step {t s : ℕ} (p : Machine t s) (tape : Fin t) (c : Configuration t s)
    (hh : p.halted c.control = true) :
    step (machine p tape) (controlConfig code c) = some (controlConfig (fun _ => test s) c) := by
  simp only [step, machine, controlConfig, code, Fin.addCases_left, hh, ↓reduceIte, Option.map_some]
  rfl

theorem stop_step {t s : ℕ} (p : Machine t s) (tape : Fin t) (c : Configuration t s)
    (hr : c.scanned tape = false) :
    step (machine p tape) (controlConfig (fun _ => test s) c) =
      some (controlConfig (fun _ => stop s) c) := by
  change readTapeBit (c.tapes tape) (c.heads tape) = false at hr
  simp [step, machine, test, controlConfig, Configuration.scanned, hr]
  rfl

end NearCubicWires.RepairOrdinary.StreamController
