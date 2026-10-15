import Proof.MachineModel.OrdinaryRankBody

/-! A fixed record-stream controller. It tests the next frame marker, runs
the actual body, returns, and emits the final stream delimiter. -/
namespace NearCubicWires.RepairOrdinary.RecordController
open LocalBitMultitape RankPlacement
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def code {s : ℕ} (state : Fin s) : Fin (s + 2) := state.castAdd 2
def test (s : ℕ) : Fin (s + 2) := (0 : Fin 2).natAdd s
def stop (s : ℕ) : Fin (s + 2) := (1 : Fin 2).natAdd s
def jump {s : ℕ} (state : Fin s) : Action 5 s := ⟨state, fun _ => none, fun _ => .stay⟩
def mapped {s : ℕ} (a : Action 5 s) : Action 5 (s + 2) := ⟨code a.nextControl, a.write, a.move⟩
def finish (s : ℕ) : Action 5 (s + 2) :=
  ⟨stop s, fun i => if i.val = 1 then some false else none,
    fun i => if i.val = 1 then .right else .stay⟩

def machine {s : ℕ} (p : Machine 5 s) : Machine 5 (s + 2) where
  descriptionBits := 0
  start := test s
  halted := Fin.addCases (fun _ => false) (fun k => k.val == 1)
  rule := Fin.addCases
    (fun state scanned => if p.halted state then some (jump (test s)) else (p.rule state scanned).map mapped)
    (fun state scanned => if state.val = 0 then
      some (if scanned 0 then jump (code p.start) else finish s) else none)

@[simp] theorem body_halted {s : ℕ} (p : Machine 5 s) (state : Fin s) :
    (machine p).halted (code state) = false := by simp [machine, code]
@[simp] theorem test_halted {s : ℕ} (p : Machine 5 s) :
    (machine p).halted (test s) = false := by simp [machine, test]
@[simp] theorem stop_halted {s : ℕ} (p : Machine 5 s) :
    (machine p).halted (stop s) = true := by simp [machine, stop]

theorem body_step {s : ℕ} (p : Machine 5 s) (c : Configuration 5 s)
    (hn : p.halted c.control = false) :
    step (machine p) (controlConfig code c) = (step p c).map (controlConfig code) := by
  simp only [step, machine, controlConfig, code, Fin.addCases_left, hn, Bool.false_eq_true,
    ↓reduceIte, Option.map_map]
  rfl

theorem body_prefix {s : ℕ} (p : Machine 5 s) (fuel : ℕ) (c : Configuration 5 s)
    (r : ExecutionReceipt 5 s) (hr : runFrom p fuel c = some r) :
    Prefix (machine p) r.peakTapeCells r.steps (controlConfig code c) (controlConfig code r.final) ∧
      p.halted r.final.control = true := by
  obtain ⟨hp, hh⟩ := prefix_of_run p fuel c r hr
  refine ⟨hp.mapControl code (fun c _ => body_halted p c.control) ?_, hh⟩
  intro c d hn hs
  rw [body_step p c hn, hs]
  rfl

theorem enter_step {s : ℕ} (p : Machine 5 s) (input output rank marks saved : List Bool)
    (sourceHead rankHead marksHead savedHead : ℕ) (hr : readTapeBit input sourceHead = true) :
    step (machine p) (config (test s) input sourceHead output rank rankHead marks marksHead saved savedHead) =
      some (controlConfig code (config p.start input sourceHead output rank rankHead marks marksHead saved savedHead)) := by
  simp [step, machine, test, config, Configuration.scanned, hr]
  rfl

theorem return_step {s : ℕ} (p : Machine 5 s) (c : Configuration 5 s) (hh : p.halted c.control = true) :
    step (machine p) (controlConfig code c) =
      some (controlConfig (fun _ => test s) c) := by
  simp only [step, machine, controlConfig, code, Fin.addCases_left, hh, ↓reduceIte, Option.map_some]
  rfl

theorem stop_step {s : ℕ} (p : Machine 5 s) (input output rank marks saved : List Bool)
    (sourceHead rankHead marksHead savedHead : ℕ) (hr : readTapeBit input sourceHead = false) :
    step (machine p) (config (test s) input sourceHead output rank rankHead marks marksHead saved savedHead) =
      some (config (stop s) input sourceHead (output ++ [false]) rank rankHead marks marksHead saved savedHead) := by
  simp [step, machine, test, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, finish, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, finish, Streaming.write_append]

end NearCubicWires.RepairOrdinary.RecordController
