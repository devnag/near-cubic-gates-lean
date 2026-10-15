import Proof.MachineModel.OrdinaryMemoryScan

/-! Four actual transitions check the read bit against the preceding sorted
cell's value, then retain this event's written bit. The comparison flag is
overwritten in place. Whole-stream iteration and the source verifier are not
asserted by this bounded operation. -/
namespace NearCubicWires.RepairOrdinary.MemoryDecision
open LocalBitMultitape MemoryLog
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accept (read previous same : Bool) : Bool := read == (same && previous)
def action (state : Fin 5) (sourceMove outMove : HeadMove)
    (previousWrite outWrite : Option Bool) : Action 3 5 :=
  ⟨state, ![none, previousWrite, outWrite], ![sourceMove, .stay, outMove]⟩
def machine : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 4
  rule := fun state bits =>
    if state.val = 0 then some (action 1 .right .left none none)
    else if state.val = 1 then some (action 2 .right .stay none (some (accept (bits 0) (bits 1) (bits 2))))
    else if state.val = 2 then some (action 3 .right .stay none none)
    else if state.val = 3 then some (action 4 .stay .stay (some (bits 0)) none)
    else none

def config (state : Fin 5) (source : List Bool) (pos : ℕ) (previous : Bool)
    (out : List Bool) (outPos : ℕ) : Configuration 3 5 :=
  ⟨state, ![pos, 0, outPos], ![source, [previous], out]⟩
@[simp] theorem config_cells (state : Fin 5) (source : List Bool) (pos : ℕ)
    (previous : Bool) (out : List Bool) (outPos : ℕ) :
    (config state source pos previous out outPos).tapeCells = source.length+1+out.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

theorem write_last (pre : List Bool) (old value : Bool) :
    writeTapeBit (pre ++ [old]) pre.length value = pre ++ [value] := by
  induction pre with
  | nil => rfl
  | cons bit pre ih => simpa [writeTapeBit] using congrArg (List.cons bit) ih

theorem start_step (source out : List Bool) (previous same : Bool) :
    step machine (config 0 source 0 previous (out ++ [same]) (out.length+1)) =
      some (config 1 source 1 previous (out ++ [same]) out.length) := by
  simp [step, machine, config]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem check_step (read after previous same : Bool) (suffix out : List Bool) :
    step machine (config 1 (frame (read :: after :: suffix)) 1 previous (out ++ [same]) out.length) =
      some (config 2 (frame (read :: after :: suffix)) 2 previous
        (out ++ [accept read previous same]) out.length) := by
  have hs : readTapeBit (frame (read :: after :: suffix)) 1 = read := rfl
  have hp : readTapeBit [previous] 0 = previous := rfl
  have ho := Streaming.read_append out [] same
  simp [step, machine, config, Configuration.scanned, hs, hp, ho]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, write_last]

theorem advance_step (source out : List Bool) (previous : Bool) (outPos : ℕ) :
    step machine (config 2 source 2 previous out outPos) =
      some (config 3 source 3 previous out outPos) := by
  simp [step, machine, config]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem retain_step (read after previous : Bool) (suffix out : List Bool) (outPos : ℕ) :
    step machine (config 3 (frame (read :: after :: suffix)) 3 previous out outPos) =
      some (config 4 (frame (read :: after :: suffix)) 3 after out outPos) := by
  have hr : readTapeBit (frame (read :: after :: suffix)) 3 = after := rfl
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, writeTapeBit]

theorem decision_run (read after previous same : Bool) (suffix out : List Bool) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom machine 4
        (config 0 (frame (read :: after :: suffix)) 0 previous (out ++ [same]) (out.length+1)) = some r ∧
      r.final = config 4 (frame (read :: after :: suffix)) 3 after
        (out ++ [accept read previous same]) out.length ∧ r.steps = 4 := by
  let space := (frame (read :: after :: suffix)).length + out.length + 2
  have tail : Prefix machine space 0
      (config 4 (frame (read :: after :: suffix)) 3 after (out ++ [accept read previous same]) out.length)
      (config 4 (frame (read :: after :: suffix)) 3 after (out ++ [accept read previous same]) out.length) :=
    Prefix.refl _ (by simp [space]; omega)
  have p3 := Prefix.step (by simp [space]; omega) (by rfl)
    (retain_step read after previous suffix (out ++ [accept read previous same]) out.length) tail
  have p2 := Prefix.step (by simp [space]; omega) (by rfl)
    (advance_step (frame (read :: after :: suffix)) (out ++ [accept read previous same]) previous out.length) p3
  have p1 := Prefix.step (by simp [space]; omega) (by rfl)
    (check_step read after previous same suffix out) p2
  have p0 := Prefix.step (by simp [space]; omega) (by rfl)
    (start_step (frame (read :: after :: suffix)) out previous same) p1
  obtain ⟨r, hr, hf, ht, _⟩ := p0.run (by rfl) (by simp [space]; omega)
  exact ⟨r, hr, hf, ht⟩

theorem accept_memory (previous current : Event) :
    accept current.read previous.after (decide (current.cell = previous.cell)) =
      decide (current.read = MemoryScan.memory previous current.cell) := by
  by_cases h : current.cell = previous.cell
  · simp only [accept, MemoryScan.memory, h, if_true, decide_true, Bool.true_and]
    cases current.read <;> cases previous.after <;> rfl
  · simp [accept, MemoryScan.memory, h]

end NearCubicWires.RepairOrdinary.MemoryDecision
