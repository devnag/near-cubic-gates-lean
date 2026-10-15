import Proof.MachineModel.OrdinaryMemoryInitialization

/-! The computation-log consumer with its literal initial-memory prefix.
Both directions use the same ordinary verifier, framed input/witness, derived
control/head walk, and chronological event stream. -/
namespace NearCubicWires.RepairOrdinary.InitializedTrace
open LocalBitMultitape MemoryLog MemoryTransition ClaimedTrace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem initial_memory (v : Verifier) (input witness : List Bool) :
    memoryOf (initialConfiguration v.machine (v.inputTapes input witness)) =
      MemoryInitialization.memory input witness := by
  funext cell
  rcases cell with ⟨tape,address⟩
  have ht0 : 0 < v.tapeCount := by have h := v.twoTapes; omega
  have ht1 : 1 < v.tapeCount := by have h := v.twoTapes; omega
  by_cases h0 : tape = 0
  · subst tape
    simp [memoryOf, initialConfiguration, Verifier.inputTapes, MemoryInitialization.memory, ht0]
  · by_cases h1 : tape = 1
    · subst tape
      simp [memoryOf, initialConfiguration, Verifier.inputTapes, MemoryInitialization.memory, ht1]
    · by_cases ht : tape < v.tapeCount <;>
        simp [memoryOf, initialConfiguration, Verifier.inputTapes, MemoryInitialization.memory,
          h0, h1, ht, readTapeBit]

theorem sound (v : Verifier) (input witness : List Bool)
    (claims : List (Fin v.tapeCount → Bool)) (finalView : View v.tapeCount v.stateCount)
    (trace : List Event)
    (hcheck : ClaimedTrace.check v.machine
      (view (initialConfiguration v.machine (v.inputTapes input witness))) claims =
        some (finalView,trace))
    (hmem : (MemoryLog.run (fun _ => false)
      (MemoryInitialization.events input witness++trace)).isSome = true)
    (hhalt : v.machine.halted finalView.control = true)
    (haccept : v.accepting finalView.control = true) :
    v.acceptsAt claims.length input witness := by
  rw [MemoryLog.run_append, MemoryInitialization.initial_run, Option.bind_some] at hmem
  cases hr : MemoryLog.run (MemoryInitialization.memory input witness) trace with
  | none => simp [hr] at hmem
  | some finalMemory =>
    rw [← initial_memory v input witness] at hr
    obtain ⟨r, hrun, hv, _⟩ := ClaimedTrace.sound v.machine
      (initialConfiguration v.machine (v.inputTapes input witness)) claims finalView trace
      finalMemory hcheck hr hhalt
    refine ⟨r, hrun, ?_⟩
    have hcontrol : r.final.control = finalView.control := congrArg View.control hv
    rw [hcontrol]
    exact haccept

theorem complete (v : Verifier) (input witness : List Bool) (fuel : ℕ)
    (r : ExecutionReceipt v.tapeCount v.stateCount)
    (hr : LocalBitMultitape.run v.machine fuel (v.inputTapes input witness) = some r) :
    ∃ claims trace,
      claims.length = r.steps ∧ trace.length = v.tapeCount*r.steps ∧
      ClaimedTrace.check v.machine
        (view (initialConfiguration v.machine (v.inputTapes input witness))) claims =
          some (view r.final,trace) ∧
      MemoryLog.run (fun _ => false) (MemoryInitialization.events input witness++trace) =
        some (memoryOf r.final) ∧
      v.machine.halted r.final.control = true ∧
      (MemoryInitialization.events input witness++trace).length =
        2*input.length+2*witness.length+2+v.tapeCount*r.steps := by
  obtain ⟨claims, trace, hc, ht, hcheck, hm, hh⟩ :=
    ClaimedTrace.complete v.machine fuel
      (initialConfiguration v.machine (v.inputTapes input witness)) r hr
  refine ⟨claims, trace, hc, ht, hcheck, ?_, hh, ?_⟩
  · rw [MemoryLog.run_append, MemoryInitialization.initial_run, Option.bind_some]
    rw [initial_memory] at hm
    exact hm
  · rw [List.length_append, MemoryInitialization.initial_count, ht]

end NearCubicWires.RepairOrdinary.InitializedTrace
