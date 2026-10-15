import Proof.MachineModel.UEmissionRun

/-! The request actually printed by a successful U evaluation. Its exact
input and finite capacities are derived from that same executed trace. -/
namespace NearCubicWires.RepairOrdinary.UEmission
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem Fields.list_ready {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d)
    (finalView : ClaimedTrace.View d.verifier.tapeCount d.verifier.stateCount) (events : List MemoryLog.Event)
    (heval : TransitionWalk.evaluate d.verifier (initialView d) d.count d.suffix=some (finalView,events)) :
    MemoryChecker.ListReady (2*ClockDyadicLedger.width raw.length) (ClockDyadicLedger.width raw.length)
      (MemoryInitialization.events d.input d.choices++events) := by
  apply TransitionWalk.initial_evaluation_ready raw.length d.verifier d.input d.choices d.count d.suffix
    finalView events h.length_bound h.input_bound h.choices_bound h.count_bound _ heval
  rw [h.code_eq]
  exact h.code_bound

theorem Fields.list_count {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d)
    (finalView : ClaimedTrace.View d.verifier.tapeCount d.verifier.stateCount) (events : List MemoryLog.Event)
    (heval : TransitionWalk.evaluate d.verifier (initialView d) d.count d.suffix=some (finalView,events)) :
    (MemoryInitialization.events d.input d.choices++events).length≤UAggregateClock.eventCap raw.length := by
  obtain ⟨claims,_,hlen,_,hcheck⟩ := TransitionWalk.evaluate_implies_trace d.verifier d.count
    (initialView d) d.suffix finalView events heval
  obtain ⟨hevents,_⟩ := MemoryChecker.check_cells d.verifier.machine claims (initialView d)
    finalView events d.count (by intro i; change 0+claims.length≤d.count; omega) hcheck
  rw [List.length_append,MemoryInitialization.initial_count,hevents,hlen]
  exact UAggregateClock.event_bound _ _ _ h.event_count h.code_bound

theorem event_request_input {N : ℕ} (d : TraceData) (events : List MemoryLog.Event)
    (hready : MemoryChecker.ListReady (2*ClockDyadicLedger.width N) (ClockDyadicLedger.width N)
      (MemoryInitialization.events d.input d.choices++events)) :
    eventWord N d events++[false]=(MemoryChecker.listRequest hready).input :=
  TransitionWalk.initial_event_input N d.verifier 0 [] 0 d.input d.choices d.count events hready

end NearCubicWires.RepairOrdinary.UEmission
