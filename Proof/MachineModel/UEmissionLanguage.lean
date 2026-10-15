import Proof.MachineModel.UEmissionFields
import Proof.MachineModel.OrdinaryMemoryCheckerTraceBounds

/-! The pure accepted predicate uses the same decoded verifier, initialized
memory, bounded claimed walk, and checked chronological events. -/
namespace NearCubicWires.RepairOrdinary.UEmission
open LocalBitMultitape SignedSortKey RepairSource VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Checked (d : TraceData) : Prop := ∃ finalView events,
  TransitionWalk.evaluate d.verifier (initialView d) d.count d.suffix = some (finalView,events) ∧
  d.verifier.machine.halted finalView.control = true ∧
  d.verifier.accepting finalView.control = true ∧
  (MemoryLog.run (fun _ => false) (MemoryInitialization.events d.input d.choices ++ events)).isSome = true

def Accepted (raw witness : List Bool) : Prop := ∃ d, Fields raw witness d ∧ Checked d

theorem Fields.tapes_bound {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d) :
    d.verifier.tapeCount ≤ d.word.length := by
  rw [←h.code_eq]
  exact VerifierEncoding.tapes_le_code_length d.verifier

theorem Fields.evaluation_ready {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d)
    (finalView : ClaimedTrace.View d.verifier.tapeCount d.verifier.stateCount) (events : List MemoryLog.Event)
    (he : TransitionWalk.evaluate d.verifier (initialView d) d.count d.suffix = some (finalView,events)) :
    MemoryChecker.ListReady (2*ClockDyadicLedger.width raw.length) (ClockDyadicLedger.width raw.length)
      (MemoryInitialization.events d.input d.choices ++ events) := by
  obtain ⟨claims,_,hlen,_,hcheck⟩ := TransitionWalk.evaluate_implies_trace d.verifier d.count _ _ _ _ he
  have hcap := (ClockDyadicLedger.guarded_bounds raw.length d.input.length d.choices.length
    d.count d.verifier.tapeCount d.word.length h.length_bound h.input_bound h.choices_bound
    h.count_bound h.tapes_bound h.code_bound).1
  have hp := (ClockDyadicLedger.width_bounds raw.length).1
  have hinput := h.input_bound.trans h.choices_bound
  have hcount := h.count_bound.trans h.choices_bound
  have htapes := ((h.tapes_bound.trans h.code_bound).trans (Nat.log_le_self 2 raw.length)).trans
    (ClockEnvelope.input_le_limit raw.length)
  apply MemoryChecker.initialized_ready d.verifier d.input d.choices claims finalView events
    (ClockDyadicLedger.width raw.length) hcheck
  · rw [hlen]
    exact hcap.le
  · omega
  · omega
  · have hb := h.choices_bound; omega
  · rw [hlen]; omega

theorem checked_iff {raw witness : List Bool} {d : TraceData} (_h : Fields raw witness d) :
    Checked d ↔ accepted d = true ∧ ∃ finalView events,
      TransitionWalk.evaluate d.verifier (initialView d) d.count d.suffix = some (finalView,events) ∧
      (MemoryLog.run (fun _ => false) (MemoryInitialization.events d.input d.choices ++ events)).isSome = true := by
  constructor
  · rintro ⟨finalView,events,he,hh,ha,hm⟩
    exact ⟨(TransitionWalk.accepted_iff _ _ _ _).2 ⟨finalView,events,he,hh,ha⟩,
      finalView,events,he,hm⟩
  · rintro ⟨ha,finalView,events,he,hm⟩
    have hflags : d.verifier.machine.halted finalView.control = true ∧
        d.verifier.accepting finalView.control = true := by
      simpa only [accepted,TransitionWalk.accepted,he,Bool.and_eq_true] using ha
    exact ⟨finalView,events,he,hflags.1,hflags.2,hm⟩

theorem Checked.sound {raw witness : List Bool} {d : TraceData}
    (h : Fields raw witness d) (hc : Checked d) : d.verifier.acceptsAt d.count d.input d.choices := by
  obtain ⟨finalView,events,he,hh,ha,hm⟩ := hc
  have hready := h.evaluation_ready finalView events he
  apply MemoryChecker.checked_evaluation_sound d.verifier d.input d.choices d.count d.suffix
    finalView events hready he
  · rw [MemoryChecker.list_result]
    exact hm
  · exact (TransitionWalk.accepted_iff _ _ _ _).2 ⟨finalView,events,he,hh,ha⟩

theorem Accepted.sound {raw witness : List Bool} (h : Accepted raw witness) :
    ∃ d, Fields raw witness d ∧ d.verifier.acceptsAt d.count d.input d.choices := by
  obtain ⟨d,hf,hc⟩ := h
  exact ⟨d,hf,hc.sound hf⟩

theorem Accepted.front_accepted {raw witness : List Bool} (h : Accepted raw witness) :
    UFront.Accepted raw witness := by
  obtain ⟨_,hf,_⟩ := h
  exact hf.front_accepted

theorem accepted_iff_checked {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d) :
    Accepted raw witness ↔ Checked d := by
  constructor
  · rintro ⟨e,he,hc⟩
    rwa [he.unique h] at hc
  · exact fun hc => ⟨d,h,hc⟩

end NearCubicWires.RepairOrdinary.UEmission
