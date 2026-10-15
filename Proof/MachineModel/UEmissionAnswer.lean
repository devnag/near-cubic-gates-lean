import Proof.MachineModel.UEmissionRequest
import Proof.MachineModel.UEmissionLanguage

/-! Select the mathematical request corresponding to the actual emitted
stream. This is a proof of the fixed checker's input, not another program. -/
namespace NearCubicWires.RepairOrdinary.UEmission
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure AnswerReady {s : ℕ} (raw witness : List Bool) (final : Configuration 157 s)
    (answer : Option MemoryChecker.Request) : Prop where
  flag : final.scanned 156=answer.isSome
  stream : ∀ req,answer=some req → final.tapes 92++[false]=req.input ∧
    final.heads 92=(final.tapes 92).length
  bounds : ∀ req,answer=some req → req.count≤UAggregateClock.eventCap raw.length ∧
    req.indexBits=2*ClockDyadicLedger.width raw.length
  meaning : UMemoryClose.answerValue answer=true ↔ Accepted raw witness

theorem checked_iff_memory {raw witness : List Bool} {d : TraceData} (hf : Fields raw witness d)
    (finalView : ClaimedTrace.View d.verifier.tapeCount d.verifier.stateCount) (events : List MemoryLog.Event)
    (he : TransitionWalk.evaluate d.verifier (initialView d) d.count d.suffix=some (finalView,events))
    (hh : d.verifier.machine.halted finalView.control=true)
    (ha : d.verifier.accepting finalView.control=true) :
    Accepted raw witness ↔
      (MemoryLog.run (fun _ => false) (MemoryInitialization.events d.input d.choices++events)).isSome=true := by
  rw [accepted_iff_checked hf]
  constructor
  · rintro ⟨v',events',he',_,_,hm⟩
    have hp := Option.some.inj (he.symm.trans he')
    have hevents : events'=events := (congrArg Prod.snd hp).symm
    simpa only [hevents] using hm
  · intro hm
    exact ⟨finalView,events,he,hh,ha,hm⟩

theorem answer_ready {s : ℕ} (raw witness : List Bool) (final : Configuration 157 s)
    (hout : Outcome raw witness final) : ∃ answer,AnswerReady raw witness final answer := by
  rcases hout with ⟨hbad,hflag⟩ | ⟨d,hf,htrace⟩
  · refine ⟨none,hflag,?_,?_,?_⟩
    · intro req h; cases h
    · intro req h; cases h
    · constructor
      · intro h; cases h
      · intro h; exact False.elim (hbad h.front_accepted)
  · cases hdecision : accepted d with
    | false =>
      refine ⟨none,htrace.decision.trans hdecision,?_,?_,?_⟩
      · intro req h; cases h
      · intro req h; cases h
      · constructor
        · intro h; cases h
        · intro h
          have ha := ((checked_iff hf).1 ((accepted_iff_checked hf).1 h)).1
          rw [hdecision] at ha
          contradiction
    | true =>
      obtain ⟨v,events,he,hh,ha⟩ := (TransitionWalk.accepted_iff _ _ _ _).1 hdecision
      have hr := hf.list_ready v events he
      let req := MemoryChecker.listRequest hr
      refine ⟨some req,htrace.decision.trans hdecision,?_,?_,?_⟩
      · intro req' hreq
        have heq : req=req' := Option.some.inj hreq
        subst req'
        obtain ⟨hword,hhead⟩ := htrace.emitted v events he
        exact ⟨by rw [hword]; exact event_request_input d events hr,hhead⟩
      · intro req' hreq
        have heq : req=req' := Option.some.inj hreq
        subst req'
        exact ⟨hf.list_count v events he,rfl⟩
      · change req.result=true ↔ Accepted raw witness
        rw [MemoryChecker.list_result]
        exact (checked_iff_memory hf v events he hh ha).symm

end NearCubicWires.RepairOrdinary.UEmission
