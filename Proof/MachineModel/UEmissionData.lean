import Proof.MachineModel.UTransitionRun

/-! Retained semantic data at the actual event emitter's boundary. All
fields are extracted from its executed decoder/witness/preparation phases. -/
namespace NearCubicWires.RepairOrdinary.UEmission
open LocalBitMultitape RecoveryExecution SignedSortKey RepairSource VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure TraceData where
  verifier : OrdinaryVerifier
  word : List Bool
  input : List Bool
  bound : List Bool
  padding : List Bool
  choices : List Bool
  count : ℕ
  suffix : List Bool

structure Fields (raw witness : List Bool) (d : TraceData) : Prop where
  source : raw=VerifierInputFields.source d.word d.input d.bound d.padding
  guards : UInputScalars.Guards raw d.input d.bound
  decoded : decode raw.length d.word=some d.verifier
  code_bound : d.word.length≤Nat.log 2 raw.length
  witness_eq : witness=binary (ClockDyadicLedger.width raw.length) d.count++d.choices++d.suffix
  input_bound : d.input.length≤d.choices.length
  choices_bound : d.choices.length≤ClockDyadicLedger.limit raw.length
  count_bound : d.count≤d.choices.length
  choices_length : d.choices.length=RadixSemantics.value d.bound

def initialView (d : TraceData) :=
  ClaimedTrace.view (initialConfiguration d.verifier.machine (d.verifier.inputTapes d.input d.choices))
def accepted (d : TraceData) := TransitionWalk.accepted d.verifier (initialView d) d.count d.suffix
def walkStore (raw witness : List Bool) (d : TraceData) :=
  UTransition.store raw witness d.verifier d.word d.input d.choices d.count
def walkBudget (raw witness : List Bool) (d : TraceData) :=
  (d.count+1)*TransitionWalk.cycleBudget (walkStore raw witness d)
def eventWord (N : ℕ) (d : TraceData) (events : List MemoryLog.Event) :=
  MemoryInitialEmission.fields (2*ClockDyadicLedger.width N) (2*ClockDyadicLedger.width N+2)
    (ClockDyadicLedger.width N) 0 (MemoryInitialization.events d.input d.choices)++
  MemoryInitialEmission.fields (2*ClockDyadicLedger.width N) (2*ClockDyadicLedger.width N+2)
    (ClockDyadicLedger.width N) (2*d.input.length+2*d.choices.length+2) events

structure TraceResult {s : ℕ} (N : ℕ) (d : TraceData) (final : Configuration 157 s) : Prop where
  decision : final.scanned 156=accepted d
  result_head : final.heads 156=0
  emitted : ∀ finalView events,TransitionWalk.evaluate d.verifier (initialView d) d.count d.suffix=
    some (finalView,events) → final.tapes 92=eventWord N d events ∧ final.heads 92=(final.tapes 92).length

theorem Fields.length_bound {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d) : 2≤raw.length := by
  rw [h.source]
  simp only [VerifierInputFields.source,List.length_append,frame_length]
  omega

theorem Fields.code_eq {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d) :
    VerifierEncoding.code d.verifier=d.word := (decode_code_length h.decoded).2

theorem Fields.event_count {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d) :
    PCPResourceLedger.events d.input.length d.choices.length d.count d.verifier.tapeCount≤
      ClockDyadicLedger.limit raw.length*(d.word.length+5) := by
  have ht : d.verifier.tapeCount≤d.word.length := by
    rw [←h.code_eq]
    exact VerifierEncoding.tapes_le_code_length d.verifier
  exact PCPResourceLedger.record_count _ _ _ _ _ _
    (h.length_bound.trans (ClockEnvelope.input_le_limit raw.length))
    h.input_bound h.choices_bound h.count_bound ht

theorem prepared_trace_run {s : ℕ} (raw witness : List Bool) (final : Configuration 139 s)
    (hp : UPrepared.Prepared raw witness final) :
    ∃ d,Fields raw witness d ∧ ∃ r,
      runFrom UTransition.machine (walkBudget raw witness d)
        (UTransition.entry (UTransition.extended final).heads (UTransition.extended final).tapes)=some r ∧
      TraceResult raw.length d r.final := by
  obtain ⟨v,word,x,bound,padding,choices,m,suffix,hraw,hguards,hd,hc,hprefix,hn,hB,hm,hchoices,r,hr,_,hflag,hhead,hevents⟩ :=
    UTransition.prepared_run raw witness final hp
  exact ⟨⟨v,word,x,bound,padding,choices,m,suffix⟩,
    ⟨hraw,hguards,hd,hc,hprefix,hn,hB,hm,hchoices⟩,r,hr,⟨hflag,hhead,hevents⟩⟩

end NearCubicWires.RepairOrdinary.UEmission
