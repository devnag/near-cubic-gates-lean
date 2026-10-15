import Proof.PCP.VerifierDecodingStartField
import Proof.PCP.VerifierDecodingHeaderSemantics

/-! Literal start-state validation on the enclosing decoder store. The code
cursor, binary bound and width come from Dimensions; only the selected six
tapes execute the already accepted range machine. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.StartLayout
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev states := Fintype.card (RecoveryCalls.Control RangeMachine.sizes)
def slot : Fin 6 → Fin 14 := ![0,11,10,7,12,13]
theorem slot_injective : Function.Injective slot := by decide
theorem slot_pick (i : Fin 14) : RecoveryFocus.pick slot i=
    ![some 0,none,none,none,none,none,none,some 3,none,none,some 2,some 1,some 4,some 5] i := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slot slot_injective 0
    | exact RecoveryFocus.pick_slot slot slot_injective 1
    | exact RecoveryFocus.pick_slot slot slot_injective 2
    | exact RecoveryFocus.pick_slot slot slot_injective 3
    | exact RecoveryFocus.pick_slot slot slot_injective 4
    | exact RecoveryFocus.pick_slot slot slot_injective 5
    | simp [RecoveryFocus.pick,slot]
  all_goals intro j; fin_cases j <;> decide
noncomputable def machine := RecoveryFocus.machine slot RangeMachine.machine

noncomputable def input {a : ℕ} (base : Configuration 11 a) : Configuration 14 states :=
  ⟨machine.start,
    fun i => Fin.addCases base.heads (fun _ : Fin 3 => 0) i,
    fun i => Fin.addCases base.tapes ![[],[false],[]] i⟩
noncomputable def output {a : ℕ} (base : Configuration 11 a) (pre bits bound : List Bool) :
    Configuration 14 states :=
  ⟨RecoveryCalls.controlCode RangeMachine.sizes none,
    fun i => if i=0 then pre.length+2*bound.length else (input base).heads i,
    fun i => if i=11 then frame (bits.take bound.length) else if i=12 then [true]
      else if i=13 then List.replicate (2*bound.length+1) false else (input base).tapes i⟩

structure Entry {a : ℕ} (base : Configuration 11 a) (pre bits bound : List Bool) : Prop where
  codeHead : base.heads 0=pre.length
  codeTape : base.tapes 0=pre++frame bits
  boundHead : base.heads 7=0
  boundTape : base.tapes 7=frame bound
  widthHead : base.heads 10=1
  widthTape : base.tapes 10=CompareMachine.word bound.length

theorem focused_input {a : ℕ} (base : Configuration 11 a) (pre bits bound : List Bool)
    (h : Entry base pre bits bound) :
    RecoveryFocus.config slot (input base).heads (input base).tapes
      (controlConfig (RecoveryCalls.code RangeMachine.sizes 0)
        (RangeMachine.fieldInput (pre++frame bits) [] bound pre.length bound.length 0))=input base := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,controlConfig,
      RangeMachine.fieldInput,RangeMachine.heads,Fin.addCases,h.codeHead,h.boundHead,h.widthHead]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,controlConfig,
      RangeMachine.fieldInput,RangeMachine.store,Fin.addCases,h.codeTape,h.boundTape,h.widthTape,
      CompareMachine.word]

theorem focused_output {a : ℕ} (base : Configuration 11 a) (pre bits bound : List Bool)
    (h : Entry base pre bits bound) :
    RecoveryFocus.config slot (input base).heads (input base).tapes
      (RecoveryCalls.stopped RangeMachine.sizes (RangeMachine.heads (pre.length+2*bound.length))
        (RangeMachine.store (pre++frame bits) (frame (bits.take bound.length)) bound bound.length
          (2*bound.length+1) true))=output base pre bits bound := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,output,RecoveryCalls.stopped,
      RangeMachine.heads,Fin.addCases,h.boundHead,h.widthHead]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,output,RecoveryCalls.stopped,
      RangeMachine.store,Fin.addCases,h.codeTape,h.boundTape,h.widthTape,CompareMachine.word]

theorem start_layout {a : ℕ} (base : Configuration 11 a) (pre bits bound : List Bool)
    (h : Entry base pre bits bound) :
    ∃ r, runFrom machine (8*bound.length+10) (input base)=some r ∧
      r.steps≤8*bound.length+10 ∧
      r.final.scanned 12=decide (RecordMachine.rangeValid bits bound) ∧
      (RecordMachine.rangeValid bits bound → r.final=output base pre bits bound) := by
  obtain ⟨r,hr,hs,hbit,hgood⟩ := RangeMachine.range_checked pre bits [] bound (by simp)
  obtain ⟨f,hfRun,hff,hfs⟩ := RecoveryFocus.run_config slot slot_injective RangeMachine.machine
    (input base).heads (input base).tapes _ _ r hr
  rw [focused_input base pre bits bound h] at hfRun
  refine ⟨f,hfRun,by omega,?_,?_⟩
  · rw [hff]
    simpa [Configuration.scanned,RecoveryFocus.config,slot_pick] using hbit
  · intro hv
    rw [hff,hgood hv,focused_output base pre bits bound h]

def headerPrefix (t s : ℕ) := Streaming.marks (HeaderMachine.word t s [])
theorem header_source {word fields : List Bool} {t s : ℕ}
    (h : HeaderMachine.parts word=some (t,s,fields)) :
    frame word=headerPrefix t s++frame fields ∧ (headerPrefix t s).length=2*t+2*s+4 := by
  have he := HeaderMachine.parts_decomposition h
  have hw : HeaderMachine.word t s fields=HeaderMachine.word t s []++fields := by
    simp [HeaderMachine.word,List.append_assoc]
  constructor
  · rw [he,hw]
    exact Streaming.frame_append _ _
  · simp [headerPrefix,Streaming.marks_length,HeaderMachine.word]
    omega

end NearCubicWires.RepairSource.VerifierDecoding.StartLayout
