import Proof.PCP.VerifierDecodingRecordEntry

/-! The state-index branch is consumed on the record validator's literal
eight tapes. Truncated/invalid fields expose a physical false flag; only a
successful range test requires the reusable complete endpoint. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem range_full (pre field tail backing bound : List Bool) (t cap : ℕ)
    (hw : bound.length=field.length) (hb : backing.length≤2*field.length+1)
    (hc : 2*field.length+1≤cap) :
    let source := pre++Streaming.marks field++tail
    ∃ r,
      runFrom rangeProgram (8*field.length+10)
        (cfg rangeProgram.start source backing bound pre.length field.length t cap false false)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode RangeMachine.sizes none)
        source (frame field) bound (pre.length+2*field.length) field.length t cap
        (decide (value field<value bound)) false ∧ r.steps=8*field.length+10 := by
  obtain ⟨base,hr,hf,hs⟩ := RangeMachine.range_run pre field tail backing bound cap hb hw
  let eh : Fin 2 → ℕ := ![1,0]
  let et : Fin 2 → List Bool := ![CompareMachine.word t,[false]]
  have he := TapeEmbedding.run_embed RangeMachine.machine eh et _ _ base hr
  have hi : TapeEmbedding.config eh et
      (controlConfig (RecoveryCalls.code RangeMachine.sizes 0)
        (RangeMachine.fieldInput (pre++Streaming.marks field++tail) backing bound pre.length field.length cap)) =
      cfg rangeProgram.start (pre++Streaming.marks field++tail) backing bound pre.length field.length t cap false false := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,controlConfig,RangeMachine.fieldInput,
        RangeMachine.heads,cfg,eh,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,controlConfig,RangeMachine.fieldInput,
        RangeMachine.store,cfg,et,Fin.addCases]
  refine ⟨TapeEmbedding.receipt eh et base,?_,?_,hs⟩
  · rw [← hi]
    exact he
  · simp only [TapeEmbedding.receipt,hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,RecoveryCalls.stopped,RangeMachine.heads,cfg,eh,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,RecoveryCalls.stopped,RangeMachine.store,cfg,et,Fin.addCases,
        max_eq_left hc]

theorem range_short (pre bits backing bound : List Bool) (t cap : ℕ)
    (hw : bits.length<bound.length) (hb : backing.length≤2*bound.length+1) :
    ∃ r,
      runFrom rangeProgram (2*bits.length+2)
        (cfg rangeProgram.start (pre++frame bits) backing bound pre.length bound.length t cap false false)=some r ∧
      r.final.scanned 4=false ∧ r.final.tapes 7=[false] ∧ r.steps=2*bits.length+2 := by
  obtain ⟨base,hr,hf,hs⟩ := RangeMachine.range_reject_run pre bits backing bound bound.length cap hw hb
  let eh : Fin 2 → ℕ := ![1,0]
  let et : Fin 2 → List Bool := ![CompareMachine.word t,[false]]
  have he := TapeEmbedding.run_embed RangeMachine.machine eh et _ _ base hr
  have hi : TapeEmbedding.config eh et
      (controlConfig (RecoveryCalls.code RangeMachine.sizes 0)
        (RangeMachine.fieldInput (pre++frame bits) backing bound pre.length bound.length cap)) =
      cfg rangeProgram.start (pre++frame bits) backing bound pre.length bound.length t cap false false := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,controlConfig,RangeMachine.fieldInput,
        RangeMachine.heads,cfg,eh,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,controlConfig,RangeMachine.fieldInput,
        RangeMachine.store,cfg,et,Fin.addCases]
  refine ⟨TapeEmbedding.receipt eh et base,?_,?_,?_,hs⟩
  · rw [← hi]
    exact he
  · simp [TapeEmbedding.receipt,hf,TapeEmbedding.config,RecoveryCalls.stopped,RangeMachine.rejected,
      RangeMachine.store,Configuration.scanned,readTapeBit,List.getD,Fin.addCases]
  · rfl

def rangeValid (bits bound : List Bool) : Prop :=
  bound.length≤bits.length ∧ value (bits.take bound.length)<value bound
instance (bits bound : List Bool) : Decidable (rangeValid bits bound) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem range_checked (pre bits backing bound : List Bool) (t cap : ℕ)
    (hb : backing.length≤2*bound.length+1) (hc : 2*bound.length+1≤cap) :
    ∃ r,
      runFrom rangeProgram (8*bound.length+10)
        (cfg rangeProgram.start (pre++frame bits) backing bound pre.length bound.length t cap false false)=some r ∧
      r.steps≤8*bound.length+10 ∧ r.final.tapes 7=[false] ∧
      r.final.scanned 4=decide (rangeValid bits bound) ∧
      (rangeValid bits bound → r.final=cfg (RecoveryCalls.controlCode RangeMachine.sizes none)
        (pre++frame bits) (frame (bits.take bound.length)) bound (pre.length+2*bound.length)
        bound.length t cap true false) := by
  by_cases hlen : bound.length≤bits.length
  · have ht : (bits.take bound.length).length=bound.length := by simp [Nat.min_eq_left hlen]
    obtain ⟨r,hr,hf,hs⟩ := range_full pre (bits.take bound.length) (frame (bits.drop bound.length))
      backing bound t cap ht.symm (by simpa only [ht] using hb) (by simpa only [ht] using hc)
    have he : pre++Streaming.marks (bits.take bound.length)++frame (bits.drop bound.length)=pre++frame bits := by
      rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    rw [he] at hr hf
    rw [ht] at hr hf hs
    refine ⟨r,hr,by omega,?_,?_,?_⟩
    · simp [hf,cfg]
    · simp [hf,cfg,Configuration.scanned,rangeValid,hlen,readTapeBit,List.getD]
    · intro hv
      have hv' := hv.2
      simpa [hv'] using hf
  · obtain ⟨r,hr,hflag,hresult,hs⟩ := range_short pre bits backing bound t cap
      (by omega) hb
    have htime : 2*bits.length+2≤8*bound.length+10 := by omega
    have hm := runFrom_moreFuel rangeProgram (2*bits.length+2) (8*bound.length+10-(2*bits.length+2)) _ r hr
    rw [Nat.add_sub_of_le htime] at hm
    exact ⟨r,hm,by omega,hresult,by simpa [rangeValid,hlen] using hflag,by simp [rangeValid,hlen]⟩

end NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
