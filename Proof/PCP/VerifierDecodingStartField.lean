import Proof.PCP.VerifierDecodingDimensions

/-! All-input start-state field validation using the same six-tape range
machine. The field output, flag and comparison workspace begin blank; the
binary bound and unary width are the actual preceding dimension outputs. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RangeMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem range_checked (pre bits backing bound : List Bool)
    (hb : backing.length≤2*bound.length+1) :
    ∃ r, runFrom machine (8*bound.length+10)
        (controlConfig (RecoveryCalls.code sizes 0)
          (fieldInput (pre++frame bits) backing bound pre.length bound.length 0))=some r ∧
      r.steps≤8*bound.length+10 ∧
      r.final.scanned 4=decide (RecordMachine.rangeValid bits bound) ∧
      (RecordMachine.rangeValid bits bound → r.final=RecoveryCalls.stopped sizes
        (heads (pre.length+2*bound.length))
        (store (pre++frame bits) (frame (bits.take bound.length)) bound bound.length
          (2*bound.length+1) true)) := by
  by_cases hlen : bound.length≤bits.length
  · have ht : (bits.take bound.length).length=bound.length := by simp [Nat.min_eq_left hlen]
    obtain ⟨r,hr,hf,hs⟩ := range_run pre (bits.take bound.length) (frame (bits.drop bound.length))
      backing bound 0 (by simpa only [ht] using hb) ht.symm
    have he : pre++Streaming.marks (bits.take bound.length)++frame (bits.drop bound.length)=
        pre++frame bits := by
      rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    rw [he] at hr hf
    rw [ht] at hr hf hs
    refine ⟨r,hr,by omega,?_,?_⟩
    · simp [hf,Configuration.scanned,RecoveryCalls.stopped,heads,store,
        RecordMachine.rangeValid,hlen,readTapeBit,List.getD]
    · intro hv
      simpa [hv.2] using hf
  · obtain ⟨r,hr,hf,hs⟩ := range_reject_run pre bits backing bound bound.length 0 (by omega) hb
    have htime : 2*bits.length+2≤8*bound.length+10 := by omega
    have hm := runFrom_moreFuel machine (2*bits.length+2) (8*bound.length+10-(2*bits.length+2)) _ r hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨r,hm,by omega,?_,by simp [RecordMachine.rangeValid,hlen]⟩
    simp [hf,Configuration.scanned,RecoveryCalls.stopped,rejected,store,
      RecordMachine.rangeValid,hlen,readTapeBit,List.getD]

def flagCapacity : Fin 6 → ℕ := ![0,0,0,0,1,0]
noncomputable def blankStart (pre bits bound : List Bool) :=
  controlConfig (RecoveryCalls.code sizes 0)
    (⟨fieldProgram.start,heads pre.length,
      ![pre++frame bits,[],CompareMachine.word bound.length,frame bound,[],[]]⟩ : Configuration 6 6)

theorem start_run (pre bits bound : List Bool) :
    ∃ r, runFrom machine (8*bound.length+10) (blankStart pre bits bound)=some r ∧
      r.steps≤8*bound.length+10 ∧
      r.final.scanned 4=decide (RecordMachine.rangeValid bits bound) ∧
      (RecordMachine.rangeValid bits bound → ZeroPadding.config flagCapacity r.final=
        RecoveryCalls.stopped sizes (heads (pre.length+2*bound.length))
          (store (pre++frame bits) (frame (bits.take bound.length)) bound bound.length
            (2*bound.length+1) true)) := by
  obtain ⟨base,hr,hs,hbit,hgood⟩ := range_checked pre bits [] bound (by simp)
  have hi : ZeroPadding.config flagCapacity (blankStart pre bits bound)=
      controlConfig (RecoveryCalls.code sizes 0)
        (fieldInput (pre++frame bits) [] bound pre.length bound.length 0) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,flagCapacity,blankStart,
        controlConfig,fieldInput,store,CompareMachine.word,ZeroPadding.pad]
  rw [←hi] at hr
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_unpad machine flagCapacity _ _ base hr
  refine ⟨r,hrun,by omega,?_,?_⟩
  · rw [←ZeroPadding.scanned_config flagCapacity r.final,hf]
    exact hbit
  · intro hv
    exact hf.trans (hgood hv)

end NearCubicWires.RepairSource.VerifierDecoding.RangeMachine
