import Proof.PCP.ProjectionNormalizationCounter
import Proof.Amplification.RecoveryUnpairCode

/-! Actual clause-count parsing followed by the complete cold keep-last
producer. The serializer count is produced from the source bytes. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Clauses
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 13 → Fin 18 := ![0,7,8,5,9,10,11,12,13,14,15,16,17]
noncomputable def first := TapeEmbedding.machine 11 ValueField.machine
noncomputable def second := RecoveryFocus.machine slots DedupReady.machine
noncomputable def machine := Composition.machine first second
noncomputable def entry (source : List Bool) (pos : ℕ) :=
  Composition.leftConfig (2+(Dedup.bodySize+2)+2+2) (TapeEmbedding.config (fun _ : Fin 11 => 0) (fun _ : Fin 11 => [])
    (ValueField.input ValueField.machine.start source pos))
def budget (rows : List SuffixScan.Clause) := ValueField.budget rows.length.bits+1+DedupReady.budget rows

theorem rows_run (pre : List Bool) (rows : List SuffixScan.Clause) :
    ∃ r,runFrom machine (budget rows)
      (entry (pre++frame rows.length.bits++SuffixScan.stream rows) pre.length)=some r ∧
      r.steps ≤ budget rows ∧ r.final.tapes 8=SuffixScan.stream rows.dedup ∧
      r.final.tapes 16=CompareMachine.word rows.dedup.length ∧
      r.final.heads 8=0 ∧ r.final.heads 16=1 := by
  obtain ⟨base,hbase,hsource,hcount,hheads,hsteps⟩ := ValueField.value_field_run pre rows.length.bits (SuffixScan.stream rows)
  let a := TapeEmbedding.receipt (fun _ : Fin 11 => 0) (fun _ : Fin 11 => []) base
  have ha := TapeEmbedding.run_embed ValueField.machine (fun _ : Fin 11 => 0) (fun _ : Fin 11 => [])
    _ _ base hbase
  obtain ⟨localRun,hl,hls,hlo,hlc,hlh,hlk⟩ := DedupReady.ready_run (pre++frame rows.length.bits) [] rows
  obtain ⟨b,hb,hbf,hbs⟩ := RecoveryFocus.run_config slots (by decide) DedupReady.machine
    a.final.heads a.final.tapes _ _ localRun hl
  have he : RecoveryFocus.config slots a.final.heads a.final.tapes
      (DedupReady.entry ((pre++frame rows.length.bits)++SuffixScan.stream rows++[]) (pre++frame rows.length.bits).length rows.length)=
      Composition.restart a.final second.start := by
    apply TransitionEvent.focused_eq slots (by decide) (Composition.restart a.final second.start)
    · rfl
    · intro i; fin_cases i
      · have hh := hheads 0
        simpa [a,TapeEmbedding.receipt,TapeEmbedding.config,Composition.restart,slots,
          DedupReady.entry,Composition.leftConfig,Rewind.recording,Rewind.config,DedupCold.entry,
          frame_length,List.length_append,Fin.addCases,Nat.add_assoc] using hh.symm
      · rfl
      · rfl
      · have hh := hheads 5
        simpa [a,TapeEmbedding.receipt,TapeEmbedding.config,Composition.restart,slots,
          DedupReady.entry,Composition.leftConfig,Rewind.recording,Rewind.config,DedupCold.entry,Fin.addCases] using hh.symm
      all_goals rfl
    · intro i; fin_cases i
      · simpa [a,TapeEmbedding.receipt,TapeEmbedding.config,Composition.restart,slots,
          DedupReady.entry,Composition.leftConfig,Rewind.recording,Rewind.config,DedupCold.entry,Fin.addCases] using hsource.symm
      · rfl
      · rfl
      · simpa [a,TapeEmbedding.receipt,TapeEmbedding.config,Composition.restart,slots,
          DedupReady.entry,Composition.leftConfig,Rewind.recording,Rewind.config,DedupCold.entry,
          Fin.addCases,RecoveryUnpair.bits_value] using hcount.symm
      all_goals rfl
    · intro i _; rfl
    · intro i _; rfl
  rw [he] at hb
  have h := Composition.run_join first second _ _ _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_,?_,?_⟩
  · change base.steps+1+b.steps ≤ _
    dsimp only [budget]
    omega
  · change b.final.tapes (slots 2)=_
    rw [hbf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)] using hlo
  · change b.final.tapes (slots 11)=_
    rw [hbf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)] using hlc
  · change b.final.heads (slots 2)=_
    rw [hbf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)] using hlh
  · change b.final.heads (slots 11)=_
    rw [hbf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)] using hlk

end NearCubicWires.RepairSource.ProjectionNormalization.Clauses
