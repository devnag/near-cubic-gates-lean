import Proof.MachineModel.OrdinaryTransitionTag

/-! One claimed scan bit and one literal action tag become the physical
read/after/move flags consumed by event emission and the checked head update. -/
namespace NearCubicWires.RepairOrdinary.ClaimedAction
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (scans : List Bool) (cursor : ℕ)
    (read oldAfter oldLow oldHigh : Bool) : Configuration 6 s :=
  TapeEmbedding.config (fun _ : Fin 1 => cursor) (fun _ : Fin 1 => scans)
    (TransitionTag.cfg q source pos read oldAfter oldLow oldHigh)

def scanner : Machine 6 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits => if q.val=0 then
      some ⟨1,fun _ => none,fun i => if i.val=5 then .right else .stay⟩
    else if q.val=1 then
      some ⟨2,fun i => if i.val=1 then some (bits 5) else none,
        fun i => if i.val=5 then .right else .stay⟩
    else none

theorem marker_step (source : List Bool) (pos : ℕ) (scans : List Bool) (cursor : ℕ)
    (read a lo hi : Bool) :
    step scanner (cfg 0 source pos scans cursor read a lo hi)=
      some (cfg 1 source pos scans (cursor+1) read a lo hi) := by
  simp [step,scanner,cfg,TransitionTag.cfg,TapeEmbedding.config,Fin.addCases]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem payload_step (source : List Bool) (pos : ℕ) (pre tail : List Bool)
    (bit read a lo hi : Bool) :
    step scanner (cfg 1 source pos (pre++true::bit::tail) (pre.length+1) read a lo hi)=
      some (cfg 2 source pos (pre++true::bit::tail) (pre.length+2) bit a lo hi) := by
  have hb : readTapeBit (pre++true::bit::tail) (pre.length+1)=bit := by
    simpa [List.append_assoc] using Streaming.read_append (pre++[true]) tail bit
  simp [step,scanner,cfg,TransitionTag.cfg,TapeEmbedding.config,Fin.addCases,Configuration.scanned,hb]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,writeTapeBit]

theorem scan_run (source : List Bool) (pos : ℕ) (pre tail : List Bool)
    (bit read a lo hi : Bool) :
    ∃ r : ExecutionReceipt 6 3,
      runFrom scanner 2 (cfg 0 source pos (pre++true::bit::tail) pre.length read a lo hi)=some r ∧
      r.final=cfg 2 source pos (pre++true::bit::tail) (pre.length+2) bit a lo hi ∧ r.steps=2 := by
  have hm := Timed.single (by rfl : scanner.halted (0 : Fin 3)=false)
    (marker_step source pos (pre++true::bit::tail) pre.length read a lo hi)
  have hp := Timed.single (by rfl : scanner.halted (1 : Fin 3)=false)
    (payload_step source pos pre tail bit read a lo hi)
  exact (hm.trans hp).run (by rfl)

noncomputable def tagger := TapeEmbedding.machine 1 TransitionTag.machine
noncomputable def machine := Composition.machine scanner tagger

theorem action_run (tagPre tagTail scanPre scanTail : List Bool) (bits : TagMachine.Word)
    (bit read a lo hi : Bool) :
    let source := tagPre++Streaming.marks (TagMachine.tagWord bits)++tagTail
    let scans := scanPre++true::bit::scanTail
    ∃ r : ExecutionReceipt 6 (3+Fintype.card (RecoveryCalls.Control TransitionTag.sizes)),
      runFrom machine 14 (cfg machine.start source tagPre.length scans scanPre.length read a lo hi)=some r ∧
      r.final=cfg ((RecoveryCalls.controlCode TransitionTag.sizes none).natAdd 3)
        source (tagPre.length+8) scans (scanPre.length+2)
        bit (TransitionTag.after bits bit) (bits 2) (bits 3) ∧ r.steps=14 := by
  let source := tagPre++Streaming.marks (TagMachine.tagWord bits)++tagTail
  let scans := scanPre++true::bit::scanTail
  obtain ⟨first,hf,hff,hfs⟩ := scan_run source tagPre.length scanPre scanTail bit read a lo hi
  obtain ⟨last,hl,hlf,hls⟩ := TransitionTag.tag_run tagPre tagTail bits bit a lo hi
  have he := TapeEmbedding.run_embed TransitionTag.machine
    (fun _ : Fin 1 => scanPre.length+2) (fun _ : Fin 1 => scans) _ _ last hl
  let endRun := TapeEmbedding.receipt
    (fun _ : Fin 1 => scanPre.length+2) (fun _ : Fin 1 => scans) last
  have hmid : Composition.restart first.final tagger.start =
      cfg tagger.start source tagPre.length scans (scanPre.length+2) bit a lo hi := by
    rw [hff]
    rfl
  have htag : runFrom tagger 11 (Composition.restart first.final tagger.start)=some endRun := by
    rw [hmid]
    exact he
  have hj := Composition.run_join scanner tagger 2 11 _ first endRun hf htag
  refine ⟨Composition.joinedReceipt first endRun,hj,?_,?_⟩
  · simp only [Composition.joinedReceipt,Composition.rightConfig,endRun,TapeEmbedding.receipt,hlf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  · simp only [Composition.joinedReceipt,endRun,TapeEmbedding.receipt,hfs,hls]

end NearCubicWires.RepairOrdinary.ClaimedAction
