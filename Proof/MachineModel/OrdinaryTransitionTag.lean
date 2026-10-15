import Proof.PCP.VerifierDecodingTag
import Proof.MachineModel.OrdinaryHeadUpdate

/-! The actual four-bit rule reader feeds physical after/move flags in eleven
transitions. Its source cursor keeps advancing; no source or event rewind. -/
namespace NearCubicWires.RepairOrdinary.TransitionTag
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Word := TagMachine.Word
noncomputable def wordCode : Word ≃ Fin (Fintype.card Word) := Fintype.equivFin _
def after (bits : Word) (read : Bool) : Bool := if bits 0 then bits 1 else read
def cfg {s : ℕ} (q : Fin s) (source : List Bool) (cursor : ℕ)
    (read oldAfter oldLow oldHigh : Bool) : Configuration 5 s :=
  ⟨q,![cursor,0,0,0,0],![source,[read],[oldAfter],[oldLow],[oldHigh]]⟩
def setter (bits : Word) : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q scan => if q.val=0 then
    some ⟨1,![none,none,some (after bits (scan 1)),some (bits 2),some (bits 3)],fun _ => .stay⟩
    else none
noncomputable def reader := TapeEmbedding.machine 4 (TagMachine.machine 4)
abbrev sizes : Fin (Fintype.card Word+1) → ℕ
  | ⟨0,_⟩ => Fintype.card TagMachine.Control
  | ⟨_+1,_⟩ => 2
instance sizes_nonzero (j : Fin (Fintype.card Word+1)) : NeZero (sizes j) := by
  obtain ⟨n,hn⟩ := j
  cases n
  · refine ⟨?_⟩
    change Fintype.card TagMachine.Control ≠ 0
    exact Fintype.card_ne_zero
  · refine ⟨?_⟩
    change 2 ≠ 0
    decide
noncomputable def programs : (j : Fin (Fintype.card Word+1)) → Machine 5 (sizes j)
  | ⟨0,_⟩ => reader
  | ⟨n+1,h⟩ => setter (wordCode.symm ⟨n,by omega⟩)
noncomputable def next :
    (j : Fin (Fintype.card Word+1)) → Fin (sizes j) → (Fin 5 → Bool) →
      Option (Fin (Fintype.card Word+1))
  | ⟨0,_⟩,q,_ => match TagMachine.code.symm q with
    | none => none
    | some (_,bits) => some (wordCode bits).succ
  | ⟨_+1,_⟩,_,_ => none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem setter_step (bits : Word) (source : List Bool) (cursor : ℕ)
    (read oldAfter oldLow oldHigh : Bool) :
    step (setter bits) (cfg 0 source cursor read oldAfter oldLow oldHigh) =
      some (cfg 1 source cursor read (after bits read) (bits 2) (bits 3)) := by
  simp [step,setter,cfg,Configuration.scanned,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [applyAction,writeTapeBit]

theorem tag_run (pre tail : List Bool) (bits : Word) (read oldAfter oldLow oldHigh : Bool) :
    let source := pre++Streaming.marks (TagMachine.tagWord bits)++tail
    ∃ r : ExecutionReceipt 5 (Fintype.card (RecoveryCalls.Control sizes)),
      runFrom machine 11 (cfg machine.start source pre.length read oldAfter oldLow oldHigh)=some r ∧
      r.final=RecoveryCalls.stopped sizes ![pre.length+8,0,0,0,0]
        ![source,[read],[after bits read],[bits 2],[bits 3]] ∧ r.steps=11 := by
  let source := pre++Streaming.marks (TagMachine.tagWord bits)++tail
  let extra : Fin 4 → List Bool := ![[read],[oldAfter],[oldLow],[oldHigh]]
  obtain ⟨base,hbase,hfinal,hsteps,_⟩ := TagMachine.tag_run pre tail bits true
  have he := TapeEmbedding.run_embed (TagMachine.machine 4) (fun _ : Fin 4 => 0) extra _ _ base hbase
  let emb := TapeEmbedding.receipt (fun _ : Fin 4 => 0) extra base
  have hin : TapeEmbedding.config (fun _ : Fin 4 => 0) extra
      (TagMachine.cfg 0 (fun _ => false) source pre.length) =
      cfg reader.start source pre.length read oldAfter oldLow oldHigh := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,TagMachine.cfg,cfg,extra,Fin.addCases]
  have hend : emb.final=cfg (TagMachine.code (some (8,bits))) source (pre.length+8)
      read oldAfter oldLow oldHigh := by
    simp only [emb,TapeEmbedding.receipt,hfinal]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,TagMachine.cfg,cfg,extra,Fin.addCases,source]
  have hrun : runFrom reader 8 (cfg reader.start source pre.length read oldAfter oldLow oldHigh)=some emb := by
    rw [← hin]
    exact he
  obtain ⟨hp,hh⟩ := prefix_of_run reader 8 _ emb hrun
  have hbody := RecoveryCalls.body_timed sizes programs 0 next 0 ⟨emb.peakTapeCells,hp⟩
  have hes : emb.steps=8 := hsteps
  rw [hes,hend] at hbody
  have hret := RecoveryCalls.return_step sizes programs 0 next 0 (wordCode bits).succ
    (cfg (TagMachine.code (some (8,bits))) source (pre.length+8) read oldAfter oldLow oldHigh)
    (by change (TagMachine.machine 4).halted (TagMachine.code (some (8,bits)))=true
        simp [TagMachine.machine])
    (by change (match TagMachine.code.symm (TagMachine.code (some (8,bits))) with
          | none => none | some (_,b) => some (wordCode b).succ)=some (wordCode bits).succ
        simp)
  have hs := setter_step bits source (pre.length+8) read oldAfter oldLow oldHigh
  have hs' : Timed (programs (wordCode bits).succ) 1
      (cfg 0 source (pre.length+8) read oldAfter oldLow oldHigh)
      (cfg 1 source (pre.length+8) read (after bits read) (bits 2) (bits 3)) := by
    change Timed (setter (wordCode.symm (wordCode bits))) 1 _ _
    rw [Equiv.symm_apply_apply]
    exact Timed.single (by rfl : (setter bits).halted (0 : Fin 2)=false) hs
  have hset := RecoveryCalls.body_timed sizes programs 0 next (wordCode bits).succ hs'
  have hstop := RecoveryCalls.stop_step sizes programs 0 next (wordCode bits).succ
    (cfg 1 source (pre.length+8) read (after bits read) (bits 2) (bits 3))
    (by simp [programs,Fin.succ,setter,cfg,sizes]) (by rfl)
  have hn0 : (machine.halted (RecoveryCalls.code sizes 0
      (TagMachine.code (some (8,bits)))))=false := by simp [machine,RecoveryCalls.machine,RecoveryCalls.code]
  have hn1 : (machine.halted (RecoveryCalls.code sizes (wordCode bits).succ 1))=false := by
    simp [machine,RecoveryCalls.machine,RecoveryCalls.code]
  have hmid : RecoveryCalls.restarted (programs (wordCode bits).succ)
      (cfg (TagMachine.code (some (8,bits))) source (pre.length+8) read oldAfter oldLow oldHigh).heads
      (cfg (TagMachine.code (some (8,bits))) source (pre.length+8) read oldAfter oldLow oldHigh).tapes =
      cfg 0 source (pre.length+8) read oldAfter oldLow oldHigh := by
    simp only [programs,Fin.succ]
    rfl
  have hret' := hret.trans (congrArg some
    (congrArg (controlConfig (RecoveryCalls.code sizes (wordCode bits).succ)) hmid))
  have h := ((hbody.trans (Timed.single hn0 hret')).trans hset).trans (Timed.single hn1 hstop)
  obtain ⟨r,hr,hf,ht⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  refine ⟨r,?_,hf,ht⟩
  exact hr

theorem after_write (bits : Word) (read : Bool) :
    after bits read=(decodeWrite [bits 0,bits 1]).getD read := by
  cases h0 : bits 0 <;> cases h1 : bits 1 <;>
    simp [after,decodeWrite,h0,h1]

theorem move_flags (bits : Word) (hv : TagMachine.valid true bits=true) :
    HeadUpdate.low (decodeMove [bits 2,bits 3])=bits 2 ∧
    HeadUpdate.high (decodeMove [bits 2,bits 3])=bits 3 := by
  cases h0 : bits 0 <;> cases h1 : bits 1 <;> cases h2 : bits 2 <;> cases h3 : bits 3 <;>
    simp_all [TagMachine.valid,decodeMove,HeadUpdate.low,HeadUpdate.high]

end NearCubicWires.RepairOrdinary.TransitionTag
