import Proof.Amplification.RecoveryRowStructureCopyRun

/-! Execute an existing local row-core call while preserving the actual
outer witness cursor and width-driver head. Both tape embeddings are
interpreter steps of the same ordinary program and add no semantic oracle. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def onCore {s : Nat} (p : Machine 46 s) := TapeEmbedding.machine 1 (TapeEmbedding.machine 5 p)

theorem core_run {s n : Nat} (p : Machine 46 s) (d out : Data) (capacity : Nat)
    (h : ReadyRun p n d.left out.left) (ht : out.right=d.right) (hh : out.rightHeads=d.rightHeads) :
    ∃ r,runFrom (onCore p) n (cfg d capacity p.start)=some r ∧
      r.final=cfg out capacity r.final.control ∧ r.steps=n := by
  obtain ⟨base,hr,htapes,hheads,hsteps⟩ := h
  let middle := TapeEmbedding.receipt d.rightHeads d.right base
  have hmiddle := TapeEmbedding.run_embed p d.rightHeads d.right n _ base hr
  have hfmiddle : middle.final=out.cfg base.final.control := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=46) (n:=5) (fun j=>?_) (fun j=>?_) i
      · simpa only [middle,TapeEmbedding.receipt,TapeEmbedding.config,Data.cfg,Fin.addCases_left] using hheads j
      · simpa only [middle,TapeEmbedding.receipt,TapeEmbedding.config,Data.cfg,Fin.addCases_right] using (congrFun hh j).symm
    · funext i
      refine Fin.addCases (m:=46) (n:=5) (fun j=>?_) (fun j=>?_) i
      · simpa only [middle,TapeEmbedding.receipt,TapeEmbedding.config,Data.cfg,Fin.addCases_left] using congrFun htapes j
      · simpa only [middle,TapeEmbedding.receipt,TapeEmbedding.config,Data.cfg,Fin.addCases_right] using (congrFun ht j).symm
  let result := TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate capacity false) middle
  have hall := TapeEmbedding.run_embed (TapeEmbedding.machine 5 p)
    (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate capacity false) n _ middle hmiddle
  have hinput : TapeEmbedding.config (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate capacity false)
      (TapeEmbedding.config d.rightHeads d.right (initialConfiguration p d.left))=cfg d capacity p.start := by rfl
  rw [hinput] at hall
  refine ⟨result,hall,?_,hsteps⟩
  change TapeEmbedding.config (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate capacity false) middle.final=_
  rw [hfmiddle]
  rfl

noncomputable def decodeCore := TapeEmbedding.machine 4 (TapeEmbedding.machine 14 (RecoveryLiteralDecode.machine 0))
noncomputable def decodeMachine := onCore decodeCore

def decoded (d : Data) (bits : List Bool) : Data :=
  {d with state:=RecoveryLiteralDecode.decodedState d.state 0 bits}

theorem decode_core_ready (d : Data) (bits : List Bool) (hd : d.state.Valid)
    (hw : bits.length=d.state.bits.length) (hf : d.state.fields 0=frame bits) :
    ReadyRun decodeCore (RecoveryDecodeStep.time bits) d.left (decoded d bits).left := by
  have h := RecoveryLiteralDecode.literal_ready d.state 0 bits hd hw hf
  rw [RecoveryLiteralDecode.decoded_output d.state 0 bits hw] at h
  exact (h.embed (d.extra.tapes d.state)).embed (RecoveryRowLeaf.extra d.kind d.flags)

theorem decoded_valid (d : Data) (bits word : List Bool) (hd : d.Valid word)
    (hw : bits.length=d.state.bits.length) : (decoded d bits).Valid word := by
  refine ⟨RecoveryLiteralDecode.decoded_valid d.state 0 bits hd.1 hw,?_,hd.2.2⟩
  exact ⟨hd.2.1.source,hd.2.1.row,hd.2.1.counter,hd.2.1.count,hd.2.1.committed,
    hd.2.1.cap,hd.2.1.prefixBound,hd.2.1.reset.trans (Nat.le_max_left _ _)⟩

theorem decode_run (d : Data) (capacity : Nat) (bits word : List Bool) (hd : d.Valid word)
    (hw : bits.length=d.state.bits.length) (hf : d.state.fields 0=frame bits) :
    ∃ r,runFrom decodeMachine (RecoveryDecodeStep.time bits) (cfg d capacity decodeMachine.start)=some r ∧
      r.final=cfg (decoded d bits) capacity r.final.control ∧ r.steps=RecoveryDecodeStep.time bits ∧
      (decoded d bits).Valid word := by
  obtain ⟨r,hr,hf,hs⟩ := core_run decodeCore d (decoded d bits) capacity
    (decode_core_ready d bits hd.1 hw hf) rfl rfl
  exact ⟨r,hr,hf,hs,decoded_valid d bits word hd hw⟩

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
