import Proof.PCP.VerifierDecodingRange

/-! Truncation is rejected by the same finite state-index validator before any
binary comparison. The valid-width branch is connected to the literal state
count field produced by BitWidthMachine.state_width_run. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RangeMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution RadixSemantics StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rejected (source bits backing bound : List Bool) (pos width capacity : ℕ) : Configuration 6 6 :=
  ⟨5,![pos,2*bits.length,bits.length+1,0,0,0],
    store source (overlay (Streaming.marks bits) backing) bound width capacity false⟩

theorem reject_layout (pre bits backing bound : List Bool) (width capacity : ℕ)
    (hw : bits.length < width) (hb : backing.length ≤ 2*width+1) :
    ∃ receipt : ExecutionReceipt 6 6,
      runFrom fieldProgram (2*bits.length+1)
        (fieldInput (pre++frame bits) backing bound pre.length width capacity) = some receipt ∧
      receipt.final = rejected (pre++frame bits) bits backing bound (pre.length+2*bits.length) width capacity ∧
      receipt.steps = 2*bits.length+1 := by
  obtain ⟨r,hr,hf,hs,_⟩ := FieldMachine.field_reject_run pre bits backing width hw hb
  let eh : Fin 3 → ℕ := fun _ => 0
  let et : Fin 3 → List Bool := ![frame bound,[false],List.replicate capacity false]
  have hp := TapeEmbedding.run_embed FieldMachine.machine eh et _ _ r hr
  let result := TapeEmbedding.receipt eh et r
  have hi : TapeEmbedding.config eh et (FieldMachine.scan 0 (pre++frame bits) pre.length width 0 [] backing) =
      fieldInput (pre++frame bits) backing bound pre.length width capacity := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,FieldMachine.scan,fieldInput,store,et,Fin.addCases,overlay]
  rw [hi] at hp
  refine ⟨result,hp,?_,hs⟩
  apply configuration_ext
  · change r.final.control = 5
    simp [hf,FieldMachine.scan]
  · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,hf,
      FieldMachine.scan,rejected,eh,Fin.addCases,Streaming.marks_length]
  · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,hf,
      FieldMachine.scan,rejected,store,et,Fin.addCases]

theorem range_reject_run (pre bits backing bound : List Bool) (width capacity : ℕ)
    (hw : bits.length < width) (hb : backing.length ≤ 2*width+1) :
    let output := rejected (pre++frame bits) bits backing bound (pre.length+2*bits.length) width capacity
    ∃ receipt,
      runFrom machine (2*bits.length+2)
        (controlConfig (RecoveryCalls.code sizes 0)
          (fieldInput (pre++frame bits) backing bound pre.length width capacity)) = some receipt ∧
      receipt.final = RecoveryCalls.stopped sizes output.heads output.tapes ∧ receipt.steps = 2*bits.length+2 := by
  dsimp only
  obtain ⟨r,hr,hf,hs⟩ := reject_layout pre bits backing bound width capacity hw hb
  have hp := prefix_of_run fieldProgram _ _ r hr
  have hbody := RecoveryCalls.body_timed sizes programs 0 next 0 ⟨r.peakTapeCells,hp.1⟩
  have hstop := RecoveryCalls.stop_step sizes programs 0 next 0 r.final hp.2 (by simp [hf,rejected,next])
  rw [hf,hs] at hbody
  rw [hf] at hstop
  have hj := hbody.trans (Timed.single (by simp [RecoveryCalls.machine,RecoveryCalls.code,controlConfig]) hstop)
  have he : 2*bits.length+1+1=2*bits.length+2 := by omega
  rw [he] at hj
  exact hj.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])

/-- Literal decoded indices are tested against s, with the exact fixed-width
encoding supplied by the already executed state-width preparation. -/
theorem state_index_run (pre bits tail backing : List Bool) (s capacity : ℕ)
    (hw : bits.length = natBitLength s) (hb : backing.length ≤ 2*bits.length+1) :
    let bound := VerifierEncoding.fixedBits (natBitLength s) s
    let source := pre++Streaming.marks bits++tail
    ∃ receipt,
      runFrom machine (8*bits.length+10)
        (controlConfig (RecoveryCalls.code sizes 0) (fieldInput source backing bound pre.length bits.length capacity)) = some receipt ∧
      receipt.final = RecoveryCalls.stopped sizes (heads (pre.length+2*bits.length))
        (store source (frame bits) bound bits.length (max capacity (2*bits.length+1))
          (decide (value bits < s))) ∧ receipt.steps = 8*bits.length+10 := by
  dsimp only
  have hv := fixedBits_value (natBitLength s) s (Nat.lt_pow_succ_log_self (by decide) s)
  simpa only [hv] using range_run pre bits tail backing (VerifierEncoding.fixedBits (natBitLength s) s) capacity hb
    (by simp [hw])

end NearCubicWires.RepairSource.VerifierDecoding.RangeMachine
