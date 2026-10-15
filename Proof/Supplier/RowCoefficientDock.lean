import Proof.Supplier.RowCoefficientLoopReset

/-! The actual loop endpoint supplies the seven normalization tapes. The
same normalizer accepts the physically retained zero padding in its flag
and magnitude slots; only its two output tapes are fresh. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientDock
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (D : ℕ) (i : Fin 7) := if i=2 ∨ i=3 then D else 0
def padded (D : ℕ) (tapes : Fin 7 → List Bool) := fun i=>ZeroPadding.pad (caps D i) (tapes i)
def slots : Fin 7 → Fin 28 := ![10,11,19,16,25,26,27]
theorem slots_injective : Function.Injective slots := by decide
def extend {s : ℕ} (c : Configuration 26 s) :=
  TapeEmbedding.config (fun _ : Fin 2=>0) (fun _=>[]) c
noncomputable def dock {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  extend (RowCoefficientLoopReset.output gs j hj pre tail indices)
def bits {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (negative : Bool) (indices : List (Fin gs.length)) :=
  RowPowerNativeReusable.blocks (RowCachedCoordinateBounds.width gs) negative
    (RowOccurrenceLoop.values gs j hj indices)

theorem bits_length {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (negative : Bool) (indices : List (Fin gs.length)) :
    (bits gs j hj negative indices).length=RowCachedCoordinateBounds.width gs*indices.length := by
  simp [bits,RowPowerNativeReusable.blocks_length,RowOccurrenceLoop.values]

theorem padded_ready (w p n cap D : ℕ) (hp : p<2^w) (hn : n<2^w) :
    ReadyRun RowCoefficientField.machine (12*w+21)
      (padded D (RowCoefficientField.input w p n cap 0))
      (padded D (RowCoefficientField.output w p n cap 0)) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := RowCoefficientField.field_ready w p n cap 0 hp hn
  obtain ⟨a,ha,af,asteps,_⟩ := ZeroPadding.run_config RowCoefficientField.machine (caps D) _ _ r hr
  refine ⟨a,ha,?_,?_,asteps.trans rs⟩
  · rw [af]; change padded D r.final.tapes=_; rw [rt]
  · intro i; rw [af]; exact rh i

theorem scratch {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (source : List Bool)
    (pos : ℕ) (positive negative : List Bool) (total driver : ℕ) (phase : Fin 5) :
    let c := RowOccurrenceLoop.cfg gs j phase source pos positive negative total driver
    let D := RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)
    c.heads 19=0 ∧ c.heads 16=0 ∧ c.tapes 19=List.replicate D false ∧ c.tapes 16=List.replicate D false := by
  simp [RowOccurrenceLoop.cfg,RowOccurrenceLoop.data,RepeatMachine.cfg,controlConfig,
    RowOccurrenceReusable.entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,
    RowOccurrenceAppend.ready,RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,
    Composition.leftConfig,Composition.restart,TapeEmbedding.config,ZeroPadding.config,
    RowCachedCoordinateReset.entry,Rewind.recording,Rewind.config,RowCachedCoordinateAppend.entry,
    RowCachedCoordinateAppend.ready,RowNativeCoordinateAppend.ready,
    RowNativeCoordinateAppend.extraHeads,RowNativeCoordinateAppend.extraTapes,
    RowCachedCoordinateReset.caps,RowOccurrenceReusable.caps,
    Fin.addCases,ZeroPadding.pad]

theorem dock_heads {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    ∀ i,(dock gs j hj pre tail indices).heads (slots i)=0 := by
  have h := scratch gs j (pre++RowOccurrenceLoop.word indices++tail)
    (pre.length+(RowOccurrenceLoop.word indices).length)
    (RowOccurrenceLoop.emitted gs j hj false indices) (RowOccurrenceLoop.emitted gs j hj true indices)
    indices.length 1 3
  have h19 : (RowCoefficientLoopReset.loopFinal gs j hj pre tail indices).heads 19=0 := h.1
  have h16 : (RowCoefficientLoopReset.loopFinal gs j hj pre tail indices).heads 16=0 := h.2.1
  intro i
  simp only [dock,extend,RowCoefficientLoopReset.output,RowCoefficientLoopReset.finish,
    SelectiveReset.finished,Rewind.config,TapeEmbedding.config]
  fin_cases i <;> simp [slots,Fin.addCases,RowCoefficientLoopReset.selected,h19,h16]

theorem dock_input {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    ∀ i,(dock gs j hj pre tail indices).tapes (slots i)=
      padded (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs))
        (RowCoefficientField.input (RowCachedCoordinateBounds.width gs*indices.length)
          (RadixSemantics.value (bits gs j hj false indices))
          (RadixSemantics.value (bits gs j hj true indices))
          (RowOccurrenceLoop.budget gs j hj indices) 0) i := by
  have h := scratch gs j (pre++RowOccurrenceLoop.word indices++tail)
    (pre.length+(RowOccurrenceLoop.word indices).length)
    (RowOccurrenceLoop.emitted gs j hj false indices) (RowOccurrenceLoop.emitted gs j hj true indices)
    indices.length 1 3
  have h19 : (RowCoefficientLoopReset.loopFinal gs j hj pre tail indices).tapes 19=
      List.replicate (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) false := h.2.2.1
  have h16 : (RowCoefficientLoopReset.loopFinal gs j hj pre tail indices).tapes 16=
      List.replicate (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) false := h.2.2.2
  have ho := RowOccurrenceLoop.cfg_outputs gs j (pre++RowOccurrenceLoop.word indices++tail)
    (pre.length+(RowOccurrenceLoop.word indices).length)
    (RowOccurrenceLoop.emitted gs j hj false indices) (RowOccurrenceLoop.emitted gs j hj true indices)
    indices.length 1 3
  have hp : (RowCoefficientLoopReset.loopFinal gs j hj pre tail indices).tapes 10=frame (bits gs j hj false indices) := by
    unfold RowCoefficientLoopReset.loopFinal
    rw [ho.1,RowOccurrenceLoop.emitted_blocks]
    simpa only [List.append_nil,frame,bits] using (frame_append (bits gs j hj false indices) []).symm
  have hn : (RowCoefficientLoopReset.loopFinal gs j hj pre tail indices).tapes 11=frame (bits gs j hj true indices) := by
    unfold RowCoefficientLoopReset.loopFinal
    rw [ho.2.1,RowOccurrenceLoop.emitted_blocks]
    simpa only [List.append_nil,frame,bits] using (frame_append (bits gs j hj true indices) []).symm
  have hb (negative : Bool) : SignedSortKey.binary (RowCachedCoordinateBounds.width gs*indices.length)
      (RadixSemantics.value (bits gs j hj negative indices))=bits gs j hj negative indices := by
    simpa only [bits_length] using BoundedCounter.binary_of_value (bits gs j hj negative indices)
  have hD : 1 ≤ RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) := by
    unfold RowCachedCoordinateBounds.outer RowCachedCoordinateBounds.size
    omega
  intro i
  simp only [dock,extend,RowCoefficientLoopReset.output,RowCoefficientLoopReset.finish,
    SelectiveReset.finished,Rewind.config,TapeEmbedding.config]
  fin_cases i <;> simp [slots,Fin.addCases,padded,caps,RowCoefficientField.input,
    RowCoefficientNormalize.input,RowCoefficientNormalize.data,RowCoefficientField.extra,
    hp,hn,h19,h16,hb,ZeroPadding.pad]
  rw [←List.replicate_succ]
  congr 1

end NearCubicWires.RepairOrdinary.RowCoefficientDock
