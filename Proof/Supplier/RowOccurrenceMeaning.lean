import Proof.Supplier.RowOccurrenceLoop

/-! Physical output and uniform cost of one completed occurrence-coordinate
loop. The two produced frames denote the signed Horner coefficient. -/
namespace NearCubicWires.RepairOrdinary.RowOccurrenceLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem call_budget {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n) (i : Fin gs.length) :
    callBudget gs j hj i≤2048*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs) := by
  have hw := RowCachedCoordinateBounds.value_width gs i.val i.isLt j hj
  have h := RowCachedCoordinateBounds.reusable_budget gs i.val i.isLt j hj _ hw
  have hs : gs.length+1≤RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs) := by
    unfold RowCachedCoordinateBounds.size
    nlinarith
  have hi := i.isLt
  unfold callBudget RowOccurrenceReusable.budget RowOccurrenceAppend.budget RowCachedCoordinateBounds.outer
  unfold RowCachedCoordinateBounds.outer at h
  omega

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
    (indices : List (Fin gs.length)) :
    budget gs j hj indices ≤ indices.length*
      (2048*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+3)+3 := by
  have h : (indices.map (callBudget gs j hj)).sum ≤ indices.length*
      (2048*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)) := by
    induction indices with
    | nil => simp
    | cons i indices ih =>
      have hi := call_budget gs j hj i
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  unfold budget
  nlinarith

def values {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
    (indices : List (Fin gs.length)) := indices.map (value gs j hj)

theorem values_fit {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
    (indices : List (Fin gs.length)) (z : ℤ) (hz : z∈values gs j hj indices) :
    natBitLength z.natAbs≤RowCachedCoordinateBounds.width gs := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
  exact RowCachedCoordinateBounds.value_width gs i.val i.isLt j hj

theorem emitted_blocks {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
    (negative : Bool) (indices : List (Fin gs.length)) :
    emitted gs j hj negative indices=marks (RowPowerNativeReusable.blocks
      (RowCachedCoordinateBounds.width gs) negative (values gs j hj indices)) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simpa [emitted,values,RowPowerNativeReusable.blocks,marks,List.flatMap_append] using ih

theorem coefficient_value {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
    (indices : List (Fin gs.length)) :
    (RadixSemantics.value (RowPowerNativeReusable.blocks (RowCachedCoordinateBounds.width gs) false
        (values gs j hj indices)) : ℤ)-
      RadixSemantics.value (RowPowerNativeReusable.blocks (RowCachedCoordinateBounds.width gs) true
        (values gs j hj indices))=
      RowPowerNativeReusable.horner ((2 : ℤ)^(RowCachedCoordinateBounds.width gs)) (values gs j hj indices) :=
  RowPowerNativeReusable.blocks_value _ _ (values_fit gs j hj indices)

theorem cfg_outputs {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (source : List Bool)
    (pos : ℕ) (positive negative : List Bool) (total driver : ℕ) (phase : Fin 5) :
    (cfg gs j phase source pos positive negative total driver).tapes 10=positive++[false] ∧
    (cfg gs j phase source pos positive negative total driver).tapes 11=negative++[false] ∧
    (cfg gs j phase source pos positive negative total driver).heads 10=positive.length ∧
    (cfg gs j phase source pos positive negative total driver).heads 11=negative.length := by
  simp [cfg,data,RepeatMachine.cfg,controlConfig,RowOccurrenceReusable.entry,
    RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,
    Composition.leftConfig,Composition.restart,TapeEmbedding.config,ZeroPadding.config,
    RowCachedCoordinateReset.entry,Rewind.recording,Rewind.config,RowCachedCoordinateAppend.entry,
    RowCachedCoordinateAppend.ready,RowNativeCoordinateAppend.ready,RowPowerNativeReusable.heads,
    RowPowerNativeReusable.tapes,RowCachedCoordinateReset.caps,RowOccurrenceReusable.caps,
    Fin.addCases,ZeroPadding.pad]

theorem coefficient_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (budget gs j hj indices)
      (cfg gs j 0 (pre++word indices++tail) pre.length [] [] indices.length 1)=some r ∧
      r.final.tapes 10=frame (RowPowerNativeReusable.blocks (RowCachedCoordinateBounds.width gs) false
        (values gs j hj indices)) ∧
      r.final.tapes 11=frame (RowPowerNativeReusable.blocks (RowCachedCoordinateBounds.width gs) true
        (values gs j hj indices)) ∧
      r.final.heads 10=2*RowCachedCoordinateBounds.width gs*indices.length ∧
      r.final.heads 11=2*RowCachedCoordinateBounds.width gs*indices.length ∧
      r.steps ≤ indices.length*(2048*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+3)+3 := by
  obtain ⟨r,hr,rf,rs⟩ := list_run gs j hj pre tail [] [] indices
  obtain ⟨hp,hn,hph,hnh⟩ := cfg_outputs gs j (pre++word indices++tail) (pre.length+(word indices).length)
    ([]++emitted gs j hj false indices) ([]++emitted gs j hj true indices) indices.length 1 3
  have hp := (congrArg (fun c=>c.tapes 10) rf).trans hp
  have hn := (congrArg (fun c=>c.tapes 11) rf).trans hn
  have hph := (congrArg (fun c=>c.heads 10) rf).trans hph
  have hnh := (congrArg (fun c=>c.heads 11) rf).trans hnh
  simp only [emitted_blocks] at hp hn hph hnh
  simp only [List.nil_append,marks_length,RowPowerNativeReusable.blocks_length,values,List.length_map] at hp hn hph hnh
  refine ⟨r,hr,?_,?_,?_,?_,rs.le.trans (budget_bound gs j hj indices)⟩
  · have hf (bits : List Bool) : marks bits++[false]=frame bits := by
      simpa only [List.append_nil,frame] using (frame_append bits []).symm
    simpa only [hf,values] using hp
  · have hf (bits : List Bool) : marks bits++[false]=frame bits := by
      simpa only [List.append_nil,frame] using (frame_append bits []).symm
    simpa only [hf,values] using hn
  · rw [hph]; ring
  · rw [hnh]; ring

end NearCubicWires.RepairOrdinary.RowOccurrenceLoop
