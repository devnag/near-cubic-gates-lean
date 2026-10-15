import Proof.Supplier.RowCoefficientDock

/-! One fixed ordinary program consumes the retained cache and the actual
ordered occurrence stream, computes one stacked coefficient, physically
rewinds its P/N words, and emits its final normalized signed field. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientWhole
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding RowCoefficientDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 2 RowCoefficientLoopReset.machine
noncomputable def last := RecoveryFocus.machine slots RowCoefficientField.machine
noncomputable def machine := Composition.machine first last
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (extend (RowCoefficientLoopReset.entry gs j pre tail indices)) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :=
  2*RowOccurrenceLoop.budget gs j hj indices+12*(RowCachedCoordinateBounds.width gs*indices.length)+24
noncomputable def result {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  install slots (dock gs j hj pre tail indices).tapes
    (padded (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs))
      (RowCoefficientField.output (RowCachedCoordinateBounds.width gs*indices.length)
        (RadixSemantics.value (bits gs j hj false indices))
        (RadixSemantics.value (bits gs j hj true indices))
        (RowOccurrenceLoop.budget gs j hj indices) 0))

theorem whole_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (budget gs j hj indices) (entry gs j pre tail indices)=some r ∧
      r.final.heads=(dock gs j hj pre tail indices).heads ∧
      r.final.tapes=result gs j hj pre tail indices ∧ r.steps=budget gs j hj indices := by
  obtain ⟨a,ha,af,asteps⟩ := RowCoefficientLoopReset.loop_run gs j hj pre tail indices
  have hr := TapeEmbedding.run_embed RowCoefficientLoopReset.machine (fun _ : Fin 2=>0)
    (fun _=>[]) _ _ a ha
  let ar := TapeEmbedding.receipt (fun _ : Fin 2=>0) (fun _=>[]) a
  have arf : ar.final=dock gs j hj pre tail indices := by
    change extend a.final=extend (RowCoefficientLoopReset.output gs j hj pre tail indices)
    rw [af]
  have hp := RadixSemantics.value_lt (bits gs j hj false indices)
  have hn := RadixSemantics.value_lt (bits gs j hj true indices)
  rw [bits_length] at hp hn
  have h := padded_ready _ _ _ (RowOccurrenceLoop.budget gs j hj indices)
    (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) hp hn
  obtain ⟨b,hb,bh,bt,bs⟩ := h.focus_at slots slots_injective
    (dock gs j hj pre tail indices).heads (dock gs j hj pre tail indices).tapes
    (dock_input gs j hj pre tail indices) (dock_heads gs j hj pre tail indices)
  have he : (⟨RowCoefficientField.machine.start,(dock gs j hj pre tail indices).heads,
      (dock gs j hj pre tail indices).tapes⟩)=Composition.restart ar.final last.start := by
    rw [arf]; rfl
  rw [he] at hb
  have whole := Composition.run_join first last _ _ _ ar b hr hb
  have ht : (2*RowOccurrenceLoop.budget gs j hj indices+2)+1+
      (12*(RowCachedCoordinateBounds.width gs*indices.length)+21)=budget gs j hj indices := by
    unfold budget
    omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt ar b,whole,bh,bt,?_⟩
  change a.steps+1+b.steps=_
  rw [asteps,bs,ht]

theorem result_field {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    result gs j hj pre tail indices 26=frame (MatrixScoreBatch.signMagnitude
      (RowCachedCoordinateBounds.width gs*indices.length)
      (RowPowerNativeReusable.horner ((2 : ℤ)^RowCachedCoordinateBounds.width gs)
        (RowOccurrenceLoop.values gs j hj indices))) := by
  have h := install_slot slots slots_injective (dock gs j hj pre tail indices).tapes
    (padded (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs))
      (RowCoefficientField.output (RowCachedCoordinateBounds.width gs*indices.length)
        (RadixSemantics.value (bits gs j hj false indices))
        (RadixSemantics.value (bits gs j hj true indices))
        (RowOccurrenceLoop.budget gs j hj indices) 0)) 5
  change result gs j hj pre tail indices 26=_ at h
  simpa only [padded,caps,show ¬((5 : Fin 7)=2 ∨ (5 : Fin 7)=3) by decide,if_false,
    ZeroPadding.pad_zero,RowCoefficientField.field_output,bits,
    RowOccurrenceLoop.coefficient_value] using h

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    budget gs j hj indices ≤ 8192*indices.length*
      RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+30 := by
  have hb := RowOccurrenceLoop.budget_bound gs j hj indices
  have hw : RowCachedCoordinateBounds.width gs+1 ≤
      RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs) := by
    unfold RowCachedCoordinateBounds.size
    omega
  have hm := Nat.mul_le_mul_left indices.length hw
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.RowCoefficientWhole
