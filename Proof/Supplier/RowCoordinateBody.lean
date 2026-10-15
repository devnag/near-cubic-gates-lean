import Proof.Supplier.RowCoordinateIncrement

/-! One actual coordinate-loop body computes and appends the stacked field,
restores its coefficient bank, then advances its own coordinate template.
All values used by the next call are physically present in the same bank. -/
namespace NearCubicWires.RepairOrdinary.RowCoordinateBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := RowCoefficientStreamClear.machine
noncomputable def last := RowCoordinateIncrement.focused
noncomputable def machine := Composition.machine first last
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (RowCoefficientStreamClear.entry gs j (RowCoefficientBounds.capacity gs indices.length)
    tail out indices) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :=
  2*RowCoefficientStream.budget gs j hj indices+2*RowCoefficientBounds.capacity gs indices.length+2*j+17

theorem coordinate_heads {n : ℕ} (gs : List (ExactThresholdGate n)) (j k F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    (RowCoefficientStreamClear.entry gs j F tail out indices).heads=
      (RowCoefficientStreamClear.entry gs k F tail out indices).heads := by
  funext i
  dsimp only [RowCoefficientStreamClear.entry,RowCoefficientStreamClear.extend,Composition.restart,
    TapeEmbedding.config,RowCoefficientStreamReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    RowCoefficientStream.entry,RowCoefficientStream.extend,RowCoefficientWhole.entry,RowCoefficientDock.extend,
    RowCoefficientLoopReset.entry,RowOccurrenceLoop.cfg,RowOccurrenceLoop.data,RepeatMachine.cfg,controlConfig,
    RowOccurrenceReusable.entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,Composition.leftConfig,
    RowCachedCoordinateReset.entry,RowCachedCoordinateAppend.entry,RowCachedCoordinateAppend.ready,
    RowNativeCoordinateAppend.ready]

theorem coordinate_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    Function.update (RowCoefficientStreamClear.entry gs j (RowCoefficientBounds.capacity gs indices.length)
      tail out indices).tapes 15 (UnaryTemplate.tape (j+1))=
      (RowCoefficientStreamClear.entry gs (j+1) (RowCoefficientBounds.capacity gs indices.length) tail out indices).tapes := by
  have hF : 1 ≤ RowCoefficientBounds.capacity gs indices.length := by unfold RowCoefficientBounds.capacity; omega
  rw [RowCoefficientReusable.entry_tapes gs j _ tail out indices hF (RowCoefficientBounds.inner_fits gs _),
    RowCoefficientReusable.entry_tapes gs (j+1) _ tail out indices hF (RowCoefficientBounds.inner_fits gs _)]
  funext i
  fin_cases i <;> simp [RowCoefficientReusable.data]

theorem body_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (budget gs j hj indices) (entry gs j tail out indices)=some r ∧
      r.final.heads=(entry gs (j+1) tail (out++frame (RowCoefficientStream.field gs j hj indices)) indices).heads ∧
      r.final.tapes=(entry gs (j+1) tail (out++frame (RowCoefficientStream.field gs j hj indices)) indices).tapes ∧
      r.steps ≤ budget gs j hj indices := by
  obtain ⟨a,ha,ah,atapes,asteps⟩ := RowCoefficientReusable.reusable_run gs j hj
    (RowCoefficientBounds.capacity gs indices.length) tail out indices
    (RowCoefficientBounds.call_fits gs j hj indices) (RowCoefficientBounds.inner_fits gs _)
  have hhead : a.final.heads 15=1 := by rw [ah]; rfl
  have htape : a.final.tapes 15=UnaryTemplate.tape j := by
    rw [atapes,RowCoefficientReusable.entry_tapes gs j _ tail _ indices
      (by unfold RowCoefficientBounds.capacity; omega) (RowCoefficientBounds.inner_fits gs _)]
    rfl
  obtain ⟨b,hb,bh,bt,bs⟩ := RowCoordinateIncrement.focused_run j a.final.heads a.final.tapes hhead htape
  have whole := Composition.run_join first last _ _ _ a b ha hb
  have htime : (2*RowCoefficientStream.budget gs j hj indices+2*RowCoefficientBounds.capacity gs indices.length+7)+1+
      (2*j+9)=budget gs j hj indices := by unfold budget; omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,?_⟩
  · change b.final.heads=_
    rw [bh,ah]
    exact coordinate_heads gs j (j+1) _ tail _ indices
  · change b.final.tapes=_
    rw [bt,atapes]
    exact coordinate_tapes gs j tail _ indices
  · change a.steps+1+b.steps ≤ _
    rw [bs]
    unfold budget
    omega

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    budget gs j hj indices ≤ 65536*(indices.length+1)*
      RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+2*n+175 := by
  have h := RowCoefficientBounds.budget_bound gs j hj indices
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RowCoordinateBody
