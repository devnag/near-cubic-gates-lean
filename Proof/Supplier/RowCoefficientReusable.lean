import Proof.Supplier.RowCoefficientStreamClear

/-! Exact same-bank endpoint for one coefficient. Rewinding and erasure
restore the original allocated entry, with only the row stream extended. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem erase_pick (i : Fin 32) : RecoveryFocus.pick RowCoefficientStreamClear.eraseSlots i=
    (if i=10 then some 0 else if i=11 then some 1 else if i=16 then some 2 else if i=19 then some 3
      else if i=25 then some 4 else if i=26 then some 5 else if i=27 then some 6 else if i=29 then some 7
      else if i=30 then some 8 else if i=31 then some 9 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ RowCoefficientStreamClear.injective 0
    | exact RecoveryFocus.pick_slot _ RowCoefficientStreamClear.injective 1
    | exact RecoveryFocus.pick_slot _ RowCoefficientStreamClear.injective 2
    | exact RecoveryFocus.pick_slot _ RowCoefficientStreamClear.injective 3
    | exact RecoveryFocus.pick_slot _ RowCoefficientStreamClear.injective 4
    | exact RecoveryFocus.pick_slot _ RowCoefficientStreamClear.injective 5
    | exact RecoveryFocus.pick_slot _ RowCoefficientStreamClear.injective 6
    | exact RecoveryFocus.pick_slot _ RowCoefficientStreamClear.injective 7
    | exact RecoveryFocus.pick_slot _ RowCoefficientStreamClear.injective 8
    | exact RecoveryFocus.pick_slot _ RowCoefficientStreamClear.injective 9
    | decide

theorem field_pick (i : Fin 28) : RecoveryFocus.pick RowCoefficientDock.slots i=
    (if i=10 then some 0 else if i=11 then some 1 else if i=19 then some 2 else if i=16 then some 3
      else if i=25 then some 4 else if i=26 then some 5 else if i=27 then some 6 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ RowCoefficientDock.slots_injective 0
    | exact RecoveryFocus.pick_slot _ RowCoefficientDock.slots_injective 1
    | exact RecoveryFocus.pick_slot _ RowCoefficientDock.slots_injective 2
    | exact RecoveryFocus.pick_slot _ RowCoefficientDock.slots_injective 3
    | exact RecoveryFocus.pick_slot _ RowCoefficientDock.slots_injective 4
    | exact RecoveryFocus.pick_slot _ RowCoefficientDock.slots_injective 5
    | exact RecoveryFocus.pick_slot _ RowCoefficientDock.slots_injective 6
    | decide

theorem heads_restore {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    RowCoefficientStreamClear.resultHeads gs j hj tail out indices=
      (RowCoefficientStreamClear.entry gs j F tail out indices).heads := by
  funext i
  fin_cases i <;> rfl

def data {n : ℕ} (gs : List (ExactThresholdGate n)) (j F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) : Fin 32 → List Bool :=
  let w := RowCachedCoordinateBounds.width gs
  let C := RowCachedCoordinateBounds.inner w
  let D := RowCachedCoordinateBounds.outer gs w
  let zC := List.replicate C false
  let zD := List.replicate D false
  let zF := List.replicate F false
  ![exactListWord gs,zC,zC,zC,zC,zC,zC,zC,zC,List.replicate w true,zF,zF,zC,
    List.replicate C true,List.replicate (C+1) false,UnaryTemplate.tape j,zF,zD,UnaryTemplate.tape n,
    zF,zD,List.replicate D true,List.replicate (D+1) false,RowOccurrenceLoop.word indices++tail,
    CompareMachine.word indices.length,zF,zF,zF,out,zF,List.replicate F true,List.replicate (F+1) false]

theorem entry_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (j F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (hF : 1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F) :
    (RowCoefficientStreamClear.entry gs j F tail out indices).tapes=data gs j F tail out indices := by
  funext i
  dsimp only [RowCoefficientStreamClear.entry,RowCoefficientStreamClear.extend,Composition.restart,
    TapeEmbedding.config,RowCoefficientStreamReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    RowCoefficientStream.entry,RowCoefficientStream.extend,RowCoefficientWhole.entry,RowCoefficientDock.extend,
    RowCoefficientLoopReset.entry,
    RowOccurrenceLoop.cfg,RowOccurrenceLoop.data,RepeatMachine.cfg,controlConfig,
    RowOccurrenceReusable.entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,RowCachedCoordinateReusable.extra,
    Composition.leftConfig,Composition.restart,RowCachedCoordinateReset.entry,ZeroPadding.config,
    Rewind.recording,Rewind.config,TapeEmbedding.config,RowCachedCoordinateAppend.entry,
    RowCachedCoordinateAppend.ready,RowCachedCoordinateAppend.extra,RowNativeCoordinateAppend.ready,
    RowNativeCoordinateAppend.extraTapes,RowPowerNativeReusable.tapes]
  fin_cases i <;> simp [data,RowCoefficientStreamClear.extra,RowCoefficientStreamReset.caps,
    RowCoefficientStreamReset.work,RowCachedCoordinateReset.caps,RowOccurrenceReusable.caps,
    Fin.addCases,ZeroPadding.pad,Nat.add_sub_of_le hD]
  all_goals rw [←List.replicate_succ]
  all_goals congr 1
  all_goals omega

def nativeData {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ)
    (source positive negative : List Bool) (total : ℕ) : Fin 25 → List Bool :=
  let w := RowCachedCoordinateBounds.width gs
  let C := RowCachedCoordinateBounds.inner w
  let D := RowCachedCoordinateBounds.outer gs w
  let zC := List.replicate C false
  let zD := List.replicate D false
  ![exactListWord gs,zC,zC,zC,zC,zC,zC,zC,zC,List.replicate w true,
    positive++[false],negative++[false],zC,List.replicate C true,List.replicate (C+1) false,
    UnaryTemplate.tape j,zD,zD,UnaryTemplate.tape n,zD,zD,List.replicate D true,
    List.replicate (D+1) false,source,CompareMachine.word total]

theorem cfg_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (phase : Fin 5)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) (total driver : ℕ) :
    (RowOccurrenceLoop.cfg gs j phase source pos positive negative total driver).tapes=
      nativeData gs j source positive negative total := by
  funext i
  dsimp only [
    RowOccurrenceLoop.cfg,RowOccurrenceLoop.data,RepeatMachine.cfg,controlConfig,
    RowOccurrenceReusable.entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,RowCachedCoordinateReusable.extra,
    Composition.leftConfig,Composition.restart,RowCachedCoordinateReset.entry,ZeroPadding.config,
    Rewind.recording,Rewind.config,TapeEmbedding.config,RowCachedCoordinateAppend.entry,
    RowCachedCoordinateAppend.ready,RowCachedCoordinateAppend.extra,RowNativeCoordinateAppend.ready,
    RowNativeCoordinateAppend.extraTapes,RowPowerNativeReusable.tapes]
  fin_cases i <;> simp [nativeData,RowCachedCoordinateReset.caps,RowOccurrenceReusable.caps,
    Fin.addCases,ZeroPadding.pad]

theorem cleared_low {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (i : Fin 16) :
    RowCoefficientStreamClear.cleared F (RowCoefficientStreamClear.resetTapes gs j hj F tail out indices) (i.castAdd 16)=
      data gs j F tail out indices (i.castAdd 16) := by
  simp only [RowCoefficientStreamClear.cleared,install,erase_pick]
  fin_cases i <;> simp [RowCoefficientStreamClear.eraseInput,data,
    RowCoefficientStreamClear.resetTapes,
    RowCoefficientStreamReset.outputTapes,RowCoefficientStreamReset.work,RowCoefficientStream.tapes,
    RowCoefficientWhole.result,install,field_pick,RowCoefficientDock.dock,RowCoefficientDock.extend,
    RowCoefficientLoopReset.output,RowCoefficientLoopReset.finish,SelectiveReset.finished,
    RowCoefficientLoopReset.loopFinal,
    cfg_tapes,nativeData,Rewind.config,TapeEmbedding.config,
    Fin.addCases,ZeroPadding.pad]

theorem cleared_high {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (i : Fin 16) :
    RowCoefficientStreamClear.cleared F (RowCoefficientStreamClear.resetTapes gs j hj F tail out indices) (i.natAdd 16)=
      data gs j F tail out indices (i.natAdd 16) := by
  simp only [RowCoefficientStreamClear.cleared,install,erase_pick]
  fin_cases i <;> simp [RowCoefficientStreamClear.eraseInput,data,
    RowCoefficientStreamClear.resetTapes,
    RowCoefficientStreamReset.outputTapes,RowCoefficientStreamReset.work,RowCoefficientStream.tapes,
    RowCoefficientWhole.result,install,field_pick,RowCoefficientDock.dock,RowCoefficientDock.extend,
    RowCoefficientLoopReset.output,RowCoefficientLoopReset.finish,SelectiveReset.finished,
    RowCoefficientLoopReset.loopFinal,
    cfg_tapes,nativeData,Rewind.config,TapeEmbedding.config,
    Fin.addCases,ZeroPadding.pad]

theorem cleared_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    RowCoefficientStreamClear.cleared F (RowCoefficientStreamClear.resetTapes gs j hj F tail out indices)=
      data gs j F tail out indices := by
  funext i
  exact Fin.addCases (m:=16) (n:=16)
    (motive:=fun k=>RowCoefficientStreamClear.cleared F
      (RowCoefficientStreamClear.resetTapes gs j hj F tail out indices) k=data gs j F tail out indices k)
    (cleared_low gs j hj F tail out indices) (cleared_high gs j hj F tail out indices) i

theorem tapes_restore {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (hF : 1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F) :
    RowCoefficientStreamClear.cleared F (RowCoefficientStreamClear.resetTapes gs j hj F tail out indices)=
      (RowCoefficientStreamClear.entry gs j F tail out indices).tapes :=
  (cleared_tapes gs j hj F tail out indices).trans (entry_tapes gs j F tail out indices hF hD).symm

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : RowCoefficientStream.budget gs j hj indices+1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F) :
    ∃ r,runFrom RowCoefficientStreamClear.machine (2*RowCoefficientStream.budget gs j hj indices+2*F+7)
      (RowCoefficientStreamClear.entry gs j F tail out indices)=some r ∧
      r.final.heads=(RowCoefficientStreamClear.entry gs j F tail
        (out++frame (RowCoefficientStream.field gs j hj indices)) indices).heads ∧
      r.final.tapes=(RowCoefficientStreamClear.entry gs j F tail
        (out++frame (RowCoefficientStream.field gs j hj indices)) indices).tapes ∧
      r.steps ≤ 2*RowCoefficientStream.budget gs j hj indices+2*F+7 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := RowCoefficientStreamClear.cleared_run gs j hj F tail out indices hF hD
  exact ⟨r,hr,rh.trans (heads_restore gs j hj F tail _ indices),
    rt.trans (tapes_restore gs j hj F tail _ indices (by omega) hD),rs⟩

end NearCubicWires.RepairOrdinary.RowCoefficientReusable
