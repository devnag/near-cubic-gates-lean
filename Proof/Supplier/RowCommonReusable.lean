import Proof.Supplier.RowCommonClear

/-! The exact common-width bank is restored after each executed coefficient.
Only the live output contains the appended common-width signed field. -/
namespace NearCubicWires.RepairOrdinary.RowCommonReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) : Fin 35→List Bool :=
  let w := RowCachedCoordinateBounds.width gs
  let C := RowCachedCoordinateBounds.inner w
  let D := RowCachedCoordinateBounds.outer gs w
  let zC := List.replicate C false
  let zD := List.replicate D false
  let zF := List.replicate F false
  ![exactListWord gs,zC,zC,zC,zC,zC,zC,zC,zC,List.replicate w true,zF,zF,zC,
    List.replicate C true,List.replicate (C+1) false,UnaryTemplate.tape j,zF,zD,UnaryTemplate.tape n,
    zF,zD,List.replicate D true,List.replicate (D+1) false,RowOccurrenceLoop.word indices++tail,
    CompareMachine.word indices.length,zF,zF,zF,zF,CompareMachine.word (p+1),zF,out,zF,
    List.replicate F true,List.replicate (F+1) false]

theorem entry_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (hF : 1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F) :
    (RowCommonClear.entry gs j p F tail out indices).tapes=data gs j p F tail out indices := by
  funext i
  dsimp only [RowCommonClear.entry,RowCommonClear.extend,Composition.restart,TapeEmbedding.config,
    RowCommonReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,RowCommonCoefficient.entry,
    RowCommonCoefficient.extend,RowCoefficientWhole.entry,RowCoefficientDock.extend,RowCoefficientLoopReset.entry]
  simp only [RowCoefficientReusable.cfg_tapes,List.nil_append,List.length_nil]
  fin_cases i <;> simp [data,RowCommonClear.extra,RowCommonReset.caps,RowCommonCoefficient.caps,
    RowCommonCoefficient.extra,RowCoefficientStreamReset.work,RowCoefficientReusable.nativeData,
    Fin.addCases,ZeroPadding.pad,Nat.add_sub_of_le hD]
  all_goals rw [←List.replicate_succ]
  all_goals congr 1
  all_goals omega

theorem erase_pick (i : Fin 35) : RecoveryFocus.pick RowCommonClear.eraseSlots i=
    (if i=10 then some 0 else if i=11 then some 1 else if i=16 then some 2 else if i=19 then some 3
      else if i=25 then some 4 else if i=26 then some 5 else if i=27 then some 6 else if i=28 then some 7
      else if i=30 then some 8 else if i=32 then some 9 else if i=33 then some 10 else if i=34 then some 11 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 0
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 1
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 2
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 3
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 4
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 5
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 6
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 7
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 8
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 9
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 10
    | exact RecoveryFocus.pick_slot _ RowCommonClear.injective 11
    | decide

theorem cleared_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    RowCommonClear.cleared F (RowCommonClear.resetTapes gs j hj p F tail out indices)=
      data gs j p F tail out indices := by
  funext i
  simp only [RowCommonClear.cleared,install,erase_pick]
  fin_cases i <;> simp [RowCommonClear.eraseInput,data,RowCommonClear.resetTapes,
    RowCommonReset.outputTapes,RowCommonCoefficient.result,install,RowCommonCoefficient.field_pick,
    RowFieldPaddingAppend.output,RowFieldPaddingAppend.extend,RowFieldPadding.output,
    RowCommonCoefficient.middle,RowCommonCoefficient.caps,RowCoefficientStreamReset.work,
    RowCoefficientWhole.result,RowCoefficientReusable.field_pick,RowCoefficientDock.dock,RowCoefficientDock.extend,
    RowCoefficientLoopReset.output,RowCoefficientLoopReset.finish,SelectiveReset.finished,
    RowCoefficientLoopReset.loopFinal,RowCoefficientReusable.cfg_tapes,RowCoefficientReusable.nativeData,
    Rewind.config,TapeEmbedding.config,Fin.addCases,ZeroPadding.pad]

theorem heads_restore {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    RowCommonClear.resultHeads gs j hj tail out indices=
      (RowCommonClear.entry gs j p F tail out indices).heads := by
  funext i
  fin_cases i <;> rfl

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : RowCoordinateLoop.width gs indices ≤ p)
    (hcall : RowCommonCoefficient.budget gs j hj p indices+1 ≤ F)
    (hF : 2*p+5 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F) :
    ∃ r,runFrom RowCommonClear.machine (2*RowCommonCoefficient.budget gs j hj p indices+2*F+7)
      (RowCommonClear.entry gs j p F tail out indices)=some r ∧
      r.final.heads=(RowCommonClear.entry gs j p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices).heads ∧
      r.final.tapes=(RowCommonClear.entry gs j p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices).tapes ∧
      r.steps ≤ 2*RowCommonCoefficient.budget gs j hj p indices+2*F+7 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := RowCommonClear.cleared_run gs j hj p F tail out indices hp hcall hF hD
  refine ⟨r,hr,rh.trans (heads_restore gs j hj p F tail _ indices),?_,rs⟩
  rw [rt,cleared_tapes,entry_tapes gs j p F tail _ indices (by omega) hD]

end NearCubicWires.RepairOrdinary.RowCommonReusable
