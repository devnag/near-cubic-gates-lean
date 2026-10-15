import Proof.MachineModel.OrdinaryMatrixRightGateBootstrap

/-! The aggregate keyed stream receives an actual final false cell after
all gates. This remains necessary when the output exceeds its cold backing. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGateFinish
open LocalBitMultitape RecoveryExecution MatrixScoreBatch MatrixRightGateNativeLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 38 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun i => if i=8 then some false else none,
    fun i => if i=8 then .right else .stay⟩
noncomputable def before (r : Request) (unused : Fin 3 → List Bool) (s : MatrixBucketGateLoop.Store r) :=
  MatrixRightGateNativeLoop.cfg r 3 r.Gates (MatrixBatchGateNativeLoop.output r)
    (MatrixBatchGateNativeLoop.output r).length (MatrixRightGateNativeLoop.output r) unused s
noncomputable def final (r : Request) (unused : Fin 3 → List Bool) (s : MatrixBucketGateLoop.Store r) : Configuration 38 2 :=
  ⟨1,Function.update (before r unused s).heads 8 ((MatrixRightGateNativeLoop.output r).length+1),
    Function.update (before r unused s).tapes 8
      (ZeroPadding.pad (MatrixScoreReusableRanks.D r) (MatrixRightGateNativeLoop.output r++[false]))⟩

theorem finish_run (r : Request) (unused : Fin 3 → List Bool) (s : MatrixBucketGateLoop.Store r) :
    ∃ actual,runFrom machine 1 (Composition.restart (before r unused s) machine.start)=some actual ∧
      actual.final=final r unused s ∧ actual.steps=1 := by
  have hhead : (before r unused s).heads 8=(MatrixRightGateNativeLoop.output r).length := by
    simp only [before,MatrixRightGateNativeLoop.cfg_heads]
    rfl
  have htape : (before r unused s).tapes 8=ZeroPadding.pad (MatrixScoreReusableRanks.D r) (MatrixRightGateNativeLoop.output r) := by
    simp only [before,MatrixRightGateNativeLoop.cfg_tapes]
    rfl
  have hs : step machine (Composition.restart (before r unused s) machine.start)=some (final r unused s) := by
    simp only [step,machine]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=8
      · subst i
        simp [applyAction,Composition.restart,final,HeadMove.apply,hhead]
      · simp [applyAction,Composition.restart,final,HeadMove.apply,hi]
    · funext i
      by_cases hi : i=8
      · subst i
        change writeTapeBit ((before r unused s).tapes 8) ((before r unused s).heads 8) false=
          ZeroPadding.pad (MatrixScoreReusableRanks.D r) (MatrixRightGateNativeLoop.output r++[false])
        rw [hhead,htape,ZeroPadding.write_pad,Streaming.write_append]
      · simp [applyAction,Composition.restart,final,hi]
  obtain ⟨actual,ha,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨actual,ha,hf,ht⟩

end NearCubicWires.RepairOrdinary.MatrixRightGateFinish
