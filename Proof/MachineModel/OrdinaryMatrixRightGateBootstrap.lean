import Proof.MachineModel.OrdinaryMatrixRightGateNativeLoop

/-! The original retained Gates driver is at head zero. One actual step
advances that driver while preserving the existing bucket cursor and every
tape of the reused right bank. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGateBootstrap
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open MatrixBucketGateLoop (Store)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 38 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,fun i => if i=37 then .right else .stay⟩
noncomputable def target (r : Request) (unused : Fin 3 → List Bool) (s : Store r) :=
  MatrixRightGateNativeLoop.cfg r 0 0 (MatrixBatchGateNativeLoop.output r) 0 [] unused s
noncomputable def input {k : ℕ} (q : Fin k) (r : Request) (unused : Fin 3 → List Bool) (s : Store r) : Configuration 38 k :=
  ⟨q,Function.update (target r unused s).heads 37 0,(target r unused s).tapes⟩

theorem boot_run (r : Request) (unused : Fin 3 → List Bool) (s : Store r) :
    ∃ actual,runFrom machine 1 (input machine.start r unused s)=some actual ∧
      actual.final.heads=(target r unused s).heads ∧ actual.final.tapes=(target r unused s).tapes ∧ actual.steps=1 := by
  let final : Configuration 38 2 := ⟨1,(target r unused s).heads,(target r unused s).tapes⟩
  have hs : step machine (input machine.start r unused s)=some final := by
    simp only [step,machine,input]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=37
      · subst i
        simp [applyAction,HeadMove.apply,final,target,MatrixRightGateNativeLoop.cfg_heads]
        rfl
      · simp [applyAction,HeadMove.apply,final,hi]
    · rfl
  obtain ⟨actual,ha,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨actual,ha,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht⟩

end NearCubicWires.RepairOrdinary.MatrixRightGateBootstrap
