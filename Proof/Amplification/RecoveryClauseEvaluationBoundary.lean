import Proof.Amplification.RecoveryClauseEvaluationGraph

/-! Each clause entry/exit bit write is one actual transition. In particular,
rejection does not assume restoration of discarded valuation workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boundaryOutput (mode : Fin 3) (input : Fin 42→List Bool) : Fin 42→List Bool :=
  Function.update (if mode=0 then Function.update input 41 [false] else input) 27
    [if mode=1 then readTapeBit (input 41) 0 else false]

theorem boundary_ready (mode : Fin 3) (input : Fin 42→List Bool) (oldResult oldAggregate : Bool)
    (hr : input 27=[oldResult]) (ha : input 41=[oldAggregate]) :
    ReadyRun (boundaryMachine mode) 1 input (boundaryOutput mode input) := by
  let last : Configuration 42 2 := ⟨1,fun _=>0,boundaryOutput mode input⟩
  have hstep : step (boundaryMachine mode) (initialConfiguration (boundaryMachine mode) input)=some last := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; rfl
    · funext i
      by_cases hi : i=27
      · subst i
        simp [last,boundaryMachine,initialConfiguration,applyAction,boundaryOutput,hr,ha,
          Configuration.scanned,writeTapeBit,readTapeBit]
      · by_cases hj : i=41
        · subst i
          by_cases hm : mode=0 <;>
            simp [last,boundaryMachine,initialConfiguration,applyAction,boundaryOutput,hm,ha,
              Configuration.scanned,writeTapeBit,readTapeBit]
        · by_cases hm : mode=0 <;>
            simp [last,boundaryMachine,initialConfiguration,applyAction,boundaryOutput,hm,hi,hj]
  obtain ⟨r,hrun,hf,hs⟩ := (Timed.single (by rfl) hstep).run (by rfl)
  exact ⟨r,hrun,by rw [hf],by intro i; rw [hf],hs⟩

@[simp] theorem boundary_result (mode : Fin 3) (input : Fin 42→List Bool) :
    boundaryOutput mode input 27=[if mode=1 then readTapeBit (input 41) 0 else false] := by
  simp [boundaryOutput]

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
