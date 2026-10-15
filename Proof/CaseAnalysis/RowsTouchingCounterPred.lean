import Proof.MachineModel.ClockLogWidth
import Proof.CaseAnalysis.RowsTouchingDrivers
import Proof.CaseAnalysis.RowsTouchingUnaryProductReady

/-! Reuse the existing unary decrement, including its literal trailing
false cell. Padding absorbs that cell without changing allocated capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.CounterPred
open LocalBitMultitape ExtDecompositionBatch RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem zero_run:
    Step ClockLogWidth.decrement 3 (fun _=>1) (fun _=>CompareMachine.word 0)
      (fun _=>1) (fun _=>CompareMachine.word 0):=by
  have first:step ClockLogWidth.decrement (ClockLogWidth.cfg 0 [false] 1)=
      some (ClockLogWidth.cfg 1 [false] 0):=rfl
  have second:step ClockLogWidth.decrement (ClockLogWidth.cfg 1 [false] 0)=
      some (ClockLogWidth.cfg 2 [false] 0):=rfl
  have third:step ClockLogWidth.decrement (ClockLogWidth.cfg 2 [false] 0)=
      some (ClockLogWidth.cfg 3 [false] 1):=rfl
  obtain ⟨r,run,rf,_⟩:=((Timed.single (by rfl) first).trans
    ((Timed.single (by rfl) second).trans (Timed.single (by rfl) third))).run (by rfl)
  exact Step.of_run run (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem body_run (k P : ℕ) (hP:k+1≤P):
    Step ClockLogWidth.decrement (2*k+3) (fun _=>1) (fun _=>ZeroPadding.pad P (CompareMachine.word k))
      (fun _=>1) (fun _=>ZeroPadding.pad P (CompareMachine.word (k-1))):=by
  cases k with
  | zero=>exact zero_run.pad (fun _=>P)
  | succ k=>
    obtain ⟨r,run,rf,_⟩:=ClockLogWidth.decrement_run k
    have actual:=(Step.of_run run (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)).pad (fun _=>P)
    have result:Step ClockLogWidth.decrement (2*k+4) (fun _=>1)
        (fun _=>ZeroPadding.pad P (CompareMachine.word (k+1))) (fun _=>1)
        (fun _=>ZeroPadding.pad P (CompareMachine.word k)):=by
      refine actual.congr rfl ?_
      funext i
      exact Drivers.padded_template P k (by omega)
    exact result.enlarge (by omega)

noncomputable def machine:=Composition.machine
  (Composition.machine (DecompositionCountPosition.move (fun _ : Fin 1=>.right)) ClockLogWidth.decrement)
  (DecompositionCountPosition.move (fun _ : Fin 1=>.left))

theorem ready_run (k P : ℕ) (hP:k+1≤P):
    Step machine (2*k+7) (fun _=>0) (fun _=>ZeroPadding.pad P (CompareMachine.word k))
      (fun _=>0) (fun _=>ZeroPadding.pad P (CompareMachine.word (k-1))):=by
  obtain ⟨r0,run0,rf0,_⟩:=DecompositionCountPosition.move_run (fun _ : Fin 1=>.right)
    (fun _=>0) (fun _=>ZeroPadding.pad P (CompareMachine.word k))
  have first:=Step.of_run run0 (congrArg Configuration.heads rf0) (congrArg Configuration.tapes rf0)
  obtain ⟨r1,run1,rf1,_⟩:=DecompositionCountPosition.move_run (fun _ : Fin 1=>.left)
    (fun _=>1) (fun _=>ZeroPadding.pad P (CompareMachine.word (k-1)))
  have last:=Step.of_run run1 (congrArg Configuration.heads rf1) (congrArg Configuration.tapes rf1)
  exact ((first.seq (body_run k P hP)).seq last).enlarge (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.CounterPred
