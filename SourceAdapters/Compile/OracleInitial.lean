import SourceAdapters.Compile.OracleClockEncoding
import SourceAdapters.Compile.BoundedInitial

/-!
proof of `thm:short-pcp-ours`, Step 4: initial gate values use the actual outer-framed data/seed word.
Each cell is a constant or one actual seed bit; no seed truth table is listed.
Control, heads, allocation and clock wires start at their literal source values.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
  NearCubicWires.LocalBitMultitape NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def initialInputCell (r : OracleCompilationRequest) (position : ℕ) : BoolExpr r.ell :=
  if position%2=0 then .const (decide (position/2<(RepairOrdinary.frame r.data).length+2*r.ell+1))
  else if position/2<(RepairOrdinary.frame r.data).length then
    .const ((RepairOrdinary.frame r.data).getD (position/2) false)
  else witnessFrameExpression (position/2-(RepairOrdinary.frame r.data).length)

theorem initialInputCell_eval (r : OracleCompilationRequest) (z : BitInput r.ell) (position : ℕ) :
    (initialInputCell r position).eval z=
      readTapeBit (RepairOrdinary.frame (r.runInput z)) position := by
  rw [NearCubicGates.Close.Cells.frame_read]
  unfold initialInputCell
  split
  · simp [BoolExpr.eval,OracleCompilationRequest.runInput,frame_length,Nat.add_assoc]
  · split
    · rename_i hp
      simp only [BoolExpr.eval,OracleCompilationRequest.runInput]
      rw [List.getD_append _ _ _ _ hp]
    · rename_i hp
      simp only [witnessFrameExpression_eval,OracleCompilationRequest.runInput,readTapeBit]
      rw [List.getD_append_right _ _ _ _ (by omega)]

theorem initialInputCell_operations (r : OracleCompilationRequest) (position : ℕ) :
    expressionOperations (initialInputCell r position) ≤ 1 := by
  unfold initialInputCell
  split
  · simp [expressionOperations]
  · split
    · simp [expressionOperations]
    · unfold witnessFrameExpression
      split
      · simp [expressionOperations]
      · split <;> simp [expressionOperations]

def initialExpression (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    Fin (clockBits p (requestWidth r) r.fuel) → BoolExpr r.ell :=
  Fin.addCases
    (Fin.addCases (fun q => .const (decide (p.base.machine.start=q)))
      (Fin.addCases
        (fun index => .const (decide ((finProdFinEquiv.symm index).2.val=0)))
        (fun index => let pair := finProdFinEquiv.symm index
          if pair.1.val=0 then initialInputCell r pair.2.val else .const false)))
    (Fin.addCases
      (fun index => let pair := finProdFinEquiv.symm index
        .const (decide ((if pair.1.val=0 then 4*(r.data.length+r.ell)+5 else 0)=pair.2.val)))
      (fun budget => .const (decide (r.fuel=budget.val))))

theorem initial_observed_cell (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (z : BitInput r.ell) (tape : Fin p.base.tapeCount) (position : Fin (requestWidth r)) :
    (requestClockState p r z).window.observed.cells tape position=
      if tape.val=0 then readTapeBit (RepairOrdinary.frame (r.runInput z)) position.val else false := by
  change readTapeBit ((requestWindow p r z).unpack.tapes tape) position.val=_
  rw [requestWindow_unpack]
  simp only [requestInitial,initialConfiguration,Program.inputTapes]
  split <;> rfl

theorem initial_length (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (z : BitInput r.ell) (tape : Fin p.base.tapeCount) :
    ((requestClockState p r z).window.lengths tape).val=
      if tape.val=0 then 4*(r.data.length+r.ell)+5 else 0 := by
  simp only [requestClockState,requestWindow,Window.pack,requestInitial,initialConfiguration,Program.inputTapes]
  split
  · simp [OracleCompilationRequest.runInput,frame_length]
    omega
  · rfl

theorem initialExpression_eval (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (z : BitInput r.ell) (index : Fin (clockBits p (requestWidth r) r.fuel)) :
    (initialExpression p r index).eval z=(requestClockState p r z).encode index := by
  refine Fin.addCases ?_ ?_ index
  · intro view
    refine Fin.addCases ?_ ?_ view
    · intro q
      simp [initialExpression,BoolExpr.eval,ClockState.encode,MachineWindow.encode,requestClockState,
        requestWindow,Window.observed,Window.pack,MachineWindow.ofConfiguration,Window.unpack,
        requestInitial,initialConfiguration]
    · intro rest
      refine Fin.addCases ?_ ?_ rest
      · intro pair
        simp only [initialExpression,Fin.addCases_left,Fin.addCases_right,BoolExpr.eval,ClockState.encode,
          MachineWindow.encode,Fin.ext_iff]
        change decide ((finProdFinEquiv.symm pair).2.val=0)=decide (0=(finProdFinEquiv.symm pair).2.val)
        simp [eq_comm]
      · intro pair
        simp only [initialExpression,Fin.addCases_left,Fin.addCases_right,ClockState.encode,
          MachineWindow.encode,initial_observed_cell]
        split
        · exact initialInputCell_eval _ _ _
        · rfl
  · intro extra
    refine Fin.addCases ?_ ?_ extra
    · intro pair
      simp only [initialExpression,Fin.addCases_left,Fin.addCases_right,BoolExpr.eval,ClockState.encode,
        Fin.ext_iff,initial_length]
    · intro budget
      simp only [initialExpression,Fin.addCases_right,BoolExpr.eval,ClockState.encode,requestClockState,Fin.ext_iff]

theorem initialExpression_operations (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (index : Fin (clockBits p (requestWidth r) r.fuel)) :
    expressionOperations (initialExpression p r index) ≤ 1 := by
  refine Fin.addCases ?_ ?_ index
  · intro view
    refine Fin.addCases ?_ ?_ view
    · intro q; simp [initialExpression,expressionOperations]
    · intro rest
      refine Fin.addCases ?_ ?_ rest
      · intro pair; simp [initialExpression,expressionOperations]
      · intro pair
        simp only [initialExpression,Fin.addCases_left,Fin.addCases_right]
        split
        · exact initialInputCell_operations _ _
        · simp [expressionOperations]
  · intro extra
    refine Fin.addCases ?_ ?_ extra
    · intro pair; simp [initialExpression,expressionOperations]
    · intro budget; simp [initialExpression,expressionOperations]

end NearCubicGates.Adapters.Compile.OracleExecution
