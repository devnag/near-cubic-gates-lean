import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyActual

/-! Frame the actual unary proof count with the existing two-tape framer.
Only its real entry/return cursor moves are added. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearchCount
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def atOne : Fin 2→Nat := ![1,0]
def move (right : Bool) : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some
    ⟨1,fun _=>none,fun i=>if i=0 then (if right then .right else .left) else .stay⟩ else none

theorem advance_step (data : Fin 2→List Bool) :
    step (move true) (initialConfiguration (move true) data)=some ⟨1,atOne,data⟩ := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem retreat_step (data : Fin 2→List Bool) :
    step (move false) ⟨0,atOne,data⟩=some ⟨1,fun _=>0,data⟩ := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

def framedPrefix := Composition.machine (move true) UnaryFrameMachine.machine
def frameMachine := Composition.machine framedPrefix (move false)
def frameInput (n : Nat) : Fin 2→List Bool := ![CompareMachine.word n,[]]
def frameOutput (n : Nat) : Fin 2→List Bool := ![CompareMachine.word n,frame (List.replicate n true)]

theorem frame_ready (n : Nat) : ClockJoin.ReadyRun frameMachine (4*n+6) (frameInput n) (frameOutput n) := by
  obtain ⟨a,ha,af,aSteps⟩ := (Timed.single (by rfl) (advance_step (frameInput n))).run (by rfl)
  obtain ⟨b,hb,bf,bSteps,_bPeak⟩ := UnaryFrameMachine.unary_frame_run n
  have ab : Composition.restart a.final UnaryFrameMachine.machine.start=UnaryFrameMachine.cfg 0 n 1 0 [] := by
    rw [af]
    rfl
  rw [←ab] at hb
  have hab:=Composition.run_join (move true) UnaryFrameMachine.machine _ _ _ a b ha hb
  obtain ⟨c,hc,cf,cSteps⟩ := (Timed.single (by rfl) (retreat_step (frameOutput n))).run (by rfl)
  have bc : Composition.restart (Composition.joinedReceipt a b).final (move false).start=
      (⟨0,atOne,frameOutput n⟩ : Configuration 2 2) := by
    change Composition.restart b.final (move false).start=_
    rw [bf]
    rfl
  rw [←bc] at hc
  have hall:=Composition.run_join framedPrefix (move false) _ _ _ (Composition.joinedReceipt a b) c hab hc
  have hbudget : (1+1+(4*n+2))+1+1=4*n+6 := by omega
  rw [hbudget] at hall
  refine ⟨_,hall,?_,?_,?_⟩
  · change c.final.tapes=frameOutput n
    rw [cf]
  · intro i
    change c.final.heads i=0
    rw [cf]
  · change (a.steps+1+b.steps)+1+c.steps≤4*n+6
    omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearchCount
