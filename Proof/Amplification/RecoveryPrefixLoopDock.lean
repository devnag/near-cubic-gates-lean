import Proof.Amplification.RecoveryPrefixLoop

/-! The physical two driver moves required at the bounded repeat's cold
call boundary. The existing repeater starts and finishes at driver head1;
this wrapper executes right/left moves and exposes native zero heads again. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixLoopDock
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
open VerifierDecoding.RepeatMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def shift (t : Nat) (move : HeadMove) : Machine (t+1) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,
    Fin.addCases (fun _ : Fin t=>.stay) (fun _ : Fin 1=>move)⟩ else none

def tapes (p : OrdinaryOracleProgram) (total : Nat) (native : Fin p.base.tapeCount→List Bool) :
    Fin (p.base.tapeCount+1)→List Bool :=
  fun i=>Fin.addCases native (fun _ : Fin 1=>VerifierDecoding.CompareMachine.word total) i
def heads (p : OrdinaryOracleProgram) (head : Nat) : Fin (p.base.tapeCount+1)→Nat :=
  fun i=>Fin.addCases (fun _ : Fin p.base.tapeCount=>0) (fun _ : Fin 1=>head) i
def shiftCfg (p : OrdinaryOracleProgram) (q : Fin 2) (total head : Nat)
    (native : Fin p.base.tapeCount→List Bool) : Configuration (p.base.tapeCount+1) 2 :=
  ⟨q,heads p head,tapes p total native⟩

theorem shift_step (p : OrdinaryOracleProgram) (move : HeadMove) (total head : Nat)
    (native : Fin p.base.tapeCount→List Bool) :
    step (shift p.base.tapeCount move) (shiftCfg p 0 total head native)=
      some (shiftCfg p 1 total (move.apply head) native) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;>
      simp [applyAction,shiftCfg,heads,HeadMove.apply]
  · rfl

def ports (p : OrdinaryOracleProgram) : Ports (p.base.tapeCount+1) :=
  ⟨by have h:=p.base.twoTapes; omega,p.base.outputTape.castAdd 1,p.base.outputFresh,
    p.queryTape.castAdd 1,p.queryFresh⟩
noncomputable def repeated (p : OrdinaryOracleProgram) : Piece (p.base.tapeCount+1) :=
  ⟨(RecoveryOracleRepeat.program p).base.stateCount,(RecoveryOracleRepeat.program p).base.machine,
    (RecoveryOracleRepeat.program p).query⟩
noncomputable def pieces (p : OrdinaryOracleProgram) : Fin 3→Piece (p.base.tapeCount+1)
  | ⟨0,_⟩ => ordinary (shift p.base.tapeCount .right)
  | ⟨1,_⟩ => repeated p
  | ⟨2,_⟩ => ordinary (shift p.base.tapeCount .left)
  | ⟨n+3,h⟩ => False.elim (by omega)
def next (p : OrdinaryOracleProgram) (j : Fin 3) (_ : Fin (pieces p j).states)
    (_ : Fin (p.base.tapeCount+1)→Bool) : Option (Fin 3) :=
  if j.val=0 then some 1 else if j.val=1 then some 2 else none
noncomputable abbrev program (p : OrdinaryOracleProgram) := (ports p).program (graph (pieces p) 0 (next p))

private theorem shift_trace (o : Nat→Bool) (p : OrdinaryOracleProgram) (move : HeadMove)
    (total head : Nat) (native : Fin p.base.tapeCount→List Bool) :
    OrdinaryOracleTrace o ((ports p).program (ordinary (shift p.base.tapeCount move))) 1
      (shiftCfg p 0 total head native) (shiftCfg p 1 total (move.apply head) native) := by
  apply single
  exact .local _ _ rfl rfl (shift_step p move total head native)

private theorem stopped_halted (p : OrdinaryOracleProgram) (output : Fin (p.base.tapeCount+1)→List Bool) :
    (program p).base.machine.halted
      (RecoveryCalls.stopped (fun j=>(pieces p j).states) (fun _=>0) output).control=true := by
  simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]

theorem ready_of_run (o : Nat→Bool) (p : OrdinaryOracleProgram) (total budget : Nat)
    (input output : Fin p.base.tapeCount→List Bool)
    (h : RecoveryPrefixLoop.Run o p total budget input output) :
    ∃ cost ≤ budget+5,Ready o (program p) cost (tapes p total input) (tapes p total output) := by
  obtain ⟨cost,hcost,hloop,hhalt⟩ := h
  have hin := graph_trace (ports p) (pieces p) 0 (next p) 0 (shift_trace o p .right total 0 input)
  have hrin := graph_return o (ports p) (pieces p) 0 (next p) 0 1
    (shiftCfg p 1 total 1 input) rfl rfl
  have he : RecoveryCalls.restarted (pieces p 1).machine (heads p 1) (tapes p total input)=
      RecoveryPrefixLoop.boundary p 0 total 0 input := by rfl
  change OrdinaryOracleTrace o (program p) 1 _
    (controlConfig (RecoveryCalls.code (fun j=>(pieces p j).states) 1)
      (RecoveryCalls.restarted (pieces p 1).machine (heads p 1) (tapes p total input))) at hrin
  rw [he] at hrin
  have hbody := graph_trace (ports p) (pieces p) 0 (next p) 1 hloop
  have hrout := graph_return o (ports p) (pieces p) 0 (next p) 1 2
    (RecoveryPrefixLoop.boundary p 3 total 0 output) hhalt rfl
  have heout : RecoveryCalls.restarted (pieces p 2).machine
      (RecoveryPrefixLoop.boundary p 3 total 0 output).heads
      (RecoveryPrefixLoop.boundary p 3 total 0 output).tapes=shiftCfg p 0 total 1 output := by rfl
  rw [heout] at hrout
  have hout := graph_trace (ports p) (pieces p) 0 (next p) 2 (shift_trace o p .left total 1 output)
  have hstop := graph_stop o (ports p) (pieces p) 0 (next p) 2 (shiftCfg p 1 total 0 output) rfl rfl
  have hwhole := trans hin (trans hrin (trans hbody (trans hrout (trans hout hstop))))
  have hc : 1+(1+(cost+(1+(1+1))))=cost+5 := by omega
  rw [hc] at hwhole
  have hstart : controlConfig (RecoveryCalls.code (fun j=>(pieces p j).states) 0)
      (shiftCfg p 0 total 0 input)=initialConfiguration (program p).base.machine (tapes p total input) := by
    apply configuration_ext
    · rfl
    · funext i; refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;>
        simp [controlConfig,shiftCfg,heads,initialConfiguration]
    · rfl
  have hfinish : RecoveryCalls.stopped (fun j=>(pieces p j).states) (heads p 0) (tapes p total output)=
      RecoveryCalls.stopped (fun j=>(pieces p j).states) (fun _=>0) (tapes p total output) := by
    congr 1
    funext i; refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp [heads]
  change OrdinaryOracleTrace o (program p) (cost+5) _
    (RecoveryCalls.stopped (fun j=>(pieces p j).states) (heads p 0) (tapes p total output)) at hwhole
  rw [hstart,hfinish] at hwhole
  exact ⟨cost+5,by omega,_,hwhole,stopped_halted p _,fun _=>rfl,rfl⟩

end NearCubicWires.RepairSource.RecoveryPrefixLoopDock
