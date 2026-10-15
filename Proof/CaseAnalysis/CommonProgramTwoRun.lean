import Proof.CaseAnalysis.CommonProgramTwoPorts

/-! The selected Case2 worker executes at the actual retained cursors and
returns its Boolean word from the common program's one output port. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def stageStart (p : Parameters) (j : Fin 6) (H : Fin (tapes p)→ℕ)
    (A : Fin (tapes p)→List Bool) : (program p).Config:=
  controlConfig (RecoveryCalls.code (fun j=>(pieces p j).states) j)
    ⟨(pieces p j).machine.start,H,A⟩

theorem two_finish (p : Parameters) (fuel : ℕ)
    (localInput out : Fin (tn p)→List Bool)
    (actual : ClockJoin.ReadyRun (two p) fuel localInput out)
    (H : Fin (tapes p)→ℕ) (A : Fin (tapes p)→List Bool)
    (hin : ∀ i,A (twoSlot p i)=localInput i) (hh : ∀ i,H (twoSlot p i)=0) :
    ∃ cost ≤ fuel+1,∃ final,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program p) cost (stageStart p 4 H A) final ∧
      (program p).base.machine.halted final.control=true ∧
      final.tapes (ports p).outputTape=out (twoLocal p 5):=by
  obtain ⟨r,hr,_heads,ht,hs⟩:=actual.focus_at (twoSlot p) (two_injective p) H A hin hh
  have body:=ordinary_trace (o:=RecoveryOracle.correctedSat) (ports p)
    (RecoveryFocus.machine (twoSlot p) (two p)) fuel _ r hr
  have halt:=(prefix_of_run (RecoveryFocus.machine (twoSlot p) (two p)) fuel _ r hr).2
  have last:=graph_stop RecoveryOracle.correctedSat (ports p) (pieces p) 0 (next p) 4
    r.final halt (by rfl)
  refine ⟨r.steps+1,by omega,_,trans (graph_trace (ports p) (pieces p) 0 (next p) 4 body) last,?_,?_⟩
  · simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · change r.final.tapes (ports p).outputTape=out (twoLocal p 5)
    rw [ht,←two_output]
    exact install_slot _ (two_injective p) _ _ _

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
