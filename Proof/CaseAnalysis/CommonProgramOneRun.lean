import Proof.CaseAnalysis.CommonProgramTwoRun
import Proof.CaseAnalysis.CommonProgramOnePorts
import Proof.MachineModel.OrdinaryOracleComposeReadyAt

/-! The original Case1 Boolean worker terminates the same common program.
Only its own selected heads need to be zero after the paid query clear. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem one_finish (p : Parameters) (fuel : ℕ)
    (localInput out : Fin (on p)→List Bool)
    (actual : Ready RecoveryOracle.correctedSat (one p) fuel localInput out)
    (H : Fin (tapes p)→ℕ) (A : Fin (tapes p)→List Bool)
    (hin : ∀ i,A (oneSlot p i)=localInput i) (hh : ∀ i,H (oneSlot p i)=0) :
    ∃ final,OrdinaryOracleTrace RecoveryOracle.correctedSat (program p) (fuel+1)
      (stageStart p 3 H A) final ∧
      (program p).base.machine.halted final.control=true ∧
      final.tapes (ports p).outputTape=out (one p).base.outputTape:=by
  obtain ⟨last,hbody,hhalt,_heads,ht⟩:=Ready.focus_at actual (ports p) (oneSlot p)
    (one_injective p) (one_query p) H A hin hh
  have stop:=graph_stop RecoveryOracle.correctedSat (ports p) (pieces p) 0 (next p) 3
    last hhalt (by rfl)
  refine ⟨_,trans (graph_trace (ports p) (pieces p) 0 (next p) 3 hbody) stop,?_,?_⟩
  · simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · change last.tapes (ports p).outputTape=out (one p).base.outputTape
    rw [ht,←one_output]
    exact install_slot _ (one_injective p) _ _ _

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
