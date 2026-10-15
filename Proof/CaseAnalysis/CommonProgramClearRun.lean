import Proof.CaseAnalysis.CommonProgramTwoRun
import Proof.CaseAnalysis.CommonProgramClearPorts

/-! The paid query clear is an actual common-graph edge into Case1. It
retains arbitrary inactive recovery cursors and charges every transition. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem restart_data {t s u : ℕ} (worker : Machine t s) (embed : Fin s→Fin u)
    (H H' : Fin t→ℕ) (A A' : Fin t→List Bool) (hh : H=H') (ha : A=A') :
    controlConfig embed (RecoveryCalls.restarted worker H A)=
      controlConfig embed (⟨worker.start,H',A'⟩ : Configuration t s):=by
  cases hh
  cases ha
  rfl

theorem clear_edge (p : Parameters) (bits query : List Bool)
    (hq : query.length ≤ CloseoutCapacity.capacity p.Aq p.Bq bits.length)
    (H : Fin (tapes p)→ℕ) (A : Fin (tapes p)→List Bool)
    (hin : ∀ i,A (clearSlot p i)=CloseoutCommonQueryClear.input bits query i)
    (hh : ∀ i,H (clearSlot p i)=0) :
    ∃ cost ≤ CloseoutCommonQueryClear.budget p.Aq p.Bq bits+1,∃ out,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program p) cost
        (stageStart p 2 H A) (stageStart p 3 H (install (clearSlot p) A out)) ∧
      out 26=List.replicate (CloseoutCapacity.capacity p.Aq p.Bq bits.length) false ∧
      out 0=frame bits:=by
  obtain ⟨out,actual,hquery,haddress⟩:=CloseoutCommonQueryClear.clear_run p.Aq p.Bq bits query hq
  obtain ⟨r,hr,heads,ht,hs⟩:=actual.focus_at (clearSlot p) (clear_injective p) H A hin hh
  have body:=ordinary_trace (o:=RecoveryOracle.correctedSat) (ports p)
    (RecoveryFocus.machine (clearSlot p) (CloseoutCommonQueryClear.machine p.Aq p.Bq)) _ _ r hr
  have halt:=(prefix_of_run
    (RecoveryFocus.machine (clearSlot p) (CloseoutCommonQueryClear.machine p.Aq p.Bq)) _ _ r hr).2
  have jump:=graph_return RecoveryOracle.correctedSat (ports p) (pieces p) 0 (next p) 2 3
    r.final halt (by rfl)
  have endpoint:=restart_data (pieces p 3).machine
    (RecoveryCalls.code (fun j=>(pieces p j).states) 3)
    r.final.heads H r.final.tapes (install (clearSlot p) A out) heads ht
  refine ⟨r.steps+1,by omega,out,?_,hquery,haddress⟩
  exact Eq.mp (congrArg (fun finish : (program p).Config=>
    OrdinaryOracleTrace RecoveryOracle.correctedSat (program p) (r.steps+1)
      (stageStart p 2 H A) finish) endpoint)
    (trans (graph_trace (ports p) (pieces p) 0 (next p) 2 body) jump)

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
