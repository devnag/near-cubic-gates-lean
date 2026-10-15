import Proof.CaseAnalysis.CommonProgramTwoRecovered
import Proof.CaseAnalysis.CommonProgramTwoRun

/-! The true recovery flag enters the actual Case2 worker using only the
same recovery result and retained address; its output halts the common graph. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def recoveryFlagLocal (p : Parameters) : Fin (rn p):=
  (369 : Fin 790).natAdd (RecoveryBoundedCold.oldTapes (source p) p.k p.degree)

theorem recovered_flag (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config) (flag : Bool)
    (hf : readTapeBit (final.tapes (recoveryFlagLocal p)) 0=flag)
    (hh : final.heads (recoveryFlagLocal p)=0) :
    (recovered p bits out padding final).scanned (recoveryFlag p)=flag:=by
  have hq:recoveryFlagLocal p≠RecoveryBoundedCold.queryPort (source p) p.k p.degree:=by
    intro he
    have hv:=congrArg Fin.val he
    change RecoveryBoundedCold.oldTapes (source p) p.k p.degree+369=
      RecoveryBoundedCold.oldTapes (source p) p.k p.degree+356 at hv
    omega
  have ht:=recovered_word p bits out padding final _ hq
  have hp:=(recovered_heads p bits out padding final (recoveryFlagLocal p)).trans hh
  exact (congrArg₂ readTapeBit ht hp).trans hf

theorem two_branch (p : Parameters) (bits word description : List Bool)
    (R B padding fuel : ℕ) (out : Fin (prefixProgram p).base.tapeCount→List Bool)
    (final : (recovery p).Config)
    (halt : (recovery p).base.machine.halted final.control=true)
    (flag : readTapeBit (final.tapes (recoveryFlagLocal p)) 0=true)
    (flagHead : final.heads (recoveryFlagLocal p)=0)
    (ha : out ⟨0,(prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩=frame bits)
    (fields : ∀ j,final.tapes (twoRecoveryLocal p j)=twoRecoveryWords word description R B j)
    (heads : ∀ j,final.heads (twoRecoveryLocal p j)=0)
    (answer : Fin (tn p)→List Bool)
    (actual : ClockJoin.ReadyRun (two p) fuel (twoInput p word description (frame bits) R B) answer) :
    ∃ cost ≤ fuel+2,∃ result,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program p) cost
        (controlConfig (RecoveryCalls.code (fun j=>(pieces p j).states) 1)
          (recovered p bits out padding final)) result ∧
      (program p).base.machine.halted result.control=true ∧
      result.tapes (ports p).outputTape=answer (twoLocal p 5):=by
  let c:=recovered p bits out padding final
  have entry:=two_recovered_entry p bits word description R B padding out final ha fields heads
  have hf:=recovered_flag p bits out padding final true flag flagHead
  have jump:=graph_return RecoveryOracle.correctedSat (ports p) (pieces p) 0 (next p) 1 4 c halt (by
    change some (if c.scanned (recoveryFlag p) then (4 : Fin 6) else 2)=some 4
    rw [hf]
    rfl)
  obtain ⟨cost,hcost,result,hr,hh,ht⟩:=two_finish p fuel _ answer actual c.heads c.tapes entry.1 entry.2
  refine ⟨1+cost,by omega,result,trans jump hr,hh,ht⟩

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
