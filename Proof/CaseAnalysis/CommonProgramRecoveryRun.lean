import Proof.CaseAnalysis.CommonProgramRecoveryInput
import Proof.MachineModel.OrdinaryOracleComposeInitial

/-! Execute the actual live prefix and the original cold recovery through
the common control graph, sharing its already paid query padding. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def afterPrefix (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool):=
  install (prefixSlot p) (input p bits) out

def recovered (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config):=
  RecoveryFocus.config (recoverySlot p) (fun _=>0) (afterPrefix p bits out)
    (ZeroPadding.config (RecoveryBoundedCold.queryCaps (source p) p.k p.degree padding) final)

theorem live_recovery_trace (p : Parameters) (bits word : List Bool)
    (W padding fuel cost : ℕ) (out : Fin (prefixProgram p).base.tapeCount→List Bool)
    (actual : Ready RecoveryOracle.correctedSat (prefixProgram p) fuel
      (CloseoutCommonPrefix.input (work p) p.refuter p.k bits) out)
    (flag : readTapeBit (out (CloseoutCommonPrefix.firstSlots (work p) p.refuter p.k
      (CloseoutRetainedRefuter.old p.refuter (CloseoutSchedule.RefuterPrefix.flagPort (work p))))) 0=true)
    (fields : ∀ j,out (prefixRecoveryFields p j)=RecoveryBoundedCold.sharedWords word W padding j)
    (final : (recovery p).Config)
    (cold : OrdinaryOracleTrace RecoveryOracle.correctedSat (recovery p) cost
      (initialConfiguration (recovery p).base.machine
        (RecoveryBoundedCold.input (source p) p.k p.degree word W)) final)
    (hq : (final.tapes (RecoveryBoundedCold.queryPort (source p) p.k p.degree)).length≤cost) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (program p) (fuel+1+cost)
      (initialConfiguration (program p).base.machine (input p bits))
      (controlConfig (RecoveryCalls.code (fun j=>(pieces p j).states) 1)
        (recovered p bits out padding final)):=by
  let mid:=afterPrefix p bits out
  have hp:=actual.focus (ports p) (prefixSlot p) (prefix_injective p) rfl
    (input p bits) (fun _=>rfl)
  have hflag:readTapeBit (mid (liveFlag p)) 0=true:=by
    change readTapeBit (install (prefixSlot p) (input p bits) out (prefixSlot p _)) 0=true
    rw [install_slot _ (prefix_injective p)]
    exact flag
  have first:=hp.call (ports p) (pieces p) 0 (next p) 0 1 (by
    intro q
    change some (if readTapeBit (mid (liveFlag p)) 0 then (1 : Fin 6) else 5)=some 1
    rw [hflag]
    rfl)
  have padded:=RecoveryBoundedCold.query_padded_trace (source p) p.k p.degree
    (hierarchy p).coefficient (pad p) (code p) word W padding cost final cold hq
  have second:=focus_from_initial (p:=recovery p) (ports p) (recoverySlot p) (recovery_injective p)
    (recovery_query p) (fun _=>0) mid
    (RecoveryBoundedCold.queryInput (source p) p.k p.degree word W padding) _ padded.1
    (recovery_input p bits word W padding out fields) (fun _=>rfl)
  exact trans first (graph_trace (ports p) (pieces p) 0 (next p) 1 second)

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
