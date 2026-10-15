import Proof.MachineModel.OrdinarySourceSATLiftKernelCall

/-! The new oracle ask charges its literal framed length and resumes the
original source branch by the exact marker equality. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.QueryGraph
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ask_call {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (ports : Ports t)
    (q : Fin p.base.stateCount) (r : OracleReturn p.base.stateCount)
    (bits : List Bool) (cap : ℕ) (heads : Fin t → ℕ) (tapes : Fin t → List Bool)
    (hq : p.query q=some r) (hh : heads ports.queryTape=0)
    (hw : tapes ports.queryTape=ZeroPadding.pad cap (frame (fourth (value bits)).bits)) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w))
      ((frame (fourth (value bits)).bits).length+2)
      (atAsk w q ⟨0,heads,tapes⟩)
      (atSource w (if RecoveryOracle.sourceSAT (CanonicalBinary.bitsValue bits) then r.onTrue else r.onFalse)
        ⟨if RecoveryOracle.sourceSAT (CanonicalBinary.bitsValue bits) then r.onTrue else r.onFalse,heads,tapes⟩) := by
  let answer := RecoveryOracle.sourceSAT (CanonicalBinary.bitsValue bits)
  let target := if answer then r.onTrue else r.onFalse
  have agree : RecoveryOracle.correctedSat (CanonicalBinary.bitsValue (fourth (value bits)).bits)=answer := by
    rw [CanonicalBinary.bitsValue_natBits,query_agrees,value_eq_bitsValue]
  have ha := OrdinaryOracleStep.ask (oracle := RecoveryOracle.correctedSat)
    (program := ports.program (askPiece p t q)) (⟨0,heads,tapes⟩ : Configuration t 3)
    (fourth (value bits)).bits
    (List.replicate (cap-(frame (fourth (value bits)).bits).length) false)
    (⟨1,2⟩ : OracleReturn 3) rfl (by simp [askPiece,hq]) hh hw
  rw [agree] at ha
  have hbody := trace_piece w ports (askNode p q) _ (pieces_ask w q) (single ha)
  have hreturn := return_piece w ports (askNode p q) (sourceNode p target) _ _
    (pieces_ask w q) (pieces_source w target)
    (⟨if answer then 2 else 1,heads,tapes⟩ : Configuration t 3)
    (by cases answer <;> rfl) (by cases ha : answer <;> simp [next,askNode,hq,target,ha])
  have ht := OrdinaryOracleCompose.trans hbody hreturn
  exact ht

end NearCubicWires.RepairSource.OrdinarySourceSATLift.QueryGraph
