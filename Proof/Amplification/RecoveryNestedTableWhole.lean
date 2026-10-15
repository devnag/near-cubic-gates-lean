import Proof.Amplification.RecoveryNestedTableOuter

namespace NearCubicWires.RepairOrdinary.RecoveryNestedTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem nested_run (x : State) (limit : Nat) (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word innerBits outerBits innerPre outerPre) :
    ∃ r,runFrom machine (budget x limit) (x.cfg machine.start)=some r ∧
      r.steps ≤ budget x limit ∧ r.final.heads 50=0 ∧ r.final.tapes 50=[answer x word innerBits outerBits] ∧
      (answer x word innerBits outerBits=true → ∃ codes,
        BalancedCNFSATEncoding.decodeNestedBalancedCNFPayload (RadixSemantics.value x.outer.key)=some codes ∧
        codes.all (tableLeafPredicate x.inner word)=true) := by
  have hi := inner_run x limit word innerBits outerBits innerPre outerPre hx
  obtain ⟨first,hr0,hh0,ht0⟩ := hi
  have ho := outer_run x limit word innerBits outerBits innerPre outerPre hx
  have hrun := RecoveryBankPair.gate_run RecoveryRowTable.returnMachine RecoveryOuterRoot.wholeMachine
    (50 : Fin 69) (50 : Fin 86)
    (RecoveryRowTable.returnBudget x.inner.base.state.bits.length limit x.innerTotal)
    (RecoveryOuterRoot.wholeBudget x.outer.data.outer.base.state.bits.length limit x.outer.total)
    (x.innerCfg (0 : Fin 1)).heads (x.innerCfg (0 : Fin 1)).tapes x.outer.heads x.outer.tapes
    (innerAnswer x word innerBits) (answer x word innerBits outerBits) first hr0 hh0 ht0 ho
  obtain ⟨r,hr,hb,hh,ht⟩ := hrun
  refine ⟨r,hr,hb,hh,?_,answer_sound x word innerBits outerBits⟩
  exact ht.trans (congrArg (fun b : Bool=>[b]) (inner_answer_and x word innerBits outerBits))

end NearCubicWires.RepairOrdinary.RecoveryNestedTable
