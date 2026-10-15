import Proof.Amplification.RecoveryBankGate

/-! The selected nested checker keeps the complete inner table and outer
checker on disjoint banks. Preparation produces both copies of innerBits. -/
namespace NearCubicWires.RepairOrdinary.RecoveryNestedTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  inner : Children
  innerTotal : Nat
  outer : RecoveryOuterRoot.State

noncomputable def State.innerCfg {s : Nat} (x : State) (q : Fin s) : Configuration 69 s :=
  RecoveryRowTable.tableCfg ⟨x.inner,[],[],[]⟩ x.innerTotal q
noncomputable def State.cfg {s : Nat} (x : State) (q : Fin s) : Configuration 155 s :=
  RecoveryBankPair.cfg (x.innerCfg (0 : Fin 1)).heads (x.innerCfg (0 : Fin 1)).tapes x.outer.heads x.outer.tapes q

noncomputable def machine := RecoveryBankPair.gateMachine RecoveryRowTable.returnMachine RecoveryOuterRoot.wholeMachine 50 50
def budget (x : State) (limit : Nat) :=
  RecoveryRowTable.returnBudget x.inner.base.state.bits.length limit x.innerTotal+
    (RecoveryOuterRoot.wholeBudget x.outer.data.outer.base.state.bits.length limit x.outer.total+1+1)+2

def innerAnswer (x : State) (word bits : List Bool) :=
  (readMany (readRow x.inner.base.state.bits.length) x.innerTotal bits).any
    (fun pair=>checkFrom [] pair.1 && pair.1.all (leafCheck (tableLeafPredicate x.inner word)))
def answer (x : State) (word innerBits outerBits : List Bool) :=
  (readMany (readRow x.inner.base.state.bits.length) x.innerTotal innerBits).any
    (fun pair=>(checkFrom [] pair.1 && pair.1.all (leafCheck (tableLeafPredicate x.inner word))) &&
      RecoveryOuterRoot.wholeAnswer x.outer pair.1 outerBits)

structure Prepared (x : State) (limit : Nat) (word innerBits outerBits innerPre outerPre : List Bool) : Prop where
  innerValid : x.inner.Valid word innerBits
  outerValid : x.outer.Valid word outerBits innerBits
  innerZero : x.inner.total=0
  outerZero : x.outer.data.outer.total=0
  innerBound : x.innerTotal ≤ limit
  outerBound : x.outer.total ≤ limit
  copiedCount : x.outer.data.total=x.innerTotal
  copiedWidth : x.outer.data.outer.base.state.bits.length=x.inner.base.state.bits.length
  innerSource : x.inner.base.source=innerPre++frame innerBits
  innerPos : x.inner.base.pos=innerPre.length
  outerSource : x.outer.data.outer.base.source=outerPre++frame outerBits
  outerPos : x.outer.data.outer.base.pos=outerPre.length
  innerCapacity : limit*(RecoveryRowLookupStream.budget x.inner.base.state.bits.length+3)+5 ≤ x.inner.lookupCapacity
  outerCapacity : limit*(RecoveryRowLookupStream.budget x.outer.data.outer.base.state.bits.length+3)+5 ≤ x.outer.data.outer.lookupCapacity

theorem inner_source_cfg {s : Nat} (x : State) (bits pre : List Bool) (q : Fin s) :
    RecoveryRowTable.tableCfg ⟨x.inner,[],bits,pre⟩ x.innerTotal q=x.innerCfg q := rfl

theorem inner_run (x : State) (limit : Nat) (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word innerBits outerBits innerPre outerPre) :
    ∃ r,runFrom RecoveryRowTable.returnMachine
        (RecoveryRowTable.returnBudget x.inner.base.state.bits.length limit x.innerTotal)
        (x.innerCfg RecoveryRowTable.returnMachine.start)=some r ∧
      r.final.heads 50=0 ∧ r.final.tapes 50=[innerAnswer x word innerBits] := by
  obtain ⟨r,hr,_,hh,ht,_⟩ := RecoveryRowTable.checked_table_run limit x.innerTotal word innerBits innerPre
    x.inner hx.innerValid hx.innerZero hx.innerBound hx.innerSource hx.innerPos hx.innerCapacity
  exact ⟨r,hr,hh,ht⟩

end NearCubicWires.RepairOrdinary.RecoveryNestedTable
