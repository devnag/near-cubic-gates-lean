import Proof.Amplification.RecoveryGatedBooleanStart

namespace NearCubicWires.RepairOrdinary.RecoveryOuterRoot
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem whole_root_run (limit : Nat) (word bits innerBits pre : List Bool) (innerRows : List Row) (innerRest : List Bool) (x : State)
    (hx : x.Valid word bits innerBits) (hj : x.data.outer.total=0) (hn : x.total ≤ limit)
    (hinnerBound : x.data.total ≤ limit)
    (hinner : readMany (readRow x.data.inner.row.width) x.data.total innerBits=some (innerRows,innerRest))
    (hs : x.data.outer.base.source=pre++frame bits) (hp : x.data.outer.base.pos=pre.length)
    (hcap : limit*(RecoveryRowLookupStream.budget x.data.outer.base.state.bits.length+3)+5 ≤ x.data.outer.lookupCapacity) :
    ∃ r,runFrom wholeMachine (wholeBudget x.data.outer.base.state.bits.length limit x.total)
        (x.cfg wholeMachine.start)=some r ∧
      r.steps ≤ wholeBudget x.data.outer.base.state.bits.length limit x.total ∧
      r.final.heads 50=0 ∧ r.final.tapes 50=[wholeAnswer x innerRows bits] ∧
      (wholeAnswer x innerRows bits=true →
        ∃ values,CanonicalBinary.decodeBalancedList (RadixSemantics.value x.key)=some values ∧
          values.all (RecoveryOuterLeaf.predicate innerRows)=true) := by
  obtain ⟨first,hr0,_,hh0,ht0,hout⟩ := table_front_run limit word bits innerBits pre innerRows innerRest x hx hj hinnerBound hn hinner hs hp hcap
  have hnxt := continuation_run limit word bits innerBits innerRows innerRest x hx first.final hout
  have hrun := RecoveryGatedSequence.boolean_start_run tableMachine rootMachine 50
    (RecoveryOuterTable.returnBudget x.data.outer.base.state.bits.length limit x.total)
    (rootBudget x.data.outer.base.state.bits.length x.total) x.heads x.tapes first
    (RecoveryRowTable.tableCheck x.data.outer.base.state.bits.length (RecoveryOuterLeaf.predicate innerRows) x.total [] bits)
    (wholeAnswer x innerRows bits) hr0 hh0 ht0 (answer_reject x innerRows bits) hnxt
  obtain ⟨r,hr,hb,hh,ht⟩ := hrun
  exact ⟨r,hr,hb,hh,ht,answer_sound x innerRows bits⟩

end NearCubicWires.RepairOrdinary.RecoveryOuterRoot
