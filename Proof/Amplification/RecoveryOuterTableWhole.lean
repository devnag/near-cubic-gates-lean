import Proof.Amplification.RecoveryOuterTableReturn

namespace NearCubicWires.RepairOrdinary.RecoveryOuterTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure RecoveryOuterLeaf
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
open RecoveryRowTable (tableCheck)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem initial_inv (limit : Nat) (word outerBits innerBits pre : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (x : State) (hx : x.Valid word outerBits innerBits) (hj : x.outer.total=0) (hn : x.total ≤ limit)
    (hp : readMany (readRow x.inner.row.width) x.total innerBits=some (innerRows,innerRest))
    (hs : x.outer.base.source=pre++frame outerBits) (hpos : x.outer.base.pos=pre.length)
    (hcap : limit*(RecoveryRowLookupStream.budget x.outer.base.state.bits.length+3)+5 ≤ x.outer.lookupCapacity) :
    Inv x.outer.base.state.bits.length limit word outerBits innerBits innerRows innerRest ⟨x,[],outerBits,pre⟩ := by
  refine ⟨hx,rfl,?_,?_,rfl,rfl,?_,hn,hs,hpos,?_,hcap⟩
  · exact hj
  · change readMany (readRow x.outer.base.state.bits.length) x.outer.total outerBits=some ([],outerBits)
    rw [hj]; rfl
  · have hw : x.inner.row.width=x.outer.base.state.bits.length := hx.2.2.1.2.1
    rw [hw] at hp
    exact hp
  · rw [hj]; omega

theorem checked_table_run (limit total : Nat) (word outerBits innerBits pre : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (x : State) (hx : x.Valid word outerBits innerBits) (hj : x.outer.total=0)
    (hn : x.total ≤ limit) (hcount : total ≤ limit)
    (hp : readMany (readRow x.inner.row.width) x.total innerBits=some (innerRows,innerRest))
    (hs : x.outer.base.source=pre++frame outerBits) (hpos : x.outer.base.pos=pre.length)
    (hcap : limit*(RecoveryRowLookupStream.budget x.outer.base.state.bits.length+3)+5 ≤ x.outer.lookupCapacity) :
    ∃ r,runFrom returnMachine (returnBudget x.outer.base.state.bits.length limit total)
        (tableCfg ⟨x,[],outerBits,pre⟩ total returnMachine.start)=some r ∧
      r.steps ≤ returnBudget x.outer.base.state.bits.length limit total ∧ r.final.heads 50=0 ∧
      r.final.tapes 50=[(readMany (readRow x.outer.base.state.bits.length) total outerBits).any
        (fun pair=>checkFrom [] pair.1 && pair.1.all (leafCheck (predicate innerRows)))] ∧
      (tableCheck x.outer.base.state.bits.length (predicate innerRows) total [] outerBits=true → ∃ out : Cursor,
        r.final=tableCfg out total r.final.control ∧
        Inv x.outer.base.state.bits.length limit word outerBits innerBits innerRows innerRest out ∧ out.data.outer.total=total) := by
  have hi := initial_inv limit word outerBits innerBits pre innerRows innerRest x hx hj hn hp hs hpos hcap
  have hb : x.outer.total+total ≤ limit := by rw [hj]; omega
  obtain ⟨r,hr,hb,hh,ht,hout⟩ := table_return_run x.outer.base.state.bits.length limit total word outerBits innerBits
    innerRows innerRest ⟨x,[],outerBits,pre⟩ hi hb
  refine ⟨r,hr,hb,hh,?_,?_⟩
  · simpa only [RecoveryRowTable.table_check_parser] using ht
  · intro ha
    obtain ⟨out,hf,hv,ht⟩ := hout ha
    exact ⟨out,hf,hv,by simpa only [hj,Nat.zero_add] using ht⟩

end NearCubicWires.RepairOrdinary.RecoveryOuterTable
