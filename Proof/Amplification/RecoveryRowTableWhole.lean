import Proof.Amplification.RecoveryRowTableReturn

/-! Complete ordinary table checker with its literal Boolean result and
successful reusable endpoint. The caller supplies the retained table copy
and the actual bounded count driver; both are charged at preparation. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem initial_inv (limit : Nat) (word bits pre : List Bool) (x : Children)
    (hx : x.Valid word bits) (hj : x.total=0)
    (hs : x.base.source=pre++RepairOrdinary.frame bits) (hp : x.base.pos=pre.length)
    (hcap : limit*(RecoveryRowLookupStream.budget x.base.state.bits.length+3)+5 ≤ x.lookupCapacity) :
    Inv x.base.state.bits.length limit word bits (tableLeafPredicate x word) ⟨x,[],bits,pre⟩ := by
  refine ⟨hx,rfl,?_,?_,rfl,rfl,rfl,hs,hp,?_,hcap⟩
  · exact hj
  · change readMany (readRow x.base.state.bits.length) x.total bits=some ([],bits)
    rw [hj]; rfl
  · rw [hj]; omega

theorem checked_table_run (limit total : Nat) (word bits pre : List Bool) (x : Children)
    (hx : x.Valid word bits) (hj : x.total=0) (hn : total ≤ limit)
    (hs : x.base.source=pre++RepairOrdinary.frame bits) (hp : x.base.pos=pre.length)
    (hcap : limit*(RecoveryRowLookupStream.budget x.base.state.bits.length+3)+5 ≤ x.lookupCapacity) :
    ∃ r,runFrom returnMachine (returnBudget x.base.state.bits.length limit total)
        (tableCfg ⟨x,[],bits,pre⟩ total returnMachine.start)=some r ∧
      r.steps ≤ returnBudget x.base.state.bits.length limit total ∧ r.final.heads 50=0 ∧
      r.final.tapes 50=[(readMany (readRow x.base.state.bits.length) total bits).any
        (fun pair=>checkFrom [] pair.1 && pair.1.all (leafCheck (tableLeafPredicate x word)))] ∧
      (tableCheck x.base.state.bits.length (tableLeafPredicate x word) total [] bits=true → ∃ out : Cursor,
        r.final=tableCfg out total r.final.control ∧
        Inv x.base.state.bits.length limit word bits (tableLeafPredicate x word) out ∧ out.data.total=total) := by
  have hi := initial_inv limit word bits pre x hx hj hs hp hcap
  have hbound : x.total+total ≤ limit := by simpa only [hj,Nat.zero_add] using hn
  obtain ⟨r,hr,hb,hh,ht,hout⟩ := table_return_run x.base.state.bits.length limit total word bits
    (tableLeafPredicate x word) ⟨x,[],bits,pre⟩ hi hbound
  refine ⟨r,hr,hb,hh,?_,?_⟩
  · simpa only [table_check_parser] using ht
  · intro ha
    obtain ⟨out,hf,hvalid,hn⟩ := hout ha
    exact ⟨out,hf,hvalid,by simpa only [hj,Nat.zero_add] using hn⟩

theorem table_return_answer (width : Nat) (P : Nat→Bool) (total : Nat) (x : Cursor)
    (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow width) total x.input=some (rows,rest)) :
    tableCheck width P total x.prior x.input=(checkFrom x.prior rows && rows.all (leafCheck P)) := by
  rw [table_check_parser,hp]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRowTable
