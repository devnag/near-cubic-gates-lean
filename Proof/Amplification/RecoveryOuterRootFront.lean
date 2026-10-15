import Proof.Amplification.RecoveryOuterRootLookup

namespace NearCubicWires.RepairOrdinary.RecoveryOuterRoot
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
open RecoveryRowTable (tableCheck)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tableMachine := TapeEmbedding.machine 1 RecoveryOuterTable.returnMachine

theorem table_cfg_embed {s : Nat} (x : RecoveryOuterTable.Cursor) (total : Nat) (key : List Bool) (q : Fin s) :
    TapeEmbedding.config (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame key) (RecoveryOuterTable.tableCfg x total q)=
      (⟨x.data,total,key⟩ : State).cfg q := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem table_front_run (limit : Nat) (word outerBits innerBits pre : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (x : State) (hx : x.Valid word outerBits innerBits) (hj : x.data.outer.total=0)
    (hn : x.data.total ≤ limit) (hcount : x.total ≤ limit)
    (hp : readMany (readRow x.data.inner.row.width) x.data.total innerBits=some (innerRows,innerRest))
    (hs : x.data.outer.base.source=pre++frame outerBits) (hpos : x.data.outer.base.pos=pre.length)
    (hcap : limit*(RecoveryRowLookupStream.budget x.data.outer.base.state.bits.length+3)+5 ≤ x.data.outer.lookupCapacity) :
    ∃ r,runFrom tableMachine (RecoveryOuterTable.returnBudget x.data.outer.base.state.bits.length limit x.total)
        (x.cfg tableMachine.start)=some r ∧
      r.steps ≤ RecoveryOuterTable.returnBudget x.data.outer.base.state.bits.length limit x.total ∧
      r.final.heads 50=0 ∧
      r.final.tapes 50=[tableCheck x.data.outer.base.state.bits.length (RecoveryOuterLeaf.predicate innerRows) x.total [] outerBits] ∧
      (tableCheck x.data.outer.base.state.bits.length (RecoveryOuterLeaf.predicate innerRows) x.total [] outerBits=true →
        ∃ out : RecoveryOuterTable.Cursor,
          r.final=(⟨out.data,x.total,x.key⟩ : State).cfg r.final.control ∧
          RecoveryOuterTable.Inv x.data.outer.base.state.bits.length limit word outerBits innerBits innerRows innerRest out ∧
          out.data.outer.total=x.total) := by
  obtain ⟨base,hr,hb,hh,ht,hout⟩ := RecoveryOuterTable.checked_table_run limit x.total word outerBits innerBits pre innerRows innerRest
    x.data hx.1 hj hn hcount hp hs hpos hcap
  let r := TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame x.key) base
  have he := TapeEmbedding.run_embed RecoveryOuterTable.returnMachine (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame x.key)
    (RecoveryOuterTable.returnBudget x.data.outer.base.state.bits.length limit x.total) _ base hr
  rw [table_cfg_embed] at he
  refine ⟨r,he,hb,hh,?_,?_⟩
  · change base.final.tapes 50=_
    rw [ht,RecoveryRowTable.table_check_parser]
  · intro ha
    obtain ⟨out,hf,hi,hj⟩ := hout ha
    refine ⟨out,?_,hi,hj⟩
    change TapeEmbedding.config (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame x.key) base.final=_
    rw [hf,table_cfg_embed]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryOuterRoot
