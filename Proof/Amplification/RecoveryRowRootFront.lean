import Proof.Amplification.RecoveryGatedSequence

namespace NearCubicWires.RepairOrdinary.RecoveryRowRoot
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tableMachine := TapeEmbedding.machine 1 RecoveryRowTable.returnMachine

theorem table_cfg_embed {s : Nat} (x : RecoveryRowTable.Cursor) (total : Nat) (key : List Bool) (q : Fin s) :
    TapeEmbedding.config (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame key) (RecoveryRowTable.tableCfg x total q)=
      (⟨x.data,total,key⟩ : State).cfg q := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem table_front_run (limit : Nat) (word bits pre : List Bool) (x : State)
    (hx : x.Valid word bits) (hj : x.data.total=0) (hn : x.total ≤ limit)
    (hs : x.data.base.source=pre++frame bits) (hp : x.data.base.pos=pre.length)
    (hcap : limit*(RecoveryRowLookupStream.budget x.data.base.state.bits.length+3)+5 ≤ x.data.lookupCapacity) :
    ∃ r,runFrom tableMachine (RecoveryRowTable.returnBudget x.data.base.state.bits.length limit x.total)
        (x.cfg tableMachine.start)=some r ∧
      r.steps ≤ RecoveryRowTable.returnBudget x.data.base.state.bits.length limit x.total ∧
      r.final.heads 50=0 ∧
      r.final.tapes 50=[RecoveryRowTable.tableCheck x.data.base.state.bits.length
        (tableLeafPredicate x.data word) x.total [] bits] ∧
      (RecoveryRowTable.tableCheck x.data.base.state.bits.length (tableLeafPredicate x.data word) x.total [] bits=true →
        ∃ out : RecoveryRowTable.Cursor,
          r.final=(⟨out.data,x.total,x.key⟩ : State).cfg r.final.control ∧
          RecoveryRowTable.Inv x.data.base.state.bits.length limit word bits (tableLeafPredicate x.data word) out ∧
          out.data.total=x.total) := by
  obtain ⟨base,hr,hb,hh,ht,hout⟩ := RecoveryRowTable.checked_table_run limit x.total word bits pre x.data
    hx.1 hj hn hs hp hcap
  let r := TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame x.key) base
  have he := TapeEmbedding.run_embed RecoveryRowTable.returnMachine (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame x.key)
    (RecoveryRowTable.returnBudget x.data.base.state.bits.length limit x.total) _ base hr
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

end NearCubicWires.RepairOrdinary.RecoveryRowRoot
