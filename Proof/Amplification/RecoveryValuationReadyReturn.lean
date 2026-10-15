import Proof.Amplification.RecoveryValuationRetained

/-! Full successful return of the capped table scan, retaining the scalar
query and source and exposing the exact physical lookup bit for its caller. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationCount
open LocalBitMultitape RecoveryExecution RecoveryValuationStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem finished_cfg {s : Nat} (d : Data) (count cap : Nat) (q : Fin s) :
    finished (cfg d count cap q) true=
      cfg {d with valid:=true} count cap (RecoveryCalls.controlCode graphSizes none) := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;>
      simp [finished,cfg,Data.cfg,RecoveryCalls.stopped,TapeEmbedding.config,Fin.addCases]

theorem ready_return (d : Data) (pre word : List Bool) (cap : Nat)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hc : 2*d.index.length+2≤d.capacity) (hfound : d.found=false) (hvalue : d.value=false) :
    ∃ r,runFrom machine (limit d.width cap) (cfg d 0 cap machine.start)=some r ∧
      r.steps≤limit d.width cap ∧ r.final.heads 7=0 ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        ∃ count out,count≤cap ∧ out.width=d.width ∧ out.index=d.index ∧ out.source=d.source ∧
          out.capacity=d.capacity ∧ out.row.length≤2*(d.width+1)+1 ∧ out.valid=true ∧
          out.value=FiniteValuation.lookup table (value d.index) ∧
          r.final=cfg out count cap (RecoveryCalls.controlCode graphSizes none) := by
  obtain ⟨r,hr,ht,hh,hvalid,hout⟩ := bounded_list d pre word cap hs hp hi hb
  obtain ⟨other,ho,_,_,_,hv⟩ := valuation_list_run d pre word cap hs hp hi hb hfound hvalue
  rw [hr] at ho
  have he := Option.some.inj ho
  cases he
  refine ⟨r,hr,ht,hh,hvalid,?_⟩
  intro table tail hparse
  obtain ⟨count,rest,hcount,hrows⟩ := readList_some d.width cap word table tail hparse
  have hsome : (readMany (readEntry d.width) count rest).isSome=true := by rw [hrows]; rfl
  let x : RecoveryValuationTable.Cursor := ⟨counted d count,rest⟩
  let y := (RepeatMachine.iterate RecoveryValuationTable.next count x).2
  have hx : RecoveryValuationTable.Inv d.width x := count_cursor d d.width cap count pre word rest hi rfl hb hs hp hcount
  have hy : RecoveryValuationTable.Inv d.width y := RecoveryValuationTable.iterate_inv count d.width x hx (by
    rw [RecoveryValuationTable.iterate_accepts]
    exact hsome)
  have hret := RecoveryValuationTable.iterate_retained count x
  have hcap := RecoveryValuationTable.iterate_capacity count x hc
  have hfinal := hout count rest hcount hsome
  rw [finished_cfg] at hfinal
  let out : Data := {y.data with valid:=true}
  change r.final=cfg out count cap (RecoveryCalls.controlCode graphSizes none) at hfinal
  obtain ⟨hcountcap,_⟩ := RecoveryCertificateCount.readCount_some cap count word rest hcount
  refine ⟨count,out,hcountcap,hret.1,hret.2.1,hret.2.2.1,hcap,hy.2.2.1,rfl,?_,hfinal⟩
  have hbit := (hv table tail hparse).2
  rw [hfinal] at hbit
  change [out.value]=[FiniteValuation.lookup table (value d.index)] at hbit
  exact List.singleton_inj.mp hbit

end NearCubicWires.RepairOrdinary.RecoveryValuationCount
