import Proof.Amplification.RecoveryValuationCursor

/-! Exact successful return of the actual capped-list program, exposing
the produced count and the physical cursor at the next certificate field. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationCount
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem list_cursor (d : Data) (pre word : List Bool) (cap : Nat)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1) :
    ∃ r,runFrom machine (limit d.width cap) (cfg d 0 cap machine.start)=some r ∧
      r.steps≤limit d.width cap ∧ r.final.heads 7=0 ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        ∃ count out,count≤cap ∧ out.width=d.width ∧ out.index=d.index ∧ out.source=d.source ∧
          out.pos=d.pos+2*(count*(d.width+2)+1) ∧ tail=word.drop (count*(d.width+2)+1) ∧
          r.final=cfg out count cap (RecoveryCalls.controlCode graphSizes none) := by
  obtain ⟨r,hr,hn,hh,ht,hf⟩ := bounded_list d pre word cap hs hp hi hb
  refine ⟨r,hr,hn,hh,ht,?_⟩
  intro table tail hparse
  obtain ⟨count,rest,hcount,hrows⟩ := readList_some d.width cap word table tail hparse
  obtain ⟨hcap,hword⟩ := RecoveryCertificateCount.readCount_some cap count word rest hcount
  let x : RecoveryValuationTable.Cursor := ⟨counted d count,rest⟩
  let y := (RepeatMachine.iterate RecoveryValuationTable.next count x).2
  let out : Data := {y.data with valid:=true}
  have hout := hf count rest hcount (by rw [hrows]; rfl)
  rw [finished_cfg] at hout
  change r.final=cfg out count cap (RecoveryCalls.controlCode graphSizes none) at hout
  have hret := RecoveryValuationTable.iterate_retained count x
  have hcursor := RecoveryValuationTable.iterate_cursor count x table tail hrows
  refine ⟨count,out,hcap,hret.1,hret.2.1,hret.2.2.1,?_,?_,hout⟩
  · change y.data.pos=d.pos+2*(count*(d.width+2)+1)
    calc
      _ = (counted d count).pos+2*count*(d.width+1) := hcursor.2.2
      _ = _ := by unfold counted; ring
  · have hword' : word=(List.replicate count true++[false])++rest := by
      simpa only [List.append_assoc,List.singleton_append] using hword
    have hdrop : word.drop (count+1)=rest := by
      rw [hword']
      exact List.drop_left' (by simp)
    have htail : tail=word.drop ((count+1)+count*(d.width+1)) := by
      rw [←List.drop_drop,hdrop]
      exact hcursor.1
    have he : (count+1)+count*(d.width+1)=count*(d.width+2)+1 := by ring
    rw [he] at htail
    exact htail

end NearCubicWires.RepairOrdinary.RecoveryValuationCount
