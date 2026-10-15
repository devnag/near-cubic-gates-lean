import Proof.Amplification.RecoveryValuationReturn

/-! Retain the successful native parser's exact count/cursor through the
inverse-padding bridge. The actual short backing remains a real execution. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem parser_retained (bits word : List Bool) :
    ∃ r,runFrom machine (RecoveryValuationCount.limit (width bits) (cap bits))
        ⟨machine.start,heads,tapes bits word⟩=some r ∧
      r.final.heads 7=0 ∧
      r.final.tapes 7=[(readList (cap bits) (readEntry (width bits)) word).isSome] ∧
      ∀ table tail,readList (cap bits) (readEntry (width bits)) word=some (table,tail) →
        ∃ count out,count≤cap bits ∧ out.width=width bits ∧ out.index=RecoveryColdHeader.zeroWord bits ∧
          out.source=frame word ∧ out.pos=2*(count*(width bits+2)+1) ∧
          tail=word.drop (count*(width bits+2)+1) ∧
          ZeroPadding.config (caps bits) r.final=RecoveryValuationCount.cfg out count (cap bits)
            (RecoveryCalls.controlCode RecoveryValuationCount.graphSizes none) := by
  have hi : (data bits word).index.length=(data bits word).width := RecoveryColdHeader.zero_length bits
  obtain ⟨base,hbase,_,hh,ht,hout⟩ := RecoveryValuationCount.list_cursor (data bits word) [] word (cap bits)
    rfl rfl hi (by simp [data])
  change runFrom machine (RecoveryValuationCount.limit (width bits) (cap bits))
    (RecoveryValuationCount.cfg (data bits word) 0 (cap bits) machine.start)=some base at hbase
  rw [←padded_input bits word] at hbase
  obtain ⟨r,hr,hf,_,_⟩ := ZeroPadding.run_unpad machine (caps bits)
    (RecoveryValuationCount.limit (width bits) (cap bits)) _ base hbase
  refine ⟨r,hr,?_,?_,?_⟩
  · have h := congrArg (fun c=>c.heads (7 : Fin 10)) hf
    exact h.trans hh
  · have h := congrArg (fun c=>c.tapes (7 : Fin 10)) hf
    simp only [ZeroPadding.config,caps,Fin.isValue,show (7 : Fin 10).val≠6 by decide,if_false,ZeroPadding.pad_zero] at h
    exact h.trans ht
  · intro table tail hparse
    obtain ⟨count,out,hc,hw,hi,hs,hpos,htail,hfinal⟩ := hout table tail hparse
    refine ⟨count,out,hc,hw,hi,hs,?_,htail,hf.trans hfinal⟩
    simpa only [data,Nat.zero_add] using hpos

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
