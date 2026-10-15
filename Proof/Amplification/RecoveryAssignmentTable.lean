import Proof.Amplification.RecoveryAssignmentTapes

/-! The actual counted table machine on the same fourteen tapes used by its
committed-prefix continuation, preserving all retained scalar words. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem table_run (d : Data) (pre word : List Bool) (cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hc : 2*d.index.length+2≤d.capacity) (hfound : d.found=false) (hvalue : d.value=false) :
    ∃ r,runFrom tableMachine (RecoveryValuationCount.limit d.width cap)
        (cfg d 0 cap binaryCount committed guard tableMachine.start)=some r ∧
      r.steps≤RecoveryValuationCount.limit d.width cap ∧ r.final.heads 7=0 ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        ∃ count out,count≤cap ∧ out.width=d.width ∧ out.index=d.index ∧ out.source=d.source ∧
          out.capacity=d.capacity ∧ out.row.length≤2*(d.width+1)+1 ∧ out.valid=true ∧
          out.value=FiniteValuation.lookup table (value d.index) ∧
          r.final=cfg out count cap binaryCount committed guard
            (RecoveryCalls.controlCode RecoveryValuationCount.graphSizes none) := by
  obtain ⟨base,hr,ht,hh,hvalid,hout⟩ := RecoveryValuationCount.ready_return d pre word cap hs hp hi hb hc hfound hvalue
  let extra : Fin 4→List Bool := ![frame binaryCount,frame committed,[guard],List.replicate d.capacity false]
  have hrun := TapeEmbedding.run_embed RecoveryValuationCount.machine (fun _ : Fin 4=>0) extra _ _ base hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 4=>0) extra base,hrun,ht,?_,?_,?_⟩
  · change base.final.heads 7=0
    exact hh
  · change base.final.tapes 7=_
    exact hvalid
  · intro table tail hparse
    obtain ⟨count,out,hcount,hw,hi,hs,hcap,hrow,hvalid,hvalue,hfinal⟩ := hout table tail hparse
    refine ⟨count,out,hcount,hw,hi,hs,hcap,hrow,hvalid,hvalue,?_⟩
    simp only [TapeEmbedding.receipt,hfinal,cfg,extra,hcap]

end NearCubicWires.RepairOrdinary.RecoveryAssignment
