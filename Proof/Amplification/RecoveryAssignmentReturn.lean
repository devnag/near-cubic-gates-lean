import Proof.Amplification.RecoveryAssignmentSelectorReturn

/-! Full successful return of the same all-code assignment machine. It
exposes exactly the retained data needed by its next paid reuse. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem assignment_return (d : Data) (pre word : List Bool) (cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hw : binaryCount.length=d.index.length) (hc : 2*binaryCount.length+3≤d.capacity)
    (hbit : RecoveryCommittedBit.rawCost d.index committed≤d.capacity)
    (hfound : d.found=false) (hvalue : d.value=false)
    (table : FiniteValuation.Table) (tail : List Bool)
    (hparse : readList cap (readEntry d.width) word=some (table,tail)) :
    ∃ r,runFrom machine (cost d cap binaryCount committed guard)
        (cfg d 0 cap binaryCount committed guard machine.start)=some r ∧
      r.steps≤cost d cap binaryCount committed guard ∧
      ∃ count out guard',count≤cap ∧ out.width=d.width ∧ out.index.length=d.index.length ∧
        out.source=d.source ∧ out.capacity=d.capacity ∧ out.row.length≤2*(d.width+1)+1 ∧
        out.valid=true ∧ out.value=FiniteValuation.assignment
          (value committed) (value binaryCount) table (value d.index) ∧
        r.final=cfg out count cap binaryCount committed guard' (RecoveryCalls.controlCode sizes none) := by
  obtain ⟨r0,hr0,_,hh0,hv0,hout0⟩ := table_run d pre word cap binaryCount committed guard
    hs hp hi hb (by omega) hfound hvalue
  obtain ⟨count,out0,hcount,hwidth,hindex,hsource,hcapacity,hrow,hvalid,hlookup,hout0⟩ := hout0 table tail hparse
  obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next 0 1 _ _ r0 hr0 (by
    simp [next,Configuration.scanned,hh0,hv0,hparse,readTapeBit,List.getD])
  rw [hout0] at h0
  change Timed machine n0 (cfg d 0 cap binaryCount committed guard machine.start)
    (cfg out0 count cap binaryCount committed guard (RecoveryCalls.code sizes 1 selectorMachine.start)) at h0
  obtain ⟨r1,hr1,_,out,guard',hw1,hi1,hs1,_,hr1row,hc1,hv1,hvalue1,hout1⟩ :=
    selector_return out0 count cap binaryCount committed guard
      (by rw [hindex]; exact hw) (by rw [hcapacity]; exact hc)
      (by rw [hindex,hcapacity]; exact hbit)
  obtain ⟨n1,hn1,h1⟩ := stop_receipt sizes programs 0 next 1 _ _ r1 hr1 (by rfl)
  rw [hout1] at h1
  change Timed machine n1
    (cfg out0 count cap binaryCount committed guard (RecoveryCalls.code sizes 1 selectorMachine.start))
    (cfg out count cap binaryCount committed guard' (RecoveryCalls.controlCode sizes none)) at h1
  have hall := h0.trans h1
  have hn : n0+n1≤cost d cap binaryCount committed guard := by
    have he : RecoveryPrefixAssignment.cost (prefixData out0 binaryCount committed guard)=
        RecoveryPrefixAssignment.cost (prefixData d binaryCount committed guard) := by
      simp [RecoveryPrefixAssignment.cost,prefixData,hindex]
    rw [he] at hn1
    unfold cost
    omega
  obtain ⟨r,hr,hf,ht⟩ := hall.run (by simp [RecoveryCalls.machine,machine,cfg,TapeEmbedding.config,RecoveryValuationCount.cfg,Data.cfg])
  have hm := runFrom_moreFuel machine (n0+n1)
    (cost d cap binaryCount committed guard-(n0+n1)) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,ht.le.trans hn,count,out,guard',hcount,hw1.trans hwidth,?_,hs1.trans hsource,
    hc1.trans hcapacity,?_,hv1.trans hvalid,?_,hf⟩
  · rw [hi1,hindex]
  · rw [hr1row]
    exact hrow
  · simpa only [hindex,hlookup,FiniteValuation.assignment] using hvalue1

end NearCubicWires.RepairOrdinary.RecoveryAssignment
