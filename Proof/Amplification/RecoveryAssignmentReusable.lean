import Proof.Amplification.RecoveryAssignmentReuseTapes

/-! The complete reusable assignment lookup: erase the old counter, clear
flags and position drivers, execute table/prefix lookup, then rewind every
local head. Every operation is part of the same finite ordinary machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scan_run (d : Data) (word : List Bool) (cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (sourceCapacity total resetCapacity : Nat)
    (hs : d.source=frame word) (hp : d.pos=0)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hw : binaryCount.length=d.index.length) (hc : 2*binaryCount.length+3≤d.capacity)
    (hbit : RecoveryCommittedBit.rawCost d.index committed≤d.capacity)
    (hreset : cost d cap binaryCount committed guard+2≤resetCapacity) :
    ∃ r,run scanMachine (2*cost d cap binaryCount committed guard+6)
        (reuseTapes d 0 cap binaryCount committed guard sourceCapacity total resetCapacity)=some r ∧
      r.steps≤2*cost d cap binaryCount committed guard+6 ∧ (∀ i,r.final.heads i=0) ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        ∃ count out guard',count≤cap ∧ out.width=d.width ∧ out.index.length=d.index.length ∧
          out.source=d.source ∧ out.pos=0 ∧ out.capacity=d.capacity ∧ out.row.length≤2*(d.width+1)+1 ∧
          out.valid=true ∧ out.value=FiniteValuation.assignment
            (value committed) (value binaryCount) table (value d.index) ∧
          r.final.tapes=reuseTapes out count cap binaryCount committed guard' sourceCapacity total resetCapacity := by
  obtain ⟨base,hr,ht,hh,hvalid,hout⟩ := rewind_run d word cap binaryCount committed guard sourceCapacity total resetCapacity
    hs hp hi hb hw hc hbit hreset
  have hrun := TapeEmbedding.run_embed rewindMachine (fun _ : Fin 1=>0)
    (fun _ : Fin 1=>List.replicate total true) _ _ base hr
  have hinput : TapeEmbedding.config (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate total true)
      (initialConfiguration rewindMachine (readyTapes d 0 cap binaryCount committed guard sourceCapacity total resetCapacity))=
      initialConfiguration scanMachine (reuseTapes d 0 cap binaryCount committed guard sourceCapacity total resetCapacity) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=15) (n:=1) (fun j=>?_) (fun j=>?_) i <;>
        simp [TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hinput] at hrun
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate total true) base,hrun,ht,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (m:=15) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simpa [TapeEmbedding.receipt,TapeEmbedding.config] using hh j
    · simp [TapeEmbedding.receipt,TapeEmbedding.config]
  · change base.final.tapes 7=_
    exact hvalid
  · intro table tail hparse
    obtain ⟨count,out,guard',hcount,hwidth,hindex,hsource,hpos,hcapacity,hrow,hvalid,hvalue,hout⟩ := hout table tail hparse
    refine ⟨count,out,guard',hcount,hwidth,hindex,hsource,hpos,hcapacity,hrow,hvalid,hvalue,?_⟩
    simp only [TapeEmbedding.receipt,TapeEmbedding.config,hout]
    rfl

theorem reusable_run (d : Data) (word : List Bool) (cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (sourceCapacity total resetCapacity : Nat) (backing : List Bool)
    (hs : d.source=frame word) (hp : d.pos=0)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hw : binaryCount.length=d.index.length) (hc : 2*binaryCount.length+3≤d.capacity)
    (hbit : RecoveryCommittedBit.rawCost d.index committed≤d.capacity)
    (hreset : cost d cap binaryCount committed guard+2≤resetCapacity)
    (hback : backing.length≤total) (htotal : 1≤total) (herase : total+1≤resetCapacity) :
    ∃ r,run reusableMachine (2*total+2*cost d cap binaryCount committed guard+11)
        (reuseInput d cap binaryCount committed guard sourceCapacity total resetCapacity backing)=some r ∧
      r.steps≤2*total+2*cost d cap binaryCount committed guard+11 ∧ (∀ i,r.final.heads i=0) ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        ∃ count out guard',count≤cap ∧ out.width=d.width ∧ out.index.length=d.index.length ∧
          out.source=d.source ∧ out.pos=0 ∧ out.capacity=d.capacity ∧ out.row.length≤2*(d.width+1)+1 ∧
          out.valid=true ∧ out.value=FiniteValuation.assignment
            (value committed) (value binaryCount) table (value d.index) ∧
          r.final.tapes=reuseTapes out count cap binaryCount committed guard' sourceCapacity total resetCapacity := by
  obtain ⟨first,hr0,ht0,hh0,hs0⟩ := reuse_clear d cap binaryCount committed guard sourceCapacity total resetCapacity backing hback htotal herase
  obtain ⟨last,hr1,ht1,hh1,hvalid,hout⟩ := scan_run d word cap binaryCount committed guard sourceCapacity total resetCapacity
    hs hp hi hb hw hc hbit hreset
  have hstart : Composition.restart first.final scanMachine.start=
      initialConfiguration scanMachine (reuseTapes d 0 cap binaryCount committed guard sourceCapacity total resetCapacity) := by
    apply configuration_ext
    · rfl
    · exact funext hh0
    · exact ht0
  have hnext : runFrom scanMachine (2*cost d cap binaryCount committed guard+6)
      (Composition.restart first.final scanMachine.start)=some last := by rw [hstart]; exact hr1
  have hall := Composition.run_join eraseMachine scanMachine (2*total+4) (2*cost d cap binaryCount committed guard+6)
    _ first last hr0 hnext
  have hinput : Composition.leftConfig _
      (initialConfiguration eraseMachine (reuseInput d cap binaryCount committed guard sourceCapacity total resetCapacity backing))=
      initialConfiguration reusableMachine (reuseInput d cap binaryCount committed guard sourceCapacity total resetCapacity backing) := by rfl
  rw [hinput] at hall
  have hcost : (2*total+4)+1+(2*cost d cap binaryCount committed guard+6)=
      2*total+2*cost d cap binaryCount committed guard+11 := by omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hh1,hvalid,?_⟩
  · change first.steps+1+last.steps≤_
    omega
  · intro table tail hparse
    obtain ⟨count,out,guard',hcount,hwidth,hindex,hsource,hpos,hcapacity,hrow,hvalid,hvalue,hout⟩ := hout table tail hparse
    exact ⟨count,out,guard',hcount,hwidth,hindex,hsource,hpos,hcapacity,hrow,hvalid,hvalue,hout⟩

end NearCubicWires.RepairOrdinary.RecoveryAssignment
