import Proof.Amplification.RecoveryAssignmentPositioned

/-! The same physical assignment scan with its retained table copy and
reusable erased counter storage. Padding changes allocated tape lengths,
never observed bits or counted transitions. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (sourceCapacity countCapacity : Nat) : Fin 14→Nat :=
  fun i=>if i=0 then sourceCapacity else if i=8 then countCapacity else 0
noncomputable def paddedTapes (d : Data) (count cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (sourceCapacity countCapacity : Nat) : Fin 14→List Bool :=
  fun i=>ZeroPadding.pad (padding sourceCapacity countCapacity i)
    ((cfg d count cap binaryCount committed guard (0 : Fin 1)).tapes i)

theorem padded_run (d : Data) (word : List Bool) (cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (sourceCapacity countCapacity : Nat)
    (hs : d.source=frame word) (hp : d.pos=0)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hw : binaryCount.length=d.index.length) (hc : 2*binaryCount.length+3≤d.capacity)
    (hbit : RecoveryCommittedBit.rawCost d.index committed≤d.capacity) :
    ∃ r,run positionedMachine (cost d cap binaryCount committed guard+2)
        (paddedTapes d 0 cap binaryCount committed guard sourceCapacity countCapacity)=some r ∧
      r.steps≤cost d cap binaryCount committed guard+2 ∧ r.final.heads 7=0 ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        ∃ count out guard',count≤cap ∧ out.width=d.width ∧ out.index.length=d.index.length ∧
          out.source=d.source ∧ out.capacity=d.capacity ∧ out.row.length≤2*(d.width+1)+1 ∧
          out.valid=true ∧ out.value=FiniteValuation.assignment
            (value committed) (value binaryCount) table (value d.index) ∧
          r.final.tapes=paddedTapes out count cap binaryCount committed guard' sourceCapacity countCapacity := by
  obtain ⟨base,hr,ht,hh,hvalid,hout⟩ := positioned_run d word cap binaryCount committed guard hs hp hi hb hw hc hbit
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config positionedMachine
    (padding sourceCapacity countCapacity) _ _ base hr
  refine ⟨r,hrun,by rw [hsteps]; exact ht,?_,?_,?_⟩
  · simpa only [hfinal,ZeroPadding.config] using hh
  · simp [hfinal,ZeroPadding.config,padding,hvalid]
  · intro table tail hparse
    obtain ⟨count,out,guard',hcount,hwidth,hindex,hsource,hcapacity,hrow,hvalid,hvalue,hout⟩ := hout table tail hparse
    refine ⟨count,out,guard',hcount,hwidth,hindex,hsource,hcapacity,hrow,hvalid,hvalue,?_⟩
    funext i
    simp only [hfinal,ZeroPadding.config,hout,paddedTapes]

end NearCubicWires.RepairOrdinary.RecoveryAssignment
