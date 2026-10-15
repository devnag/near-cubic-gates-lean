import Proof.Amplification.RecoveryAssignmentPosition

/-! Whole assignment scan from zero head positions and reused flags. The
initial driver positioning/flag clearing and its call return are charged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem positioned_run (d : Data) (word : List Bool) (cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool)
    (hs : d.source=frame word) (hp : d.pos=0)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hw : binaryCount.length=d.index.length) (hc : 2*binaryCount.length+3≤d.capacity)
    (hbit : RecoveryCommittedBit.rawCost d.index committed≤d.capacity) :
    ∃ r,run positionedMachine (cost d cap binaryCount committed guard+2)
        (inputTapes d cap binaryCount committed guard)=some r ∧
      r.steps≤cost d cap binaryCount committed guard+2 ∧ r.final.heads 7=0 ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        ∃ count out guard',count≤cap ∧ out.width=d.width ∧ out.index.length=d.index.length ∧
          out.source=d.source ∧ out.capacity=d.capacity ∧ out.row.length≤2*(d.width+1)+1 ∧
          out.valid=true ∧ out.value=FiniteValuation.assignment
            (value committed) (value binaryCount) table (value d.index) ∧
          r.final.tapes=(cfg out count cap binaryCount committed guard' (0 : Fin 1)).tapes := by
  obtain ⟨first,hr0,hf0,ht0⟩ := position_run d cap binaryCount committed guard hp
  obtain ⟨last,hr1,ht1,hh1,hv1,_⟩ := assignment_run (clean d) [] word cap binaryCount committed guard
    hs hp hi hb hw hc hbit rfl rfl
  have hstart : Composition.restart first.final machine.start=
      cfg (clean d) 0 cap binaryCount committed guard machine.start := by rw [hf0]; rfl
  have hnext : runFrom machine (cost d cap binaryCount committed guard)
      (Composition.restart first.final machine.start)=some last := by rw [hstart]; exact hr1
  have hall := Composition.run_join positionMachine machine 1 (cost d cap binaryCount committed guard)
    _ first last hr0 hnext
  have hinput : Composition.leftConfig _
      (initialConfiguration positionMachine (inputTapes d cap binaryCount committed guard))=
      initialConfiguration positionedMachine (inputTapes d cap binaryCount committed guard) := by rfl
  rw [hinput] at hall
  have hcost : 1+1+cost d cap binaryCount committed guard=cost d cap binaryCount committed guard+2 := by omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hh1,hv1,?_⟩
  · change first.steps+1+last.steps≤_
    change last.steps≤cost d cap binaryCount committed guard at ht1
    omega
  · intro table tail hparse
    obtain ⟨other,ho,_,count,out,guard',hcount,hwidth,hindex,hsource,hcapacity,hrow,hvalid,hvalue,hout⟩ :=
      assignment_return (clean d) [] word cap binaryCount committed guard hs hp hi hb hw hc hbit rfl rfl table tail hparse
    rw [hr1] at ho
    have he := Option.some.inj ho
    cases he
    refine ⟨count,out,guard',hcount,hwidth,hindex,hsource,hcapacity,hrow,hvalid,hvalue,?_⟩
    simp only [Composition.joinedReceipt,Composition.rightConfig,hout]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryAssignment
