import Proof.Amplification.RecoveryAssignmentReusable
import Proof.Amplification.RecoveryTablePrefix

/-! Each reusable literal lookup consumes the table source produced by the
one bounded physical witness copy. Its result refers to the original witness
table, including exact malformed-prefix rejection. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem readList_take_some (width cap limit : Nat) (word : List Bool)
    (hl : cap*(width+2)+1≤limit) (table : FiniteValuation.Table) (tail : List Bool)
    (hp : readList cap (readEntry width) word=some (table,tail)) :
    ∃ rest,readList cap (readEntry width) (word.take limit)=some (table,rest) := by
  have h := readList_take_table width cap limit word hl
  rw [hp] at h
  cases ht : readList cap (readEntry width) (word.take limit) with
  | none => rw [ht] at h; contradiction
  | some pair =>
    rcases pair with ⟨table',rest⟩
    rw [ht] at h
    have he : table'=table := Option.some.inj h
    subst table'
    exact ⟨rest,rfl⟩

theorem retained_run (d : Data) (word : List Bool) (cap prefixLimit : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (total resetCapacity : Nat) (backing : List Bool)
    (hs : d.source=frame (word.take prefixLimit)) (hp : d.pos=0)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hw : binaryCount.length=d.index.length) (hc : 2*binaryCount.length+3≤d.capacity)
    (hbit : RecoveryCommittedBit.rawCost d.index committed≤d.capacity)
    (hreset : cost d cap binaryCount committed guard+2≤resetCapacity)
    (hback : backing.length≤total) (htotal : 1≤total) (herase : total+1≤resetCapacity)
    (hprefix : cap*(d.width+2)+1≤prefixLimit) :
    ∃ r,run reusableMachine (2*total+2*cost d cap binaryCount committed guard+11)
        (reuseInput d cap binaryCount committed guard (2*prefixLimit+1) total resetCapacity backing)=some r ∧
      r.steps≤2*total+2*cost d cap binaryCount committed guard+11 ∧ (∀ i,r.final.heads i=0) ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        ∃ count out guard',count≤cap ∧ out.width=d.width ∧ out.index.length=d.index.length ∧
          out.source=d.source ∧ out.pos=0 ∧ out.capacity=d.capacity ∧ out.row.length≤2*(d.width+1)+1 ∧
          out.valid=true ∧ out.value=FiniteValuation.assignment
            (value committed) (value binaryCount) table (value d.index) ∧
          r.final.tapes=reuseTapes out count cap binaryCount committed guard' (2*prefixLimit+1) total resetCapacity := by
  obtain ⟨r,hr,ht,hh,hvalid,hout⟩ := reusable_run d (word.take prefixLimit) cap binaryCount committed guard
    (2*prefixLimit+1) total resetCapacity backing hs hp hi hb hw hc hbit hreset hback htotal herase
  have hstatus := congrArg Option.isSome (readList_take_table d.width cap prefixLimit word hprefix)
  simp only [Option.isSome_map] at hstatus
  refine ⟨r,hr,ht,hh,?_,?_⟩
  · exact hvalid.trans (congrArg List.singleton hstatus)
  · intro table tail hparse
    obtain ⟨rest,hrest⟩ := readList_take_some d.width cap prefixLimit word hprefix table tail hparse
    exact hout table rest hrest

theorem retained_source (d : Data) (word : List Bool) (cap prefixLimit : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (total resetCapacity : Nat) (backing : List Bool)
    (hs : d.source=frame (word.take prefixLimit)) :
    reuseInput d cap binaryCount committed guard (2*prefixLimit+1) total resetCapacity backing 0=
      ZeroPadding.pad (2*prefixLimit+1) (frame (word.take prefixLimit)) := by
  simp [reuseInput,reuseTapes,readyTapes,paddedTapes,padding,cfg_tapes,Fin.addCases,hs]

end NearCubicWires.RepairOrdinary.RecoveryAssignment
