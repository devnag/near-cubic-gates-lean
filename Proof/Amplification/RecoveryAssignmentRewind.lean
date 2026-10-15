import Proof.Amplification.RecoveryAssignmentPadded

/-! Paid rewind of each reused table/committed-word lookup. It resets the
bounded retained table source and every local driver, with allocated reset
storage explicit and preserved for the next call. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def rewindMachine := Rewind.machine positionedMachine
noncomputable def readyTapes (d : Data) (count cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (sourceCapacity countCapacity resetCapacity : Nat) : Fin 15→List Bool :=
  fun i=>Fin.addCases (paddedTapes d count cap binaryCount committed guard sourceCapacity countCapacity)
    (fun _ : Fin 1=>List.replicate resetCapacity false) i

theorem rewind_run (d : Data) (word : List Bool) (cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (sourceCapacity countCapacity resetCapacity : Nat)
    (hs : d.source=frame word) (hp : d.pos=0)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hw : binaryCount.length=d.index.length) (hc : 2*binaryCount.length+3≤d.capacity)
    (hbit : RecoveryCommittedBit.rawCost d.index committed≤d.capacity)
    (hreset : cost d cap binaryCount committed guard+2≤resetCapacity) :
    ∃ r,run rewindMachine (2*cost d cap binaryCount committed guard+6)
        (readyTapes d 0 cap binaryCount committed guard sourceCapacity countCapacity resetCapacity)=some r ∧
      r.steps≤2*cost d cap binaryCount committed guard+6 ∧ (∀ i,r.final.heads i=0) ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        ∃ count out guard',count≤cap ∧ out.width=d.width ∧ out.index.length=d.index.length ∧
          out.source=d.source ∧ out.pos=0 ∧ out.capacity=d.capacity ∧ out.row.length≤2*(d.width+1)+1 ∧
          out.valid=true ∧ out.value=FiniteValuation.assignment
            (value committed) (value binaryCount) table (value d.index) ∧
          r.final.tapes=readyTapes out count cap binaryCount committed guard' sourceCapacity countCapacity resetCapacity := by
  obtain ⟨base,hr,hbound,_,hvalid,hout⟩ := padded_run d word cap binaryCount committed guard sourceCapacity countCapacity
    hs hp hi hb hw hc hbit
  obtain ⟨r,hrun,ht,hcReset,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace positionedMachine _ _ base hr resetCapacity
  have hbase : base.steps≤resetCapacity := hbound.trans hreset
  have hn : 2*base.steps+2≤2*cost d cap binaryCount committed guard+6 := by omega
  have hm := runFrom_moreFuel rewindMachine (2*base.steps+2)
    (2*cost d cap binaryCount committed guard+6-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hsteps.le.trans hn,hh,?_,?_⟩
  · have h7 := ht 7
    change r.final.tapes 7=base.final.tapes 7 at h7
    exact h7.trans hvalid
  · intro table tail hparse
    obtain ⟨count,out,guard',hcount,hwidth,hindex,hsource,hcapacity,hrow,hvalid,hvalue,hout⟩ := hout table tail hparse
    refine ⟨count,{out with pos:=0},guard',hcount,hwidth,hindex,hsource,rfl,hcapacity,hrow,hvalid,hvalue,?_⟩
    funext i
    refine Fin.addCases (m:=14) (n:=1) (motive:=fun j=>r.final.tapes j=
      readyTapes {out with pos:=0} count cap binaryCount committed guard' sourceCapacity countCapacity resetCapacity j) ?_ ?_ i
    · intro j
      simp only [readyTapes,Fin.addCases_left]
      rw [ht j,hout]
      rfl
    · intro j
      fin_cases j
      change r.final.tapes (Fin.natAdd 14 (0 : Fin 1))=List.replicate resetCapacity false
      simpa only [Nat.max_eq_left hbase] using hcReset

end NearCubicWires.RepairOrdinary.RecoveryAssignment
