import Proof.SourceAssembly.SourcePoolIndexState

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyPoolIndex
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PoolColdSource
noncomputable section
attribute [local irreducible] PoolCold.machine Cold.machine SourceAssemblyIndexExact.framed
  reset frameIndex first machine
def budget {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w P : Nat) : Nat :=
  PoolEntryLoop.budget occ.length B q w+1+Cold.runtimeCoefficient a*(P+2)^Cold.runtimeDegree a+
    1+(2*SourceEnvelope.capacity a P+2)+1+
    (2*SourceAssemblyIndexExact.budget (counts a (CloseoutRowsUniversal.pool live occ))+
      4*(natListWord (counts a (CloseoutRowsUniversal.pool live occ))).length+7)

theorem run {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w P : Nat) (top : List Bool)
    (hw : 0<w) (hqw : q≤w)
    (hb : ∀ g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈occ,(g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w)
    (hqP : q≤P)
    (hi : (segment (CloseoutRowsUniversal.pool live occ) top).length≤1000*(P+2)^2) :
    ∃ HH AA, Step (machine a) (budget a live occ B w P)
      (Fin.addCases (Fin.addCases (PoolCold.start live occ B w top).heads (PoolCold.coldHeads a))
        (fun _ : Fin 6=>0))
      (Fin.addCases (Fin.addCases (PoolCold.start live occ B w top).tapes (PoolCold.coldData a P q))
        (fun _ : Fin 6=>[])) HH AA ∧
      HH (indexPorts a 7)=0 ∧
      AA (indexPorts a 7)=RepairOrdinary.frame (natListWord (counts a (CloseoutRowsUniversal.pool live occ))) := by
  obtain ⟨H,O,paid,fields,ndh,ndt⟩:=SourceAssemblyPoolCount.run a live occ B w P top
    hw hqw hb hm hqP hi
  obtain ⟨_cache,_cacheH,count,countH,src,srcH,_total,_totalH,_q,_qH,_scratch,_scratchH,
    driver,driverH,log,logH⟩:=fields
  let gs:=CloseoutRowsUniversal.pool live occ
  let C:=SourceEnvelope.capacity a P
  let EH:=dockH (PoolCold.slots a)
    (Fin.addCases (PoolCold.finish live occ B w top).heads (PoolCold.coldHeads a)) H
  let EA:=install (PoolCold.slots a)
    (Fin.addCases (PoolCold.finish live occ B w top).tapes (PoolCold.coldData a P q)) O
  let BH : Fin (baseTapes a+6)→Nat:=fun i=>Fin.addCases EH (fun _ : Fin 6=>0) i
  let BA : Fin (baseTapes a+6)→List Bool:=fun i=>Fin.addCases EA (fun _ : Fin 6=>[]) i
  have firstRun:=paid.embed (fun _ : Fin 6=>0) (fun _ : Fin 6=>[])
  have oldH (j : Fin 5) : BH (resetPorts a j)=H (coldPorts a j) := by
    simp only [BH,EH,resetPorts,slots,Fin.addCases_left,old,
      dockH_slot _ (PoolCold.slots_injective a)]
  have oldA (j : Fin 5) : BA (resetPorts a j)=O (coldPorts a j) := by
    simp only [BA,EA,resetPorts,slots,Fin.addCases_left,old,
      install_slot _ (PoolCold.slots_injective a)]
  have cp : 1≤C := by
    have h:=SourceEnvelope.capacity_covers a P
    have hp:1≤(SourceEnvelope.aggregate a P+1)^2:=Nat.one_le_pow 2 _ (by omega)
    dsimp [C]
    omega
  have hsrc: (segment gs top).length≤C:=SourceEnvelope.source_position a gs top P hi
  have hcount:(countWord a gs).length≤C:=SourceEnvelope.count_position a gs top P hqP hi
  let localA : Fin 3→List Bool:=![segment gs top,countWord a gs,UnaryTemplate.tape gs.length]
  let localH : Fin 3→Nat:=![(segment gs top).length,(countWord a gs).length,1]
  have rh : ∀ j,BH (resetPorts a j)=SourceAssemblyClear.join localH 0 0 j :=
    fun j=>(oldH j).trans (port_join a H _ _ _ _ _ srcH countH ndh driverH logH j)
  have ra : ∀ j,BA (resetPorts a j)=SourceAssemblyClear.join localA
      (List.replicate C true) (List.replicate (C+1) false) j :=
    fun j=>(oldA j).trans (port_join a O _ _ _ _ _ src count ndt driver log j)
  have hl : ∀ j,localH j≤C := by
    intro j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>i.elim0))) j
    · exact hsrc
    · exact hcount
    · exact cp
  have back:=(SourceAssemblyClear.rewind_run localA localH C hl).dock
      (resetPorts a) (reset_injective a) BH BA rh ra
  rw [install_existing (resetPorts a) BA _ ra] at back
  let RH:=dockH (resetPorts a) BH (fun _=>0)
  have resetH (j : Fin 5) : RH (resetPorts a j)=0:=dockH_slot _ (reset_injective a) _ _ j
  have freshH (j : Fin 6) : RH (slots a (j.natAdd 5))=0 := by
    have he:=dockH_other (resetPorts a) BH (fun _=>0) (slots a (j.natAdd 5)) (by
      intro k hk
      have h:=slots_injective a hk
      have hv:=congrArg Fin.val h
      have hk:=k.isLt
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega)
    change RH (slots a (j.natAdd 5))=0
    rw [show RH (slots a (j.natAdd 5))=BH (slots a (j.natAdd 5)) from he]
    simp only [BH,slots,Fin.addCases_right]
  have freshA (j : Fin 6) : BA (slots a (j.natAdd 5))=[] := by
    simp only [BA,slots,Fin.addCases_right]
  let tail:=RepairOrdinary.frame top++gs.flatMap (fun g=>RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g))
  obtain ⟨F,framed,field⟩:=SourceAssemblyIndexExact.framed_run (counts a gs) tail []
  have ih : ∀ j,RH (indexPorts a j)=0 := by
    intro j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>i.elim0))))))))) j
    · exact resetH 0
    · exact freshH 0
    · exact freshH 1
    · exact resetH 1
    · exact resetH 2
    · exact freshH 2
    · exact freshH 3
    · exact freshH 4
    · exact freshH 5
  have ia : ∀ j,BA (indexPorts a j)=AppendOutputFrame.input
      (SourceAssemblyIndexExact.input (counts a gs) tail []) j := by
    intro j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>i.elim0))))))))) j
    · have h:BA (indexPorts a 0)=segment gs top := (oldA 0).trans src
      change BA (indexPorts a 0)=natWord (counts a gs).length++tail
      rw [counts_length]
      exact h.trans (by simp only [ExtDecompositionBatch.segment,tail,List.append_assoc])
    · exact freshA 0
    · exact freshA 1
    · exact (oldA 1).trans count
    · have h:BA (indexPorts a 4)=UnaryTemplate.tape gs.length := (oldA 2).trans ndt
      change BA (indexPorts a 4)=UnaryTemplate.tape (counts a gs).length
      rw [counts_length]
      exact h
    · exact freshA 2
    · exact freshA 3
    · exact freshA 4
    · exact freshA 5
  have lastRun:=framed.dock (indexPorts a) (index_injective a) RH BA ih ia
  refine ⟨dockH (indexPorts a) RH (fun _=>0),install (indexPorts a) BA F,?_,?_,?_⟩
  · simpa only [machine,first,reset,frameIndex,budget,C,gs] using (firstRun.seq back).seq lastRun
  · exact dockH_slot _ (index_injective a) _ _ 7
  · exact (install_slot _ (index_injective a) _ _ 7).trans field

end
end SourceAssemblyPoolIndex
