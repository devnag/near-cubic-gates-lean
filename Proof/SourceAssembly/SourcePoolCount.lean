import Proof.SourceAssembly.SourceCountDriver

/- The SAME native paired-writer/decomposition run, retaining its physically
produced occurrence template as well as cache/count/source outputs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyPoolCount
open NearCubicWires LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairSource SupplierPipeline RepairRepresentation VerifierDecoding P1Closure
open PoolColdSource.PoolCold
open scoped BigOperators
attribute [local irreducible] PoolEntryOccurrence.machine Cold.machine
theorem run {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w P : Nat) (top : List Bool)
    (hw : 0<w) (hqw : q≤w)
    (hb : ∀ g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈occ,(g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w)
    (hqP : q≤P)
    (hi : (segment (CloseoutRowsUniversal.pool live occ) top).length≤1000*(P+2)^2) :
    ∃ H O, Step (machine a)
      (PoolEntryLoop.budget occ.length B q w+1+
        Cold.runtimeCoefficient a*(P+2)^Cold.runtimeDegree a)
      (Fin.addCases (start live occ B w top).heads (coldHeads a))
      (Fin.addCases (start live occ B w top).tapes (coldData a P q))
      (dockH (slots a) (Fin.addCases (finish live occ B w top).heads (coldHeads a)) H)
      (install (slots a) (Fin.addCases (finish live occ B w top).tapes (coldData a P q)) O) ∧
      (O (Cold.port a (cch a))=exactListWord (GS a (CloseoutRowsUniversal.pool live occ)) ∧
      H (Cold.port a (cch a))=0 ∧
      O (Cold.port a (cnt a))=countWord a (CloseoutRowsUniversal.pool live occ) ∧
      H (Cold.port a (cnt a))=(countWord a (CloseoutRowsUniversal.pool live occ)).length ∧
      O (sourcePort a)=segment (CloseoutRowsUniversal.pool live occ) top ∧
      H (sourcePort a)=(segment (CloseoutRowsUniversal.pool live occ) top).length ∧
      O (Cold.port a (tot a))=UnaryTemplate.tape (ExtDecompositionBatch.B a (CloseoutRowsUniversal.pool live occ)) ∧
      H (Cold.port a (tot a))=1 ∧
      O (Cold.port a (dom a))=UnaryTemplate.tape q ∧ H (Cold.port a (dom a))=1 ∧
      O (Cold.port a (scr a))=List.replicate (ExtDecompositionBatch.B a (CloseoutRowsUniversal.pool live occ)) false ∧
      H (Cold.port a (scr a))=0 ∧
      O (Cold.port a (drv a))=List.replicate (SourceEnvelope.capacity a P) true ∧
      H (Cold.port a (drv a))=0 ∧
      O (Cold.port a (wsp a))=List.replicate (SourceEnvelope.capacity a P+1) false ∧
      H (Cold.port a (wsp a))=0) ∧
      H (SourceAssemblyCountDriver.port a)=1 ∧
      O (SourceAssemblyCountDriver.port a)=UnaryTemplate.tape (CloseoutRowsUniversal.pool live occ).length := by
  obtain ⟨r,hr,hfinal,_hs⟩ := PoolEntryLoop.segment_run live occ B w top hw hqw hb hm
  have writer : Step PoolEntryLoop.machine (PoolEntryLoop.budget occ.length B q w)
      (start live occ B w top).heads (start live occ B w top).tapes
      (finish live occ B w top).heads (finish live occ B w top).tapes :=
    Step.of_run hr (congrArg Configuration.heads hfinal) (congrArg Configuration.tapes hfinal)
  obtain ⟨H,O,source,fields⟩ := Cold.cold_run a P (CloseoutRowsUniversal.pool live occ) top hqP hi
  have driver := SourceAssemblyCountDriver.retained a P (CloseoutRowsUniversal.pool live occ) top hqP hi H O source
  have paid := source.enlarge (Cold.budget_bound a P (CloseoutRowsUniversal.pool live occ) top hqP hi)
  have middle := writer.embed (coldHeads a) (coldData a P q)
  have last := paid.dock (slots a) (slots_injective a)
    (Fin.addCases (finish live occ B w top).heads (coldHeads a))
    (Fin.addCases (finish live occ B w top).tapes (coldData a P q))
    (by
      intro j
      by_cases hj : j=sourcePort a
      · subst j
        rw [slots,if_pos rfl,Fin.addCases_left,source_heads]
        rfl
      · rw [slots,if_neg hj,Fin.addCases_right]
        exact cold_heads_other a _ j hj)
    (by
      intro j
      by_cases hj : j=sourcePort a
      · subst j
        rw [slots,if_pos rfl,Fin.addCases_left,source_data]
        change ZeroPadding.pad 0 (PoolEntryBaseline.bank live B w _ _ 61)=_
        rw [ZeroPadding.pad_zero,PoolEntryBaseline.bank_output]
      · rw [slots,if_neg hj,Fin.addCases_right]
        exact cold_data_other a P q _ j hj)
  exact ⟨H,O,middle.seq last,fields,driver⟩

end SourceAssemblyPoolCount
