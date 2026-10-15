import Proof.CaseAnalysis.RecoveryPreparedLayout

/-! The physically initialized bank is the literal initial state consumed
by the original count compiler, with the one shared description arity. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
open LocalBitMultitape RecoveryRootRound BoundedOracleStructuralCircuit
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (q bound Q clauses B : ℕ) : Fin 12→List Bool:=
  Function.update (RecoveryBoundedColdMetadata.extra q bound Q clauses B) 6
    (ZeroPadding.pad B (List.replicate (rowWidth q bound*(bound+1)) true))
noncomputable def targetData (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) : Fin 158→List Bool:=
  Fin.addCases (m:=153) (n:=5)
    (RecoveryBoundedCountUniform.scanData
      (RecoveryBoundedCountBank.data B B (RecoveryBoundedGrammarBank.base 0 B [] [] [] source)
        proj (2^q) (RecoveryBoundedGrammarCold.metadata q bound 0 C B (extra q bound Q clauses B))
        (RecoveryBoundedColdDrivers.driver B bound) (RecoveryBoundedColdDrivers.driver B 0)) bound)
    (fun j=>List.replicate (RecoveryBoundedColdScalarMetadata.values q bound C Q clauses j) true)

theorem prepared_other (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool)
    (i : Fin 158) (h : ∀ j,driverSlots j≠i) :
    preparedData q bound C Q clauses B proj source i=workData q bound C Q clauses B proj source i :=
  install_other _ _ _ i h

theorem metadata_source (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (j : Fin 5) :
    metadataData q bound C Q clauses B proj source (RecoveryBoundedColdScalarMetadata.sourceSlot j)=
      List.replicate (RecoveryBoundedColdScalarMetadata.values q bound C Q clauses j) true := by
  fin_cases j
  all_goals
    rw [metadataData,RecoveryBoundedColdScalarMetadata.output,install_other _ _ _ _ (by decide)]
    first
      | exact install_slot RecoveryBoundedColdScalarMetadata.loadSlots RecoveryBoundedColdScalarMetadata.load_injective _ _ 0
      | exact install_slot RecoveryBoundedColdScalarMetadata.loadSlots RecoveryBoundedColdScalarMetadata.load_injective _ _ 1
      | exact install_slot RecoveryBoundedColdScalarMetadata.loadSlots RecoveryBoundedColdScalarMetadata.load_injective _ _ 2
      | exact install_slot RecoveryBoundedColdScalarMetadata.loadSlots RecoveryBoundedColdScalarMetadata.load_injective _ _ 3
      | exact install_slot RecoveryBoundedColdScalarMetadata.loadSlots RecoveryBoundedColdScalarMetadata.load_injective _ _ 4

private theorem pad_empty (B : ℕ) : ZeroPadding.pad B []=List.replicate B false := by simp [ZeroPadding.pad]

theorem work_mark (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool)
    (i : Fin 158) (hi : ∃ j : Fin 73,RecoveryBoundedColdWork.work j=i) :
    workData q bound C Q clauses B proj source i=List.replicate B false := by
  obtain ⟨j,rfl⟩:=hi
  have he : RecoveryBoundedColdWork.slots (j.castAdd 2)=RecoveryBoundedColdWork.work j := by
    simp only [RecoveryBoundedColdWork.slots,Fin.addCases_left]
  rw [←he]
  change install RecoveryBoundedColdWork.slots _
    (RecoveryBoundedColdWork.data B (List.replicate B false))
    (RecoveryBoundedColdWork.slots (j.castAdd 2))=List.replicate B false
  rw [install_slot _ RecoveryBoundedColdWork.injective]
  simp only [RecoveryBoundedColdWork.data,Fin.addCases_left]

theorem metadata_at (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool)
    (i : Fin 158) (hlo : (117 : ℕ)≤(i : Fin 158).val) (hhi : (i : Fin 158).val<150) :
    metadataData q bound C Q clauses B proj source i=
      RecoveryBoundedGrammarCold.metadata q bound 0 C B (RecoveryBoundedColdMetadata.extra q bound Q clauses B)
        ⟨i.val-117,by omega⟩ := by
  let j : Fin 33:=⟨i.val-117,by omega⟩
  have hx : (j.natAdd 79).castAdd 2=((j.castAdd 2).natAdd 1).natAdd 78 := by
    apply Fin.ext
    simp only [Fin.val_castAdd,Fin.val_natAdd]
    omega
  have he : RecoveryBoundedColdScalarMetadata.metadataSlots (j.castAdd 4)=i := by
    apply Fin.ext
    simp only [RecoveryBoundedColdScalarMetadata.metadataSlots,RecoveryBoundedCountScalarDock.slots,
      RecoveryBoundedGrammarAdvance.outerSlots,Fin.addCases_left,Fin.val_castAdd]
    rw [hx]
    simp only [RecoveryBoundedCountBank.grammarSlots,Fin.addCases_right,Fin.val_natAdd,Fin.val_castAdd]
    dsimp only [j]
    omega
  have h:=metadata_slot q bound C Q clauses B proj source (j.castAdd 4)
  rw [he] at h
  simpa only [RecoveryBoundedColdMetadata.output,RecoveryBoundedGrammarAdvance.bank,Fin.addCases_left] using h

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
