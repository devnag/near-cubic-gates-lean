import Proof.CaseAnalysis.RecoveryPreparedTargets

/-! Join only the checked changed-tape projections. The enclosing compiler
sees its exact original bank without unfolding the initialization machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepared_target (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) :
    preparedData q bound C Q clauses B proj source=targetData q bound C Q clauses B proj source := by
  apply HierarchyWidth.install_eq driverSlots driver_injective
  · exact target_drivers q bound C Q clauses B proj source
  · intro i hd
    symm
    change install RecoveryBoundedColdWork.slots (metadataData q bound C Q clauses B proj source)
      (RecoveryBoundedColdWork.data B (List.replicate B false)) i=targetData q bound C Q clauses B proj source i
    by_cases hw : ∃ j,RecoveryBoundedColdWork.slots j=i
    · obtain ⟨j,rfl⟩:=hw
      rw [install_slot _ RecoveryBoundedColdWork.injective]
      exact (target_work q bound C Q clauses B proj source j hd).symm
    · have hw' : ∀ j,RecoveryBoundedColdWork.slots j≠i:=by simpa only [not_exists] using hw
      rw [install_other _ _ _ i hw']
      change install RecoveryBoundedColdScalarMetadata.metadataSlots
        (RecoveryBoundedColdScalarMetadata.loaded (input q bound C Q clauses B proj source) q bound C Q clauses B)
        (RecoveryBoundedColdMetadata.output q bound C Q clauses B) i=targetData q bound C Q clauses B proj source i
      by_cases hm : ∃ j,RecoveryBoundedColdScalarMetadata.metadataSlots j=i
      · obtain ⟨j,rfl⟩:=hm
        rw [install_slot _ RecoveryBoundedColdScalarMetadata.metadata_injective]
        exact (target_metadata q bound C Q clauses B proj source j hd).symm
      · have hm' : ∀ j,RecoveryBoundedColdScalarMetadata.metadataSlots j≠i:=by simpa only [not_exists] using hm
        rw [install_other _ _ _ i hm']
        change install RecoveryBoundedColdScalarMetadata.loadSlots (input q bound C Q clauses B proj source)
          (RecoveryBoundedColdScalarLoad.bank (RecoveryBoundedColdScalarMetadata.values q bound C Q clauses) B 5) i=
          targetData q bound C Q clauses B proj source i
        by_cases hl : ∃ j,RecoveryBoundedColdScalarMetadata.loadSlots j=i
        · obtain ⟨j,rfl⟩:=hl
          rw [install_slot _ RecoveryBoundedColdScalarMetadata.load_injective]
          exact (target_load q bound C Q clauses B proj source j hm').symm
        · have hl' : ∀ j,RecoveryBoundedColdScalarMetadata.loadSlots j≠i:=by simpa only [not_exists] using hl
          rw [install_other _ _ _ i hl']
          exact target_other q bound C Q clauses B proj source i hd hw' hm' hl'

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
