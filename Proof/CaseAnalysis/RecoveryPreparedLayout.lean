import Proof.CaseAnalysis.RecoveryDrivers
import Proof.CaseAnalysis.RecoveryPosition
import Proof.CaseAnalysis.RecoveryCountCircuit

/-! The cold original bank starts only with real source/projector words,
five raw scalars and paid backing drivers. Every other work cell is empty. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def shared (B : ℕ) (source : List Bool) (i : Fin 78):=
  if i=70 then source else if i=76 then List.replicate B true
  else if i=77 then List.replicate (B+1) false else []
def input (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) : Fin 158→List Bool:=
  Fin.addCases (m:=153) (n:=5)
    (Fin.addCases (m:=116) (n:=37)
      (Fin.addCases (m:=78) (n:=38) (shared B source) (RecoveryBoundedFixedRestart.extra proj (2^q)))
      (Fin.addCases (m:=36) (n:=1) (fun _=>[]) (fun _=>CompareMachine.word bound)))
    (fun j=>List.replicate (RecoveryBoundedColdScalarMetadata.values q bound C Q clauses j) true)
noncomputable def metadataData (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool):=
  RecoveryBoundedColdScalarMetadata.output (input q bound C Q clauses B proj source) q bound C Q clauses B
noncomputable def workData (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool):=
  install RecoveryBoundedColdWork.slots (metadataData q bound C Q clauses B proj source)
    (RecoveryBoundedColdWork.data B (List.replicate B false))
def driverSlots : Fin 7→Fin 158:=![140,139,138,150,151,144,116]
noncomputable def preparedData (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool):=
  install driverSlots (workData q bound C Q clauses B proj source)
    (RecoveryBoundedColdDrivers.output bound (rowWidth q bound) B)
theorem driver_injective : Function.Injective driverSlots:=by decide

theorem source_input (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (j : Fin 5) :
    input q bound C Q clauses B proj source (RecoveryBoundedColdScalarMetadata.sourceSlot j)=
      List.replicate (RecoveryBoundedColdScalarMetadata.values q bound C Q clauses j) true := by
  simp only [input,RecoveryBoundedColdScalarMetadata.sourceSlot,Fin.addCases_right]

theorem metadata_input (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (j : Fin 37) :
    input q bound C Q clauses B proj source (RecoveryBoundedColdScalarMetadata.metadataSlots j)=
      RecoveryBoundedColdScalarMetadata.blank B j := by
  fin_cases j <;> rfl

theorem metadata_slot (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (j : Fin 37) :
    metadataData q bound C Q clauses B proj source (RecoveryBoundedColdScalarMetadata.metadataSlots j)=
      RecoveryBoundedColdMetadata.output q bound C Q clauses B j :=
  install_slot _ RecoveryBoundedColdScalarMetadata.metadata_injective _ _ j

theorem metadata_other (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool)
    (i : Fin 158) (hm : ∀ j,RecoveryBoundedColdScalarMetadata.metadataSlots j≠i)
    (hl : ∀ j,RecoveryBoundedColdScalarMetadata.loadSlots j≠i) :
    metadataData q bound C Q clauses B proj source i=input q bound C Q clauses B proj source i := by
  rw [metadataData,RecoveryBoundedColdScalarMetadata.output,install_other _ _ _ i hm]
  exact install_other _ _ _ i hl

theorem work_input (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (j : Fin 75) :
    metadataData q bound C Q clauses B proj source (RecoveryBoundedColdWork.slots j)=
      RecoveryBoundedColdWork.data B [] j := by
  fin_cases j
  all_goals first
    | exact metadata_slot q bound C Q clauses B proj source 35
    | exact metadata_slot q bound C Q clauses B proj source 36
    | (rw [metadata_other q bound C Q clauses B proj source _ (by decide) (by decide)];rfl)

theorem work_other (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool)
    (i : Fin 158) (h : ∀ j,RecoveryBoundedColdWork.slots j≠i) :
    workData q bound C Q clauses B proj source i=metadataData q bound C Q clauses B proj source i :=
  install_other _ _ _ i h

theorem drivers_input (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (j : Fin 7) :
    workData q bound C Q clauses B proj source (driverSlots j)=
      RecoveryBoundedColdDrivers.start bound (rowWidth q bound) B j := by
  fin_cases j
  · rw [work_other _ _ _ _ _ _ _ _ _ (by decide)]
    exact metadata_slot q bound C Q clauses B proj source 23
  · rw [work_other _ _ _ _ _ _ _ _ _ (by decide)]
    exact (metadata_slot q bound C Q clauses B proj source 22).trans (by
      change ZeroPadding.pad B (List.replicate 0 true)=List.replicate B false
      simp [ZeroPadding.pad])
  · rw [work_other _ _ _ _ _ _ _ _ _ (by decide)]
    exact metadata_slot q bound C Q clauses B proj source 21
  · exact install_slot RecoveryBoundedColdWork.slots RecoveryBoundedColdWork.injective _ _ 71
  · exact install_slot RecoveryBoundedColdWork.slots RecoveryBoundedColdWork.injective _ _ 72
  · rw [work_other _ _ _ _ _ _ _ _ _ (by decide)]
    exact (metadata_slot q bound C Q clauses B proj source 27).trans (by
      change ZeroPadding.pad B (List.replicate 0 true)=List.replicate B false
      simp [ZeroPadding.pad])
  · rw [work_other _ _ _ _ _ _ _ _ _ (by decide)]
    exact metadata_slot q bound C Q clauses B proj source 34

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
