import Proof.CaseAnalysis.RecoveryPreparedMeaning

/-! Small projections keep the literal cold-bank equality opaque at its
enclosing compiler boundary. No machine or data representation is changed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem pad_empty (B : ℕ) : ZeroPadding.pad B []=List.replicate B false := by simp [ZeroPadding.pad]

theorem target_drivers (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (j : Fin 7) :
    targetData q bound C Q clauses B proj source (driverSlots j)=
      RecoveryBoundedColdDrivers.output bound (BoundedOracleStructuralCircuit.rowWidth q bound) B j := by
  fin_cases j <;> simp [targetData,driverSlots,RecoveryBoundedCountUniform.scanData,RecoveryBoundedCountBank.data,
    RecoveryBoundedCountBank.extras,RecoveryBoundedGrammarCold.metadata,extra,
    RecoveryBoundedColdMetadata.extra,RecoveryBoundedColdMetadata.extraValues,RecoveryBoundedGrammarScalarAdd.unary,
    RecoveryBoundedColdDrivers.output,RecoveryBoundedColdDrivers.bank,Fin.addCases,pad_empty]

theorem target_work (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (j : Fin 75)
    (hd : ∀ k,driverSlots k≠RecoveryBoundedColdWork.slots j) :
    targetData q bound C Q clauses B proj source (RecoveryBoundedColdWork.slots j)=
      RecoveryBoundedColdWork.data B (List.replicate B false) j := by
  fin_cases j
  all_goals first
    | exact False.elim (hd 3 rfl)
    | exact False.elim (hd 4 rfl)
    | (simp [targetData,RecoveryBoundedColdWork.slots,RecoveryBoundedColdWork.work,RecoveryBoundedRowErase.work,
        RecoveryBoundedColdWork.data,RecoveryBoundedCountUniform.scanData,RecoveryBoundedCountBank.data,
        RecoveryBoundedFixedRestart.data,RecoveryBoundedFixedContinue.data,
        RecoveryBoundedFixedContinue.padded,RecoveryBoundedFixedContinue.capacity,
        RecoveryBoundedGrammarBank.base,Fin.addCases,pad_empty])

theorem target_metadata (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (j : Fin 37)
    (hd : ∀ k,driverSlots k≠RecoveryBoundedColdScalarMetadata.metadataSlots j) :
    targetData q bound C Q clauses B proj source (RecoveryBoundedColdScalarMetadata.metadataSlots j)=
      RecoveryBoundedColdMetadata.output q bound C Q clauses B j := by
  fin_cases j
  all_goals first
    | exact False.elim (hd 0 rfl)
    | exact False.elim (hd 1 rfl)
    | exact False.elim (hd 2 rfl)
    | exact False.elim (hd 5 rfl)
    | exact False.elim (hd 6 rfl)
    | (simp [targetData,RecoveryBoundedColdScalarMetadata.metadataSlots,RecoveryBoundedCountScalarDock.slots,
        RecoveryBoundedCountBank.grammarSlots,RecoveryBoundedGrammarAdvance.outerSlots,
        RecoveryBoundedCountUniform.scanData,RecoveryBoundedCountBank.data,RecoveryBoundedCountBank.extras,
        RecoveryBoundedFixedRestart.data,RecoveryBoundedFixedContinue.data,RecoveryBoundedFixedContinue.padded,
        RecoveryBoundedFixedContinue.capacity,RecoveryBoundedGrammarBank.base,RecoveryBoundedColdMetadata.output,
        RecoveryBoundedGrammarAdvance.bank,RecoveryBoundedGrammarCold.metadata,extra,Fin.addCases])

theorem target_load (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (j : Fin 12)
    (hm : ∀ k,RecoveryBoundedColdScalarMetadata.metadataSlots k≠RecoveryBoundedColdScalarMetadata.loadSlots j) :
    targetData q bound C Q clauses B proj source (RecoveryBoundedColdScalarMetadata.loadSlots j)=
      RecoveryBoundedColdScalarLoad.bank (RecoveryBoundedColdScalarMetadata.values q bound C Q clauses) B 5 j := by
  fin_cases j
  all_goals first
    | exact False.elim (hm 18 rfl)
    | exact False.elim (hm 20 rfl)
    | exact False.elim (hm 23 rfl)
    | exact False.elim (hm 24 rfl)
    | exact False.elim (hm 25 rfl)
    | exact False.elim (hm 35 rfl)
    | exact False.elim (hm 36 rfl)
    | rfl

theorem target_other (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) (i : Fin 158)
    (hd : ∀ j,driverSlots j≠i) (hw : ∀ j,RecoveryBoundedColdWork.slots j≠i)
    (hm : ∀ j,RecoveryBoundedColdScalarMetadata.metadataSlots j≠i)
    (hl : ∀ j,RecoveryBoundedColdScalarMetadata.loadSlots j≠i) :
    input q bound C Q clauses B proj source i=targetData q bound C Q clauses B proj source i := by
  have keep : i=20 ∨ i=25 ∨ i=70 ∨ i=75 ∨ ((78 : ℕ) ≤ (i : Fin 158).val ∧ (i : Fin 158).val ≤ 115) ∨ i=152 := by
    have complete : ∀ i : Fin 158,
        (∀ j,driverSlots j≠i) → (∀ j,RecoveryBoundedColdWork.slots j≠i) →
        (∀ j,RecoveryBoundedColdScalarMetadata.metadataSlots j≠i) →
        (∀ j,RecoveryBoundedColdScalarMetadata.loadSlots j≠i) →
        i=20 ∨ i=25 ∨ i=70 ∨ i=75 ∨ ((78 : ℕ) ≤ (i : Fin 158).val ∧ (i : Fin 158).val ≤ 115) ∨ i=152 := by decide
    exact complete i hd hw hm hl
  fin_cases i
  all_goals first
    | (solve | simp at keep)
    | (simp [input,shared,targetData,RecoveryBoundedCountUniform.scanData,RecoveryBoundedCountBank.data,
        RecoveryBoundedFixedRestart.data,RecoveryBoundedFixedRestart.extra,RecoveryBoundedFixedContinue.data,
        RecoveryBoundedFixedContinue.padded,RecoveryBoundedFixedContinue.capacity,
        RecoveryBoundedGrammarBank.base,Fin.addCases,pad_empty])

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
