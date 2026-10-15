import Proof.CaseAnalysis.RecoveryLiteralDock

/-! The physical reader/decoder supplies the checked literal's exact ports.
All statements retain the original71-bank and the same framed reference list. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralPrepared
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def decoded (A : Fin 71→List Bool) (bits : List Bool) (C : ℕ) (out : Fin 11→List Bool):=
  install RecoveryBoundedLiteralLoad.driverSlots (RecoveryBoundedLiteralLoad.loaded A bits C) out
theorem decoded_driver (A : Fin 71→List Bool) (bits : List Bool) (C : ℕ)
    (out : Fin 11→List Bool) (j : Fin 11) :
    decoded A bits C out (RecoveryBoundedLiteralLoad.driverSlots j)=out j :=
  install_slot _ RecoveryBoundedLiteralLoad.driver_injective _ _ j
theorem decoded_old (A : Fin 71→List Bool) (bits : List Bool) (C : ℕ)
    (out : Fin 11→List Bool) (i : Fin 71) (hi : i.val<61) (h48 : i≠48) (h49 : i≠49) :
    decoded A bits C out i=A i := by
  have hn : ∀ j,RecoveryBoundedLiteralLoad.driverSlots j≠i := by
    intro j he
    fin_cases j
    all_goals first
      | exact h48 he.symm
      | exact h49 he.symm
      | have hv:=congrArg (fun k : Fin 71=>k.val) he
        norm_num [RecoveryBoundedLiteralLoad.driverSlots] at hv
        omega
  have h61 : i≠61 := by intro he;subst i;omega
  rw [decoded,install_other _ _ _ _ hn]
  exact Function.update_of_ne h61 _ _

theorem clean_driver (A : Fin 71→List Bool) (second : Bool) (C : ℕ) (j : Fin 11) :
    RecoveryBoundedLiteralReset.output A second C (RecoveryBoundedLiteralLoad.driverSlots j)=List.replicate C false := by
  have he : RecoveryBoundedLiteralLoad.driverSlots j=RecoveryBoundedLiteralReset.workSlots second (j.castAdd 3) := by
    fin_cases j <;> rfl
  rw [he]
  exact install_slot _ (RecoveryBoundedLiteralReset.work_injective second) _ _ _
theorem clean_other (A : Fin 71→List Bool) (second : Bool) (C : ℕ) (i : Fin 71)
    (hi : ∀ j,RecoveryBoundedLiteralReset.workSlots second j≠i) :
    RecoveryBoundedLiteralReset.output A second C i=A i := install_other _ _ _ _ hi
theorem head_old (H : Fin 71→ℕ) (position : ℕ) (i : Fin 71) (hi : i.val<61) :
    RecoveryBoundedLiteralLoad.heads H position i=H i := by
  have hn : i≠70 := by intro he;subst i;omega
  exact Function.update_of_ne hn _ _

theorem lookup (A : Fin 71→List Bool) (second : Bool) (C L : ℕ) (before : List ℕ)
    (ref : ℕ) (tail bits : List Bool) (out : Fin 11→List Bool)
    (hSource : A 59=RecoveryBoundedClauseLookup.source before ref tail)
    (hLog : A 43=List.replicate L false)
    (hIndex : out 9=ZeroPadding.pad C (RepairSource.VerifierDecoding.CompareMachine.word before.length)) :
    ∀ j,decoded (RecoveryBoundedLiteralReset.output A second C) bits C out
      (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseSelect.lookupSlots j))=
      RecoveryBoundedClauseLookup.input before ref C L tail j := by
  intro j
  fin_cases j
  · rw [decoded_old _ _ _ _ _ (by decide) (by decide) (by decide),clean_other _ _ _ _ (by cases second <;> decide)]
    exact hSource
  · rw [decoded_old _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact install_slot _ (RecoveryBoundedLiteralReset.work_injective second) _ _ 11
  · exact (decoded_driver _ _ _ _ 9).trans hIndex
  · rw [decoded_old _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact install_slot _ (RecoveryBoundedLiteralReset.work_injective second) _ _ 12
  · rw [decoded_old _ _ _ _ _ (by decide) (by decide) (by decide),clean_other _ _ _ _ (by cases second <;> decide)]
    exact hLog

theorem gate_unchanged (A : Fin 71→List Bool) (bits : List Bool) (C : ℕ)
    (out : Fin 11→List Bool) (second : Bool) (j : Fin 29) :
    decoded A bits C out (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) j))=
      A (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) j)) := by
  apply decoded_old
  all_goals cases second <;> fin_cases j <;> decide
theorem replace_unchanged (A : Fin 71→List Bool) (bits : List Bool) (C : ℕ)
    (out : Fin 11→List Bool) (second : Bool) (j : Fin 5) :
    decoded A bits C out (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseReplace.slots second j))=
      A (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseReplace.slots second j)) := by
  apply decoded_old
  all_goals cases second <;> fin_cases j <;> decide

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralPrepared
