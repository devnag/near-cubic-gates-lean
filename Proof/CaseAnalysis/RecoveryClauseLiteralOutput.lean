import Proof.CaseAnalysis.RecoveryLiteralOutput
import Proof.CaseAnalysis.RecoveryClausePrepared

/-! Actual whole streaming-literal output fields for the next clause stage.
Every unspecified tape is retained, including the original source stream. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseLiteralOutput
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prepared (A : Fin 71→List Bool) (second : Bool) (bits : List Bool)
    (C : ℕ) (work : Fin 11→List Bool):=
  RecoveryBoundedLiteralPrepared.decoded (RecoveryBoundedLiteralReset.output A second C) bits C work
noncomputable def data (A : Fin 71→List Bool) (second neg : Bool) (before : List ℕ)
    (ref node C : ℕ) (out bits : List Bool) (work : Fin 11→List Bool):=
  RecoveryBoundedLiteralDock.output second neg (prepared A second bits C work) before ref node C out

theorem prepared_other (A : Fin 71→List Bool) (second : Bool) (bits : List Bool) (C : ℕ)
    (work : Fin 11→List Bool) (i : Fin 71)
    (hi : ∀ j,RecoveryBoundedLiteralReset.workSlots second j≠i) :
    prepared A second bits C work i=A i := by
  have hd : ∀ j,RecoveryBoundedLiteralLoad.driverSlots j≠i := by
    intro j
    have h:=hi (j.castAdd 3)
    fin_cases j <;> exact h
  have h61 : i≠61:=fun he=>hi 0 he.symm
  rw [prepared,RecoveryBoundedLiteralPrepared.decoded,install_other _ _ _ _ hd]
  change Function.update (RecoveryBoundedLiteralReset.output A second C) 61 (ZeroPadding.pad C (frame bits)) i=A i
  rw [Function.update_of_ne h61]
  exact RecoveryBoundedLiteralPrepared.clean_other A second C i hi

theorem data_other (A : Fin 71→List Bool) (second neg : Bool) (before : List ℕ)
    (ref node C : ℕ) (out bits : List Bool) (work : Fin 11→List Bool) (i : Fin 71)
    (hi : ∀ j,RecoveryBoundedLiteralReset.workSlots second j≠i) (h20 : i≠20) (h25 : i≠25) :
    data A second neg before ref node C out bits work i=A i := by
  have h30 : i≠30:=fun he=>hi 12 he.symm
  have h37 : i≠37:=fun he=>hi 11 he.symm
  have ht : i≠RecoveryBoundedLiteralReset.target second:=fun he=>hi 13 he.symm
  rw [data,RecoveryBoundedLiteralDock.output_other _ _ _ _ _ _ _ _ _ h20 h25 h30 h37 ht]
  exact prepared_other A second bits C work i hi

theorem data_driver (A : Fin 71→List Bool) (second neg : Bool) (before : List ℕ)
    (ref node C : ℕ) (out bits : List Bool) (work : Fin 11→List Bool) (j : Fin 11) :
    data A second neg before ref node C out bits work (RecoveryBoundedLiteralLoad.driverSlots j)=work j := by
  rw [data,RecoveryBoundedLiteralDock.output_other _ _ _ _ _ _ _ _ _
    (by fin_cases j <;> decide) (by fin_cases j <;> decide)
    (by fin_cases j <;> decide) (by fin_cases j <;> decide)
    (by cases second <;> fin_cases j <;> decide)]
  exact RecoveryBoundedLiteralPrepared.decoded_driver _ _ _ _ j

theorem data_graph (A : Fin 71→List Bool) (second neg : Bool) (before : List ℕ)
    (ref node C : ℕ) (out bits : List Bool) (work : Fin 11→List Bool) (ha : A 20=out) :
    data A second neg before ref node C out bits work 20=
      out++if neg then RecoveryBoundedLiteral.emitted second ref else [] := by
  apply RecoveryBoundedLiteralDock.output_graph
  exact (prepared_other A second bits C work 20 (by cases second <;> decide)).trans ha
theorem data_count (A : Fin 71→List Bool) (second neg : Bool) (before : List ℕ)
    (ref node C : ℕ) (out bits : List Bool) (work : Fin 11→List Bool) (ha : A 25=List.replicate node true) :
    data A second neg before ref node C out bits work 25=List.replicate (node+neg.toNat) true := by
  apply RecoveryBoundedLiteralDock.output_count
  exact (prepared_other A second bits C work 25 (by cases second <;> decide)).trans ha
theorem data_reference (A : Fin 71→List Bool) (second neg : Bool) (before : List ℕ)
    (ref node C : ℕ) (out bits : List Bool) (work : Fin 11→List Bool) :
    data A second neg before ref node C out bits work (RecoveryBoundedLiteralReset.target second)=
      ZeroPadding.pad C (List.replicate (if neg then node else ref) true) :=
  RecoveryBoundedLiteralDock.output_reference _ _ _ _ _ _ _ _

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseLiteralOutput
