import Proof.CaseAnalysis.RecoveryLiteralStream

/-! Only the original literal's graph/count/reference and two lookup scratch
fields change. These opaque equalities retain all decoder/source storage. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralDock
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_old (second neg : Bool) (A : Fin 71→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) (j : Fin 61) :
    output second neg A before ref node C out (slots j)=
      RecoveryBoundedLiteral.output second neg (fun i=>A (slots i)) before ref node C out j :=
  install_slot slots slots_injective _ _ j

theorem output_other (second neg : Bool) (A : Fin 71→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) (i : Fin 71)
    (h20 : i≠20) (h25 : i≠25) (h30 : i≠30) (h37 : i≠37)
    (ht : i≠RecoveryBoundedLiteralReset.target second) :
    output second neg A before ref node C out i=A i := by
  by_cases hi : ∃ j,slots j=i
  · obtain ⟨j,rfl⟩:=hi
    have h20' : j≠20:=fun he=>h20 (congrArg slots he)
    have h25' : j≠25:=fun he=>h25 (congrArg slots he)
    have h30' : j≠30:=fun he=>h30 (congrArg slots he)
    have h37' : j≠37:=fun he=>h37 (congrArg slots he)
    have ht' : j≠RecoveryBoundedClauseSelect.target second := by
      intro he
      apply ht
      rw [he]
      cases second <;> rfl
    rw [output_old]
    cases neg <;> cases second
    all_goals simp [RecoveryBoundedClauseSelect.target] at ht'
    all_goals simp [RecoveryBoundedLiteral.output,RecoveryBoundedLiteralNode.output,RecoveryBoundedClauseReplace.output,
        RecoveryBoundedClauseGate.output,RecoveryBoundedLiteral.kind_second,RecoveryBoundedClauseSelect.output,
        RecoveryBoundedClauseSelect.lookupOutput,RecoveryBoundedClauseSelect.target,
        h20',h25',h30',h37',ht']
  · exact install_other slots A _ i (by intro j he;exact hi ⟨j,he⟩)

theorem output_graph (second neg : Bool) (A : Fin 71→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) (h20 : A 20=out) :
    output second neg A before ref node C out 20=out++if neg then RecoveryBoundedLiteral.emitted second ref else [] := by
  exact (output_old second neg A before ref node C out 20).trans
    (RecoveryBoundedLiteral.output_graph second neg _ before ref node C out h20)
theorem output_count (second neg : Bool) (A : Fin 71→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) (h25 : A 25=List.replicate node true) :
    output second neg A before ref node C out 25=List.replicate (node+neg.toNat) true := by
  exact (output_old second neg A before ref node C out 25).trans
    (RecoveryBoundedLiteral.output_count second neg _ before ref node C out h25)
theorem output_reference (second neg : Bool) (A : Fin 71→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) :
    output second neg A before ref node C out (RecoveryBoundedLiteralReset.target second)=
      ZeroPadding.pad C (List.replicate (if neg then node else ref) true) := by
  have h:=output_old second neg A before ref node C out (RecoveryBoundedClauseSelect.target second)
  rw [RecoveryBoundedLiteral.output_reference] at h
  cases second <;> exact h

theorem output_prefix (second neg : Bool) (A : Fin 71→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) :
    output second neg A before ref node C out 37=ZeroPadding.pad C (RecoveryBoundedSelectorLoop.sourceWord before) := by
  rw [show (37 : Fin 71)=slots 37 by rfl,output_old]
  cases second <;> cases neg <;> rfl
theorem output_selected_frame (second neg : Bool) (A : Fin 71→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) :
    output second neg A before ref node C out 30=ZeroPadding.pad C (frame (List.replicate ref true)) := by
  rw [show (30 : Fin 71)=slots 30 by rfl,output_old]
  cases second <;> cases neg <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralDock
