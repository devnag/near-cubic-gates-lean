import Proof.CaseAnalysis.RecoveryLiteralNode

/-! Opaque literal boundaries: the exact query lookup supplies the original
NOT operand while all graph, source and reset fields remain retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def kind (second : Bool) : Fin 4:=if second then 1 else 0
theorem kind_second (second : Bool) : RecoveryBoundedLiteralNode.second (kind second)=second := by cases second <;> rfl
theorem kind_native (second : Bool) : RecoveryBoundedClauseGate.nativeKind (kind second)=0 := by cases second <;> rfl

theorem selected_gate (second : Bool) (A : Fin 61→List Bool) (before : List ℕ) (ref C : ℕ) (out : List Bool)
    (hA : ∀ j,A (RecoveryBoundedClauseGate.slots (kind second) j)=RecoveryBoundedUniversalGates.data 0 0 C out j) :
    ∀ j,RecoveryBoundedClauseSelect.output A second before ref C (RecoveryBoundedClauseGate.slots (kind second) j)=
      RecoveryBoundedUniversalGates.data ref 0 C out j := by
  intro j
  have h:=hA j
  fin_cases j <;> cases second <;> first | rfl | exact h

theorem selected_replace (second : Bool) (A : Fin 61→List Bool) (before : List ℕ) (ref node C : ℕ)
    (hA : ∀ j,A (RecoveryBoundedClauseReplace.slots second j)=RecoveryBoundedClauseReplace.data node 0 C 0 j) :
    ∀ j,RecoveryBoundedClauseSelect.output A second before ref C (RecoveryBoundedClauseReplace.slots second j)=
      RecoveryBoundedClauseReplace.data node ref C 0 j := by
  intro j
  have h:=hA j
  fin_cases j <;> cases second <;> first | rfl | exact h

theorem selected_flag (second : Bool) (A : Fin 61→List Bool) (before : List ℕ) (ref C : ℕ) :
    RecoveryBoundedClauseSelect.output A second before ref C 48=A 48 := by cases second <;> rfl

def emitted (second : Bool) (ref : ℕ):=RecoveryBoundedClauseNative.emitted (RecoveryBoundedClauseGate.nativeKind (kind second)) ref 0
def output (second negative : Bool) (A : Fin 61→List Bool) (before : List ℕ) (ref node C : ℕ) (out : List Bool):=
  if negative then RecoveryBoundedLiteralNode.output (RecoveryBoundedClauseSelect.output A second before ref C)
    (kind second) node C (out++emitted second ref)
  else RecoveryBoundedClauseSelect.output A second before ref C
def heads (second negative : Bool) (H : Fin 61→ℕ) (ref : ℕ) (out : List Bool):=
  if negative then RecoveryBoundedClauseGate.heads H (out++emitted second ref) else H

theorem emitted_not (n ref : ℕ) (second : Bool) :
    emitted second ref=PCPPRequestNodeSchema.native (.not ref : BooleanNode n) := by
  rw [emitted,kind_native]
  exact RecoveryBoundedClauseNative.not_native n ref

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
