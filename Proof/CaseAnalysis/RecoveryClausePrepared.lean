import Proof.CaseAnalysis.RecoveryClauseState

/-! The original clause bank supplies all reset literal gate/count ports.
The old selected operand may be nonzero; its executed erase supplies zero. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseState
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {H : Fin 71→ℕ} {A : Fin 71→List Bool} {node left right C L : ℕ}
  {out pre source refs : List Bool}

theorem clean_gate (h : State H A node left right C L out pre source refs) (second : Bool) :
    ∀ j,RecoveryBoundedLiteralReset.output A second C
      (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) j))=
      RecoveryBoundedUniversalGates.data 0 0 C out j := by
  intro j
  by_cases hj1 : j=1
  · subst j
    have hs : RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) 1)=
        RecoveryBoundedLiteralReset.workSlots second 13 := by cases second <;> rfl
    rw [hs]
    change RecoveryBoundedLiteralReset.output A second C (RecoveryBoundedLiteralReset.workSlots second 13)=ZeroPadding.pad C []
    simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
    exact install_slot _ (RecoveryBoundedLiteralReset.work_injective second) _ _ 13
  by_cases hj25 : j=25
  · subst j
    have hs : RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) 25)=34 := by
      cases second <;> rfl
    rw [hs,RecoveryBoundedLiteralPrepared.clean_other A second C 34 (by cases second <;> decide)]
    change A 34=ZeroPadding.pad C []
    simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
    exact h.zeroA
  have hs : RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) j)=gate j := by
    cases second <;> fin_cases j <;> first | rfl | contradiction
  have hn : ∀ k,RecoveryBoundedLiteralReset.workSlots second k≠gate j := by
    cases second <;> fin_cases j <;> first | contradiction | decide
  have hd : RecoveryBoundedUniversalGates.data left right C out j=RecoveryBoundedUniversalGates.data 0 0 C out j := by
    fin_cases j <;> first | rfl | contradiction
  rw [hs,RecoveryBoundedLiteralPrepared.clean_other A second C (gate j) hn]
  exact (h.gateA j).trans hd

theorem clean_replace (h : State H A node left right C L out pre source refs) (second : Bool) :
    ∀ j,RecoveryBoundedLiteralReset.output A second C
      (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseReplace.slots second j))=
      RecoveryBoundedClauseReplace.data node 0 C 0 j := by
  intro j
  fin_cases j
  · change RecoveryBoundedLiteralReset.output A second C 25=List.replicate node true
    rw [RecoveryBoundedLiteralPrepared.clean_other A second C 25 (by cases second <;> decide)]
    exact h.restoreA 0
  · have hs : RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseReplace.slots second 1)=
        RecoveryBoundedLiteralReset.workSlots second 13 := by cases second <;> rfl
    change RecoveryBoundedLiteralReset.output A second C
      (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseReplace.slots second 1))=ZeroPadding.pad C []
    rw [hs]
    simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
    exact install_slot _ (RecoveryBoundedLiteralReset.work_injective second) _ _ 13
  · change RecoveryBoundedLiteralReset.output A second C 32=List.replicate C false
    rw [RecoveryBoundedLiteralPrepared.clean_other A second C 32 (by cases second <;> decide)]
    exact h.restoreA 2
  · change RecoveryBoundedLiteralReset.output A second C 22=List.replicate C true
    rw [RecoveryBoundedLiteralPrepared.clean_other A second C 22 (by cases second <;> decide)]
    exact h.restoreA 3
  · change RecoveryBoundedLiteralReset.output A second C 23=List.replicate (C+1) false
    rw [RecoveryBoundedLiteralPrepared.clean_other A second C 23 (by cases second <;> decide)]
    exact h.restoreA 4

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseState
