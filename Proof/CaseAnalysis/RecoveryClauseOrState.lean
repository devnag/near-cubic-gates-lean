import Proof.CaseAnalysis.RecoveryClauseOrLayout

/-! The original OR operation returns the same clause bank, retaining all
source/query streams and arbitrary bounded literal scratch. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseOr
open LocalBitMultitape RepairRepresentation RecoveryRootRound RecoveryBoundedClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem node_state (H : Fin 71→ℕ) (A : Fin 71→List Bool) (node left right C L : ℕ)
    (out pre source refs result : List Bool) (h : State H A node left right C L out pre source refs) :
    State (heads H result) (data A node C result) (node+1) node right C L result pre source refs := by
  have aGate : ∀ j,data A node C result (gate j)=RecoveryBoundedUniversalGates.data node right C result j := by
    intro j
    by_cases hj1 : j=1
    · subst j;rfl
    by_cases hj20 : j=20
    · subst j
      change result=ZeroPadding.pad 0 result
      exact (ZeroPadding.pad_zero _).symm
    have h20 : gate j≠20 := by fin_cases j <;> first | contradiction | decide
    have h25 : gate j≠25 := by fin_cases j <;> decide
    have h45 : gate j≠45 := by fin_cases j <;> first | contradiction | decide
    have hd : RecoveryBoundedUniversalGates.data left right C out j=RecoveryBoundedUniversalGates.data node right C result j := by
      fin_cases j <;> first | rfl | contradiction
    exact (data_other A node C result (gate j) h20 h25 h45).trans ((h.gateA j).trans hd)
  refine ⟨?_,aGate,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    by_cases hj : j=20
    · subst j;rfl
    have h20 : gate j≠20 := by fin_cases j <;> first | contradiction | decide
    change Function.update H 20 result.length (gate j)=PCPPNativeClauseBank.heads result j
    rw [Function.update_of_ne h20]
    have he : PCPPNativeClauseBank.heads out j=PCPPNativeClauseBank.heads result j := by
      simp only [PCPPNativeClauseBank.heads,if_neg hj]
    exact (h.gateH j).trans he
  · intro j
    have hj : restore j≠20 := by fin_cases j <;> decide
    change Function.update H 20 result.length (restore j)=0
    rw [Function.update_of_ne hj]
    exact h.restoreH j
  · intro j
    fin_cases j
    · rfl
    · rfl
    · rw [data_other _ _ _ _ _ (by decide) (by decide) (by decide)]
      exact h.restoreA 2
    · rw [data_other _ _ _ _ _ (by decide) (by decide) (by decide)]
      exact h.restoreA 3
    · rw [data_other _ _ _ _ _ (by decide) (by decide) (by decide)]
      exact h.restoreA 4
  · exact h.zeroH
  · rw [data_other _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact h.zeroA
  · intro j
    have hj : scratch j≠20 := by fin_cases j <;> decide
    change Function.update H 20 result.length (scratch j)=0
    rw [Function.update_of_ne hj]
    exact h.scratchH j
  · intro j
    rw [data_other _ _ _ _ _ (by fin_cases j <;> decide) (by fin_cases j <;> decide) (by fin_cases j <;> decide)]
    exact h.scratchBound j
  · exact h.refsH
  · rw [data_other _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact h.refsA
  · exact h.logH
  · rw [data_other _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact h.logA
  · exact h.sourceH
  · rw [data_other _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact h.sourceA

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseOr
