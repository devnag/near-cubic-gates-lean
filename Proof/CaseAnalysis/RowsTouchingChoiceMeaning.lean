import Proof.CaseAnalysis.RowsTouchingComparisonRatio
import Proof.CaseAnalysis.RowsTouchingChoiceLayout

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
open SupplierTouching
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def decision {q G : ℕ} (support : Fin G→Finset (Fin q))
    (selected rest : Finset (Fin q)) (coordinate : Fin q) (k : ℕ):Bool:=
  decide (0<k)&&decide (k*Complement.score support selected rest k≤
    (rest.card+1-k)*Complement.score support (insert coordinate selected) rest (k-1))

theorem decision_exact {q G : ℕ} (support : Fin G→Finset (Fin q))
    (selected rest : Finset (Fin q)) (coordinate : Fin q) (k : ℕ) (hk:k≤rest.card+1):
    decision support selected rest coordinate k=true ↔
      k≠0 ∧ conditionalTouchNumerator support (insert coordinate selected) rest (k-1)*Nat.choose rest.card k≤
        conditionalTouchNumerator support selected rest k*Nat.choose rest.card (k-1):=by
  unfold decision
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  by_cases hz:k=0
  · simp [hz]
  have hp:0<k:=by omega
  rw [Complement.score_comparison,Complement.feasible_comparison rest.card k _ _ hp hk]
  simp only [hp,ne_eq,hz,not_false_eq_true,true_and,Nat.mul_comm k,Nat.mul_comm (rest.card+1-k)]

theorem forced_decision {q G : ℕ} (support : Fin G→Finset (Fin q))
    (selected rest : Finset (Fin q)) (coordinate : Fin q):
    decision support selected rest coordinate (rest.card+1)=true:=by
  have hz:Complement.score support selected rest (rest.card+1)=0:=by
    unfold Complement.score
    apply Finset.sum_eq_zero
    intro g _
    have small:(rest\support g).card<rest.card+1:=
      Nat.lt_succ_of_le (Finset.card_le_card Finset.sdiff_subset)
    simp [Nat.choose_eq_zero_of_lt small]
  simp [decision,hz]

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
