import Proof.CaseAnalysis.RowsTouchingSelectorState

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
open SupplierTouching
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem step_solution {q G : ℕ} (support : Fin G→Finset (Fin q)) (w P j : ℕ) (st : State q)
    (hj:j<q) (hk:st.k≤q-j):
    touchingSelectAux support st.selected st.k ((List.finRange q).drop j)=
      touchingSelectAux support (step support w P j st).selected (step support w P j st).k
        ((List.finRange q).drop (j+1)):=by
  simpa only [step,dif_pos hj] using original_step support st.selected j st.k hj hk

theorem states_solution {q G : ℕ} (support : Fin G→Finset (Fin q)) (w P : ℕ) (initial : State q)
    (hP:q+1≤P) (hi:Valid w P 0 initial) (j : ℕ) (hj:j≤q):
    touchingSelectAux support initial.selected initial.k (List.finRange q)=
      touchingSelectAux support (states support w P initial j).selected (states support w P initial j).k
        ((List.finRange q).drop j):=by
  induction j with
  | zero=>simp only [states,List.drop_zero]
  | succ j ih=>
    have valid:=states_valid support w P initial hP hi j (by omega)
    exact (ih (by omega)).trans (step_solution support w P j _ (by omega) (by have h:=valid.1;omega))

theorem final_selected {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P : ℕ) (initial : State q)
    (hP:q+1≤P) (hi:Valid w P 0 initial) (hs:initial.selected=∅) (hk:initial.k=K):
    (states support w P initial q).selected=touchingSelect support K:=by
  have actual:=states_solution support w P initial hP hi q (Nat.le_refl q)
  have empty:(List.finRange q).drop q=[]:=List.drop_eq_nil_of_le (by simp)
  simpa only [hs,hk,empty,touchingSelectAux,touchingSelect] using actual.symm

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
