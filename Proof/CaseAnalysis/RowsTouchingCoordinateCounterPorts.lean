import Proof.CaseAnalysis.RowsTouchingCoordinatePorts

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem counter_after (k h : ℕ) (flag : Bool):
    CounterUpdate.after ![k,h,k-1] flag=![nextK k flag,nextH h flag,nextK k flag-1]:=by
  cases flag <;> funext i
  all_goals fin_cases i <;> simp [CounterUpdate.after,CounterUpdate.reduced,nextK,nextH]

theorem counter_fields (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (j : Fin 4):
    data q G K k h w P C D E source mask st (counterSlots j)=CounterUpdate.data P ![k,h,k-1] st.flag j:=by
  fin_cases j <;> rfl

theorem counter_outside (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (i : Fin 35) (hi:∀ j,counterSlots j≠i):
    data q G K (nextK k st.flag) (nextH h st.flag) w P C D E source mask st i=
      data q G K k h w P C D E source mask st i:=by
  revert hi
  refine cases35 (p:=fun i=>(∀ j,counterSlots j≠i)→
    data q G K (nextK k st.flag) (nextH h st.flag) w P C D E source mask st i=
      data q G K k h w P C D E source mask st i) ?_ ?_ ?_ ?_ ?_ i
  · intro j _;rw [data_low,data_low]
  · intro j hj;rw [data_middle,data_middle]
    apply vector15
    · intro he;subst j;exact False.elim (hj 0 rfl)
    · intro _;rfl
    · intro _;rfl
    · intro _;rfl
    · intro he;subst j;exact False.elim (hj 2 rfl)
  · intro _;rw [data_count,data_count]
  · intro _;rw [data_log,data_log]
  · intro j hj;rw [data_last,data_last]
    apply vector9
    · intro he;subst j;exact False.elim (hj 1 rfl)
    · intro _;rfl
    · intro _;rfl
    · intro _;rfl
    · intro _;rfl

theorem counter_installed (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell) (st : Store):
    install counterSlots (data q G K k h w P C D E source mask st)
      (CounterUpdate.data P (CounterUpdate.after ![k,h,k-1] st.flag) st.flag)=
      data q G K (nextK k st.flag) (nextH h st.flag) w P C D E source mask st:=by
  rw [counter_after]
  apply HierarchyWidth.install_eq _ (by decide)
  · exact counter_fields q G K (nextK k st.flag) (nextH h st.flag) w P C D E source mask st
  · exact counter_outside q G K k h w P C D E source mask st

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
