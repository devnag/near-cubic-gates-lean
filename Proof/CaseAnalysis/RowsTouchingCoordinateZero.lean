import Proof.CaseAnalysis.RowsTouchingCoordinatePorts

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def gateScore (mode : Bool) (st : Store):ℕ:=if mode then st.gate.included else st.gate.excluded

theorem zero_fields (mode : Bool) (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (j : Fin 4):
    data q G K k h w P C D E source mask st (zeroSlots mode j)=
      (![frame (binary w 0),frame (binary w (gateScore mode st)),
        List.replicate (2*w+1) true,List.replicate (4*w+3) false] : Fin 4→List Bool) j:=by
  cases mode <;> fin_cases j <;> rfl

theorem zero_outside (mode : Bool) (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (i : Fin 35) (hi:∀ j,zeroSlots mode j≠i):
    data q G K k h w P C D E source mask (cleared st mode) i=data q G K k h w P C D E source mask st i:=by
  revert hi
  refine cases35 (p:=fun i=>(∀ j,zeroSlots mode j≠i)→
    data q G K k h w P C D E source mask (cleared st mode) i=
      data q G K k h w P C D E source mask st i) ?_ ?_ ?_ ?_ ?_ i
  · intro j _;rw [data_low,data_low];rfl
  · intro j hj;rw [data_middle,data_middle]
    apply vector15
    · intro _;rfl
    · intro he;subst j;cases mode
      · exact False.elim (hj 1 rfl)
      · rfl
    · intro he;subst j;cases mode
      · rfl
      · exact False.elim (hj 1 rfl)
    · intro _;rfl
    · intro _;rfl
  · intro _;rw [data_count,data_count]
  · intro _;rw [data_log,data_log]
  · intro j _;rw [data_last,data_last];rfl

theorem zero_installed (mode : Bool) (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell) (st : Store):
    install (zeroSlots mode) (data q G K k h w P C D E source mask st)
      ![frame (binary w 0),frame (binary w 0),List.replicate (2*w+1) true,List.replicate (4*w+3) false]=
      data q G K k h w P C D E source mask (cleared st mode):=by
  apply HierarchyWidth.install_eq _ (by cases mode <;> decide)
  · intro j
    have actual:=zero_fields mode q G K k h w P C D E source mask (cleared st mode) j
    have hz:gateScore mode (cleared st mode)=0:=by cases mode <;> rfl
    simpa only [hz] using actual
  · exact zero_outside mode q G K k h w P C D E source mask st

theorem zero_run (mode : Bool) (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell) (st : Store):
    Step (zero mode) (4*w+6) heads (data q G K k h w P C D E source mask st)
      heads (data q G K k h w P C D E source mask (cleared st mode)):=by
  have actual:=Choice.zero_copy w (frame (binary w (gateScore mode st))) (by simp [frame_length,binary_length])
  have localHeads:∀ j,heads (zeroSlots mode j)=0:=by intro j;cases mode <;> fin_cases j <;> rfl
  have focused:=actual.dock (zeroSlots mode) (by cases mode <;> decide) heads
    (data q G K k h w P C D E source mask st) localHeads (zero_fields mode q G K k h w P C D E source mask st)
  exact focused.congr (dockH_existing _ _ _ localHeads) (zero_installed mode q G K k h w P C D E source mask st)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
