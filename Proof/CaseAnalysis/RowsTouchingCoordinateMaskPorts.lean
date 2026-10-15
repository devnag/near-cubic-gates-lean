import Proof.CaseAnalysis.RowsTouchingCoordinatePorts

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def shifted (mask : List MaskShift.Cell) (st : Store):Store:=
  {st with carry:=MaskShift.carry mask mask.length}

theorem support_masks (mask : List MaskShift.Cell):
    SupportScan.masks (supportCells mask)=![mask.map MaskShift.live,mask.map MaskShift.current,mask.map MaskShift.remaining]:=by
  funext i;fin_cases i <;> simp [SupportScan.masks,supportCells,List.map_map,Function.comp_def,
    MaskShift.live,MaskShift.current,MaskShift.remaining]

theorem mask_fields (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (j : Fin 7):
    data q G K k h w P C D E source mask st (maskSlots j)=MaskShift.readyData st.flag mask st.carry q E j:=by
  fin_cases j
  · exact congrFun (support_masks mask) 0
  · exact congrFun (support_masks mask) 1
  · exact congrFun (support_masks mask) 2
  · rfl
  · rfl
  · rfl
  · rfl

theorem mask_outside (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (i : Fin 35) (hi:∀ j,maskSlots j≠i):
    data q G K k h w P C D E source (MaskShift.transformed st.flag mask) (shifted mask st) i=
      data q G K k h w P C D E source mask st i:=by
  revert hi
  refine cases35 (p:=fun i=>(∀ j,maskSlots j≠i)→
    data q G K k h w P C D E source (MaskShift.transformed st.flag mask) (shifted mask st) i=
      data q G K k h w P C D E source mask st i) ?_ ?_ ?_ ?_ ?_ i
  · intro j hj;rw [data_low,data_low]
    apply vector9
    · intro _;rfl
    · intro he;subst j;exact False.elim (hj 0 rfl)
    · intro he;subst j;exact False.elim (hj 1 rfl)
    · intro he;subst j;exact False.elim (hj 2 rfl)
    · intro _;rfl
  · intro j _;rw [data_middle,data_middle];rfl
  · intro _;rw [data_count,data_count]
  · intro _;rw [data_log,data_log]
  · intro j hj;rw [data_last,data_last]
    apply vector9
    · intro _;rfl
    · intro _;rfl
    · intro _;rfl
    · intro _;rfl
    · intro he;subst j;exact False.elim (hj 4 rfl)

theorem mask_installed (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell) (st : Store):
    install maskSlots (data q G K k h w P C D E source mask st)
      (MaskShift.readyData st.flag (MaskShift.transformed st.flag mask) (MaskShift.carry mask mask.length) q E)=
      data q G K k h w P C D E source (MaskShift.transformed st.flag mask) (shifted mask st):=by
  apply HierarchyWidth.install_eq _ (by decide)
  · exact mask_fields q G K k h w P C D E source (MaskShift.transformed st.flag mask) (shifted mask st)
  · exact mask_outside q G K k h w P C D E source mask st

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
