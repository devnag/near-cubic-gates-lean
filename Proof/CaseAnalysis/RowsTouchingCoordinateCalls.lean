import Proof.CaseAnalysis.RowsTouchingCoordinateMaskPorts
import Proof.CaseAnalysis.RowsTouchingCoordinateCounterPorts

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem choose_run (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell) (st : Store)
    (hl:st.left.length≤2*w+1) (hr:st.right.length≤2*w+1) (hs:st.gate.scratch.length≤2*w+1)
    (hleft:k*st.gate.excluded<2^w) (hright:h*st.gate.included<2^w):
    Step choose (Choice.budget w k h) heads (data q G K k h w P C D E source mask st)
      heads (data q G K k h w P C D E source mask (chosen w k h st)):=by
  have actual:=Choice.choice_run w st.gate.excluded st.gate.included k h P (choiceStore st) hl hr hs hleft hright
  have localHeads:∀ j,heads (choiceSlots j)=0:=by intro j;fin_cases j <;> rfl
  have focused:=actual.dock choiceSlots (by decide) heads (data q G K k h w P C D E source mask st)
    localHeads (choice_fields q G K k h w P C D E source mask st)
  exact focused.congr (dockH_existing _ _ _ localHeads) (choice_installed q G K k h w P C D E source mask st)

theorem mask_run (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell) (st : Store)
    (hlen:mask.length=q) (hc:st.carry=false) (hE:4*q+3≤E):
    Step shift (8*q+8) heads (data q G K k h w P C D E source mask st) heads
      (data q G K k h w P C D E source (MaskShift.transformed st.flag mask) (shifted mask st)):=by
  have actual:=MaskShift.shift_run st.flag mask E (by rw [hlen];exact hE)
  rw [hlen] at actual
  have localHeads:∀ j,heads (maskSlots j)=MaskShift.readyHeads j:=by intro j;fin_cases j <;> rfl
  have localData:∀ j,data q G K k h w P C D E source mask st (maskSlots j)=
      MaskShift.readyData st.flag mask false q E j:=by
    intro j
    simpa only [hc] using mask_fields q G K k h w P C D E source mask st j
  have focused:=actual.dock maskSlots (by decide) heads (data q G K k h w P C D E source mask st) localHeads localData
  have installed:=mask_installed q G K k h w P C D E source mask st
  rw [hlen] at installed
  exact focused.congr (dockH_existing _ _ _ localHeads) installed

theorem counters_run (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell) (st : Store)
    (hk:k+1≤P) (hh:h+1≤P):
    Step counters (2*k+2*h+2*(k-1)+17) heads (data q G K k h w P C D E source mask st) heads
      (data q G K (nextK k st.flag) (nextH h st.flag) w P C D E source mask st):=by
  have hP:∀ i : Fin 3,(![k,h,k-1] : Fin 3→ℕ) i+1≤P:=by
    intro i;fin_cases i
    · exact hk
    · exact hh
    · change k-1+1≤P;omega
  have actual:=CounterUpdate.update_run P ![k,h,k-1] st.flag hP
  have localHeads:∀ j,heads (counterSlots j)=0:=by intro j;fin_cases j <;> rfl
  have focused:=actual.dock counterSlots (by decide) heads (data q G K k h w P C D E source mask st)
    localHeads (counter_fields q G K k h w P C D E source mask st)
  exact focused.congr (dockH_existing _ _ _ localHeads) (counter_installed q G K k h w P C D E source mask st)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
