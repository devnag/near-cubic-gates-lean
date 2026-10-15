import Proof.CaseAnalysis.RowsTouchingSelectorLoop

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
open LocalBitMultitape CloseoutRowsGateSupport RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem data_mask {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E j : ℕ)
    (st : State q) (tail : List Bool):data support K w P C D E j st tail 1=gateMembers st.selected:=by
  change SupportScan.masks (Coordinate.supportCells (MaskShift.cells st.selected j)) 0=_
  rw [Coordinate.support_masks]
  change (MaskShift.cells st.selected j).map MaskShift.live=_
  simp only [MaskShift.cells,List.map_ofFn,Function.comp_def,MaskShift.live,gateMembers]

theorem entry_mask {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E : ℕ)
    (initial : State q) (tail : List Bool) (j : ℕ):
    (entry support K w P C D E initial tail j []).tapes 1=
      gateMembers (states support w P initial j).selected:=data_mask support K w P C D E j (states support w P initial j) tail

theorem final_mask {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E : ℕ)
    (initial : State q) (tail : List Bool) (hP:q+1≤P) (hi:Valid w P 0 initial)
    (hs:initial.selected=∅) (hk:initial.k=K):
    (RepeatMachine.cfg 3 (entry support K w P C D E initial tail q []) q 1).tapes
      ((1 : Fin 35).castAdd 1)=gateMembers (SupplierTouching.touchingSelect support K):=by
  change (entry support K w P C D E initial tail q []).tapes 1=_
  rw [entry_mask,final_selected support K w P initial hP hi hs hk]

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
