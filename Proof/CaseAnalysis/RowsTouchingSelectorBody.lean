import Proof.CaseAnalysis.RowsTouchingSelectorState

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E j : ℕ)
    (st : State q) (tail : List Bool):Fin 35→List Bool:=
  Coordinate.data q G K st.k st.h w P C D E (GateFoldReady.supportWord support++tail)
    (MaskShift.cells st.selected j) st.store

theorem body_run {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E j : ℕ)
    (st : State q) (tail : List Bool) (hj:j<q) (hv:Valid w P j st)
    (hwidth:q+G+1≤w) (hprod:2*q+G≤w) (hP:q+1≤P)
    (hC:P+1≤C) (hScan:2*q+3≤C) (hW:2*w+3≤C)
    (hLookup:Lookup.budget (PascalReady.width q) (q+1) q q+2≤C)
    (hD:GateFold.budget q w P G≤D) (hE:4*q+3≤E):
    Step Coordinate.machine (Coordinate.budget q G w P) Coordinate.heads
      (data support K w P C D E j st tail) Coordinate.heads
      (data support K w P C D E (j+1) (step support w P j st) tail):=by
  let records:=Gate.records support st.selected (remaining q j) ⟨j,hj⟩
  have len:records.length=G:=List.length_ofFn
  have hq:∀ xs∈records,xs.length=q:=by
    intro xs hxs
    rcases List.mem_ofFn.mp hxs with ⟨g,rfl⟩
    exact SupportScan.cells_length _ _ _ _
  have masks:∀ xs∈records,SupportScan.masks xs=
      SupportScan.masks (Coordinate.supportCells (MaskShift.cells st.selected j)):=by
    intro xs hxs
    rcases List.mem_ofFn.mp hxs with ⟨g,rfl⟩
    rw [support_cells st.selected j hj]
    simp only [SupportScan.cells_masks]
  have actual:=Coordinate.coordinate_run q K st.k st.h w P C D E records
    (MaskShift.cells st.selected j) st.store tail hq masks (MaskShift.cells_length _ _) (hv.2.2.2.2 hj)
    (by have h:=hv.1;omega) (by have h:=hv.1;omega) (by rw [len];exact hwidth)
    (by rw [len];exact hprod) hP hv.2.1 ⟨hv.2.2.1,hv.2.2.2.1⟩ hC hScan hW hLookup
    (by rw [len];exact hD) hE
  have pick:=picked_exact support st.selected j st.k st.h w P st.store hj hv.1
    ⟨hv.2.2.1,hv.2.2.2.1⟩
  dsimp only at actual
  rw [pick,MaskShift.transformed_cells _ st.selected j hj] at actual
  simpa only [data,step,dif_pos hj,records,len,GateFoldReady.records_word] using actual

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
