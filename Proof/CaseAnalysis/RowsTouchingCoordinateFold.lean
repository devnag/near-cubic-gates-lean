import Proof.CaseAnalysis.RowsTouchingCoordinateLayout

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fold_run (q K k h w P C D E : ℕ) (records : List (List SupportScan.Cell))
    (mask : List MaskShift.Cell) (st : Store) (tail : List Bool)
    (hq:∀ xs∈records,xs.length=q)
    (hmask:∀ xs∈records,SupportScan.masks xs=SupportScan.masks (supportCells mask))
    (hk:k≤q) (hw:q+1≤w) (hwidth:q+records.length+1≤w) (hP:q+1≤P)
    (valid:Gate.Valid q w P st.gate) (hzero:st.gate.excluded=0 ∧ st.gate.included=0)
    (hC:P+1≤C) (hScan:2*q+3≤C) (hW:2*w+3≤C)
    (hLookup:Lookup.budget (PascalReady.width q) (q+1) q q+2≤C)
    (hD:GateFold.budget q w P records.length≤D):
    Step fold (GateFoldReady.budget q w P records.length) heads
      (data q records.length K k h w P C D E (records.flatMap GateFold.word++tail) mask st) heads
      (data q records.length K k h w P C D E (records.flatMap GateFold.word++tail) mask
        {st with gate:=Gate.states q k w P records st.gate records.length}):=by
  have actual:=(GateFoldReady.ready_run q k w P C D records (supportCells mask) st.gate tail
    hq hmask hk hw hwidth hP valid hzero hC hScan hW hLookup hD).embed extraHeads (extra q K h w P E st)
  exact actual.congr_in rfl rfl |>.congr rfl rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
