import Proof.CaseAnalysis.RowsTouchingCoordinateCalls
import Proof.CaseAnalysis.RowsTouchingCoordinateFold
import Proof.CaseAnalysis.RowsTouchingCoordinateZero
import Proof.CaseAnalysis.RowsTouchingCoordinateBounds

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def folded (q k w P : ℕ) (records : List (List SupportScan.Cell)) (st : Store):Store:=
  {st with gate:=Gate.states q k w P records st.gate records.length}
def budget (q G w P : ℕ):ℕ:=GateFoldReady.budget q w P G+Choice.budget w q q+
  (8*q+8)+(6*q+17)+2*(4*w+6)+5
def advanced (q k h w P : ℕ) (records : List (List SupportScan.Cell)) (mask : List MaskShift.Cell) (st : Store):Store:=
  zeroed (shifted mask (chosen w k h (folded q k w P records st)))

theorem coordinate_run (q K k h w P C D E : ℕ) (records : List (List SupportScan.Cell))
    (mask : List MaskShift.Cell) (st : Store) (tail : List Bool)
    (hq:∀ xs∈records,xs.length=q)
    (hmask:∀ xs∈records,SupportScan.masks xs=SupportScan.masks (supportCells mask))
    (hlen:mask.length=q) (hc:st.carry=false) (hk:k≤q) (hh:h≤q)
    (hwidth:q+records.length+1≤w) (hprod:2*q+records.length≤w) (hP:q+1≤P)
    (valid:Valid q w P st) (hzero:st.gate.excluded=0 ∧ st.gate.included=0)
    (hC:P+1≤C) (hScan:2*q+3≤C) (hW:2*w+3≤C)
    (hLookup:Lookup.budget (PascalReady.width q) (q+1) q q+2≤C)
    (hD:GateFold.budget q w P records.length≤D) (hE:4*q+3≤E):
    let picked:=(chosen w k h (folded q k w P records st)).flag
    Step machine (budget q records.length w P) heads
      (data q records.length K k h w P C D E (records.flatMap GateFold.word++tail) mask st) heads
      (data q records.length K (nextK k picked) (nextH h picked) w P C D E
        (records.flatMap GateFold.word++tail) (MaskShift.transformed picked mask)
        (advanced q k h w P records mask st)):=by
  dsimp only
  let fg:=folded q k w P records st
  let cg:=chosen w k h fg
  let mg:=shifted mask cg
  let source:=records.flatMap GateFold.word++tail
  let nextMask:=MaskShift.transformed cg.flag mask
  have fvalid:Gate.Valid q w P fg.gate:=Gate.states_valid q k w P records st.gate hq hP valid.1 _ (Nat.le_refl _)
  have scores:fg.gate.excluded≤records.length*2^q ∧ fg.gate.included≤records.length*2^q:=by
    have raw:=Gate.states_scores q k w P records st.gate hq records.length (Nat.le_refl _)
    simpa only [fg,folded,hzero.1,hzero.2,Nat.zero_add] using raw
  have first:=fold_run q K k h w P C D E records mask st tail hq hmask hk (by omega) hwidth hP
    valid.1 hzero hC hScan hW hLookup hD
  have second:=choose_run q records.length K k h w P C D E source mask fg valid.2.1 valid.2.2 fvalid.2.2.2
    (product_fits q records.length w k fg.gate.excluded hk scores.1 hprod)
    (product_fits q records.length w h fg.gate.included hh scores.2 hprod)
  have third:=mask_run q records.length K k h w P C D E source mask cg hlen hc hE
  have fourth:=counters_run q records.length K k h w P C D E source nextMask mg (by omega) (by omega)
  have fifth:=zero_run false q records.length K (nextK k cg.flag) (nextH h cg.flag) w P C D E source nextMask mg
  have sixth:=zero_run true q records.length K (nextK k cg.flag) (nextH h cg.flag) w P C D E source nextMask (cleared mg false)
  have choiceCost:Choice.budget w k h≤Choice.budget w q q:=by
    have hm:=Nat.mul_le_mul_right (12*w+16) (Nat.add_le_add hk hh)
    unfold Choice.budget
    omega
  have counterCost:2*k+2*h+2*(k-1)+17≤6*q+17:=by omega
  exact (((((first.seq second).seq third).seq fourth).seq fifth).seq sixth).enlarge (by
    unfold budget
    omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
