import Proof.CaseAnalysis.RowsTouchingChoiceLayout
import Proof.CaseAnalysis.RowsTouchingOverwrite

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem zero_copy (w : ℕ) (backing : List Bool) (hb:backing.length≤2*w+1):
    Step RecoveryBoundedTapeCopy.machine (4*w+6) (fun _=>0)
      ![frame (binary w 0),backing,List.replicate (2*w+1) true,List.replicate (4*w+3) false]
      (fun _=>0) ![frame (binary w 0),frame (binary w 0),List.replicate (2*w+1) true,List.replicate (4*w+3) false]:=by
  have actual:=Step.of_ready (Overwrite.ready (frame (binary w 0)) backing (2*w+1) (4*w+3)
    (by simp [frame_length,binary_length]) hb (by omega))
  exact actual.enlarge (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
