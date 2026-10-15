import Proof.CaseAnalysis.RowsTouchingSupportLayout

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportReady
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SupportScan
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scanned_run (P : ℕ) (pre tail : List Bool) (xs : List Cell):
    Step SupportScan.machine (2*xs.length+1) ![pre.length,0,0,0,1,0,0]
      (raw P (pre++frame (xs.map Prod.fst)++tail) xs 0 false false)
      ![pre.length+2*xs.length+1,xs.length,xs.length,xs.length,1+count xs,0,0]
      (raw P (pre++frame (xs.map Prod.fst)++tail) xs (count xs) (xs.any touched) (xs.any current)):=by
  have padded:=(SupportScan.counter_step pre tail xs).pad (pads P)
  have aligned:=padded.congr_in rfl (raw_eq P (pre++frame (xs.map Prod.fst)++tail) xs 0 false false)
  exact aligned.congr rfl (raw_eq P (pre++frame (xs.map Prod.fst)++tail) xs (count xs) (xs.any touched) (xs.any current))

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportReady
