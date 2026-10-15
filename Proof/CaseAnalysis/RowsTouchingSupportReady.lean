import Proof.CaseAnalysis.RowsTouchingSupportCore

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportReady
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SupportScan
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ready_run (P C : ℕ) (pre tail : List Bool) (xs : List Cell) (hC:2*xs.length+3≤C):
    Step machine (4*xs.length+8) (heads pre.length)
      (data P C (pre++frame (xs.map Prod.fst)++tail) xs 0 false false)
      (heads (pre.length+2*xs.length+1))
      (data P C (pre++frame (xs.map Prod.fst)++tail) xs (count xs) (xs.any touched) (xs.any current)):=by
  have both:=core_run P pre tail xs
  have reset:=both.mask selected (by intro i hi;fin_cases i <;> first | rfl | exact False.elim (by simp [selected] at hi)) hC
  have enlarged:=reset.enlarge (m:=4*xs.length+8) (by omega)
  have aligned:=enlarged.congr_in (heads_in pre.length)
    (data_eq P C (pre++frame (xs.map Prod.fst)++tail) xs 0 false false)
  have finished:=aligned.congr (heads_out (pre.length+2*xs.length+1) xs.length (1+count xs))
    (data_eq P C (pre++frame (xs.map Prod.fst)++tail) xs (count xs) (xs.any touched) (xs.any current))
  exact finished

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportReady
