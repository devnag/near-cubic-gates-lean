import Proof.CaseAnalysis.RowsTouchingSupportPadded

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportReady
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SupportScan
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem core_run (P : ℕ) (pre tail : List Bool) (xs : List Cell):
    Step core (2*xs.length+3) ![pre.length,0,0,0,0,0,0]
      (raw P (pre++frame (xs.map Prod.fst)++tail) xs 0 false false)
      ![pre.length+2*xs.length+1,xs.length,xs.length,xs.length,1+count xs,0,0]
      (raw P (pre++frame (xs.map Prod.fst)++tail) xs (count xs) (xs.any touched) (xs.any current)):=by
  let source:=pre++frame (xs.map Prod.fst)++tail
  obtain ⟨s,srun,sf,_⟩:=DecompositionCountPosition.move_run directions ![pre.length,0,0,0,0,0,0]
    (raw P source xs 0 false false)
  have positioned:Step move 1 ![pre.length,0,0,0,0,0,0] (raw P source xs 0 false false)
      ![pre.length,0,0,0,1,0,0] (raw P source xs 0 false false):=by
    refine Step.of_run srun ?_ ?_
    · rw [sf];funext i;fin_cases i <;> rfl
    · rw [sf]
  exact (positioned.seq (scanned_run P pre tail xs)).enlarge (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportReady
