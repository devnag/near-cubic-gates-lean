import Proof.CaseAnalysis.RowsTouchingRowWidth
import Proof.Circuits.MatrixBucketDimensionsIncrement
import Proof.MachineModel.OrdinaryMatrixBucketRootPower

/-! Paid short count copies and in-place count increment. Padded count
words retain their full backing; no logical trimming is used. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Drivers
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem padded_template (P q : ℕ) (hP:q+2≤P):
    ZeroPadding.pad P (UnaryTemplate.tape q)=ZeroPadding.pad P (CompareMachine.word q):=by
  have ht:UnaryTemplate.tape q=ZeroPadding.pad (q+2) (CompareMachine.word q):=by
    simp [UnaryTemplate.tape,CompareMachine.word,ZeroPadding.pad]
  rw [ht]
  exact MatrixBucketRootPower.pad_pad (q+2) P (CompareMachine.word q) hP

theorem copy_run (source : List Bool) (P C : ℕ) (hP:source.length≤P) (hC:P+1≤C):
    Step RecoveryBoundedTapeCopy.machine (2*P+4) (fun _=>0)
      ![source,[],List.replicate P true,List.replicate C false]
      (fun _=>0) ![source,ZeroPadding.pad P source,List.replicate P true,List.replicate C false]:=by
  have h:=RecoveryBoundedTapeCopy.copy_ready source P C
  rw [CloseoutRowsMetadataCopy.copied_pad source P hP,Nat.max_eq_left hC] at h
  exact Step.of_ready h

theorem increment_run (q P : ℕ) (hP:q+3≤P):
    Step MatrixBucketDimensions.Increment.machine (2*q+5) (fun _=>0)
      (fun _=>ZeroPadding.pad P (CompareMachine.word q)) (fun _=>0)
      (fun _=>ZeroPadding.pad P (CompareMachine.word (q+1))):=by
  have h:=(Step.of_ready (MatrixBucketDimensions.Increment.increment_run q)).pad (fun _=>P)
  simpa only [padded_template P q (by omega),padded_template P (q+1) (by omega)] using h

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Drivers
