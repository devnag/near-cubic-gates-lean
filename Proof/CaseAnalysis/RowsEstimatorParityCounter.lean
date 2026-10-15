import Proof.CaseAnalysis.RowsEstimatorParityAlternating

/-! Increment the retained original coordinate or staircase index without allocating a reset log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Counter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bs=>if q=0 then some (if bs 0 then ⟨0,fun _=>none,fun _=>.right⟩
      else ⟨1,fun _=>some true,fun _=>.left⟩)
    else if q=1 then some (if bs 0 then ⟨1,fun _=>none,fun _=>.left⟩
      else ⟨2,fun _=>none,fun _=>.right⟩)
    else none
def cfg (q : Fin 3) (n pos : ℕ) : Configuration 1 3:=⟨q,fun _=>pos,fun _=>CompareMachine.word n⟩

theorem true_read (n k : ℕ) (hk : k<n) : readTapeBit (CompareMachine.word n) (k+1)=true := by
  simp [CompareMachine.word,readTapeBit,List.getD,hk]

theorem next_step (n k : ℕ) (hk : k<n) : step machine (cfg 0 n (k+1))=some (cfg 0 n (k+2)) := by
  simp [step,machine,cfg,Configuration.scanned,true_read n k hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i;rfl
  · rfl

theorem write_step (n : ℕ) : step machine (cfg 0 n (n+1))=some (cfg 1 (n+1) n) := by
  have hz:readTapeBit (CompareMachine.word n) (n+1)=false:=by simp [CompareMachine.word,readTapeBit,List.getD]
  have hw:writeTapeBit (CompareMachine.word n) (n+1) true=CompareMachine.word (n+1):=by
    simpa [CompareMachine.word,List.replicate_add] using Streaming.write_append (CompareMachine.word n) true
  simp [step,machine,cfg,Configuration.scanned,hz]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i;simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i;exact hw

theorem back_step (n k : ℕ) (hk : k<n) : step machine (cfg 1 n (k+1))=some (cfg 1 n k) := by
  simp [step,machine,cfg,Configuration.scanned,true_read n k hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i;simp [applyAction,HeadMove.apply]
  · rfl

theorem stop_step (n : ℕ) : step machine (cfg 1 n 0)=some (cfg 2 n 1) := by
  simp [step,machine,cfg,Configuration.scanned,CompareMachine.word,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i;rfl
  · rfl

theorem back_time (n k : ℕ) (hk : k≤n) : Timed machine (k+1) (cfg 1 n k) (cfg 2 n 1) := by
  induction k with
  | zero=>exact Timed.single (by rfl) (stop_step n)
  | succ k ih=>exact Timed.step (by rfl) (back_step n k (by omega)) (ih (by omega))

theorem forward_time (n k left : ℕ) (he:k+left=n) :
    Timed machine (left+1) (cfg 0 n (k+1)) (cfg 1 (n+1) n) := by
  induction left generalizing k with
  | zero=>
    have h:k=n:=by omega
    subst k
    exact Timed.single (by rfl) (write_step n)
  | succ left ih=>
    have rest:=ih (k+1) (by omega)
    rw [show k+1+1=k+2 by omega] at rest
    exact Timed.step (by rfl) (next_step n k (by omega)) rest

theorem increment_run (n : ℕ) :
    Step machine (2*n+2) (fun _=>1) (fun _=>CompareMachine.word n)
      (fun _=>1) (fun _=>CompareMachine.word (n+1)) := by
  have actual:=(forward_time n 0 n (by omega)).trans (back_time (n+1) n (by omega))
  rw [show n+1+(n+1)=2*n+2 by omega] at actual
  obtain ⟨r,hr,rf,_⟩:=actual.run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Counter
