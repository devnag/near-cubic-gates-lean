import Proof.Amplification.RecoveryPrefixOutput

/-! Physically append the final false cell needed to turn the retained
Compare.word into the polynomial producer's UnaryTemplate.tape. Their binary
observations agree, but their allocated lists are not equal before this pass. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixDriverSeal
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=2
  rule := fun q bits=>if q.val=0 then some ⟨1,fun _=>none,fun _=>.right⟩ else
    if q.val=1 then some (if bits 0 then ⟨1,fun _=>none,fun _=>.right⟩
      else ⟨2,fun _=>some false,fun _=>.stay⟩) else none

def cfg (q : Fin 3) (n pos : Nat) : Configuration 1 3 :=
  ⟨q,fun _=>pos,fun _=>VerifierDecoding.CompareMachine.word n⟩
def finished (n : Nat) : Configuration 1 3 :=
  ⟨2,fun _=>n+1,fun _=>UnaryTemplate.tape n⟩

theorem enter (n : Nat) : step raw (cfg 0 n 0)=some (cfg 1 n 1) := rfl

theorem advance (n pos : Nat) (hp : pos<n) : step raw (cfg 1 n (pos+1))=some (cfg 1 n (pos+2)) := by
  have hr : readTapeBit (VerifierDecoding.CompareMachine.word n) (pos+1)=true := by
    simp [VerifierDecoding.CompareMachine.word,readTapeBit,List.getD,hp]
  simp [step,raw,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · rfl
  · rfl

theorem stop (n : Nat) : step raw (cfg 1 n (n+1))=some (finished n) := by
  have hr : readTapeBit (VerifierDecoding.CompareMachine.word n) (n+1)=false := by
    simp [VerifierDecoding.CompareMachine.word,readTapeBit,List.getD]
  simp only [step,raw,cfg,Configuration.scanned,hr]
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    change writeTapeBit (VerifierDecoding.CompareMachine.word n) (n+1) false=UnaryTemplate.tape n
    have h := Streaming.write_append (VerifierDecoding.CompareMachine.word n) false
    simpa only [VerifierDecoding.CompareMachine.word,List.length_cons,List.length_replicate,
      List.cons_append,UnaryTemplate.tape] using h

theorem suffix (n remaining pos : Nat) (hp : pos+remaining=n) :
    Timed raw (remaining+1) (cfg 1 n (pos+1)) (finished n) := by
  induction remaining generalizing pos with
  | zero =>
    have he : pos=n := by omega
    subst pos
    exact Timed.single (by rfl) (stop n)
  | succ remaining ih =>
    exact Timed.step (by rfl) (advance n pos (by omega)) (ih (pos+1) (by omega))

def machine := Rewind.machine raw

theorem seal_ready (n : Nat) :
    ClockJoin.ReadyRun machine (2*n+6) ![VerifierDecoding.CompareMachine.word n,[]]
      ![UnaryTemplate.tape n,List.replicate (n+2) false] := by
  have h := Timed.step (by rfl) (enter n) (suffix n n 0 (by omega))
  obtain ⟨base,hbase,hf,hsteps⟩ := h.run (by rfl)
  have hin : cfg 0 n 0=initialConfiguration raw (fun _=>VerifierDecoding.CompareMachine.word n) := rfl
  rw [hin] at hbase
  obtain ⟨r,hr,ht,hlog,hh,hs,_⟩ := Rewind.Workspace.reset_workspace raw (n+1+1)
    (fun _=>VerifierDecoding.CompareMachine.word n) base hbase 0
  have he : 2*base.steps+2=2*n+6 := by omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,by omega⟩
  · convert hr using 2 <;> first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hf,finished] using ht 0
    · simpa [hsteps] using hlog

end NearCubicWires.RepairSource.RecoveryPrefixDriverSeal
