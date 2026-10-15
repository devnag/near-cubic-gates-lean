import Proof.MachineModel.OrdinarySourceSATLift

/-! A fixed local unary scale-and-append call for the selected refuter request.
Its driver is physical raw unary data and its output head streams forward. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.RequestScale
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (k : ℕ) (q : Fin (k+3)) (driver out : HeadMove) (bit : Option Bool) : Action 2 (k+3) :=
  ⟨q,![none,bit],![driver,out]⟩
def machine (k : ℕ) : Machine 2 (k+3) where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==k+2
  rule := fun q scanned =>
    if q.val=0 then some (if scanned 0 then action k 1 .right .stay none
      else action k ⟨k+2,by omega⟩ .stay .stay none)
    else if h : q.val ≤ k then some (action k ⟨q.val+1,by omega⟩ .stay .right (some true))
    else if q.val=k+1 then some (action k 0 .stay .stay none)
    else none

def cfg (k : ℕ) (q : Fin (k+3)) (total pos : ℕ) (out : List Bool) : Configuration 2 (k+3) :=
  ⟨q,![pos,out.length],![List.replicate total true,out]⟩

theorem enter (k total pos : ℕ) (out : List Bool) (hp : pos<total) :
    step (machine k) (cfg k 0 total pos out)=some (cfg k 1 total (pos+1) out) := by
  have hr : readTapeBit (List.replicate total true) pos=true := by simp [readTapeBit,List.getD,hp]
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem write (k total pos j : ℕ) (out : List Bool) (hj : j<k) :
    step (machine k) (cfg k ⟨j+1,by omega⟩ total pos out)=
      some (cfg k ⟨j+2,by omega⟩ total pos (out++[true])) := by
  simp [step,machine,cfg,show j+1 ≤ k by omega]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action,Streaming.write_append]

theorem return_step (k total pos : ℕ) (out : List Bool) :
    step (machine k) (cfg k ⟨k+1,by omega⟩ total pos out)=some (cfg k 0 total pos out) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem stop (k total : ℕ) (out : List Bool) :
    step (machine k) (cfg k 0 total total out)=some (cfg k ⟨k+2,by omega⟩ total total out) := by
  have hr : readTapeBit (List.replicate total true) total=false := by simp [readTapeBit,List.getD]
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem block (k total pos j remaining : ℕ) (out : List Bool) (hj : j+remaining=k) :
    Timed (machine k) (remaining+1) (cfg k ⟨j+1,by omega⟩ total pos out)
      (cfg k 0 total pos (out++List.replicate remaining true)) := by
  induction remaining generalizing j out with
  | zero =>
    have he : j=k := by omega
    subst j
    simpa using Timed.single (by simp [machine,cfg]) (return_step k total pos out)
  | succ remaining ih =>
    have h := Timed.step (by simp [machine,cfg]; omega) (write k total pos j out (by omega))
      (ih (j+1) (out++[true]) (by omega))
    simpa [List.replicate_succ,List.append_assoc] using h

theorem all (k total pos n : ℕ) (out : List Bool) (hn : pos+n=total) :
    Timed (machine k) ((k+2)*n+1) (cfg k 0 total pos out)
      (cfg k ⟨k+2,by omega⟩ total total (out++List.replicate (k*n) true)) := by
  induction n generalizing pos out with
  | zero =>
    have he : pos=total := by omega
    subst pos
    simpa using Timed.single (by simp [machine,cfg]) (stop k total out)
  | succ n ih =>
    have first := Timed.step (by simp [machine,cfg]) (enter k total pos out (by omega))
      (block k total (pos+1) 0 k out (by omega))
    have whole := first.trans (ih (pos+1) (out++List.replicate k true) (by omega))
    have hc : (k+1+1)+((k+2)*n+1)=(k+2)*(n+1)+1 := by ring
    have hw : (out++List.replicate k true)++List.replicate (k*n) true=
        out++List.replicate (k*(n+1)) true := by
      rw [List.append_assoc,←List.replicate_add,Nat.add_comm k (k*n),←Nat.mul_succ]
    rw [hc,hw] at whole
    exact whole

theorem run (k n : ℕ) (out : List Bool) : ∃ r,
    runFrom (machine k) ((k+2)*n+1) (cfg k 0 n 0 out)=some r ∧
    r.final=cfg k ⟨k+2,by omega⟩ n n (out++List.replicate (k*n) true) ∧
    r.steps=(k+2)*n+1 := by
  exact (all k n 0 n out (by omega)).run (by simp [machine,cfg])

end NearCubicWires.RepairSource.OrdinarySourceSATLift.RequestScale
