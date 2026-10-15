import Proof.PCP.PCPFieldMoves

/-! Reusable raw unary copy for the physical midpoint traversal. Both heads
are reset; finite zero padding remains allocated and is preserved. -/
namespace NearCubicWires.RepairOrdinary.PCPUnaryCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bits => if q.val=0 then some
    (if bits 0 then ⟨0,![none,some true],fun _ => .right⟩
      else ⟨1,fun _ => none,fun _ => .stay⟩) else none
def cfg (q : Fin 2) (n done : ℕ) : Configuration 2 2 :=
  ⟨q,fun _ => done,![List.replicate n true,List.replicate done true]⟩

theorem copy_step (n done : ℕ) (hn : done<n) :
    step raw (cfg 0 n done)=some (cfg 0 n (done+1)) := by
  have hr : readTapeBit (List.replicate n true) done=true := by
    simp [readTapeBit,List.getD,hn]
  have hRule : raw.rule 0 (cfg 0 n done).scanned=
      some ⟨0,![none,some true],fun _ => .right⟩ := by
    simp [raw,cfg,Configuration.scanned,hr]
  change Option.map (applyAction (cfg 0 n done)) (raw.rule 0 (cfg 0 n done).scanned)=_
  rw [hRule]
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i
    · rfl
    · change writeTapeBit (List.replicate done true) done true=List.replicate (done+1) true
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using
        Streaming.write_append (List.replicate done true) true

theorem stop_step (n : ℕ) : step raw (cfg 0 n n)=some (cfg 1 n n) := by
  have hr : readTapeBit (List.replicate n true) n=false := by simp [readTapeBit,List.getD]
  have hRule : raw.rule 0 (cfg 0 n n).scanned=
      some ⟨1,fun _ => none,fun _ => .stay⟩ := by
    simp [raw,cfg,Configuration.scanned,hr]
  change Option.map (applyAction (cfg 0 n n)) (raw.rule 0 (cfg 0 n n).scanned)=_
  rw [hRule]
  rfl

theorem loop (remaining done : ℕ) :
    Timed raw (remaining+1) (cfg 0 (done+remaining) done)
      (cfg 1 (done+remaining) (done+remaining)) := by
  induction remaining generalizing done with
  | zero => simpa only [Nat.add_zero] using Timed.single (by rfl) (stop_step done)
  | succ remaining ih =>
    have ht := ih (done+1)
    rw [show done+1+remaining=done+(remaining+1) by omega] at ht
    exact Timed.step (by rfl) (copy_step _ done (by omega)) ht

def machine : Machine 3 4 := Rewind.machine raw

theorem copy_ready (n sourceCap outCap logCap : ℕ) :
    ReadyRun machine (2*n+4)
      ![ZeroPadding.pad sourceCap (List.replicate n true),
        List.replicate outCap false,List.replicate logCap false]
      ![ZeroPadding.pad sourceCap (List.replicate n true),
        ZeroPadding.pad outCap (List.replicate n true),List.replicate (max logCap (n+1)) false] := by
  obtain ⟨base,hr,hf,hs⟩ := (loop n 0).run (by rfl)
  obtain ⟨first,hfirst,hfinal,hsteps,_⟩ := Rewind.recorded_run raw _ _ base hr 0
    (by intro i; rfl)
  have he : 0+2*base.steps+2=2*n+4 := by omega
  rw [he] at hfirst hsteps
  let caps : Fin 3 → ℕ := ![sourceCap,outCap,logCap]
  obtain ⟨r,hrun,hrt,hrs,_⟩ := ZeroPadding.run_config machine caps _ _ first hfirst
  have hi : ZeroPadding.config caps (Rewind.recording (cfg 0 (0+n) 0) 0)=
      initialConfiguration machine
        ![ZeroPadding.pad sourceCap (List.replicate n true),
          List.replicate outCap false,List.replicate logCap false] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      fin_cases i
      · change ZeroPadding.pad sourceCap (List.replicate (0+n) true)=
          ZeroPadding.pad sourceCap (List.replicate n true)
        rw [Nat.zero_add]
      · change ZeroPadding.pad outCap []=List.replicate outCap false
        simp [ZeroPadding.pad]
      · change ZeroPadding.pad logCap []=List.replicate logCap false
        simp [ZeroPadding.pad]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,?_,hrs.trans hsteps⟩
  · rw [hrt,hfinal,hf,hs]
    simp only [Nat.zero_add]
    funext i
    fin_cases i
    · rfl
    · rfl
    · change ZeroPadding.pad logCap (List.replicate (n+1) false)=_
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  · intro i
    rw [hrt,hfinal]
    fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.PCPUnaryCopy
