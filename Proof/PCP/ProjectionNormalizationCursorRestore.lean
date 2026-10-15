import Proof.PCP.ProjectionNormalizationClauseEquality

/-! The keep-last suffix scan must return to its arbitrary entry cursor.
Only right moves of that source cursor are logged. The executed reset then
consumes exactly those marks; every other source and output cursor is retained. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.CursorRestore
open LocalBitMultitape RepairOrdinary RecoveryExecution
open Rewind (config recording rewinding)
open SelectiveReset (finished)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def NoLeft {t s : ℕ} (p : Machine t s) (target : Fin t) : Prop :=
  ∀ q bits a,p.rule q bits=some a → a.move target≠.left

def recordAction {t s : ℕ} (target : Fin t) (a : Action t s) : Action (t+1) (s+2) where
  nextControl := a.nextControl.castAdd 2
  write := Fin.addCases a.write (fun _ => if a.move target=.right then some true else none)
  move := Fin.addCases a.move (fun _ => if a.move target=.right then .right else .stay)
def machine {t s : ℕ} (p : Machine t s) (target : Fin t) : Machine (t+1) (s+2) where
  descriptionBits := 0
  start := p.start.castAdd 2
  halted := (Rewind.machine p).halted
  rule := fun state scanned => Fin.addCases
    (fun c => if p.halted c then some (Rewind.bridgeAction t s)
      else (p.rule c (fun i => scanned (i.castAdd 1))).map (recordAction target))
    (fun k => if k.val=0 then
      if scanned ((0 : Fin 1).natAdd t) then
        some (MaskedReset.rewindAction s (fun i => decide (i=target)))
      else some (Rewind.finishAction t s) else none) state

theorem apply_record {t s : ℕ} (target : Fin t) (c : Configuration t s) (a : Action t s) (n : ℕ) :
    applyAction (recording c n) (recordAction target a)=
      recording (applyAction c a) (n+if a.move target=.right then 1 else 0) := by
  have hw : writeTapeBit (List.replicate n true) n true=List.replicate (n+1) true := by
    simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using Streaming.write_append (List.replicate n true) true
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [applyAction,recordAction,recording,config]
    · cases hm : a.move target <;> simp [applyAction,recordAction,recording,config,hm,HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [applyAction,recordAction,recording,config]
    · cases hm : a.move target <;> simp [applyAction,recordAction,recording,config,hm,hw]

theorem record_step {t s : ℕ} (p : Machine t s) (target : Fin t) (forward : NoLeft p target)
    (c d : Configuration t s) (count : ℕ) (hn : p.halted c.control=false) (hs : step p c=some d) :
    ∃ delta,delta≤1 ∧ d.heads target=c.heads target+delta ∧
      step (machine p target) (recording c count)=some (recording d (count+delta)) := by
  cases hr : p.rule c.control c.scanned with
  | none => simp [step,hr] at hs
  | some a =>
    have hd : applyAction c a=d := by simpa [step,hr] using hs
    subst d
    let delta := if a.move target=.right then 1 else 0
    refine ⟨delta,?_,?_,?_⟩
    · dsimp [delta]; split <;> omega
    · have hf := forward c.control c.scanned a hr
      change (a.move target).apply (c.heads target)=c.heads target+delta
      cases hm : a.move target <;> simp_all [delta,HeadMove.apply]
    · have hrule : (machine p target).rule (recording c count).control (recording c count).scanned=
          some (recordAction target a) := by
        simp [machine,recording,config,Configuration.scanned,hn]
        exact ⟨a,hr,rfl⟩
      simp only [step,hrule,Option.map_some,Option.some.injEq]
      exact apply_record target c a count

theorem bridge_step {t s : ℕ} (p : Machine t s) (target : Fin t)
    (c : Configuration t s) (count : ℕ) (hh : p.halted c.control=true) :
    step (machine p target) (recording c count)=some (rewinding (s := s) c.heads c.tapes count 0) := by
  simp [step,machine,recording,config,hh]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction,Rewind.bridgeAction,rewinding,config,HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction,Rewind.bridgeAction,rewinding,config]

theorem rewind_step {t s : ℕ} (p : Machine t s) (target : Fin t)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (n z : ℕ) :
    step (machine p target) (rewinding (s := s) heads tapes (n+1) z)=
      some (rewinding (s := s) (fun i => if i=target then heads i-1 else heads i) tapes n (z+1)) := by
  have hr := Streaming.read_counter n z
  simp [step,machine,rewinding,config,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · by_cases h : j=target <;> simp [applyAction,MaskedReset.rewindAction,HeadMove.apply,h]
    · simp [applyAction,MaskedReset.rewindAction,HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction,MaskedReset.rewindAction,Streaming.erase_counter]

theorem finish_step {t s : ℕ} (p : Machine t s) (target : Fin t)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (z : ℕ) :
    step (machine p target) (rewinding (s := s) heads tapes 0 z)=
      some (finished (s := s) heads tapes z) := by
  simp [step,machine,rewinding,config,Configuration.scanned,Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction,Rewind.finishAction,finished,config,HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction,Rewind.finishAction,finished,config]

theorem rewind_timed {t s : ℕ} (p : Machine t s) (target : Fin t)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (n z : ℕ) :
    Timed (machine p target) (n+1) (rewinding (s := s) heads tapes n z)
      (finished (s := s) (fun i => if i=target then heads i-n else heads i) tapes (n+z)) := by
  induction n generalizing heads z with
  | zero =>
    simpa using Timed.single
      (by simp [machine,Rewind.machine,rewinding,config]) (finish_step p target heads tapes z)
  | succ n ih =>
    let next := fun i => if i=target then heads i-1 else heads i
    have ht := ih next (z+1)
    have he : (fun i => if i=target then next i-n else next i)=
        fun i => if i=target then heads i-(n+1) else heads i := by
      funext i; by_cases h : i=target <;> simp [next,h,Nat.sub_sub,Nat.add_comm 1 n]
    rw [he] at ht
    have h := Timed.step (by simp [machine,Rewind.machine,rewinding,config])
      (rewind_step p target heads tapes n z) ht
    simpa only [Nat.add_assoc,Nat.add_comm 1 z] using h

theorem recording_timed {t s space n : ℕ} {p : Machine t s} {c d : Configuration t s}
    (hp : Prefix p space n c d) (target : Fin t) (forward : NoLeft p target) (count : ℕ) :
    ∃ delta,delta≤n ∧ d.heads target=c.heads target+delta ∧
      Timed (machine p target) n (recording c count) (recording d (count+delta)) := by
  induction hp generalizing count with
  | refl c _ => exact ⟨0,by omega,by omega,by simpa using Timed.refl (machine p target) (recording c count)⟩
  | @step n c d e _ hn hs _ ih =>
    obtain ⟨first,hfirst,hd,hstep⟩ := record_step p target forward c d count hn hs
    obtain ⟨rest,hrest,he,ht⟩ := ih (count+first)
    refine ⟨first+rest,by omega,by omega,?_⟩
    have h := Timed.step (by simp [machine,Rewind.machine,recording,config]) hstep ht
    simpa only [Nat.add_assoc] using h

theorem restore_run {t s : ℕ} (p : Machine t s) (target : Fin t) (forward : NoLeft p target)
    (fuel : ℕ) (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c=some source) :
    ∃ r delta,runFrom (machine p target) (2*source.steps+2) (recording c 0)=some r ∧
      delta ≤ source.steps ∧ r.steps=source.steps+delta+2 ∧
      r.final=finished (s := s) (fun i => if i=target then c.heads i else source.final.heads i)
        source.final.tapes delta := by
  obtain ⟨hp,hh⟩ := prefix_of_run p fuel c source hr
  obtain ⟨delta,hdelta,hhead,ht⟩ := recording_timed hp target forward 0
  simp only [Nat.zero_add] at ht
  have he : (fun i => if i=target then source.final.heads i-delta else source.final.heads i)=
      fun i => if i=target then c.heads i else source.final.heads i := by
    funext i; by_cases h : i=target
    · subst i; simp [hhead]
    · simp [h]
  have reset := rewind_timed p target source.final.heads source.final.tapes delta 0
  rw [he] at reset
  simp only [Nat.add_zero] at reset
  have bridge := Timed.step (by simp [machine,Rewind.machine,recording,config])
    (bridge_step p target source.final delta hh) reset
  obtain ⟨r,hrun,hf,hs⟩ := (ht.trans bridge).run (by simp [machine,Rewind.machine,finished,config])
  have hmore := runFrom_moreFuel (machine p target) _ (source.steps-delta) _ r hrun
  have htime : source.steps+(delta+1+1)+(source.steps-delta)=2*source.steps+2 := by omega
  rw [htime] at hmore
  exact ⟨r,delta,hmore,hdelta,by omega,hf⟩

end NearCubicWires.RepairSource.ProjectionNormalization.CursorRestore
