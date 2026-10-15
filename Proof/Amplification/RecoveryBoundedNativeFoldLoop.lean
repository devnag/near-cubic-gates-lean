import Proof.Amplification.RecoveryBoundedNativeFoldRun
import Proof.Amplification.RecoveryBoundedNativeFoldMeaning

/-! The retained physical limit drives the original reverse reference fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFoldLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution RepairSource.VerifierDecoding
open RecoveryBoundedNativeFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  acc : ℕ
  offset : ℕ
  erased : ℕ
  out : List Bool
def State.next (conjunction : Bool) (ref : ℕ) (a : State) : State :=
  ⟨a.acc+1,a.offset+1,2*ref+1+a.erased,a.out++emitted conjunction ref a.acc⟩
def State.iterate (conjunction : Bool) : List ℕ→State→State
  | [],a=>a
  | ref::refs,a=>State.iterate conjunction refs (a.next conjunction ref)
def stack (pre : List Bool) (refs : List ℕ) := pre++RecoveryBoundedNativeUnaryLoop.stackWords refs.reverse
noncomputable def State.entry (conjunction : Bool) (C : ℕ) (flag : Bool)
    (pre : List Bool) (refs : List ℕ) (a : State) :=
  RecoveryBoundedNativeFold.entry conjunction a.acc C (stack pre refs).length flag a.out
    (stack pre refs++List.replicate a.erased false)
noncomputable def machine (conjunction : Bool):=RepeatMachine.machine (RecoveryBoundedNativeFold.machine conjunction) (fun _ _=>true)
noncomputable def configuration (phase : Fin 5) (conjunction : Bool) (C : ℕ) (flag : Bool)
    (pre : List Bool) (refs : List ℕ) (a : State) (total driver : ℕ) :=
  RepeatMachine.cfg phase (a.entry conjunction C flag pre refs) total driver

theorem stack_cons (pre : List Bool) (ref : ℕ) (refs : List ℕ) :
    stack pre (ref::refs)=stack pre refs++(frame (List.replicate ref true)).reverse := by
  simp [stack,RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_append,List.append_assoc]

theorem stack_cons_length (pre : List Bool) (ref : ℕ) (refs : List ℕ) :
    (stack pre (ref::refs)).length=(stack pre refs).length+2*ref+1 := by
  rw [stack_cons]
  simp [frame_length,Nat.add_assoc]

private theorem cfg_data {t s : ℕ} (phase : Fin 5) (c d : Configuration t s) (total driver : ℕ)
    (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem loop_run (conjunction : Bool) (W C total : ℕ) (flag : Bool)
    (pre : List Bool) (refs : List ℕ) (a : State)
    (htotal : a.offset+refs.length=total) (href : ∀ r∈refs,r ≤ W)
    (ha : a.acc+refs.length ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom (machine conjunction) (refs.length*(24*C+66)+total+3)
      (configuration 0 conjunction C flag pre refs a total (a.offset+1))=some r ∧
      r.final=configuration 3 conjunction C flag pre [] (a.iterate conjunction refs) total 1 ∧
      r.steps ≤ refs.length*(24*C+66)+total+3 := by
  induction refs generalizing a with
  | nil=>
    have hoff : a.offset=total := by simpa using htotal
    obtain ⟨r,hr,rf,rs⟩:=(RepeatMachine.exhaust (RecoveryBoundedNativeFold.machine conjunction) (fun _ _=>true)
      (a.entry conjunction C flag pre []) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,rf,?_⟩
    · simpa only [machine,configuration,hoff,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using rs.le
  | cons ref refs ih=>
    obtain ⟨first,hfirst,fs,fh,ft⟩:=RecoveryBoundedNativeFold.bounded_run conjunction ref a.acc W C a.erased flag
      a.out (stack pre refs) (href ref (by simp)) (by simp only [List.length_cons] at ha; omega) hC
    have hi : RecoveryBoundedNativeFold.entry conjunction a.acc C ((stack pre refs).length+2*ref+1) flag a.out
        (stack pre refs++(frame (List.replicate ref true)).reverse++List.replicate a.erased false)=
        a.entry conjunction C flag pre (ref::refs) := by
      unfold State.entry
      rw [stack_cons_length,stack_cons]
    rw [hi] at hfirst
    have hiteration:=RepeatMachine.iteration (RecoveryBoundedNativeFold.machine conjunction) (fun _ _=>true)
      (a.entry conjunction C flag pre (ref::refs)) total a.offset first rfl
      (by simp only [List.length_cons] at htotal; omega) hfirst
    change Timed (machine conjunction) (first.steps+2)
      (configuration 0 conjunction C flag pre (ref::refs) a total (a.offset+1))
      (RepeatMachine.cfg 0 first.final total (a.offset+2)) at hiteration
    rw [cfg_data 0 first.final ((a.next conjunction ref).entry conjunction C flag pre refs)
      total (a.offset+2) fh ft] at hiteration
    obtain ⟨last,hl,lf,ls⟩:=ih (a.next conjunction ref)
      (by simp only [State.next,List.length_cons] at *; omega)
      (by intro r hr; exact href r (by simp [hr]))
      (by simp only [State.next,List.length_cons] at *; omega)
    rcases hiteration with ⟨space,hprefix⟩
    obtain ⟨r,hr,rf,rs,_⟩:=hprefix.followedBy last hl
    have hbudget : first.steps+2+(refs.length*(24*C+66)+total+3) ≤
        (ref::refs).length*(24*C+66)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel (machine conjunction) _
      ((ref::refs).length*(24*C+66)+total+3-(first.steps+2+(refs.length*(24*C+66)+total+3))) _ r hr
    rw [Nat.add_sub_of_le hbudget] at more
    refine ⟨r,more,rf.trans lf,?_⟩
    rw [rs]
    omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFoldLoop
