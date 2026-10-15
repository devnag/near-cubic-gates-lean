import Proof.MachineModel.OrdinaryTransitionWalkInitialConsumer

/-! The only final event-stream write: after emission succeeds, physically
append its false delimiter at the retained append cursor. The caller wraps
the entire emission plus this step in one output-only recorded reset. -/
namespace NearCubicWires.RepairOrdinary.UMemoryClose
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def delimiter {t : ℕ} (event flag : Fin t) : Machine t 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q bits => if q.val=0 then some
    ⟨1,fun i => if bits flag && decide (i=event) then some false else none,fun _ => .stay⟩ else none

def delimited {t s : ℕ} (event flag : Fin t) (c : Configuration t s) : Configuration t 2 :=
  ⟨1,c.heads,fun i => if c.scanned flag && decide (i=event)
    then writeTapeBit (c.tapes i) (c.heads i) false else c.tapes i⟩

theorem delimiter_step {t s : ℕ} (event flag : Fin t) (c : Configuration t s) :
    step (delimiter event flag) (Composition.restart c 0) = some (delimited event flag c) := by
  simp only [step,delimiter,Composition.restart,Fin.val_zero,↓reduceIte,Option.map_some]
  congr 1
  apply configuration_ext
  · rfl
  · funext i
    simp only [applyAction,HeadMove.apply,delimited]
  · funext i
    simp only [applyAction,delimited,Configuration.scanned]
    split_ifs <;> rfl

theorem delimiter_run {t s : ℕ} (event flag : Fin t) (c : Configuration t s) :
    ∃ r,runFrom (delimiter event flag) 1 (Composition.restart c 0)=some r ∧
      r.final=delimited event flag c ∧ r.steps=1 := by
  exact (Timed.step (by rfl) (delimiter_step event flag c)
    (Timed.refl (delimiter event flag) (delimited event flag c))).run (by rfl)

theorem delimited_other {t s : ℕ} (event flag i : Fin t) (c : Configuration t s)
    (hi : i ≠ event) : (delimited event flag c).tapes i=c.tapes i := by
  simp only [delimited,hi,decide_false,Bool.and_false,Bool.false_eq_true,↓reduceIte]

theorem delimited_flag {t s : ℕ} (event flag : Fin t) (c : Configuration t s)
    (hne : event ≠ flag) : (delimited event flag c).scanned flag=c.scanned flag := by
  unfold Configuration.scanned
  rw [delimited_other event flag flag c (Ne.symm hne)]
  rfl

theorem delimited_event {t s : ℕ} (event flag : Fin t) (c : Configuration t s)
    (hflag : c.scanned flag=true) (hpos : c.heads event=(c.tapes event).length) :
    (delimited event flag c).tapes event=c.tapes event++[false] := by
  simp only [delimited,hflag,decide_true,Bool.and_self,↓reduceIte,hpos]
  exact Streaming.write_append (c.tapes event) false

def emissionPrefix {t s : ℕ} (p : Machine t s) (event flag : Fin t) : Machine t (s+2) :=
  Composition.machine p (delimiter event flag)

theorem emission_prefix_run {t s : ℕ} (p : Machine t s) (event flag : Fin t)
    (fuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom p fuel c=some r) :
    ∃ result,runFrom (emissionPrefix p event flag) (fuel+2) (Composition.leftConfig 2 c)=some result ∧
      result.final=Composition.rightConfig s (delimited event flag r.final) ∧ result.steps=r.steps+2 := by
  obtain ⟨tail,ht,hf,hs⟩ := delimiter_run event flag r.final
  have hjoin := Composition.run_join p (delimiter event flag) fuel 1 c r tail hr ht
  refine ⟨Composition.joinedReceipt r tail,?_,?_,?_⟩
  · exact hjoin
  · change Composition.rightConfig s tail.final=_
    rw [hf]
  · change r.steps+1+tail.steps=r.steps+2
    omega

end NearCubicWires.RepairOrdinary.UMemoryClose
