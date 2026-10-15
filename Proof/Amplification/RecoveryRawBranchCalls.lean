import Proof.Amplification.RecoveryRawBranchState

/-! The actual raw frontend retains the independent SAT bank. On success
its produced count remains at head1 and directly drives the existing
raw-SAT replay through the fixed shared-tape wiring. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def output (x : State) (word : List Bool) (k : Nat) : State := ⟨(RecoveryRawViewEntry.output x.view word k).1,x.eval⟩
def total (x : State) (word : List Bool) (k : Nat) := (RecoveryRawViewEntry.output x.view word k).2

theorem view_run (x : State) (word : List Bool) (k : Nat) (hx : x.view.Valid)
    (hs : x.view.inner.stream.source=frame word) (hp : x.view.inner.stream.pos=2*k) :
    ∃ r,runFrom viewMachine (RecoveryRawViewEntry.budget x.view) (cfg x 0 viewMachine.start)=some r ∧
      r.steps ≤ 536870912*(x.view.width+1)^4 ∧
      r.final.heads 28=0 ∧ r.final.tapes 28=[RecoveryRawViewEntry.answer x.view word k] ∧
      r.final.heads 93=0 ∧ r.final.tapes 93=[x.eval.clause.result] ∧
      (RecoveryRawViewEntry.answer x.view word k=true →
        r.final=cfg (output x word k) (total x word k) r.final.control) := by
  obtain ⟨base,hr,hb,hh,ht,hout⟩ := RecoveryRawViewEntry.entry_run x.view word k hx hs hp
  obtain ⟨r,hrun,hsteps,hf⟩ := RecoveryBankPair.left_run RecoveryRawViewEntry.machine (RecoveryRawViewEntry.budget x.view)
    (RecoveryRawViewEnd.cfg x.view 0 RecoveryRawViewEntry.machine.start) base hr (fun _ : Fin 70=>0) x.eval.tapes
  refine ⟨r,hrun,(hsteps.le.trans hb).trans (RecoveryRawViewEntry.budget_bound x.view hx),?_,?_,?_,?_,?_⟩
  · rw [hf]; exact hh
  · rw [hf]; exact ht
  · rw [hf]; rfl
  · rw [hf]; rfl
  · intro ha
    rw [hf,hout ha]
    rfl

theorem eval_run (x : State) (width cap n : Nat) (word : List Bool)
    (hx : RecoveryRawSAT.Inv width cap 0 0 word x.eval) (hn : n ≤ 3*(width+1)) :
    ∃ r,runFrom evalMachine (RecoveryRawSATTable.budget width n) (cfg x n evalMachine.start)=some r ∧
      r.steps ≤ 67108864*(width+1)^3 ∧ r.final.heads 93=0 ∧
      r.final.tapes 93=[RecoveryRawSATTable.answer width cap 0 0 n word x.eval.code] := by
  obtain ⟨base,hr,hb,hh,ht⟩ := RecoveryRawSATTable.table_run width cap 0 0 n word x.eval hx
  obtain ⟨r,hrun,hf,hs⟩ := RecoveryFocus.run_config evalSlots eval_injective RecoveryRawSATTable.machine
    (cfg x n evalMachine.start).heads (cfg x n evalMachine.start).tapes _ _ base hr
  have hi : RecoveryFocus.config evalSlots (cfg x n evalMachine.start).heads (cfg x n evalMachine.start).tapes
      (RecoveryRawSATEnd.cfg x.eval.tapes n RecoveryRawSATTable.machine.start)=cfg x n evalMachine.start :=
    eval_config x n evalMachine.start
  rw [hi] at hrun
  refine ⟨r,hrun,(hs.le.trans hb).trans (RecoveryRawSATTable.budget_bound width n hn),?_,?_⟩
  · rw [hf]
    change (RecoveryFocus.config evalSlots (cfg x n evalMachine.start).heads (cfg x n evalMachine.start).tapes
      base.final).heads (evalSlots 27)=0
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot evalSlots eval_injective]
    exact hh
  · rw [hf]
    change (RecoveryFocus.config evalSlots (cfg x n evalMachine.start).heads (cfg x n evalMachine.start).tapes
      base.final).tapes (evalSlots 27)=_
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot evalSlots eval_injective]
    exact ht

end NearCubicWires.RepairOrdinary.RecoveryRawBranch
