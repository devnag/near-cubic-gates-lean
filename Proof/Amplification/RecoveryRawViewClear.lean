import Proof.Amplification.RecoveryRawViewErase

/-! Complete counter reuse: pay the move from sentinel head1 to zero,
execute the bounded sweep/reset, then physically restore sentinel head1. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clear_front_run (x : State) (hx : x.Valid) :
    ∃ r,runFrom clearFront (2*x.capacity+6) (x.cfg clearFront.start)=some r ∧
      r.final.heads=counterHeads (cleared x) (0 : Fin 1) ∧
      r.final.tapes=((cleared x).cfg (0 : Fin 1)).tapes ∧ r.steps=2*x.capacity+6 := by
  obtain ⟨first,hr0,hf0,hs0⟩ := move_run .left (x.cfg (0 : Fin 2)).heads (x.cfg (0 : Fin 2)).tapes
  have hf0' : first.final=⟨1,counterHeads x (0 : Fin 2),(x.cfg (0 : Fin 2)).tapes⟩ := by
    rw [hf0]
    rfl
  obtain ⟨last,hr1,hf1,hs1⟩ := erase_run x hx
  have hi : Composition.restart first.final eraseMachine.start=
      ⟨eraseMachine.start,counterHeads x eraseMachine.start,(x.cfg eraseMachine.start).tapes⟩ := by
    rw [hf0']; rfl
  rw [←hi] at hr1
  have h := Composition.run_join (moveCounter .left) eraseMachine 1 (2*x.capacity+4) _ first last hr0 hr1
  have he : 1+1+(2*x.capacity+4)=2*x.capacity+6 := by omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt first last,h,?_,?_,?_⟩
  · change last.final.heads=_
    rw [hf1]; rfl
  · change last.final.tapes=_
    rw [hf1]; rfl
  · change first.steps+1+last.steps=_
    rw [hs0,hs1]
    omega

theorem clear_run (x : State) (hx : x.Valid) :
    ∃ r,runFrom clearMachine (clearCost x) (x.cfg clearMachine.start)=some r ∧
      r.final=(cleared x).cfg r.final.control ∧ r.steps=clearCost x := by
  obtain ⟨first,hr0,hh0,ht0,hs0⟩ := clear_front_run x hx
  obtain ⟨last,hr1,hf1,hs1⟩ := move_run .right first.final.heads first.final.tapes
  have h := Composition.run_join clearFront (moveCounter .right) (2*x.capacity+6) 1 _ first last hr0 hr1
  have he : (2*x.capacity+6)+1+1=clearCost x := by unfold clearCost; omega
  rw [he] at h
  have hh : Function.update first.final.heads 35 (HeadMove.right.apply (first.final.heads 35))=
      ((cleared x).cfg (0 : Fin 1)).heads := by
    rw [hh0]
    change Function.update (Function.update ((cleared x).cfg (0 : Fin 1)).heads 35 0) 35 1=_
    exact counter_restore _ rfl
  refine ⟨Composition.joinedReceipt first last,h,?_,?_⟩
  · apply configuration_ext
    · rfl
    · change last.final.heads=_
      rw [hf1,hh]
      rfl
    · change last.final.tapes=_
      rw [hf1,ht0]
      rfl
  · change first.steps+1+last.steps=_
    rw [hs0,hs1]
    exact he

end NearCubicWires.RepairOrdinary.RecoveryRawView
