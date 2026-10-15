import Proof.Amplification.RecoveryRawViewClear

/-! The whole verified clause executes on the left bank while retaining
the outer formula tail and the reusable count-cap tape. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def finished (x : State) : State :=
  let inner := RecoveryRawClause.inverted (RecoveryRawLiteralBound.output (RecoveryRawClause.out x.count x.inner).2)
  {x with inner:=inner}
def clauseAnswer (x : State) := RecoveryRawClause.answer x.count x.inner

theorem finished_width (x : State) : (finished x).width=x.width :=
  (RecoveryRawClause.final_stable x.count x.inner).2.1

theorem finished_capacity (x : State) : (finished x).capacity=x.capacity := by
  change 8192*((finished x).width+1)^2=8192*(x.width+1)^2
  rw [finished_width]

theorem finished_valid (x : State) (hx : x.Valid) : (finished x).Valid := by
  have hi := RecoveryRawClause.out_inv x.width x.count x.inner ⟨hx.1,rfl⟩
  have hv := RecoveryRawClause.inverted_valid _ (RecoveryRawLiteralBound.output_valid _ hi.1)
  exact ⟨hv,hx.2.1,hx.2.2.1.trans (finished_width x).symm,hx.2.2.2.1,
    by rw [finished_width]; exact hx.2.2.2.2⟩

theorem finished_cfg {s : Nat} (x : State) (q : Fin s) :
    TapeEmbedding.config State.extraHeads x.extra
      (RecoveryRawClause.paddedCfg x.capacity (finished x).inner x.count q)=(finished x).cfg q := by
  unfold State.cfg
  rw [inner_cfg_padded,finished_capacity]
  rfl

theorem clause_run (x : State) (hx : x.Valid) :
    ∃ r,runFrom clauseMachine (RecoveryRawClause.budget x.width x.count) (x.cfg clauseMachine.start)=some r ∧
      r.steps ≤ RecoveryRawClause.budget x.width x.count ∧
      r.final.heads 28=0 ∧ r.final.tapes 28=[clauseAnswer x] ∧
      (clauseAnswer x=true → r.final=(finished x).cfg r.final.control) := by
  have hrun := RecoveryRawClause.padded_clause_run x.width x.count x.capacity x.inner ⟨hx.1,rfl⟩
  obtain ⟨base,hr,hb,hh,ht,hf⟩ := hrun
  have h := TapeEmbedding.run_embed RecoveryRawClause.machine State.extraHeads x.extra
    (RecoveryRawClause.budget x.width x.count) _ base hr
  have hi : TapeEmbedding.config State.extraHeads x.extra
      (RecoveryRawClause.paddedCfg x.capacity x.inner x.count RecoveryRawClause.machine.start)=x.cfg clauseMachine.start := by
    unfold State.cfg
    rw [inner_cfg_padded]
    rfl
  rw [hi] at h
  refine ⟨TapeEmbedding.receipt State.extraHeads x.extra base,h,hb,hh,ht,?_⟩
  intro ha
  change TapeEmbedding.config State.extraHeads x.extra base.final=_
  rw [hf ha]
  exact finished_cfg x _

end NearCubicWires.RepairOrdinary.RecoveryRawView
