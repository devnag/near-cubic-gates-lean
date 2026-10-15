import Proof.Amplification.RecoveryRawViewEntryGraph

/-! The entry's produced outer counter drives the accepted whole view
machine; its literal result and complete successful endpoint are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Result (bit : Bool) (target : State×Nat) (e : Configuration 66 1) : Prop :=
  e.heads 28=0 ∧ e.tapes 28=[bit] ∧ (bit=true → e=RecoveryRawViewEnd.cfg target.1 target.2 0)

theorem view_trace (x : State) (word : List Bool) (k total : Nat) (hx : x.Valid)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) (hn : total ≤ x.limit) :
    ∃ n e,n ≤ viewBudget x.width+1 ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 2)
        (RecoveryRawViewEnd.cfg (advanced x total) total RecoveryRawViewWhole.machine.start))
      (RecoveryCalls.stopped sizes e.heads e.tapes) ∧
      Result (RecoveryRawViewWhole.answer word total (cursor x k total))
        (RecoveryRawViewEnd.tested (RecoveryRawViewLoop.out word total (cursor x k total)).2.data,total) e := by
  have hrun := RecoveryRawViewWhole.view_run x.width total word (cursor x k total) (cursor_valid x word k total hx hs hp)
  obtain ⟨r,hr,_,hh,ht,hf⟩ := hrun
  have htrace := stop_receipt sizes programs 0 next 2 (RecoveryRawViewWhole.budget x.width total) _ r hr (by rfl)
  obtain ⟨n,hcost,h⟩ := htrace
  have hb := RecoveryRawViewWhole.budget_bound x.width total (hn.trans hx.2.2.2.2)
  refine ⟨n,⟨0,r.final.heads,r.final.tapes⟩,by exact hcost.trans (Nat.add_le_add_right hb 1),h,hh,ht,?_⟩
  intro ha
  apply configuration_ext
  · rfl
  · change r.final.heads=_
    rw [hf ha]; rfl
  · change r.final.tapes=_
    rw [hf ha]; rfl

end NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
