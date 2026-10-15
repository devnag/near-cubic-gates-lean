import Proof.Amplification.RecoveryRawViewBodyState

/-! The final two actual calls of the raw-view body: copy the extracted
clause word, execute its bounded checker, and pay both call returns. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Result (answer : Bool) (target : State) (e : Configuration 65 1) : Prop :=
  e.heads 28=0 ∧ e.tapes 28=[answer] ∧ (answer=true → e=target.cfg 0)

theorem clause_trace (x : State) (hx : x.Valid) :
    ∃ n e,n ≤ clauseBudget x.width x.limit+1 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 5) (x.cfg clauseMachine.start))
        (RecoveryCalls.stopped sizes e.heads e.tapes) ∧ Result (clauseAnswer x) (finished x) e := by
  have hrun := RecoveryRawView.clause_run x hx
  obtain ⟨r,hr,_,hh,ht,hf⟩ := hrun
  have htrace := stop_receipt sizes programs 0 next 5 (RecoveryRawClause.budget x.width x.count) _ r hr (by rfl)
  obtain ⟨n,hn,h⟩ := htrace
  refine ⟨n,⟨0,r.final.heads,r.final.tapes⟩,?_,h,hh,ht,?_⟩
  · exact hn.trans (Nat.add_le_add_right (clause_budget_mono x.width x.count x.limit hx.2.2.2.1) 1)
  · intro ha
    apply configuration_ext
    · rfl
    · change r.final.heads=_
      rw [hf ha]; rfl
    · change r.final.tapes=_
      rw [hf ha]; rfl

theorem copy_trace (x : State) (bits : List Bool) (hx : x.Valid)
    (hw : bits.length=x.width) (hf : x.outer.fields 0=frame bits) :
    ∃ n e,n ≤ copyBudget x.width x.limit ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 4) (x.cfg RecoveryRawView.copyMachine.start))
        (RecoveryCalls.stopped sizes e.heads e.tapes) ∧
      Result (clauseAnswer (copied x bits)) (finished (copied x bits)) e := by
  obtain ⟨first,hr,hout,_⟩ := RecoveryRawView.copy_run x bits hw hf
  have htrace := call_receipt sizes programs 0 next 4 5 (8*bits.length+8) _ first hr (by rfl)
  obtain ⟨n0,hn0,h0⟩ := htrace
  have htail := clause_trace (copied x bits) (copied_valid x bits hx hw)
  obtain ⟨n1,e,hn1,h1,he⟩ := htail
  rw [hout] at h0
  have h := h0.trans h1
  refine ⟨n0+n1,e,?_,h,he⟩
  rw [copied_width x bits hw] at hn1
  change n1 ≤ clauseBudget x.width x.limit+1 at hn1
  rw [hw] at hn0
  unfold copyBudget
  omega

end NearCubicWires.RepairOrdinary.RecoveryRawViewBody
