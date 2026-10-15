import Proof.Amplification.RecoveryRawViewEntryBranch

/-! Whole raw-view entry with the outer counter produced from the retained
witness, including malformed counts, loop execution and exact final answer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_trace (x : State) (word : List Bool) (k : Nat) (hx : x.Valid)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    ∃ n e,n ≤ budget x ∧ Timed machine n (RecoveryRawViewEnd.cfg x 0 machine.start)
      (RecoveryCalls.stopped sizes e.heads e.tapes) ∧ Result (answer x word k) (output x word k) e := by
  obtain ⟨first,hr,he,_⟩ := flag_run x
  have htrace := call_receipt sizes programs 0 next 0 1 1 _ first hr (by rfl)
  obtain ⟨n0,hn0,h0⟩ := htrace
  have htail := count_trace (flagged x false) word k (flagged_valid x false hx) hs hp rfl
  obtain ⟨n1,e,hn1,h1,hresult⟩ := htail
  rw [he] at h0
  have h := h0.trans h1
  refine ⟨n0+n1,e,?_,h,hresult⟩
  change n1 ≤ countBudget x at hn1
  unfold budget
  omega

theorem entry_run (x : State) (word : List Bool) (k : Nat) (hx : x.Valid)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    ∃ r,runFrom machine (budget x) (RecoveryRawViewEnd.cfg x 0 machine.start)=some r ∧
      r.steps ≤ budget x ∧ r.final.heads 28=0 ∧ r.final.tapes 28=[answer x word k] ∧
      (answer x word k=true →
        r.final=RecoveryRawViewEnd.cfg (output x word k).1 (output x word k).2 r.final.control) := by
  obtain ⟨n,e,hn,h,hh,ht,hf⟩ := entry_trace x word k hx hs hp
  obtain ⟨r,hr,he,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel machine n (budget x-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hsteps.le.trans hn,?_,?_,?_⟩
  · rw [he]; exact hh
  · rw [he]; exact ht
  · intro ha
    apply configuration_ext
    · rfl
    · rw [he]
      change e.heads=_
      rw [hf ha]; rfl
    · rw [he]
      change e.tapes=_
      rw [hf ha]; rfl

theorem budget_bound (x : State) (hx : x.Valid) : budget x ≤ 536870912*(x.width+1)^4 := by
  have hlinear : x.width+1 ≤ (x.width+1)^4 := by
    nlinarith [Nat.zero_le (x.width^4),Nat.zero_le (x.width^3),sq_nonneg (x.width : Nat)]
  have hlimit := hx.2.2.2.2
  unfold budget countBudget viewBudget
  nlinarith [show 0<(x.width+1)^4 by positivity]

end NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
