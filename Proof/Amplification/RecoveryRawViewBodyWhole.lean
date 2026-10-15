import Proof.Amplification.RecoveryRawViewBodyOuter

/-! Complete actual raw-view clause body, including the initial false bit,
all executed gates, counter reuse and clause validation. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bodyOutput (x : State) (word : List Bool) (k : Nat) := outerOutput (flagged x false) word k

theorem answer_eq_outer (x : State) (word : List Bool) (k : Nat) :
    answer x word k=outerAnswer (flagged x false) word k := by
  unfold answer outerAnswer
  change (if RadixSemantics.value x.outer.bits=0 then false else _)=
    (if RadixSemantics.value x.outer.bits=0 then false else _)
  by_cases hz : RadixSemantics.value x.outer.bits=0
  · rw [if_pos hz,if_pos hz]
  · rw [if_neg hz,if_neg hz]
    unfold countAnswer
    change (match readCount x.limit (word.drop k) with
      | none=>false | some (n,_)=>clauseAnswer (prepared x n))=
      (readCount x.limit (word.drop k)).any (fun pair=>clauseAnswer (prepared x pair.1))
    cases h : readCount x.limit (word.drop k) <;> rfl

theorem body_trace (x : State) (word : List Bool) (k : Nat)
    (hx : x.Valid) (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    ∃ n e,n ≤ budget x ∧ Timed machine n (x.cfg machine.start)
      (RecoveryCalls.stopped sizes e.heads e.tapes) ∧ Result (answer x word k) (bodyOutput x word k) e := by
  obtain ⟨first,hr,he,_⟩ := RecoveryRawView.flag_run x false
  have htrace := call_receipt sizes programs 0 next 0 1 1 _ first hr (by rfl)
  obtain ⟨n0,hn0,h0⟩ := htrace
  have htail := outer_trace (flagged x false) word k (flagged_valid x false hx) hs hp rfl
  obtain ⟨n1,e,hn1,h1,hresult⟩ := htail
  rw [he] at h0
  have h := h0.trans h1
  refine ⟨n0+n1,e,?_,h,?_⟩
  · change n1 ≤ outerBudget x at hn1
    unfold budget
    omega
  · rw [answer_eq_outer]
    exact hresult

theorem body_run (x : State) (word : List Bool) (k : Nat)
    (hx : x.Valid) (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    ∃ r,runFrom machine (budget x) (x.cfg machine.start)=some r ∧
      r.steps ≤ budget x ∧ r.final.heads 28=0 ∧ r.final.tapes 28=[answer x word k] ∧
      (answer x word k=true → r.final=(bodyOutput x word k).cfg r.final.control) := by
  obtain ⟨n,e,hn,h,hh,ht,hf⟩ := body_trace x word k hx hs hp
  obtain ⟨r,hr,he,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel machine n (budget x-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hsteps.le.trans hn,?_,?_,?_⟩
  · rw [he]
    exact hh
  · rw [he]
    exact ht
  · intro ha
    apply configuration_ext
    · rfl
    · rw [he]
      change e.heads=_
      rw [hf ha]
      rfl
    · rw [he]
      change e.tapes=_
      rw [hf ha]
      rfl

end NearCubicWires.RepairOrdinary.RecoveryRawViewBody
