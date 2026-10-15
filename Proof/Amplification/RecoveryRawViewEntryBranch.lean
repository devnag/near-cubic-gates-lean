import Proof.Amplification.RecoveryRawViewEntryTail

/-! The outer-count result gates the whole view machine. Rejected counts
stop with the retained false flag; successful counts provide the exact
runtime loop driver, cursor and cap inequality. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem count_trace (x : State) (word : List Bool) (k : Nat) (hx : x.Valid)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k)
    (hfalse : x.inner.stream.data.present=false) :
    ∃ n e,n ≤ countBudget x ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 1) (RecoveryRawViewEnd.cfg x 0 countMachine.start))
      (RecoveryCalls.stopped sizes e.heads e.tapes) ∧ Result (countAnswer x word k) (countOutput x word k) e := by
  have hrun := count_run x word k hs hp
  obtain ⟨first,hr,_,hc,hh,ht,hout⟩ := hrun
  cases hparse : readCount x.limit (word.drop k) with
  | none=>
    have hne : first.final.control≠3 := by
      intro he
      have hh := hc.mp he
      simp only [hparse,Option.isSome_none,Bool.false_eq_true] at hh
    have hn : next 1 first.final.control first.final.scanned=none := by
      change (if first.final.control.val=3 then some (2 : Fin 3) else none)=none
      apply if_neg
      intro he
      exact hne (Fin.ext he)
    have htrace := stop_receipt sizes programs 0 next 1 (3*x.limit+3) _ first hr hn
    obtain ⟨n,hn,h⟩ := htrace
    refine ⟨n,⟨0,first.final.heads,first.final.tapes⟩,?_,h,hh,?_,?_⟩
    · unfold countBudget
      omega
    · change first.final.tapes 28=_
      rw [ht,hfalse]
      simp only [countAnswer,hparse,Option.any_none]
    · simp only [countAnswer,hparse,Option.any_none,Bool.false_eq_true,IsEmpty.forall_iff]
  | some pair=>
    rcases pair with ⟨total,rest⟩
    obtain ⟨htotal,he⟩ := hout total rest hparse
    have hn : next 1 first.final.control first.final.scanned=some 2 := by
      change (if first.final.control.val=3 then some (2 : Fin 3) else none)=some 2
      rw [he]
      rfl
    have htrace := call_receipt sizes programs 0 next 1 2 (3*x.limit+3) _ first hr hn
    obtain ⟨n0,hn0,h0⟩ := htrace
    have htail := view_trace x word k total hx hs hp htotal
    obtain ⟨n1,e,hn1,h1,hresult⟩ := htail
    rw [he] at h0
    have h := h0.trans h1
    refine ⟨n0+n1,e,?_,h,?_⟩
    · unfold countBudget
      omega
    · simpa only [countAnswer,countOutput,hparse,Option.any_some] using hresult

end NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
