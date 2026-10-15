import Proof.Amplification.RecoveryRawBranchFront

/-! Whole prepared raw/default checker. The syntax frontend's failure
requires no reset: its retained result cell is physically set false. On
success the actual tag and index gates lead to the default or SAT run. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem combined_budget (x : State) (n0 n1 : Nat) (hx : x.view.Valid)
    (h0 : n0 ≤ RecoveryRawViewEntry.budget x.view+1)
    (h1 : n1 ≤ tailBudget x.view.width) : n0+n1 ≤ budget x.view.width := by
  have hb := RecoveryRawViewEntry.budget_bound x.view hx
  have hp : (x.view.width+1)^3 ≤ (x.view.width+1)^4 := by
    calc
      _ = 1*(x.view.width+1)^3 := by omega
      _ ≤ (x.view.width+1)*(x.view.width+1)^3 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hpos : 1 ≤ (x.view.width+1)^4 := Nat.one_le_pow _ _ (by omega)
  unfold tailBudget at h1
  unfold budget
  omega

theorem raw_trace (x : State) (word : List Bool) (k : Nat) (hx : x.view.Valid)
    (hs : x.view.inner.stream.source=frame word) (hp : x.view.inner.stream.pos=2*k)
    (heval : RecoveryRawSAT.Inv x.view.width x.eval.valuation.cap 0 0 word x.eval) :
    ∃ n,∃ outHeads : Fin 136→Nat,∃ outTapes : Fin 136→List Bool,n ≤ budget x.view.width ∧
      Timed machine n (cfg x 0 machine.start) (RecoveryCalls.stopped sizes outHeads outTapes) ∧
      outHeads 93=0 ∧ outTapes 93=[answer x word k] := by
  obtain ⟨first,hr,_,hh28,ht28,hh93,ht93,hf⟩ := view_run x word k hx hs hp
  cases ha : RecoveryRawViewEntry.answer x.view word k
  · have hv : first.final.scanned 28=false := by
      change readTapeBit (first.final.tapes 28) (first.final.heads 28)=false
      rw [hh28,ht28,ha]
      rfl
    have hn : next 0 first.final.control first.final.scanned=some 3 := by
      simp only [next,hv,Bool.false_eq_true,ite_false]
      rfl
    obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next 0 3 (RecoveryRawViewEntry.budget x.view)
      (cfg x 0 viewMachine.start) first hr hn
    obtain ⟨n1,outHeads,outTapes,hn1,h1,hh,ht⟩ := reject_trace first.final.heads first.final.tapes
      x.eval.clause.result hh93 ht93
    refine ⟨n0+n1,outHeads,outTapes,combined_budget x n0 n1 hx hn0 (by unfold tailBudget; omega),h0.trans h1,hh,?_⟩
    simp only [answer,ha,Bool.false_and]
    exact ht
  · have hv : first.final.scanned 28=true := by
      change readTapeBit (first.final.tapes 28) (first.final.heads 28)=true
      rw [hh28,ht28,ha]
      rfl
    have hv' : (output x word k).view.inner.stream.data.present=true := by
      have ht := ht28
      rw [hf ha,ha] at ht
      change [(output x word k).view.inner.stream.data.present]=[true] at ht
      exact List.singleton_inj.mp ht
    obtain ⟨n0,hn0,h0⟩ := checked_front x word k first hr (hf ha) hv
    obtain ⟨n1,outHeads,outTapes,hn1,h1,hh,ht⟩ := checked_trace x word k hx heval ha hv'
    exact ⟨n0+n1,outHeads,outTapes,combined_budget x n0 n1 hx hn0 hn1,h0.trans h1,hh,ht⟩

theorem raw_run (x : State) (word : List Bool) (k : Nat) (hx : x.view.Valid)
    (hs : x.view.inner.stream.source=frame word) (hp : x.view.inner.stream.pos=2*k)
    (heval : RecoveryRawSAT.Inv x.view.width x.eval.valuation.cap 0 0 word x.eval) :
    ∃ r,runFrom machine (budget x.view.width) (cfg x 0 machine.start)=some r ∧
      r.steps ≤ 1073741824*(x.view.width+1)^4 ∧ r.final.heads 93=0 ∧
      r.final.tapes 93=[answer x word k] := by
  obtain ⟨n,outHeads,outTapes,hn,h,hh,ht⟩ := raw_trace x word k hx hs hp heval
  obtain ⟨r,hr,hf,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel machine n (budget x.view.width-n) (cfg x 0 machine.start) r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hsteps.le.trans hn,by rw [hf]; exact hh,by rw [hf]; exact ht⟩

end NearCubicWires.RepairOrdinary.RecoveryRawBranch
