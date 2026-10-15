import Proof.Amplification.RecoveryRawViewWholeTail

/-! Complete prepared outer raw-view execution: bounded clause iteration,
physical empty-tail test, and exact Boolean result on every branch. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewWhole
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding RecoveryRawViewLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem rejected_run (width total : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x) (ha : (out word total x).1=false) :
    ∃ r,runFrom machine (budget width total) (RecoveryRawViewEnd.cfg x.data total machine.start)=some r ∧
      r.steps ≤ budget width total ∧ r.final.heads 28=0 ∧ r.final.tapes 28=[answer word total x] ∧
      (answer word total x=true →
        r.final=RecoveryRawViewEnd.cfg (RecoveryRawViewEnd.tested (out word total x).2.data) total r.final.control) := by
  have hrun := loop_return width total word x hx
  obtain ⟨first,hr,_,hf,hh,hbad⟩ := hrun
  have hphase : first.final.control=RepeatMachine.phaseCode bodyStates 4 := by
    have h := hf
    simp only [RepeatMachine.Result,ha,Bool.false_eq_true,ite_false] at h
    exact h
  have hn : next 0 first.final.control first.final.scanned=none := by
    change (if first.final.control=RepeatMachine.phaseCode bodyStates 3 then some (1 : Fin 2) else none)=none
    rw [hphase]
    exact if_neg phases_ne
  have htrace := stop_receipt sizes programs 0 next 0 (RecoveryRawViewLoop.budget width total) _ first hr hn
  obtain ⟨n,hn,h⟩ := htrace
  obtain ⟨r,hrr,hff,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hc : n ≤ budget width total := by unfold budget; omega
  have hm := runFrom_moreFuel machine n (budget width total-n) _ r hrr
  rw [Nat.add_sub_of_le hc] at hm
  have hanswer : answer word total x=false := by simp only [answer,ha,Bool.false_and]
  refine ⟨r,hm,hs.le.trans hc,?_,?_,?_⟩
  · rw [hff]; exact hh
  · rw [hff,hanswer]; exact hbad ha
  · simp only [hanswer,Bool.false_eq_true,IsEmpty.forall_iff]

theorem accepted_loop_run (width total : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x) (ha : (out word total x).1=true) :
    ∃ r,runFrom machine (budget width total) (RecoveryRawViewEnd.cfg x.data total machine.start)=some r ∧
      r.steps ≤ budget width total ∧ r.final.heads 28=0 ∧ r.final.tapes 28=[answer word total x] ∧
      (answer word total x=true →
        r.final=RecoveryRawViewEnd.cfg (RecoveryRawViewEnd.tested (out word total x).2.data) total r.final.control) := by
  have hrun := loop_return width total word x hx
  obtain ⟨first,hr,_,hf,_,_⟩ := hrun
  have hout : first.final=RepeatMachine.cfg 3 (source (out word total x).2) total 1 := by
    have h := hf
    simp only [RepeatMachine.Result,ha,ite_true] at h
    exact h
  have htrace := success_call total (RecoveryRawViewLoop.budget width total) (out word total x).2 _ first hr hout
  obtain ⟨n0,hn0,h0⟩ := htrace
  have hv := out_inv width total word x hx ha
  have htail := end_trace width total word (out word total x).2 hv
  obtain ⟨n1,hn1,h1⟩ := htail
  have h := h0.trans h1
  have hc : n0+n1 ≤ budget width total := by unfold budget; omega
  obtain ⟨r,hrr,hff,hs⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel machine (n0+n1) (budget width total-(n0+n1)) _ r hrr
  rw [Nat.add_sub_of_le hc] at hm
  refine ⟨r,hm,hs.le.trans hc,?_,?_,?_⟩
  · rw [hff]; rfl
  · rw [hff]
    change [(RecoveryRawViewEnd.tested (out word total x).2.data).inner.stream.data.present]=[answer word total x]
    rw [RecoveryRawViewEnd.tested_answer]
    simp only [answer,ha,Bool.true_and]
  · intro _
    rw [hff]
    rfl

theorem view_run (width total : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x) :
    ∃ r,runFrom machine (budget width total) (RecoveryRawViewEnd.cfg x.data total machine.start)=some r ∧
      r.steps ≤ budget width total ∧ r.final.heads 28=0 ∧ r.final.tapes 28=[answer word total x] ∧
      (answer word total x=true →
        r.final=RecoveryRawViewEnd.cfg (RecoveryRawViewEnd.tested (out word total x).2.data) total r.final.control) := by
  cases ha : (out word total x).1
  · exact rejected_run width total word x hx ha
  · exact accepted_loop_run width total word x hx ha

theorem budget_bound (width total : Nat) (ht : total ≤ 3*(width+1)) :
    budget width total ≤ 268435456*(width+1)^4 := by
  have hloop := RecoveryRawViewLoop.budget_bound width total ht
  have hsq : (width+1)^2 ≤ (width+1)^4 := by
    nlinarith [Nat.zero_le (width^4),Nat.zero_le (width^3),sq_nonneg (width : Nat)]
  unfold budget
  nlinarith [show 0<(width+1)^4 by positivity]

end NearCubicWires.RepairOrdinary.RecoveryRawViewWhole
