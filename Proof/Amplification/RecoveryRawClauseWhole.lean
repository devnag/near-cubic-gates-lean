import Proof.Amplification.RecoveryRawClauseTail

/-! Whole prepared raw-clause run. Its acceptance bit requires both the
supplied number of present literals and the actual empty remaining tail. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawClause
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RecoveryRawLiteralBound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem phases_ne : RepeatMachine.phaseCode bodyStates 4≠RepeatMachine.phaseCode bodyStates 3 := by
  intro h
  have he : (4 : Fin 5)=3 := Sum.inr.inj ((RepeatMachine.code bodyStates).injective h)
  exact (by decide : (4 : Fin 5)≠3) he

theorem clause_run (width total : Nat) (x : State) (hx : RecoveryRawLiteralLoop.Inv width x) :
    ∃ r,runFrom machine (budget width total) (cfg x total machine.start)=some r ∧
      r.steps ≤ budget width total ∧ r.final.heads 28=0 ∧
      r.final.tapes 28=[answer total x] ∧
      (answer total x=true → r.final=cfg (inverted (output (out total x).2)) total r.final.control) := by
  have hrun := RecoveryRawLiteralLoop.loop_return width total x hx
  obtain ⟨first,hr,hb,hf,hh,_,hbad⟩ := hrun
  have hi : controlConfig (RecoveryCalls.code sizes 0)
      (RepeatMachine.cfg 0 (RecoveryRawLiteralLoop.source x) total 1)=cfg x total machine.start := rfl
  cases ha : (out total x).1
  · have hphase : first.final.control=RepeatMachine.phaseCode bodyStates 4 := by
      have h := hf
      simp only [RepeatMachine.Result,show (RepeatMachine.iterate RecoveryRawLiteralLoop.next total x).1=false from ha,
        Bool.false_eq_true,ite_false] at h
      exact h
    have hn : next 0 first.final.control first.final.scanned=none := by
      change (if first.final.control=RepeatMachine.phaseCode bodyStates 3 then some (1 : Fin 3) else none)=none
      rw [hphase]
      exact if_neg phases_ne
    have htrace := stop_receipt sizes programs 0 next 0 (RecoveryRawLiteralLoop.budget width total) _ first hr hn
    obtain ⟨n,hn,h⟩ := htrace
    rw [hi] at h
    obtain ⟨r,hrr,hff,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hc : n ≤ budget width total := by unfold budget; omega
    have hm := runFrom_moreFuel machine n (budget width total-n) _ r hrr
    rw [Nat.add_sub_of_le hc] at hm
    have hanswer : answer total x=false := by simp only [answer,ha,Bool.false_and]
    refine ⟨r,hm,hs.le.trans hc,?_,?_,?_⟩
    · rw [hff]; exact hh
    · rw [hff,hanswer]; exact hbad ha
    · simp only [hanswer,Bool.false_eq_true,IsEmpty.forall_iff]
  · have hout : first.final=RepeatMachine.cfg 3 (RecoveryRawLiteralLoop.source (out total x).2) total 1 := by
      have h := hf
      simp only [RepeatMachine.Result,show (RepeatMachine.iterate RecoveryRawLiteralLoop.next total x).1=true from ha,
        ite_true] at h
      exact h
    have hn : next 0 first.final.control first.final.scanned=some 1 := by
      change (if first.final.control=RepeatMachine.phaseCode bodyStates 3 then some (1 : Fin 3) else none)=some 1
      rw [hout]; exact if_pos rfl
    have htrace := call_receipt sizes programs 0 next 0 1 (RecoveryRawLiteralLoop.budget width total) _ first hr hn
    obtain ⟨n0,hn0,h0⟩ := htrace
    have hv := out_inv width total x hx
    obtain ⟨n1,hn1,h1⟩ := tail_trace (out total x).2 total hv.1
    rw [hout] at h0
    have h := h0.trans h1
    rw [hi] at h
    have hcost : cost (out total x).2 ≤ RecoveryRawLiteralLoop.bodyBudget width := by
      have hc := RecoveryRawLiteralBound.cost_bound (out total x).2 hv.1
      rw [hv.2] at hc
      exact hc
    have hc : n0+n1 ≤ budget width total := by unfold budget; omega
    obtain ⟨r,hrr,hff,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hm := runFrom_moreFuel machine (n0+n1) (budget width total-(n0+n1)) _ r hrr
    rw [Nat.add_sub_of_le hc] at hm
    refine ⟨r,hm,hs.le.trans hc,?_,?_,?_⟩
    · rw [hff]; rfl
    · rw [hff]
      change [(inverted (output (out total x).2)).stream.data.present]=[answer total x]
      rw [inverted_output_bit]
      simp only [answer,ha,Bool.true_and]
    · intro _
      rw [hff]
      rfl

end NearCubicWires.RepairOrdinary.RecoveryRawClause
