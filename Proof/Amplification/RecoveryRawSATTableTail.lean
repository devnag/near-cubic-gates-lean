import Proof.Amplification.RecoveryRawSATTableGraph

/-! Actual successful and rejected exits of the raw-SAT table controller.
The false exit is written after the loop; the true branch executes the
remaining outer-code test before returning its Boolean. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSATTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawSAT
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem accepted_trace (width cap committed count total : Nat) (word : List Bool)
    (x : State) (hx : Inv width cap committed count word x)
    (ha : prefixCheck (clauseCheck width cap committed count word) total x.code=true) :
    ∃ n heads tapes,n ≤ budget width total ∧ heads 27=0 ∧
      tapes 27=[answer width cap committed count total word x.code] ∧
      Timed machine n (RecoveryRawSATEnd.cfg x.tapes total machine.start)
        (RecoveryCalls.stopped sizes heads tapes) := by
  have hrun := RecoveryRawSATLoop.loop_run width cap committed count total word x hx
  obtain ⟨first,hr,_,_,_,_,hout⟩ := hrun
  obtain ⟨out,hf,hv,hcode⟩ := hout ha
  have hn : next 0 first.final.control first.final.scanned=some 1 := by
    change some (if first.final.control=RepeatMachine.phaseCode bodyStates 3 then (1 : Fin 3) else 2)=some 1
    rw [hf]
    exact if_pos rfl |> congrArg some
  have hcall := call_receipt sizes programs 0 next 0 1 (RecoveryRawSATLoop.budget width total) _ first hr hn
  obtain ⟨n0,hn0,h0⟩ := hcall
  rw [hf,end_restart] at h0
  have htest := RecoveryRawSATEnd.test_run out total hv.valid.2.2.1
  obtain ⟨last,hr1,hf1,_⟩ := htest
  have hstop := stop_receipt sizes programs 0 next 1 (RecoveryRawSATEnd.budget out) _ last hr1 (by rfl)
  obtain ⟨n1,hn1,h1⟩ := hstop
  rw [hf1] at h1
  have hb := end_budget width cap committed count word out hv
  refine ⟨n0+n1,(RecoveryRawSATEnd.cfg (RecoveryRawSATEnd.output out) total (0 : Fin 1)).heads,
    (RecoveryRawSATEnd.cfg (RecoveryRawSATEnd.output out) total (0 : Fin 1)).tapes,?_,rfl,?_,h0.trans h1⟩
  · unfold budget
    omega
  · change RecoveryRawSATEnd.output out 27=[answer width cap committed count total word x.code]
    rw [RecoveryRawSATEnd.output_answer,hcode]
    simp only [answer,ha,Bool.true_and]

theorem rejected_trace (width cap committed count total : Nat) (word : List Bool)
    (x : State) (hx : Inv width cap committed count word x)
    (ha : prefixCheck (clauseCheck width cap committed count word) total x.code=false) :
    ∃ n heads tapes,n ≤ budget width total ∧ heads 27=0 ∧
      tapes 27=[answer width cap committed count total word x.code] ∧
      Timed machine n (RecoveryRawSATEnd.cfg x.tapes total machine.start)
        (RecoveryCalls.stopped sizes heads tapes) := by
  have hrun := RecoveryRawSATLoop.loop_run width cap committed count total word x hx
  obtain ⟨first,hr,_,hphase,hh,⟨bit,ht⟩,_⟩ := hrun
  have hn : next 0 first.final.control first.final.scanned=some 2 := by
    change some (if first.final.control=RepeatMachine.phaseCode bodyStates 3 then (1 : Fin 3) else 2)=some 2
    rw [hphase,ha]
    simp only [Bool.false_eq_true,if_false]
    exact congrArg some (if_neg phases_ne)
  have hcall := call_receipt sizes programs 0 next 0 2 (RecoveryRawSATLoop.budget width total) _ first hr hn
  obtain ⟨n0,hn0,h0⟩ := hcall
  let c := RecoveryCalls.restarted rejectMachine first.final.heads first.final.tapes
  have hreject := reject_run c rfl hh bit ht
  obtain ⟨last,hr1,hf1,_⟩ := hreject
  have hstop := stop_receipt sizes programs 0 next 2 1 c last hr1 (by rfl)
  obtain ⟨n1,hn1,h1⟩ := hstop
  rw [hf1] at h1
  refine ⟨n0+n1,(rejected c).heads,(rejected c).tapes,?_,hh,?_,h0.trans h1⟩
  · unfold budget
    omega
  · change [false]=[answer width cap committed count total word x.code]
    simp only [answer,ha,Bool.false_and]

end NearCubicWires.RepairOrdinary.RecoveryRawSATTable
