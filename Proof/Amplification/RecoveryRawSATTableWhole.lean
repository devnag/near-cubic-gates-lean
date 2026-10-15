import Proof.Amplification.RecoveryRawSATTableTail

/-! Whole prepared raw-SAT replay with an actual count driver and exact
Boolean output. The final empty-list test is included in the runtime. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSATTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawSAT
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem table_trace (width cap committed count total : Nat) (word : List Bool)
    (x : State) (hx : Inv width cap committed count word x) :
    ∃ n heads tapes,n ≤ budget width total ∧ heads 27=0 ∧
      tapes 27=[answer width cap committed count total word x.code] ∧
      Timed machine n (RecoveryRawSATEnd.cfg x.tapes total machine.start)
        (RecoveryCalls.stopped sizes heads tapes) := by
  cases ha : prefixCheck (clauseCheck width cap committed count word) total x.code
  · exact rejected_trace width cap committed count total word x hx ha
  · exact accepted_trace width cap committed count total word x hx ha

theorem table_run (width cap committed count total : Nat) (word : List Bool)
    (x : State) (hx : Inv width cap committed count word x) :
    ∃ r,runFrom machine (budget width total)
        (RecoveryRawSATEnd.cfg x.tapes total machine.start)=some r ∧
      r.steps ≤ budget width total ∧ r.final.heads 27=0 ∧
      r.final.tapes 27=[answer width cap committed count total word x.code] := by
  obtain ⟨n,heads,tapes,hn,hh,ht,h⟩ := table_trace width cap committed count total word x hx
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel machine n (budget width total-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hs.le.trans hn,by rw [hf]; exact hh,by rw [hf]; exact ht⟩

theorem budget_bound (width total : Nat) (ht : total ≤ 3*(width+1)) :
    budget width total ≤ 67108864*(width+1)^3 := by
  unfold budget RecoveryRawSATLoop.budget RecoveryRawSAT.budget
  calc
    _ ≤ 3*(width+1)*(8388608*(width+1)^2+3)+3+262144*(width+1)^2+5 := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (width^3),sq_nonneg (width : Nat)]

end NearCubicWires.RepairOrdinary.RecoveryRawSATTable
