import Proof.Amplification.RecoveryRawBranchGraph

/-! Paid terminal calls for raw/default dispatch. Rejections may keep an
arbitrary failed frontend state, while the untouched SAT result cell has
its known zero head and singleton tape. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tailBudget (width : Nat) := 67108864*(width+1)^3+2

theorem reject_trace (heads : Fin 136→Nat) (tapes : Fin 136→List Bool) (old : Bool)
    (hh : heads 93=0) (ht : tapes 93=[old]) :
    ∃ n,∃ outHeads : Fin 136→Nat,∃ outTapes : Fin 136→List Bool,n ≤ 2 ∧
      Timed machine n ⟨RecoveryCalls.code sizes 3 (0 : Fin 2),heads,tapes⟩ (RecoveryCalls.stopped sizes outHeads outTapes) ∧
      outHeads 93=0 ∧ outTapes 93=[false] := by
  obtain ⟨r,hr,_,hrh,hrt⟩ := reject_run heads tapes old hh ht
  obtain ⟨n,hn,h⟩ := stop_receipt sizes programs 0 next 3 1 (⟨0,heads,tapes⟩ : Configuration 136 2) r hr (by rfl)
  refine ⟨n,r.final.heads,r.final.tapes,hn,h,?_,?_⟩
  · rw [hrh]; exact hh
  · rw [hrt,Function.update_self]

theorem default_trace (x : State) (total : Nat) (hv : x.view.inner.stream.data.present=true) :
    ∃ n,∃ outHeads : Fin 136→Nat,∃ outTapes : Fin 136→List Bool,n ≤ 2 ∧
      Timed machine n (cfg x total (RecoveryCalls.code sizes 2 (0 : Fin 2))) (RecoveryCalls.stopped sizes outHeads outTapes) ∧
      outHeads 93=0 ∧ outTapes 93=[true] := by
  have ht : (cfg x total (0 : Fin 2)).tapes 28=[true] := by
    change [x.view.inner.stream.data.present]=[true]
    rw [hv]
  obtain ⟨r,hr,_,hrh,hrt⟩ := RecoveryBankPair.flag_run (93 : Fin 136) 28 (cfg x total (0 : Fin 2)).heads
    (cfg x total (0 : Fin 2)).tapes x.eval.clause.result true rfl rfl rfl ht
  obtain ⟨n,hn,h⟩ := stop_receipt sizes programs 0 next 2 1 (cfg x total (0 : Fin 2)) r hr (by rfl)
  refine ⟨n,r.final.heads,r.final.tapes,hn,h,?_,?_⟩
  · rw [hrh]; rfl
  · rw [hrt,Function.update_self]

theorem eval_trace (x : State) (width cap total : Nat) (word : List Bool)
    (hx : RecoveryRawSAT.Inv width cap 0 0 word x.eval) (hn : total ≤ 3*(width+1)) :
    ∃ n,∃ outHeads : Fin 136→Nat,∃ outTapes : Fin 136→List Bool,n ≤ tailBudget width ∧
      Timed machine n (cfg x total (RecoveryCalls.code sizes 1 evalMachine.start))
        (RecoveryCalls.stopped sizes outHeads outTapes) ∧
      outHeads 93=0 ∧ outTapes 93=[RecoveryRawSATTable.answer width cap 0 0 total word x.eval.code] := by
  obtain ⟨r,hr,_,hh,ht⟩ := eval_run x width cap total word hx hn
  obtain ⟨n,hn',h⟩ := stop_receipt sizes programs 0 next 1 (RecoveryRawSATTable.budget width total)
    (cfg x total evalMachine.start) r hr (by rfl)
  have hb := RecoveryRawSATTable.budget_bound width total hn
  exact ⟨n,r.final.heads,r.final.tapes,by unfold tailBudget; omega,h,hh,ht⟩

end NearCubicWires.RepairOrdinary.RecoveryRawBranch
