import Proof.Amplification.RecoveryRawViewState

/-! Actual outer-list extraction on its retained bank. The inner witness
cursor, literal counter and cap driver survive the call unchanged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem outer_run (x : State) (hx : x.outer.Valid) :
    ∃ r,runFrom outerMachine (RecoveryStoredListCell.time x.outer.bits) (x.cfg outerMachine.start)=some r ∧
      r.final=(outerStep x).cfg r.final.control ∧ r.steps=RecoveryStoredListCell.time x.outer.bits := by
  obtain ⟨base,hr,ht,hh,hs⟩ := RecoveryClauseState.cell_ready x.outer 0 hx
  have h0 := TapeEmbedding.run_embed (RecoveryClauseState.machine 0) (fun _ : Fin 1=>1)
    (fun _=>CompareMachine.word x.limit) (RecoveryStoredListCell.time x.outer.bits) _ base hr
  have hrun := RecoveryBankPair.right_run (TapeEmbedding.machine 1 (RecoveryClauseState.machine 0))
    (RecoveryStoredListCell.time x.outer.bits) _
    (TapeEmbedding.receipt (fun _ : Fin 1=>1) (fun _=>CompareMachine.word x.limit) base) h0
    (x.innerCfg outerMachine.start).heads (x.innerCfg outerMachine.start).tapes
  obtain ⟨r,h,hn,hf⟩ := hrun
  refine ⟨r,h,?_,hn.trans hs⟩
  apply configuration_ext
  · rfl
  · rw [hf]
    change Fin.addCases (m:=36) (n:=29) (motive:=fun _=>Nat) (x.innerCfg outerMachine.start).heads
      (Fin.addCases (m:=28) (n:=1) (motive:=fun _=>Nat) base.final.heads (fun _=>1))=_
    rw [show base.final.heads=(fun _=>0) from funext hh]
    rfl
  · rw [hf]
    change Fin.addCases (m:=36) (n:=29) (motive:=fun _=>List Bool) (x.innerCfg outerMachine.start).tapes
      (Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool) base.final.tapes (fun _=>CompareMachine.word x.limit))=_
    rw [ht]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryRawView
