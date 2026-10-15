import Proof.MachineModel.OrdinarySourceSATLiftSourceReady

/-! The final delimiter-driven copy produces a fresh exact framed output;
no tape truncation or final source-head promise is assumed for free. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem finish (p : OrdinaryOracleProgram) (word : List Bool)
    (heads : Fin (tapes p) → ℕ) (data : Fin (tapes p) → List Bool)
    (hready : OutputReady p word heads data) :
    ∃ cost final,cost ≤ 4*word.length+5 ∧
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program p) cost (atCall p 6 heads data) final ∧
      (program p).base.machine.halted final.control=true ∧
      final.tapes (program p).base.outputTape=frame word := by
  obtain ⟨base,hbase,hbt,hbh,hbs⟩ := PCPFieldMoves.ready_run word [] 0 0
  have h : ClockJoin.ReadyRun PCPFieldMoves.readyMachine (4*word.length+4)
      ![frame word++[],[],[]] (PCPFieldMoves.output [] word [] 0 0) :=
    ⟨base,hbase,hbt,hbh,hbs.le⟩
  have hout := hready.fresh (output p) (by rfl)
  have hlog := hready.fresh (log p) (by dsimp [log]; omega)
  obtain ⟨r,hr,_hh,ht,hs⟩ := h.focus_at (finalSlots p) (final_injective p) heads data
    (by intro i; fin_cases i
        · simpa [finalSlots] using hready.tape
        · exact hout.2
        · exact hlog.2)
    (by intro i; fin_cases i
        · exact hready.head
        · exact hout.1
        · exact hlog.1)
  have htrace := ordinary_trace (o := RecoveryOracle.correctedSat) (ports p) _ _ _ r hr
  have stopped := stop_trace p r.steps heads data r.final htrace (prefix_of_run _ _ _ r hr).2
  refine ⟨r.steps+1,_,by omega,stopped,?_,?_⟩
  · simp [program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · change r.final.tapes (output p)=frame word
    rw [ht]
    change install (finalSlots p) data (PCPFieldMoves.output [] word [] 0 0) (finalSlots p 1)=_
    rw [install_slot _ (final_injective p)]
    simp [PCPFieldMoves.output]

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
