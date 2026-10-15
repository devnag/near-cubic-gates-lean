import Proof.Amplification.RecoveryRowStructureCopyTapes

/-! Actual paid copy from the retained row code to the existing unpair input.
It runs at the streamed row boundary, preserving the global witness cursor,
width driver, clause payload and all unrelated tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copy_run (d : Data) (capacity : Nat) (word : List Bool) (hd : d.Valid word)
    (hw : d.code.length=d.state.bits.length) (hc : 2*d.code.length+1≤capacity)
    (hr : 4*d.code.length+3≤d.state.capacity) :
    ∃ r,runFrom copyMachine (8*d.code.length+8) (cfg d capacity copyMachine.start)=some r ∧
      r.final=cfg (copied d) capacity r.final.control ∧ r.steps=8*d.code.length+8 ∧
      (copied d).Valid word := by
  have hb : (d.state.fields 0).length≤2*d.code.length+1 := by simpa only [hw] using hd.1.2 0
  have h := RecoveryRootRound.copy_ready d.code (d.state.fields 0) capacity d.state.capacity hb
  rw [Nat.max_eq_left hc,Nat.max_eq_left hr] at h
  obtain ⟨r,hrun,hheads,htapes,hsteps⟩ := h.focus_at copySlots copySlots_injective
    (cfg d capacity copyMachine.start).heads (cfg d capacity copyMachine.start).tapes
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hrun,?_,hsteps,copied_valid d word hd hw⟩
  apply configuration_ext
  · rfl
  · exact hheads
  · rw [htapes,copy_output _ d.code capacity d.state.capacity (by rfl) (by rfl) (by rfl)]
    exact (copied_tapes d capacity).symm

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
