import Proof.Amplification.RecoveryRawViewEraseInstall

/-! Actual bounded counter sweep at head zero. Its driver and reset tape
are the retained inner unpair workspace; source/cap cursors are untouched. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem erase_run (x : State) (hx : x.Valid) :
    ∃ r,runFrom eraseMachine (2*x.capacity+4)
        ⟨eraseMachine.start,counterHeads x eraseMachine.start,(x.cfg eraseMachine.start).tapes⟩=some r ∧
      r.final=⟨r.final.control,counterHeads (cleared x) r.final.control,((cleared x).cfg r.final.control).tapes⟩ ∧
      r.steps=2*x.capacity+4 := by
  have hb := counter_length x eraseMachine.start hx
  have hraw := RecoveryScratchErase.erase_ready x.capacity x.inner.stream.data.data.capacity
    (fun _ : Fin 1=>(x.cfg eraseMachine.start).tapes 35) (fun _=>hb)
  have h : ReadyRun (RecoveryScratchErase.resetMachine 1) (2*x.capacity+4)
      ![(x.cfg eraseMachine.start).tapes 35,List.replicate x.capacity true,
        List.replicate x.inner.stream.data.data.capacity false]
      ![List.replicate x.capacity false,List.replicate x.capacity true,
        List.replicate (max x.inner.stream.data.data.capacity (x.capacity+1)) false] := by
    convert hraw using 1 <;> funext i <;> fin_cases i <;> rfl
  have hrun := h.focus_at eraseSlots eraseSlots_injective
    (counterHeads x eraseMachine.start) (x.cfg eraseMachine.start).tapes
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  obtain ⟨r,hr,hh,ht,hs⟩ := hrun
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · unfold counterHeads
    rw [cleared_heads]
    exact hh
  · have hi := erase_install (x.cfg eraseMachine.start).tapes x.capacity
      (max x.inner.stream.data.data.capacity (x.capacity+1)) rfl
    have he := cleared_tapes x eraseMachine.start
    exact ht.trans (hi.trans he.symm)

end NearCubicWires.RepairOrdinary.RecoveryRawView
