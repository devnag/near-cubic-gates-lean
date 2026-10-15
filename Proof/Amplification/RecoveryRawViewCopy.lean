import Proof.Amplification.RecoveryRawViewCopyHeads

/-! A paid framed copy hands the actual extracted clause code to the
retained inner checker. Both reset workspaces remain physically allocated. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copy_run (x : State) (bits : List Bool) (hw : bits.length=x.width)
    (hf : x.outer.fields 0=frame bits) :
    ∃ r,runFrom copyMachine (8*bits.length+8) (x.cfg copyMachine.start)=some r ∧
      r.final=(copied x bits).cfg r.final.control ∧ r.steps=8*bits.length+8 := by
  have hb : (frame x.inner.stream.data.data.bits).length ≤ 2*bits.length+1 := by
    rw [frame_length,hw]
    exact Nat.le_refl _
  have h := RecoveryRootRound.copy_ready bits (frame x.inner.stream.data.data.bits)
    x.outer.capacity x.inner.stream.data.data.capacity hb
  obtain ⟨r,hr,hh,ht,hs⟩ := h.focus_at copySlots copySlots_injective
    (x.cfg copyMachine.start).heads (x.cfg copyMachine.start).tapes
    (by intro j; fin_cases j
        · exact hf
        · rfl
        · rfl
        · rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · exact hh.trans (copied_heads x bits r.final.control).symm
  · have hi := copy_install (x.cfg copyMachine.start).tapes bits
      (max x.outer.capacity (2*bits.length+1))
      (max x.inner.stream.data.data.capacity (4*bits.length+3)) hf
    have he := copied_tapes x bits copyMachine.start hw
    exact ht.trans (hi.trans he.symm)

end NearCubicWires.RepairOrdinary.RecoveryRawView
