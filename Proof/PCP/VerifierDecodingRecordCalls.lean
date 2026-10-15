import Proof.PCP.VerifierDecodingRecordScans

/-! Paid returns of the fixed single-record call graph. These prefixes retain
the actual streaming heads and workspace rather than requiring every head to
be at zero. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem call_prefix (node dest : Fin 7) (fuel : ℕ)
    (input : Configuration 8 (sizes node)) (r : ExecutionReceipt 8 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=some dest) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (controlConfig (RecoveryCalls.code sizes dest)
        (RecoveryCalls.restarted (programs dest) r.final.heads r.final.tapes)) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next node dest r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem stop_prefix (node : Fin 7) (fuel : ℕ)
    (input : Configuration 8 (sizes node)) (r : ExecutionReceipt 8 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next node r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem bounded_run {n budget : ℕ}
    {input output : Configuration 8 (Fintype.card (RecoveryCalls.Control sizes))}
    (h : Timed machine n input output) (hb : n≤budget)
    (hh : machine.halted output.control=true) :
    ∃ r, runFrom machine budget input=some r ∧ r.final=output ∧ r.steps≤budget := by
  obtain ⟨r,hr,hf,hs⟩ := h.run hh
  have hm := runFrom_moreFuel machine n (budget-n) input r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r,hm,hf,hs.trans_le hb⟩

theorem false_result {q : ℕ} (final : Configuration 8 q) (hf : final.tapes 7=[false]) :
    final.scanned 7=false := by
  simp only [Configuration.scanned,hf]
  cases final.heads 7 <;> simp [readTapeBit,List.getD]

theorem success_tail (source backing bound : List Bool) (pos j t cap : ℕ) (rangeFlag : Bool) :
    Timed machine 2
      (cfg (RecoveryCalls.code sizes 6 (programs 6).start) source backing bound pos j t cap rangeFlag false)
      (cfg (RecoveryCalls.controlCode sizes none) source backing bound pos j t cap rangeFlag true) := by
  obtain ⟨r,hr,hf,hs⟩ := success_run source backing bound pos j t cap rangeFlag
  have ht := stop_prefix 6 1 _ r hr (by rfl)
  rw [hf,hs] at ht
  exact ht

end NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
