import Proof.Amplification.RecoveryCompactBranchTail

/-! Actual original-code replay followed by its physical marker-result
branch. No supplied classification chooses the control-flow continuation. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCompactBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem front_trace (marker : MarkerState) (x : CheckState) (hm : marker.Valid) :
    ∃ n,n ≤ RecoveryMarker.budget marker.width+1 ∧
      Timed machine n (cfg marker x machine.start) (entryCfg (RecoveryMarker.output marker) x) := by
  obtain ⟨r,hr,_,hf⟩ := replay_run marker x hm
  cases ha : (RecoveryMarker.output marker).inner.present
  · have hn : next 0 r.final.control r.final.scanned=some 2 := by
      rw [hf]
      simp only [next,marker_bit,ha,Bool.false_eq_true,ite_false]
      rfl
    obtain ⟨n,hn,h⟩ := call_receipt sizes programs 0 next 0 2 (RecoveryMarker.budget marker.width)
      (cfg marker x replayMachine.start) r hr hn
    have he : controlConfig (RecoveryCalls.code sizes 2)
        (RecoveryCalls.restarted (programs 2) r.final.heads r.final.tapes)=entryCfg (RecoveryMarker.output marker) x := by
      rw [hf]
      simp only [entryCfg,ha,Bool.false_eq_true,ite_false]
      rfl
    rw [he] at h
    exact ⟨n,hn,h⟩
  · have hn : next 0 r.final.control r.final.scanned=some 1 := by
      rw [hf]
      simp only [next,marker_bit,ha,ite_true]
      rfl
    obtain ⟨n,hn,h⟩ := call_receipt sizes programs 0 next 0 1 (RecoveryMarker.budget marker.width)
      (cfg marker x replayMachine.start) r hr hn
    have he : controlConfig (RecoveryCalls.code sizes 1)
        (RecoveryCalls.restarted (programs 1) r.final.heads r.final.tapes)=entryCfg (RecoveryMarker.output marker) x := by
      rw [hf]
      simp only [entryCfg,ha,ite_true]
      rfl
    rw [he] at h
    exact ⟨n,hn,h⟩

end NearCubicWires.RepairOrdinary.RecoveryCompactBranch
