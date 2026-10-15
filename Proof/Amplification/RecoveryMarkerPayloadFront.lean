import Proof.Amplification.RecoveryMarkerPayloadTail

/-! The controller actually copies the marker fields before its polarity
branch. Its exact endpoint is the selected existing checker entry. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem front_trace (marker : MarkerState) (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (words : Fin 3→List Bool) (hw : ∀ j,(words j).length=x.inner.base.state.bits.length)
    (hs : ∀ j,marker.tapes (RecoveryMarkerSave.target j)=frame (words j)) :
    ∃ n,n ≤ 24*x.inner.base.state.bits.length+27 ∧
      Timed machine n (cfg marker x machine.start) (entryCfg marker (output x words)) := by
  obtain ⟨hb,hc,hz⟩ := prepared_bounds x limit word innerBits outerBits innerPre outerPre hx
  obtain ⟨r,hr,hf,_⟩ := handoff_run marker x x.inner.base.state.bits.length words hw hs hb hc hz
  cases hm : marker.outer.result
  · have hn : next 0 r.final.control r.final.scanned=some 2 := by
      rw [hf]
      simp only [next,polarity,hm,Bool.false_eq_true,ite_false]
      rfl
    obtain ⟨n,hn,h⟩ := call_receipt sizes programs 0 next 0 2 (24*x.inner.base.state.bits.length+26)
      (cfg marker x RecoveryMarkerHandoff.machine.start) r hr hn
    have he : controlConfig (RecoveryCalls.code sizes 2)
        (RecoveryCalls.restarted (programs 2) r.final.heads r.final.tapes)=entryCfg marker (output x words) := by
      rw [hf]
      simp only [entryCfg,hm,Bool.false_eq_true,ite_false]
      rfl
    rw [he] at h
    exact ⟨n,by omega,h⟩
  · have hn : next 0 r.final.control r.final.scanned=some 1 := by
      rw [hf]
      simp only [next,polarity,hm,ite_true]
      rfl
    obtain ⟨n,hn,h⟩ := call_receipt sizes programs 0 next 0 1 (24*x.inner.base.state.bits.length+26)
      (cfg marker x RecoveryMarkerHandoff.machine.start) r hr hn
    have he : controlConfig (RecoveryCalls.code sizes 1)
        (RecoveryCalls.restarted (programs 1) r.final.heads r.final.tapes)=entryCfg marker (output x words) := by
      rw [hf]
      simp only [entryCfg,hm,ite_true]
      rfl
    rw [he] at h
    exact ⟨n,by omega,h⟩

end NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
