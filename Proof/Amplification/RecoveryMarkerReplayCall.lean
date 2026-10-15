import Proof.Amplification.RecoveryMarkerPayloadCorrected

/-! Original-code marker replay on the212-tape compact checker bank. The
entire existing table bank and all its streaming heads survive unchanged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCompactBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def replayMachine := RecoveryBankPair.leftMachine (u:=155) RecoveryMarker.machine

theorem replay_run (marker : MarkerState) (x : CheckState) (hm : marker.Valid) :
    ∃ r,runFrom replayMachine (RecoveryMarker.budget marker.width) (cfg marker x replayMachine.start)=some r ∧
      r.steps ≤ RecoveryMarker.budget marker.width ∧
      r.final=cfg (RecoveryMarker.output marker) x r.final.control := by
  obtain ⟨base,hr,hb,hh,ht⟩ := RecoveryMarker.marker_run marker hm
  obtain ⟨r,hrun,hs,hf⟩ := RecoveryBankPair.left_run RecoveryMarker.machine (RecoveryMarker.budget marker.width)
    (initialConfiguration RecoveryMarker.machine marker.tapes) base hr
    (x.cfg (0 : Fin 1)).heads (x.cfg (0 : Fin 1)).tapes
  refine ⟨r,hrun,hs.le.trans hb,?_⟩
  have hheads : base.final.heads=fun _=>0 := funext hh
  rw [hf,hheads,ht]
  rfl

theorem marker_bit (marker : MarkerState) (x : CheckState) {s : Nat} (q : Fin s) :
    (cfg marker x q).scanned 28=marker.inner.present := by
  change readTapeBit [marker.inner.present] 0=marker.inner.present
  rfl

end NearCubicWires.RepairOrdinary.RecoveryCompactBranch
