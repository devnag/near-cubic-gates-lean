import Proof.MachineModel.OrdinaryTransitionWalkRun

/-! Consumer for the certificate layout: after the binary m field and B
choices, the same retained witness supplies m literal t-bit vectors. Padding
is ignored, and the output is exactly the existing claimed-trace contract. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey MemoryLog
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem certificate_run (d : Store) (v : OrdinaryVerifier)
    (view : ClaimedTrace.View v.tapeCount v.stateCount) (hr : Ready d v view)
    (claims : List (Fin v.tapeCount→Bool)) (pre padding : List Bool)
    (hcount : d.m-d.index=claims.length)
    (hsource : d.lookup.scans=pre++frame (traceBits claims++padding)) (hpos : d.lookup.scanPos=pre.length) :
    ∃ r,runFrom machine ((claims.length+1)*cycleBudget d) (cfg machine.start d)=some r ∧
      r.steps≤(claims.length+1)*cycleBudget d ∧ r.final.heads 41=0 ∧
      (r.final.scanned 41=true ↔ ∃ finalView events,
        ClaimedTrace.check v.machine view claims=some (finalView,events) ∧
        v.machine.halted finalView.control=true ∧ v.accepting finalView.control=true) ∧
      (∀ finalView events,ClaimedTrace.check v.machine view claims=some (finalView,events) →
        r.final.tapes 33=d.out++MemoryInitialEmission.fields (2*d.w) (2*d.w+2) d.w d.serial events ∧
        r.final.heads 33=(r.final.tapes 33).length ∧
        r.final.tapes 31=binary (2*d.w) (d.serial+events.length) ∧ r.final.heads 31=0 ∧
        r.final.tapes 6=frame (binary d.lookup.j finalView.control.val) ∧ r.final.heads 6=0) := by
  obtain ⟨r,hrun,hsteps,hout⟩ := walk_run d v view hr pre (traceBits claims++padding) hsource hpos
  rw [hcount] at hrun hsteps hout
  have hscan : r.final.scanned 41=accepted v view claims.length (traceBits claims++padding) := by
    simp only [Configuration.scanned,hout.cursor,hout.decision,readTapeBit,List.getD,
      List.getElem?_cons_zero,Option.getD_some]
  refine ⟨r,hrun,hsteps,hout.cursor,?_,?_⟩
  · rw [hscan]
    exact accepted_trace v view claims padding
  · intro finalView events hcheck
    apply hout.emitted finalView events
    rw [evaluate_trace]
    exact hcheck

end NearCubicWires.RepairOrdinary.TransitionWalk
