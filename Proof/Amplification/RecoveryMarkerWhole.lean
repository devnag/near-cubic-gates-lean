import Proof.Amplification.RecoveryMarkerEntry

/-! Whole prepared marker execution from the retained original code.
All local copies, polarity saves, signed literal checks, clause/outer-tail
tests, call returns and final Boolean writes are included in one bound. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem marker_trace (x : State) (hx : x.Valid) :
    ∃ n,n ≤ budget x.width ∧ Timed machine n (initialConfiguration machine x.tapes)
      (RecoveryCalls.stopped sizes (fun _=>0) (output x).tapes) := by
  have h0 := (RecoveryMarkerFlags.answer_ready x false).call sizes programs 0 next 0 1 (by intro q; rfl)
  have hv : (RecoveryMarkerFlags.answered x false).Valid := hx
  obtain ⟨n,hn,h⟩ := start_trace (RecoveryMarkerFlags.answered x false) hv
  change n ≤ 29360128*(x.width+1)^2 at hn
  refine ⟨2+n,?_,?_⟩
  · unfold budget
    nlinarith only [hn,show 0<(x.width+1)^2 by positivity]
  · exact h0.trans h

theorem marker_run (x : State) (hx : x.Valid) :
    ∃ r,run machine (budget x.width) x.tapes=some r ∧ r.steps ≤ budget x.width ∧
      (∀ i,r.final.heads i=0) ∧ r.final.tapes=(output x).tapes := by
  obtain ⟨n,hn,h⟩ := marker_trace x hx
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := run_moreFuel machine n (budget x.width-n) x.tapes r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hs.le.trans hn,by intro i; rw [hf]; rfl,by rw [hf]; rfl⟩

theorem output_valid (x : State) (hx : x.Valid) : (output x).Valid := by
  have hy := loaded_valid (RecoveryMarkerFlags.answered x false) hx
  have hz := empty_valid _ hy
  dsimp only [output]
  split
  · split
    · exact hz
    · exact payload_valid _ hz
  · exact hy

end NearCubicWires.RepairOrdinary.RecoveryMarker
