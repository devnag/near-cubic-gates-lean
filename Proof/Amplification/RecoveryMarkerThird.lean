import Proof.Amplification.RecoveryMarkerPrefix

/-! The actual optional third-clause branch. An absent outer cell ends
the two-clause marker; a present cell executes the whole signed prefix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem third_trace (x : State) (hx : x.Valid) :
    ∃ n,n ≤ thirdBudget x.width ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 5) (initialConfiguration (programs 5) x.tapes))
      (RecoveryCalls.stopped sizes (fun _=>0) (thirdOutput x).tapes) := by
  obtain ⟨n0,hn0,hready⟩ := load_ready x hx
  have hv := loaded_valid x hx
  have hw := loaded_width x hx
  cases ha : (loaded x).outer.flag
  · have h0 := hready.call sizes programs 0 next 5 9 (by
      intro q
      change some (if readTapeBit [(loaded x).outer.flag] 0 then (6 : Fin 11) else 9)=some 9
      change some (if (loaded x).outer.flag then (6 : Fin 11) else 9)=some 9
      rw [ha]; rfl)
    refine ⟨n0+1+2,?_,?_⟩
    · unfold thirdBudget
      nlinarith only [hn0,show 0<(x.width+1)^2 by positivity]
    · have ho : thirdOutput x=RecoveryMarkerFlags.answered (loaded x) true := by
        simp only [thirdOutput,ha,Bool.false_eq_true,ite_false]
      rw [ho]
      exact h0.trans (true_stop _)
  · have h0 := hready.call sizes programs 0 next 5 6 (by
      intro q
      change some (if readTapeBit [(loaded x).outer.flag] 0 then (6 : Fin 11) else 9)=some 6
      change some (if (loaded x).outer.flag then (6 : Fin 11) else 9)=some 6
      rw [ha]; rfl)
    obtain ⟨n1,hn1,h1⟩ := prefix_trace (loaded x) hv
    rw [hw] at hn1
    refine ⟨n0+1+n1,?_,?_⟩
    · unfold thirdBudget prefixBudget at *
      nlinarith only [hn0,hn1,show 0<(x.width+1)^2 by positivity]
    · have ho : thirdOutput x=prefixOutput (loaded x) := by
        simp only [thirdOutput,ha,ite_true]
      rw [ho]
      exact h0.trans h1

theorem third_valid (x : State) (hx : x.Valid) : (thirdOutput x).Valid := by
  have hy := loaded_valid x hx
  dsimp only [thirdOutput]
  split
  · exact prefix_valid _ hy
  · exact hy

theorem third_width (x : State) (hx : x.Valid) : (thirdOutput x).width=x.width := by
  have hy := loaded_width x hx
  dsimp only [thirdOutput]
  split
  · exact (prefix_width _).trans hy
  · exact hy

end NearCubicWires.RepairOrdinary.RecoveryMarker
