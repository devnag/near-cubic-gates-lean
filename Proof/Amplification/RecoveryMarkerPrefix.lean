import Proof.Amplification.RecoveryMarkerReadyCalls

/-! The whole optional committed-prefix branch executes its two signed
literal atoms and the final original outer-code tail test. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countOutput (x : State) : State :=
  let y := RecoveryMarkerAtom.output 2 x
  if y.inner.present then outerOutput y else RecoveryMarkerFlags.answered y false

theorem count_trace (x : State) (hx : x.Valid) :
    ∃ n,n ≤ 2097152*(x.width+1)^2 ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 7) (initialConfiguration (programs 7) x.tapes))
      (RecoveryCalls.stopped sizes (fun _=>0) (countOutput x).tapes) := by
  obtain ⟨n0,hn0,hready⟩ := atom_ready 2 x hx
  have hv := RecoveryMarkerAtom.output_valid 2 x hx
  have hw := RecoveryMarkerAtom.output_width 2 x
  cases ha : (RecoveryMarkerAtom.output 2 x).inner.present
  · have h0 := hready.call sizes programs 0 next 7 10 (by
      intro q
      change some (if readTapeBit [(RecoveryMarkerAtom.output 2 x).inner.present] 0 then (8 : Fin 11) else 10)=some 10
      change some (if (RecoveryMarkerAtom.output 2 x).inner.present then (8 : Fin 11) else 10)=some 10
      rw [ha]; rfl)
    refine ⟨n0+1+2,?_,?_⟩
    · unfold RecoveryMarkerAtom.budget at hn0
      nlinarith only [hn0,show 0<(x.width+1)^2 by positivity]
    · have ho : countOutput x=RecoveryMarkerFlags.answered (RecoveryMarkerAtom.output 2 x) false := by
        simp only [countOutput,ha,Bool.false_eq_true,ite_false]
      rw [ho]
      exact h0.trans (false_stop _)
  · have h0 := hready.call sizes programs 0 next 7 8 (by
      intro q
      change some (if readTapeBit [(RecoveryMarkerAtom.output 2 x).inner.present] 0 then (8 : Fin 11) else 10)=some 8
      change some (if (RecoveryMarkerAtom.output 2 x).inner.present then (8 : Fin 11) else 10)=some 8
      rw [ha]; rfl)
    obtain ⟨n1,hn1,h1⟩ := outer_trace (RecoveryMarkerAtom.output 2 x) hv
    rw [hw] at hn1
    refine ⟨n0+1+n1,?_,?_⟩
    · unfold RecoveryMarkerAtom.budget at hn0
      nlinarith only [hn0,hn1,show 0<(x.width+1)^2 by positivity]
    · have ho : countOutput x=outerOutput (RecoveryMarkerAtom.output 2 x) := by
        simp only [countOutput,ha,ite_true]
      rw [ho]
      exact h0.trans h1

theorem prefix_trace (x : State) (hx : x.Valid) :
    ∃ n,n ≤ prefixBudget x.width ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 6) (initialConfiguration (programs 6) x.tapes))
      (RecoveryCalls.stopped sizes (fun _=>0) (prefixOutput x).tapes) := by
  obtain ⟨n0,hn0,hready⟩ := atom_ready 1 x hx
  have hv := RecoveryMarkerAtom.output_valid 1 x hx
  have hw := RecoveryMarkerAtom.output_width 1 x
  cases ha : (RecoveryMarkerAtom.output 1 x).inner.present
  · have h0 := hready.call sizes programs 0 next 6 10 (by
      intro q
      change some (if readTapeBit [(RecoveryMarkerAtom.output 1 x).inner.present] 0 then (7 : Fin 11) else 10)=some 10
      change some (if (RecoveryMarkerAtom.output 1 x).inner.present then (7 : Fin 11) else 10)=some 10
      rw [ha]; rfl)
    refine ⟨n0+1+2,?_,?_⟩
    · unfold prefixBudget RecoveryMarkerAtom.budget at *
      nlinarith only [hn0,show 0<(x.width+1)^2 by positivity]
    · have ho : prefixOutput x=RecoveryMarkerFlags.answered (RecoveryMarkerAtom.output 1 x) false := by
        simp only [prefixOutput,ha,Bool.false_eq_true,ite_false]
      rw [ho]
      exact h0.trans (false_stop _)
  · have h0 := hready.call sizes programs 0 next 6 7 (by
      intro q
      change some (if readTapeBit [(RecoveryMarkerAtom.output 1 x).inner.present] 0 then (7 : Fin 11) else 10)=some 7
      change some (if (RecoveryMarkerAtom.output 1 x).inner.present then (7 : Fin 11) else 10)=some 7
      rw [ha]; rfl)
    obtain ⟨n1,hn1,h1⟩ := count_trace (RecoveryMarkerAtom.output 1 x) hv
    rw [hw] at hn1
    refine ⟨n0+1+n1,?_,?_⟩
    · unfold prefixBudget RecoveryMarkerAtom.budget at *
      nlinarith only [hn0,hn1,show 0<(x.width+1)^2 by positivity]
    · have ho : prefixOutput x=countOutput (RecoveryMarkerAtom.output 1 x) := by
        simp only [prefixOutput,ha,ite_true,countOutput,outerOutput]
      rw [ho]
      exact h0.trans h1

end NearCubicWires.RepairOrdinary.RecoveryMarker
