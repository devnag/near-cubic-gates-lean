import Proof.Amplification.RecoveryMarkerThird

/-! The full marker payload branch loads its actual second clause,
executes the singleton payload atom, and handles the optional prefix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def payloadAtomOutput (x : State) : State :=
  let y := RecoveryMarkerAtom.output 0 x
  if y.inner.present then thirdOutput y else RecoveryMarkerFlags.answered y false

theorem payload_atom_trace (x : State) (hx : x.Valid) :
    ∃ n,n ≤ 12582912*(x.width+1)^2 ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 4) (initialConfiguration (programs 4) x.tapes))
      (RecoveryCalls.stopped sizes (fun _=>0) (payloadAtomOutput x).tapes) := by
  obtain ⟨n0,hn0,hready⟩ := atom_ready 0 x hx
  have hv := RecoveryMarkerAtom.output_valid 0 x hx
  have hw := RecoveryMarkerAtom.output_width 0 x
  cases ha : (RecoveryMarkerAtom.output 0 x).inner.present
  · have h0 := hready.call sizes programs 0 next 4 10 (by
      intro q
      change some (if readTapeBit [(RecoveryMarkerAtom.output 0 x).inner.present] 0 then (5 : Fin 11) else 10)=some 10
      change some (if (RecoveryMarkerAtom.output 0 x).inner.present then (5 : Fin 11) else 10)=some 10
      rw [ha]; rfl)
    refine ⟨n0+1+2,?_,?_⟩
    · unfold RecoveryMarkerAtom.budget at hn0
      nlinarith only [hn0,show 0<(x.width+1)^2 by positivity]
    · have ho : payloadAtomOutput x=RecoveryMarkerFlags.answered (RecoveryMarkerAtom.output 0 x) false := by
        simp only [payloadAtomOutput,ha,Bool.false_eq_true,ite_false]
      rw [ho]
      exact h0.trans (false_stop _)
  · have h0 := hready.call sizes programs 0 next 4 5 (by
      intro q
      change some (if readTapeBit [(RecoveryMarkerAtom.output 0 x).inner.present] 0 then (5 : Fin 11) else 10)=some 5
      change some (if (RecoveryMarkerAtom.output 0 x).inner.present then (5 : Fin 11) else 10)=some 5
      rw [ha]; rfl)
    obtain ⟨n1,hn1,h1⟩ := third_trace (RecoveryMarkerAtom.output 0 x) hv
    rw [hw] at hn1
    refine ⟨n0+1+n1,?_,?_⟩
    · unfold RecoveryMarkerAtom.budget at hn0
      unfold thirdBudget at hn1
      nlinarith only [hn0,hn1,show 0<(x.width+1)^2 by positivity]
    · have ho : payloadAtomOutput x=thirdOutput (RecoveryMarkerAtom.output 0 x) := by
        simp only [payloadAtomOutput,ha,ite_true]
      rw [ho]
      exact h0.trans h1

theorem payload_trace (x : State) (hx : x.Valid) :
    ∃ n,n ≤ payloadBudget x.width ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 3) (initialConfiguration (programs 3) x.tapes))
      (RecoveryCalls.stopped sizes (fun _=>0) (payloadOutput x).tapes) := by
  obtain ⟨n0,hn0,hready⟩ := load_ready x hx
  have hv := loaded_valid x hx
  have hw := loaded_width x hx
  cases ha : (loaded x).outer.flag
  · have h0 := hready.call sizes programs 0 next 3 10 (by
      intro q
      change some (if readTapeBit [(loaded x).outer.flag] 0 then (4 : Fin 11) else 10)=some 10
      change some (if (loaded x).outer.flag then (4 : Fin 11) else 10)=some 10
      rw [ha]; rfl)
    refine ⟨n0+1+2,?_,?_⟩
    · unfold payloadBudget
      nlinarith only [hn0,show 0<(x.width+1)^2 by positivity]
    · have ho : payloadOutput x=RecoveryMarkerFlags.answered (loaded x) false := by
        simp only [payloadOutput,ha,Bool.false_eq_true,ite_false]
      rw [ho]
      exact h0.trans (false_stop _)
  · have h0 := hready.call sizes programs 0 next 3 4 (by
      intro q
      change some (if readTapeBit [(loaded x).outer.flag] 0 then (4 : Fin 11) else 10)=some 4
      change some (if (loaded x).outer.flag then (4 : Fin 11) else 10)=some 4
      rw [ha]; rfl)
    obtain ⟨n1,hn1,h1⟩ := payload_atom_trace (loaded x) hv
    rw [hw] at hn1
    refine ⟨n0+1+n1,?_,?_⟩
    · unfold payloadBudget
      nlinarith only [hn0,hn1,show 0<(x.width+1)^2 by positivity]
    · have ho : payloadOutput x=payloadAtomOutput (loaded x) := by
        simp only [payloadOutput,ha,ite_true,payloadAtomOutput]
      rw [ho]
      exact h0.trans h1

theorem payload_valid (x : State) (hx : x.Valid) : (payloadOutput x).Valid := by
  have hy := loaded_valid x hx
  have hz := RecoveryMarkerAtom.output_valid 0 _ hy
  dsimp only [payloadOutput]
  split
  · split
    · exact third_valid _ hz
    · exact hz
  · exact hy

end NearCubicWires.RepairOrdinary.RecoveryMarker
