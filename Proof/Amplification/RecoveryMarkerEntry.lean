import Proof.Amplification.RecoveryMarkerPayload

/-! The real marker entry checks the first outer cell and its empty
clause before entering the payload and optional prefix branches. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leadingOutput (x : State) : State :=
  let y := emptyStep x
  if y.inner.data.flag then RecoveryMarkerFlags.answered y false else payloadOutput y
def startOutput (x : State) : State :=
  let y := loaded x
  if y.outer.flag then leadingOutput y else RecoveryMarkerFlags.answered y false

theorem leading_trace (x : State) (hx : x.Valid) :
    ∃ n,n ≤ 25165824*(x.width+1)^2 ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 2) (initialConfiguration (programs 2) x.tapes))
      (RecoveryCalls.stopped sizes (fun _=>0) (leadingOutput x).tapes) := by
  have hready := empty_ready x hx.1
  have hv := empty_valid x hx
  have hw : (emptyStep x).width=x.width := RecoveryClauseState.after_length x.inner.data 0
  have hc := RecoveryStoredListCell.time_bound x.inner.data.bits
  change RecoveryStoredListCell.time x.inner.data.bits ≤ 262144*(x.width+1)^2 at hc
  cases ha : (emptyStep x).inner.data.flag
  · have h0 := hready.call sizes programs 0 next 2 3 (by
      intro q
      change some (if readTapeBit [(emptyStep x).inner.data.flag] 0 then (10 : Fin 11) else 3)=some 3
      change some (if (emptyStep x).inner.data.flag then (10 : Fin 11) else 3)=some 3
      rw [ha]; rfl)
    obtain ⟨n1,hn1,h1⟩ := payload_trace (emptyStep x) hv
    rw [hw] at hn1
    refine ⟨RecoveryStoredListCell.time x.inner.data.bits+1+n1,?_,?_⟩
    · unfold payloadBudget at hn1
      nlinarith only [hc,hn1,show 0<(x.width+1)^2 by positivity]
    · have ho : leadingOutput x=payloadOutput (emptyStep x) := by
        simp only [leadingOutput,ha,Bool.false_eq_true,ite_false]
      rw [ho]
      exact h0.trans h1
  · have h0 := hready.call sizes programs 0 next 2 10 (by
      intro q
      change some (if readTapeBit [(emptyStep x).inner.data.flag] 0 then (10 : Fin 11) else 3)=some 10
      change some (if (emptyStep x).inner.data.flag then (10 : Fin 11) else 3)=some 10
      rw [ha]; rfl)
    refine ⟨RecoveryStoredListCell.time x.inner.data.bits+1+2,?_,?_⟩
    · nlinarith only [hc,show 0<(x.width+1)^2 by positivity]
    · have ho : leadingOutput x=RecoveryMarkerFlags.answered (emptyStep x) false := by
        simp only [leadingOutput,ha,ite_true]
      rw [ho]
      exact h0.trans (false_stop _)

theorem start_trace (x : State) (hx : x.Valid) :
    ∃ n,n ≤ 29360128*(x.width+1)^2 ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 1) (initialConfiguration (programs 1) x.tapes))
      (RecoveryCalls.stopped sizes (fun _=>0) (startOutput x).tapes) := by
  obtain ⟨n0,hn0,hready⟩ := load_ready x hx
  have hv := loaded_valid x hx
  have hw := loaded_width x hx
  cases ha : (loaded x).outer.flag
  · have h0 := hready.call sizes programs 0 next 1 10 (by
      intro q
      change some (if readTapeBit [(loaded x).outer.flag] 0 then (2 : Fin 11) else 10)=some 10
      change some (if (loaded x).outer.flag then (2 : Fin 11) else 10)=some 10
      rw [ha]; rfl)
    refine ⟨n0+1+2,?_,?_⟩
    · nlinarith only [hn0,show 0<(x.width+1)^2 by positivity]
    · have ho : startOutput x=RecoveryMarkerFlags.answered (loaded x) false := by
        simp only [startOutput,ha,Bool.false_eq_true,ite_false]
      rw [ho]
      exact h0.trans (false_stop _)
  · have h0 := hready.call sizes programs 0 next 1 2 (by
      intro q
      change some (if readTapeBit [(loaded x).outer.flag] 0 then (2 : Fin 11) else 10)=some 2
      change some (if (loaded x).outer.flag then (2 : Fin 11) else 10)=some 2
      rw [ha]; rfl)
    obtain ⟨n1,hn1,h1⟩ := leading_trace (loaded x) hv
    rw [hw] at hn1
    refine ⟨n0+1+n1,?_,?_⟩
    · nlinarith only [hn0,hn1,show 0<(x.width+1)^2 by positivity]
    · have ho : startOutput x=leadingOutput (loaded x) := by
        simp only [startOutput,ha,ite_true]
      rw [ho]
      exact h0.trans h1

end NearCubicWires.RepairOrdinary.RecoveryMarker
