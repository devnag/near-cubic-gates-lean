import Proof.Amplification.RecoveryMarkerGraph

/-! Bounded actual marker callees and fixed terminal writes. These
interfaces retain exact output tapes while exposing the actual paid time. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem atom_ready (which : Fin 3) (x : State) (hx : x.Valid) :
    ∃ n,n ≤ RecoveryMarkerAtom.budget x.width ∧
      ReadyRun (RecoveryMarkerAtom.machine which) n x.tapes (RecoveryMarkerAtom.output which x).tapes := by
  obtain ⟨r,hr,hs,hh,ht⟩ := RecoveryMarkerAtom.atom_run which x hx
  have h := ready_of_run (RecoveryMarkerAtom.machine which) (RecoveryMarkerAtom.budget x.width) x.tapes r hr hh
  rw [ht] at h
  exact ⟨r.steps,hs,h⟩

theorem load_ready (x : State) (hx : x.Valid) :
    ∃ n,n ≤ 524288*(x.width+1)^2 ∧ ReadyRun loadMachine n x.tapes (loaded x).tapes := by
  obtain ⟨r,hr,hf,hs⟩ := load_run x hx
  have hh : ∀ i,r.final.heads i=0 := by intro i; rw [hf]; rfl
  have h := ready_of_run loadMachine (loadCost x) x.tapes r hr hh
  rw [hf] at h
  exact ⟨r.steps,hs.trans (load_cost_bound x hx),h⟩

theorem true_stop (x : State) :
    Timed machine 2 (controlConfig (RecoveryCalls.code sizes 9)
      (initialConfiguration (programs 9) x.tapes))
      (RecoveryCalls.stopped sizes (fun _=>0) (RecoveryMarkerFlags.answered x true).tapes) :=
  (RecoveryMarkerFlags.answer_ready x true).stop sizes programs 0 next 9 (by intro q; rfl)

theorem false_stop (x : State) :
    Timed machine 2 (controlConfig (RecoveryCalls.code sizes 10)
      (initialConfiguration (programs 10) x.tapes))
      (RecoveryCalls.stopped sizes (fun _=>0) (RecoveryMarkerFlags.answered x false).tapes) :=
  (RecoveryMarkerFlags.answer_ready x false).stop sizes programs 0 next 10 (by intro q; rfl)

def outerOutput (x : State) := RecoveryMarkerFlags.answered (outerStep x) (!(outerStep x).outer.flag)

theorem outer_trace (x : State) (hx : x.Valid) :
    ∃ n,n ≤ 262144*(x.width+1)^2+3 ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 8) (initialConfiguration (programs 8) x.tapes))
      (RecoveryCalls.stopped sizes (fun _=>0) (outerOutput x).tapes) := by
  have hready := outer_ready x hx.2.1
  have hc := RecoveryStoredListCell.time_bound x.outer.bits
  unfold RecoveryStoredListCell.budget at hc
  rw [hx.2.2] at hc
  cases ha : (outerStep x).outer.flag
  · have h0 := hready.call sizes programs 0 next 8 9 (by
      intro q
      change some (if readTapeBit [(outerStep x).outer.flag] 0 then (10 : Fin 11) else 9)=some 9
      change some (if (outerStep x).outer.flag then (10 : Fin 11) else 9)=some 9
      rw [ha]; rfl)
    refine ⟨(RecoveryStoredListCell.time x.outer.bits+1)+2,by omega,?_⟩
    have ho : outerOutput x=RecoveryMarkerFlags.answered (outerStep x) true := by
      simp only [outerOutput,ha,Bool.not_false]
    rw [ho]
    exact h0.trans (true_stop (outerStep x))
  · have h0 := hready.call sizes programs 0 next 8 10 (by
      intro q
      change some (if readTapeBit [(outerStep x).outer.flag] 0 then (10 : Fin 11) else 9)=some 10
      change some (if (outerStep x).outer.flag then (10 : Fin 11) else 9)=some 10
      rw [ha]; rfl)
    refine ⟨(RecoveryStoredListCell.time x.outer.bits+1)+2,by omega,?_⟩
    have ho : outerOutput x=RecoveryMarkerFlags.answered (outerStep x) false := by
      simp only [outerOutput,ha,Bool.not_true]
    rw [ho]
    exact h0.trans (false_stop (outerStep x))

end NearCubicWires.RepairOrdinary.RecoveryMarker
