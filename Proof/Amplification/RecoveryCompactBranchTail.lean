import Proof.Amplification.RecoveryCompactBranchGraph

/-! The compact branch's actual accepting-marker continuation and its
physical rejecting-marker return. Both expose the literal corrected SAT
soundness needed by the final all-code verifier. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCompactBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def entryCfg (marker : MarkerState) (x : CheckState) :=
  if marker.inner.present then cfg marker x (RecoveryCalls.code sizes 1 RecoveryMarkerPayload.machine.start)
  else cfg marker x (RecoveryCalls.code sizes 2 (RecoveryBankPair.flagMachine (107 : Fin 212) 28).start)

theorem tail_trace (original : MarkerState) (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (hl : limit ≤ 3*(x.inner.base.state.bits.length+1))
    (hm : original.Valid) (hw : original.width=x.inner.base.state.bits.length)
    (hc0 : (RecoveryMarkerMetadata.read original).committed=frame (List.replicate original.width false))
    (hn0 : (RecoveryMarkerMetadata.read original).count=frame (List.replicate original.width false))
    (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest)) :
    ∃ n,∃ outHeads : Fin 212→Nat,∃ outTapes : Fin 212→List Bool,
      n ≤ RecoveryMarkerPayload.budget x.inner.base.state.bits.length+2 ∧
      Timed machine n (entryCfg (RecoveryMarker.output original) x) (RecoveryCalls.stopped sizes outHeads outTapes) ∧
      outHeads 107=0 ∧ (∃ bit,outTapes 107=[bit]) ∧
      (outTapes 107=[true] → correctedSat (RecoveryMarker.outerCode original)=true) := by
  cases ha : (RecoveryMarker.output original).inner.present
  · have hfalse : tapes (RecoveryMarker.output original) x 28=[false] := by
      change [(RecoveryMarker.output original).inner.present]=[false]
      rw [ha]
    obtain ⟨r,hr,_,hh,ht⟩ := RecoveryBankPair.flag_run (107 : Fin 212) 28 (heads x)
      (tapes (RecoveryMarker.output original) x) x.inner.base.valid false rfl rfl rfl hfalse
    obtain ⟨n,hn,h⟩ := stop_receipt sizes programs 0 next 2 1
      (cfg (RecoveryMarker.output original) x (programs 2).start) r hr (by rfl)
    have ht0 : r.final.tapes 107=[false] := by rw [ht,Function.update_self]
    refine ⟨n,r.final.heads,r.final.tapes,by omega,?_,?_,⟨false,ht0⟩,?_⟩
    · simp only [entryCfg,ha,Bool.false_eq_true,ite_false]
      exact h
    · rw [hh]
      rfl
    · intro haccept
      have he := List.singleton_inj.mp (ht0.symm.trans haccept)
      contradiction
  · obtain ⟨r,hr,_,hh,ht,hs⟩ := RecoveryMarkerPayload.accepted_payload_run original x limit
      word innerBits outerBits innerPre outerPre hx hl hm hw hc0 hn0 ha table rest hp
    obtain ⟨n,hn,h⟩ := stop_receipt sizes programs 0 next 1 (RecoveryMarkerPayload.budget x.inner.base.state.bits.length)
      (cfg (RecoveryMarker.output original) x RecoveryMarkerPayload.machine.start) r hr (by rfl)
    refine ⟨n,r.final.heads,r.final.tapes,by omega,?_,hh,ht,hs⟩
    simp only [entryCfg,ha,ite_true]
    exact h

end NearCubicWires.RepairOrdinary.RecoveryCompactBranch
