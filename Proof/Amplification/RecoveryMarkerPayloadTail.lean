import Proof.Amplification.RecoveryMarkerPayloadGraph

/-! Both physical polarity branches execute their existing whole checker
and pay the final call return. The accepted branch retains one shared
valuation in the compact semantic result. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def entryCfg (marker : MarkerState) (x : CheckState) :=
  if marker.outer.result then cfg marker x (RecoveryCalls.code sizes 1 flatMachine.start)
  else cfg marker x (RecoveryCalls.code sizes 2 nestedMachine.start)

theorem tail_trace (marker : MarkerState) (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (hl : limit ≤ 3*(x.inner.base.state.bits.length+1))
    (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest)) :
    ∃ n,∃ outHeads : Fin 212→Nat,∃ outTapes : Fin 212→List Bool,
      n ≤ payloadBudget x.inner.base.state.bits.length+1 ∧
      Timed machine n (entryCfg marker x) (RecoveryCalls.stopped sizes outHeads outTapes) ∧
      outHeads 107=0 ∧ outTapes 107=[answer marker x word innerBits outerBits] ∧
      (outTapes 107=[true] → payloadMeaning x marker.outer.result) := by
  cases hm : marker.outer.result
  · obtain ⟨r,hr,_,hh,ht,hs⟩ := nested_run marker x limit word innerBits outerBits innerPre outerPre hx hl table rest hp
    obtain ⟨n,hn,h⟩ := stop_receipt sizes programs 0 next 2 (payloadBudget x.inner.base.state.bits.length)
      (cfg marker x nestedMachine.start) r hr (by rfl)
    refine ⟨n,r.final.heads,r.final.tapes,hn,?_,hh,?_,?_⟩
    · simp only [entryCfg,hm,Bool.false_eq_true,ite_false]
      exact h
    · simp only [answer,hm,Bool.false_eq_true,ite_false]
      exact ht
    · exact hs
  · obtain ⟨r,hr,_,hh,ht,hs⟩ := flat_bounded_run marker x limit word innerBits outerBits innerPre outerPre hx hl table rest hp
    obtain ⟨n,hn,h⟩ := stop_receipt sizes programs 0 next 1 (payloadBudget x.inner.base.state.bits.length)
      (cfg marker x flatMachine.start) r hr (by rfl)
    refine ⟨n,r.final.heads,r.final.tapes,hn,?_,hh,?_,?_⟩
    · simp only [entryCfg,hm,ite_true]
      exact h
    · simp only [answer,hm,ite_true]
      exact ht
    · exact hs

end NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
