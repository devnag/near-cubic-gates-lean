import Proof.Amplification.RecoveryMarkerPayloadFront

/-! Complete actual compact payload execution: copy the saved fields,
branch on physical polarity, execute the selected whole flat/nested table
checker, and return its answer with the exact common valuation meaning. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem payload_run (marker : MarkerState) (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (hl : limit ≤ 3*(x.inner.base.state.bits.length+1))
    (words : Fin 3→List Bool) (hw : ∀ j,(words j).length=x.inner.base.state.bits.length)
    (hs : ∀ j,marker.tapes (RecoveryMarkerSave.target j)=frame (words j))
    (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest)) :
    ∃ r,runFrom machine (budget x.inner.base.state.bits.length) (cfg marker x machine.start)=some r ∧
      r.steps ≤ 268435456*(x.inner.base.state.bits.length+1)^3 ∧
      r.final.heads 107=0 ∧ r.final.tapes 107=[answer marker (output x words) word innerBits outerBits] ∧
      (r.final.tapes 107=[true] → payloadMeaning (output x words) marker.outer.result) := by
  obtain ⟨n0,hn0,h0⟩ := front_trace marker x limit word innerBits outerBits innerPre outerPre hx words hw hs
  have hy := output_prepared x limit word innerBits outerBits innerPre outerPre hx words hw
  obtain ⟨n1,outHeads,outTapes,hn1,h1,hh,ht,hsound⟩ := tail_trace marker (output x words) limit
    word innerBits outerBits innerPre outerPre hy hl table rest hp
  have h := h0.trans h1
  obtain ⟨r,hr,hf,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb : n0+n1 ≤ budget x.inner.base.state.bits.length := by
    change n1 ≤ payloadBudget x.inner.base.state.bits.length+1 at hn1
    unfold budget
    omega
  have hm := runFrom_moreFuel machine (n0+n1) (budget x.inner.base.state.bits.length-(n0+n1)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  refine ⟨r,hm,(hsteps.le.trans hb).trans (budget_le _),?_,?_,?_⟩
  · rw [hf]
    exact hh
  · rw [hf]
    exact ht
  · rw [hf]
    exact hsound

end NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
