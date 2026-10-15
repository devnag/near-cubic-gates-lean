import Proof.Amplification.RecoveryCanonicalPayloadRun

/-! Canonical completeness at the original-code entry of the very same
prepared compact branch. All marker parsing, field copies, selected table
checking and call returns occur in its actual execution. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCompactBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff RadixSemantics
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_compact_run (original : MarkerState) (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (hl : limit ≤ 3*(x.inner.base.state.bits.length+1))
    (hm : original.Valid) (hw : original.width=x.inner.base.state.bits.length)
    (hc0 : (RecoveryMarkerMetadata.read original).committed=frame (List.replicate original.width false))
    (hn0 : (RecoveryMarkerMetadata.read original).count=frame (List.replicate original.width false))
    (flat : Bool) (payload : List Bool) (tail : RecoveryMarker.TailWords)
    (hcode : RecoveryMarker.outerCode original=Encodable.encode (RecoveryMarker.formula flat payload tail))
    (table : FiniteValuation.Table) (rest : List Bool)
    (innerRows outerRows : List Row) (innerRest outerRest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest))
    (hi : readMany (readRow x.inner.base.state.bits.length) x.innerTotal innerBits=some (innerRows,innerRest))
    (ho : readMany (readRow x.outer.data.outer.base.state.bits.length) x.outer.total outerBits=some (outerRows,outerRest))
    (hcheck : RecoveryMarkerPayload.certificateAnswer flat (RecoveryMarker.tailCommitted tail) (RecoveryMarker.tailCount tail)
      (value payload) table innerRows outerRows=true) :
    ∃ r,runFrom machine (budget x.inner.base.state.bits.length) (cfg original x machine.start)=some r ∧
      r.steps ≤ 1073741824*(x.inner.base.state.bits.length+1)^3 ∧ r.final.heads 107=0 ∧ r.final.tapes 107=[true] := by
  obtain ⟨n0,hn0',h0⟩ := front_trace original x hm
  have ha := RecoveryMarker.canonical_marker original flat payload tail hcode
  simp only [entryCfg,ha,ite_true] at h0
  obtain ⟨base,hr,_,hh,ht⟩ := RecoveryMarkerPayload.canonical_payload_run original x limit
    word innerBits outerBits innerPre outerPre hx hl hm hw hc0 hn0 flat payload tail hcode
    table rest innerRows outerRows innerRest outerRest hp hi ho hcheck
  obtain ⟨n1,hn1,h1⟩ := stop_receipt sizes programs 0 next 1 (RecoveryMarkerPayload.budget x.inner.base.state.bits.length)
    (cfg (RecoveryMarker.output original) x RecoveryMarkerPayload.machine.start) base hr (by rfl)
  have h := h0.trans h1
  obtain ⟨r,hrun,hf,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb : n0+n1 ≤ budget x.inner.base.state.bits.length := by
    rw [hw] at hn0'
    unfold budget
    omega
  have hmrun := runFrom_moreFuel machine (n0+n1) (budget x.inner.base.state.bits.length-(n0+n1)) _ r hrun
  rw [Nat.add_sub_of_le hb] at hmrun
  refine ⟨r,hmrun,(hsteps.le.trans hb).trans (budget_le _),?_,?_⟩
  · rw [hf]; exact hh
  · rw [hf]; exact ht

end NearCubicWires.RepairOrdinary.RecoveryCompactBranch
