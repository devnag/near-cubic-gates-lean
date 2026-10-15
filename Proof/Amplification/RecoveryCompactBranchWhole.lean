import Proof.Amplification.RecoveryCompactBranchFront

/-! Whole prepared compact branch from the original encoded query. The
actual marker replay chooses payload checking or a physical false return;
every accepting result proves corrected SAT for that same original code. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCompactBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem compact_run (original : MarkerState) (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (hl : limit ≤ 3*(x.inner.base.state.bits.length+1))
    (hm : original.Valid) (hw : original.width=x.inner.base.state.bits.length)
    (hc0 : (RecoveryMarkerMetadata.read original).committed=frame (List.replicate original.width false))
    (hn0 : (RecoveryMarkerMetadata.read original).count=frame (List.replicate original.width false))
    (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest)) :
    ∃ r,runFrom machine (budget x.inner.base.state.bits.length) (cfg original x machine.start)=some r ∧
      r.steps ≤ 1073741824*(x.inner.base.state.bits.length+1)^3 ∧ r.final.heads 107=0 ∧
      (∃ bit,r.final.tapes 107=[bit]) ∧
      (r.final.tapes 107=[true] → correctedSat (RecoveryMarker.outerCode original)=true) := by
  obtain ⟨n0,hn0',h0⟩ := front_trace original x hm
  obtain ⟨n1,outHeads,outTapes,hn1,h1,hh,ht,hs⟩ := tail_trace original x limit
    word innerBits outerBits innerPre outerPre hx hl hm hw hc0 hn0 table rest hp
  have h := h0.trans h1
  have hb : n0+n1 ≤ budget x.inner.base.state.bits.length := by
    rw [hw] at hn0'
    unfold budget
    omega
  exact finish_run x.inner.base.state.bits.length (RecoveryMarker.outerCode original) (n0+n1)
    (cfg original x machine.start) outHeads outTapes h hb hh ht hs

end NearCubicWires.RepairOrdinary.RecoveryCompactBranch
