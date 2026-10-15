import Proof.Amplification.RecoveryCanonicalPayloadAnswer

/-! Canonical completeness of actual marker-field copying and selected
table checking. The original marker controls polarity and all three scalar
values; no canonical reencoding of the saved padded words is required. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
open LocalBitMultitape RecoveryMarkerHandoff RadixSemantics
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_payload_run (original : MarkerState) (x : CheckState) (limit : Nat)
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
    (hcheck : certificateAnswer flat (RecoveryMarker.tailCommitted tail) (RecoveryMarker.tailCount tail)
      (value payload) table innerRows outerRows=true) :
    ∃ r,runFrom machine (budget x.inner.base.state.bits.length)
        (cfg (RecoveryMarker.output original) x machine.start)=some r ∧
      r.steps ≤ 268435456*(x.inner.base.state.bits.length+1)^3 ∧ r.final.heads 107=0 ∧ r.final.tapes 107=[true] := by
  obtain ⟨p,c,n,hpl,hcl,hnl,hpv,hcv,hnv,hfields⟩ := RecoveryMarker.canonical_fields original hm hc0 hn0
    flat payload tail hcode
  let words : Fin 3→List Bool := ![p,c,n]
  have hwords : ∀ j,(words j).length=x.inner.base.state.bits.length := by
    intro j
    fin_cases j
    · exact hpl.trans hw
    · exact hcl.trans hw
    · exact hnl.trans hw
  have hs := RecoveryMarker.field_sources (RecoveryMarker.output original) flat p c n hfields
  obtain ⟨r,hr,hb,hh,ht,_⟩ := payload_run (RecoveryMarker.output original) x limit
    word innerBits outerBits innerPre outerPre hx hl words hwords hs table rest hp
  have hflat : (RecoveryMarker.output original).outer.result=flat := congrArg RecoveryMarkerMetadata.Fields.flat hfields
  have hanswer := answer_certificate (RecoveryMarker.output original) x words word innerBits outerBits
    table rest innerRows outerRows innerRest outerRest hp hi ho
  change answer (RecoveryMarker.output original) (output x words) word innerBits outerBits=
    certificateAnswer (RecoveryMarker.output original).outer.result (value c) (value n) (value p) table innerRows outerRows at hanswer
  rw [hflat,hcv,hnv,hpv,hcheck] at hanswer
  exact ⟨r,hr,hb,hh,by rw [ht,hanswer]⟩

end NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
