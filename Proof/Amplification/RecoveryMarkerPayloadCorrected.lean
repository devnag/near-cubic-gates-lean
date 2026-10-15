import Proof.Amplification.RecoveryMarkerPayloadWhole

/-! Actual accepted marker metadata feeds the actual selected payload
execution. Every accepting payload run proves the literal corrected SAT
predicate for the original code, using its exact decoded marker form. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff RadixSemantics
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem accepted_payload_run (original : MarkerState) (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (hl : limit ≤ 3*(x.inner.base.state.bits.length+1))
    (hm : original.Valid) (hw : original.width=x.inner.base.state.bits.length)
    (hc0 : (RecoveryMarkerMetadata.read original).committed=frame (List.replicate original.width false))
    (hn0 : (RecoveryMarkerMetadata.read original).count=frame (List.replicate original.width false))
    (ha : (RecoveryMarker.output original).inner.present=true)
    (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest)) :
    ∃ r,runFrom machine (budget x.inner.base.state.bits.length)
        (cfg (RecoveryMarker.output original) x machine.start)=some r ∧
      r.steps ≤ 268435456*(x.inner.base.state.bits.length+1)^3 ∧
      r.final.heads 107=0 ∧
      (∃ bit,r.final.tapes 107=[bit]) ∧
      (r.final.tapes 107=[true] → correctedSat (RecoveryMarker.outerCode original)=true) := by
  obtain ⟨flat,payload,committed,count,tail,hpwidth,hcwidth,hnwidth,hcode,hcomm,hcount,hfields⟩ :=
    RecoveryMarker.accepted_fields original hm hc0 hn0 ha
  let words : Fin 3→List Bool := ![payload,committed,count]
  have hwords : ∀ j,(words j).length=x.inner.base.state.bits.length := by
    intro j
    fin_cases j
    · exact hpwidth.trans hw
    · exact hcwidth.trans hw
    · exact hnwidth.trans hw
  have hs := RecoveryMarker.field_sources (RecoveryMarker.output original) flat payload committed count hfields
  obtain ⟨r,hr,hb,hh,ht,hsound⟩ := payload_run (RecoveryMarker.output original) x limit
    word innerBits outerBits innerPre outerPre hx hl words hwords hs table rest hp
  refine ⟨r,hr,hb,hh,⟨_,ht⟩,?_⟩
  intro haccept
  obtain ⟨codes,hd,hmeaning⟩ := hsound haccept
  have hflat : (RecoveryMarker.output original).outer.result=flat := congrArg RecoveryMarkerMetadata.Fields.flat hfields
  change (if (RecoveryMarker.output original).outer.result then CanonicalBinary.decodeBalancedList (value payload)
    else BalancedCNFSATEncoding.decodeNestedBalancedCNFPayload (value payload))=some codes at hd
  rw [hflat] at hd
  change compactMeaning ⟨_,value committed,value count⟩ at hmeaning
  rw [hcomm,hcount] at hmeaning
  exact RecoveryMarker.marker_corrected (RecoveryMarker.outerCode original) flat payload tail codes hcode hd hmeaning

end NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
