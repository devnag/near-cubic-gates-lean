import Proof.Amplification.RecoveryCanonicalMeaning

/-! Canonical marker certificates execute the same full compact branch
and therefore the physical disjunction of the all-code checker. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem compact_accept (code : Nat) (c : Certificate) (hc : Fits code c) (hsel : selected c=c)
    (htags : RawSyntaxCertificate.tagsValid c.view=true)
    (hcheck : markerCheck (RawSyntaxCertificate.project c.view) c.table c.inner c.outer=true) :
    ∃ r,runFrom RecoveryAllCode.machine (RecoveryAllCode.budget (RecoveryColdView.width code.bits))
      (RecoveryAllCode.cfg (canonicalState code c) RecoveryAllCode.machine.start)=some r ∧
      r.final.heads 93=0 ∧ r.final.tapes 93=[true] := by
  let x := canonicalState code c
  have hx := canonical_prepared code c hc
  have hw : x.width=RecoveryColdView.width code.bits := RecoveryColdAllCode.state_width _ _ _ _ _ _ _
  obtain ⟨flat,payload,tail,hformula,ha⟩ := marker_case c hsel hcheck
  have hcode : RecoveryMarker.outerCode x.marker=Encodable.encode (RecoveryMarker.formula flat payload tail) := by
    have hc0 : x.code=code := RecoveryColdAllCode.state_code _ _ _ _ _ _ _
    exact hx.code_eq.trans (hc0.trans ((canonical_code code c hc htags).trans (congrArg Encodable.encode hformula)))
  have hp : readList x.compact.inner.base.extra.cap (readEntry x.compact.inner.base.state.bits.length)
      (witness code c)=some (c.table,suffix code c) := by
    change readList (RecoveryColdView.limit code.bits) (readEntry (RecoveryColdHeader.zeroWord code.bits).length)
      (witness code c)=_
    rw [RecoveryColdHeader.zero_length]
    exact valuation_parse code c hc
  have hi : readMany (readRow x.compact.inner.base.state.bits.length) x.compact.innerTotal (innerBuffer code c)=
      some (c.inner,innerRest code c) := by
    change readMany (readRow (RecoveryColdHeader.zeroWord code.bits).length) c.inner.length (innerBuffer code c)=_
    rw [RecoveryColdHeader.zero_length]
    exact inner_rows code c hc
  have ho : readMany (readRow x.compact.outer.data.outer.base.state.bits.length) x.compact.outer.total (outerBuffer code c)=
      some (c.outer,outerRest code c) := by
    change readMany (readRow (RecoveryColdHeader.zeroWord code.bits).length) c.outer.length (outerBuffer code c)=_
    rw [RecoveryColdHeader.zero_length]
    exact outer_rows code c hc
  obtain ⟨branch,hbranch,_,hbh,hbt⟩ := RecoveryCompactBranch.canonical_compact_run x.marker x.compact
    (RecoveryColdView.limit code.bits) (witness code c) (innerBuffer code c) (outerBuffer code c) [] []
    hx.compact_ready hx.limit_bound hx.marker_valid hx.marker_width hx.committed_zero hx.count_zero
    flat payload tail hcode c.table (suffix code c) c.inner c.outer (innerRest code c) (outerRest code c) hp hi ho ha
  rw [hx.width_eq] at hbranch
  obtain ⟨r,hr,_,hrh,hrt⟩ := RecoveryAllCode.accept_right x (RecoveryColdView.limit code.bits)
    (witness code c) (c.table.length*(RecoveryColdView.width code.bits+2)+1)
    (innerBuffer code c) (outerBuffer code c) [] [] hx branch hbranch hbh hbt
  rw [hw] at hr
  exact ⟨r,hr,hrh,hrt⟩

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
