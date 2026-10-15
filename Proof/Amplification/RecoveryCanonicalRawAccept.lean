import Proof.Amplification.RecoveryCanonicalRawFields

/-! Canonical accepted-default and raw-SAT branches of the same all-code
machine, using the original full valuation word and exact input code. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem default_accept (code : Nat) (c : Certificate) (hc : Fits code c)
    (htags : RawSyntaxCertificate.tagsValid c.view=false) :
    ∃ r,runFrom RecoveryAllCode.machine (RecoveryAllCode.budget (RecoveryColdView.width code.bits))
      (RecoveryAllCode.cfg (canonicalState code c) RecoveryAllCode.machine.start)=some r ∧
      r.final.heads 93=0 ∧ r.final.tapes 93=[true] := by
  let x := canonicalState code c
  have hx := canonical_prepared code c hc
  have he : x.code=code := RecoveryColdAllCode.state_code _ _ _ _ _ _ _
  have hcheck : RawSyntaxCertificate.check (RecoveryRawViewBody.code x.raw.view) c.view=true := by
    rw [hx.raw_code,he]
    exact hc.1
  obtain ⟨hn,hnc⟩ := raw_counts code c hc
  obtain ⟨branch,hbranch,_,hbh,hbt⟩ := RecoveryRawBranch.canonical_default_run x.raw
    (witness code c) (valuationPrefix code c) (tableWords code c) c.view
    hx.raw_valid hx.raw_source (raw_position code c) hx.raw_eval (raw_word code c) hcheck hn hnc htags
  obtain ⟨r,hr,_,hrh,hrt⟩ := RecoveryAllCode.accept_left x (RecoveryColdView.limit code.bits)
    (witness code c) (c.table.length*(RecoveryColdView.width code.bits+2)+1)
    (innerBuffer code c) (outerBuffer code c) [] [] hx branch hbranch hbh hbt
  rw [canonical_width code c] at hr
  exact ⟨r,hr,hrh,hrt⟩

theorem raw_accept (code : Nat) (c : Certificate) (hc : Fits code c)
    (htags : RawSyntaxCertificate.tagsValid c.view=true)
    (hraw : wellSizedCNFEncoding code (RawSyntaxCertificate.project c.view)=true)
    (hsat : FiniteValuation.check ⟨RawSyntaxCertificate.project c.view,0,0⟩ c.table=true) :
    ∃ r,runFrom RecoveryAllCode.machine (RecoveryAllCode.budget (RecoveryColdView.width code.bits))
      (RecoveryAllCode.cfg (canonicalState code c) RecoveryAllCode.machine.start)=some r ∧
      r.final.heads 93=0 ∧ r.final.tapes 93=[true] := by
  let x := canonicalState code c
  have hx := canonical_prepared code c hc
  have he : x.code=code := RecoveryColdAllCode.state_code _ _ _ _ _ _ _
  have hcheck : RawSyntaxCertificate.check (RecoveryRawViewBody.code x.raw.view) c.view=true := by
    rw [hx.raw_code,he]
    exact hc.1
  have hbound : RecoveryRawViewLoop.boundedView (RadixSemantics.value x.raw.view.inner.bound) c.view=true := by
    rw [hx.raw_bound,he]
    exact raw_bounded code c hraw
  have hp : readList x.raw.eval.valuation.cap (readEntry x.raw.view.width) (witness code c)=
      some (c.table,suffix code c) := by
    change readList (RecoveryColdView.limit code.bits) (readEntry x.width) (witness code c)=_
    rw [canonical_width code c]
    exact valuation_parse code c hc
  have hcode : x.raw.eval.code=Encodable.encode (RawSyntaxCertificate.project c.view) :=
    he.trans (canonical_code code c hc htags)
  have hlen : (RawSyntaxCertificate.project c.view).length=c.view.length := List.length_map _
  obtain ⟨hn,hnc⟩ := raw_counts code c hc
  obtain ⟨branch,hbranch,_,hbh,hbt⟩ := RecoveryRawBranch.canonical_sat_run x.raw
    (witness code c) (valuationPrefix code c) (tableWords code c) c.view
    (RawSyntaxCertificate.project c.view) c.table (suffix code c)
    hx.raw_valid hx.raw_source (raw_position code c) hx.raw_eval (raw_word code c) hcheck hn hnc
    hx.raw_tags (by rfl) htags hbound hcode hlen hp hsat
  obtain ⟨r,hr,_,hrh,hrt⟩ := RecoveryAllCode.accept_left x (RecoveryColdView.limit code.bits)
    (witness code c) (c.table.length*(RecoveryColdView.width code.bits+2)+1)
    (innerBuffer code c) (outerBuffer code c) [] [] hx branch hbranch hbh hbt
  rw [canonical_width code c] at hr
  exact ⟨r,hr,hrh,hrt⟩

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
