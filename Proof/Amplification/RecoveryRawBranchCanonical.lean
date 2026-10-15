import Proof.Amplification.RecoveryRawBranchCanonicalFields

/-! Bounded canonical completeness for both raw/default cases of the same
executed controller. The SAT case consumes the one canonical valuation;
the malformed-tag case takes the actual accepted-empty default. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_default_run (x : State) (word pre suffix : List Bool) (view : RawSyntaxCertificate.View)
    (hx : x.view.Valid) (hs : x.view.inner.stream.source=frame word)
    (hp : x.view.inner.stream.pos=2*pre.length)
    (heval : RecoveryRawSAT.Inv x.view.width x.eval.valuation.cap 0 0 word x.eval)
    (hw : word=pre++(RawSyntaxCertificate.pack x.view.width view++suffix))
    (hc : RawSyntaxCertificate.check (RecoveryRawViewBody.code x.view) view=true)
    (hn : view.length ≤ x.view.limit) (hcounts : ∀ clause∈view,clause.length ≤ x.view.limit)
    (ht : RawSyntaxCertificate.tagsValid view=false) :
    ∃ r,runFrom machine (budget x.view.width) (cfg x 0 machine.start)=some r ∧
      r.steps ≤ 1073741824*(x.view.width+1)^4 ∧ r.final.heads 93=0 ∧ r.final.tapes 93=[true] := by
  have ha := RecoveryRawViewEntry.canonical_answer x.view word pre suffix view hx hs hp hw hc hn hcounts
  have hf := (checked_flags x word pre.length view hx hs hp hc ha).1
  have ha' : answer x word pre.length=true := by
    simp only [answer,ha,Bool.true_and,hf,ht,Bool.and_false,Bool.false_eq_true,ite_false]
  obtain ⟨r,hr,hb,hh,ho⟩ := raw_run x word pre.length hx hs hp heval
  rw [ha'] at ho
  exact ⟨r,hr,hb,hh,ho⟩

theorem canonical_sat_run (x : State) (word pre suffix : List Bool) (view : RawSyntaxCertificate.View)
    (formula : EncodedCNF) (table : FiniteValuation.Table) (rest : List Bool)
    (hx : x.view.Valid) (hs : x.view.inner.stream.source=frame word)
    (hp : x.view.inner.stream.pos=2*pre.length)
    (heval : RecoveryRawSAT.Inv x.view.width x.eval.valuation.cap 0 0 word x.eval)
    (hw : word=pre++(RawSyntaxCertificate.pack x.view.width view++suffix))
    (hc : RawSyntaxCertificate.check (RecoveryRawViewBody.code x.view) view=true)
    (hn : view.length ≤ x.view.limit) (hcounts : ∀ clause∈view,clause.length ≤ x.view.limit)
    (ht0 : x.view.inner.tags=true) (hb0 : x.view.inner.bounded=true)
    (ht : RawSyntaxCertificate.tagsValid view=true)
    (hi : RecoveryRawViewLoop.boundedView (RadixSemantics.value x.view.inner.bound) view=true)
    (hcode : x.eval.code=Encodable.encode formula) (hlen : formula.length=view.length)
    (hparse : readList x.eval.valuation.cap (readEntry x.view.width) word=some (table,rest))
    (hcheck : FiniteValuation.check ⟨formula,0,0⟩ table=true) :
    ∃ r,runFrom machine (budget x.view.width) (cfg x 0 machine.start)=some r ∧
      r.steps ≤ 1073741824*(x.view.width+1)^4 ∧ r.final.heads 93=0 ∧ r.final.tapes 93=[true] := by
  have ha := RecoveryRawViewEntry.canonical_answer x.view word pre suffix view hx hs hp hw hc hn hcounts
  obtain ⟨hft,hfb⟩ := checked_flags x word pre.length view hx hs hp hc ha
  have hsatisfied : evaluated x word pre.length=true := by
    unfold evaluated
    rw [canonical_total x word pre suffix view hw hn,←hlen,hcode]
    exact RecoveryRawSATTable.canonical_answer x.view.width x.eval.valuation.cap 0 0 word formula table rest hparse hcheck
  have ha' : answer x word pre.length=true := by
    simp only [answer,ha,Bool.true_and,hft,hfb,ht0,hb0,ht,hi,ite_true,hsatisfied]
  obtain ⟨r,hr,hb,hh,ho⟩ := raw_run x word pre.length hx hs hp heval
  rw [ha'] at ho
  exact ⟨r,hr,hb,hh,ho⟩

end NearCubicWires.RepairOrdinary.RecoveryRawBranch
