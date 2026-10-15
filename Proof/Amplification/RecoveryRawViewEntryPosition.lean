import Proof.Amplification.RecoverySATBound

/-! Canonical end position of the existing raw-view entry. The cold table
scanner reuses this executed grammar reader on a separate bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding RepairSource.RecoveryOracle
open CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_position (x : State) (word pre suffix : List Bool) (view : RawSyntaxCertificate.View)
    (hx : x.Valid) (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*pre.length)
    (hword : word=pre++(RawSyntaxCertificate.pack x.width view++suffix))
    (hcode : RawSyntaxCertificate.check (RecoveryRawViewBody.code x) view=true)
    (hlen : view.length≤x.limit) (hcounts : ∀ clause∈view,clause.length≤x.limit) :
    (output x word pre.length).1.inner.stream.pos=
      2*(pre.length+(RawSyntaxCertificate.pack x.width view).length) ∧
    (output x word pre.length).1.inner.stream.source=frame word := by
  let rest := view.flatMap (RawSyntaxCertificate.packClause x.width)++suffix
  have hparse : readCount x.limit (word.drop pre.length)=some (view.length,rest) := by
    rw [hword,List.drop_left]
    simpa only [RawSyntaxCertificate.pack,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,rest] using
      readCount_pack x.limit view.length hlen rest
  let before := pre++List.replicate view.length true++[false]
  have hv := cursor_valid (flagged x false) word pre.length view.length (flagged_valid x false hx) hs hp
  have hw : word=before++(view.flatMap (RawSyntaxCertificate.packClause x.width)++suffix) := by
    simpa only [before,RawSyntaxCertificate.pack,List.append_assoc] using hword
  have hpos : (cursor (flagged x false) pre.length view.length).pos=before.length := by
    simp only [cursor,before,List.length_append,List.length_replicate,List.length_singleton]
  have hc : RecoveryRawViewBody.code (cursor (flagged x false) pre.length view.length).data=Encodable.encode view :=
    ((RawSyntaxCertificate.check_iff _ _).mp hcode).symm
  have ho := RecoveryRawViewLoop.canonical_out x.width word before suffix view
    (cursor (flagged x false) pre.length view.length) hv hw hpos hc hcounts
  have hi := RecoveryRawViewLoop.out_inv x.width view.length word
    (cursor (flagged x false) pre.length view.length) hv ho.1
  rw [output_some x word pre.length view.length rest hparse]
  refine ⟨?_,hi.2.2.1⟩
  change (RecoveryRawViewLoop.out word view.length (cursor (flagged x false) pre.length view.length)).2.data.inner.stream.pos=_
  rw [hi.2.2.2,ho.2.2]
  simp only [before,RawSyntaxCertificate.pack,List.length_append,List.length_replicate,List.length_singleton]
  omega

theorem canonical_run_position (x : State) (word pre suffix : List Bool) (view : RawSyntaxCertificate.View)
    (hx : x.Valid) (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*pre.length)
    (hword : word=pre++(RawSyntaxCertificate.pack x.width view++suffix))
    (hcode : RawSyntaxCertificate.check (RecoveryRawViewBody.code x) view=true)
    (hlen : view.length≤x.limit) (hcounts : ∀ clause∈view,clause.length≤x.limit) :
    ∃ r,runFrom machine (budget x) (RecoveryRawViewEnd.cfg x 0 machine.start)=some r ∧
      r.steps≤budget x ∧ r.final.heads 28=0 ∧ r.final.tapes 28=[true] ∧
      r.final.heads 29=2*(pre.length+(RawSyntaxCertificate.pack x.width view).length) ∧
      r.final.tapes 29=frame word := by
  have ha := canonical_answer x word pre suffix view hx hs hp hword hcode hlen hcounts
  have hp' := canonical_position x word pre suffix view hx hs hp hword hcode hlen hcounts
  obtain ⟨r,hr,hb,hh,ht,hf⟩ := entry_run x word pre.length hx hs hp
  refine ⟨r,hr,hb,hh,ht.trans (congrArg (fun b : Bool=>[b]) ha),?_,?_⟩
  · rw [hf ha]
    exact hp'.1
  · rw [hf ha]
    exact hp'.2

end NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
