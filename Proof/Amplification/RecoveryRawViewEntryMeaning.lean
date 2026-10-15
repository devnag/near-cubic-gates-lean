import Proof.Amplification.RecoveryRawViewEntryWhole

/-! The produced-count entry retains exact syntax soundness and canonical
completeness on the unchanged TableFirst raw-view payload. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding RepairSource.RecoveryOracle
open CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem accepted_case (x : State) (word : List Bool) (k : Nat) (ha : answer x word k=true) :
    ∃ n rest,readCount x.limit (word.drop k)=some (n,rest) ∧
      RecoveryRawViewWhole.answer word n (cursor (flagged x false) k n)=true := by
  change (readCount x.limit (word.drop k)).any
    (fun pair=>RecoveryRawViewWhole.answer word pair.1 (cursor (flagged x false) k pair.1))=true at ha
  rw [Option.any_eq_true] at ha
  obtain ⟨pair,hp,hv⟩ := ha
  exact ⟨pair.1,pair.2,hp,hv⟩

theorem output_some (x : State) (word : List Bool) (k n : Nat) (rest : List Bool)
    (hp : readCount x.limit (word.drop k)=some (n,rest)) :
    output x word k=(RecoveryRawViewEnd.tested
      (RecoveryRawViewLoop.out word n (cursor (flagged x false) k n)).2.data,n) := by
  change (match readCount x.limit (word.drop k) with
    | none=>(flagged x false,0)
    | some (m,_)=>
      (RecoveryRawViewEnd.tested (RecoveryRawViewLoop.out word m (cursor (flagged x false) k m)).2.data,m))=_
  rw [hp]

theorem accepted_syntax (x : State) (word : List Bool) (k : Nat) (hx : x.Valid)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k)
    (ha : answer x word k=true) :
    ∃ view : RawSyntaxCertificate.View,RawSyntaxCertificate.check (RecoveryRawViewBody.code x) view=true ∧
      (output x word k).1.inner.tags=(x.inner.tags && RawSyntaxCertificate.tagsValid view) ∧
      (output x word k).1.inner.bounded=
        (x.inner.bounded && RecoveryRawViewLoop.boundedView (RadixSemantics.value x.inner.bound) view) := by
  obtain ⟨n,rest,hparse,hcheck⟩ := accepted_case x word k ha
  have hv := cursor_valid (flagged x false) word k n (flagged_valid x false hx) hs hp
  obtain ⟨view,hcode,htags,hbounded⟩ := RecoveryRawViewLoop.accepted_syntax x.width n word
    (cursor (flagged x false) k n) hv hcheck
  refine ⟨view,hcode,?_⟩
  rw [output_some x word k n rest hparse]
  exact ⟨htags,hbounded⟩

theorem canonical_answer (x : State) (word pre suffix : List Bool) (view : RawSyntaxCertificate.View)
    (hx : x.Valid) (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*pre.length)
    (hword : word=pre++(RawSyntaxCertificate.pack x.width view++suffix))
    (hcode : RawSyntaxCertificate.check (RecoveryRawViewBody.code x) view=true)
    (hlen : view.length ≤ x.limit) (hcounts : ∀ clause∈view,clause.length ≤ x.limit) :
    answer x word pre.length=true := by
  let rest := view.flatMap (RawSyntaxCertificate.packClause x.width)++suffix
  have hparse : readCount x.limit (word.drop pre.length)=some (view.length,rest) := by
    rw [hword,List.drop_left]
    simpa only [RawSyntaxCertificate.pack,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,rest] using
      readCount_pack x.limit view.length hlen rest
  change (readCount x.limit (word.drop pre.length)).any
    (fun pair=>RecoveryRawViewWhole.answer word pair.1 (cursor (flagged x false) pre.length pair.1))=true
  rw [hparse]
  change RecoveryRawViewWhole.answer word view.length (cursor (flagged x false) pre.length view.length)=true
  let before := pre++List.replicate view.length true++[false]
  have hv := cursor_valid (flagged x false) word pre.length view.length (flagged_valid x false hx) hs hp
  have hw : word=before++(view.flatMap (RawSyntaxCertificate.packClause x.width)++suffix) := by
    simpa only [before,RawSyntaxCertificate.pack,List.append_assoc] using hword
  have hpos : (cursor (flagged x false) pre.length view.length).pos=before.length := by
    simp only [cursor,before,List.length_append,List.length_replicate,List.length_singleton]
  have hc : RecoveryRawViewBody.code (cursor (flagged x false) pre.length view.length).data=Encodable.encode view :=
    ((RawSyntaxCertificate.check_iff _ _).mp hcode).symm
  exact RecoveryRawViewLoop.canonical_answer x.width word before suffix view
    (cursor (flagged x false) pre.length view.length) hv hw hpos hc hcounts

end NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
