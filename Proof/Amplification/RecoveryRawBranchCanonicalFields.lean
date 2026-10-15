import Proof.Amplification.RecoveryRawBranchSound

/-! Canonical raw-view input identifies the actual produced count and
accumulated tag/bound flags. The uniqueness argument uses ordinary encoded
view injectivity, never a reencoding premise about an executed tape. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_total (x : State) (word pre suffix : List Bool) (view : RawSyntaxCertificate.View)
    (hw : word=pre++(RawSyntaxCertificate.pack x.view.width view++suffix))
    (hn : view.length ≤ x.view.limit) : total x word pre.length=view.length := by
  let rest := view.flatMap (RawSyntaxCertificate.packClause x.view.width)++suffix
  have hp : readCount x.view.limit (word.drop pre.length)=some (view.length,rest) := by
    rw [hw,List.drop_left]
    simpa only [RawSyntaxCertificate.pack,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,rest] using
      readCount_pack x.view.limit view.length hn rest
  unfold total
  rw [RecoveryRawViewEntry.output_some x.view word pre.length view.length rest hp]

theorem checked_flags (x : State) (word : List Bool) (k : Nat) (view : RawSyntaxCertificate.View)
    (hx : x.view.Valid) (hs : x.view.inner.stream.source=frame word)
    (hp : x.view.inner.stream.pos=2*k)
    (hc : RawSyntaxCertificate.check (RecoveryRawViewBody.code x.view) view=true)
    (ha : RecoveryRawViewEntry.answer x.view word k=true) :
    (output x word k).view.inner.tags=(x.view.inner.tags && RawSyntaxCertificate.tagsValid view) ∧
    (output x word k).view.inner.bounded=
      (x.view.inner.bounded && RecoveryRawViewLoop.boundedView (RadixSemantics.value x.view.inner.bound) view) := by
  obtain ⟨actual,hactual,ht,hb⟩ := RecoveryRawViewEntry.accepted_syntax x.view word k hx hs hp ha
  have he : Encodable.encode actual=Encodable.encode view :=
    ((RawSyntaxCertificate.check_iff _ _).mp hactual).trans ((RawSyntaxCertificate.check_iff _ _).mp hc).symm
  have hv : actual=view := by
    have hd := congrArg (Encodable.decode (α:=RawSyntaxCertificate.View)) he
    simpa only [Encodable.encodek,Option.some.injEq] using hd
  subst actual
  exact ⟨ht,hb⟩

end NearCubicWires.RepairOrdinary.RecoveryRawBranch
