import Proof.Amplification.RecoveryRawViewSyntax

/-! Canonical completeness for one retained raw-view clause. The existing
codec's scalar payload is skipped by its exact length; only its actual
count prefix controls the natural-code traversal. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding RepairSource.RecoveryOracle
open CompactCertificate.Serialization RecoveryRawViewBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_step (word pre suffix : List Bool) (head : List (Nat×Nat))
    (tail : RawSyntaxCertificate.View) (x : Cursor)
    (hword : word=pre++(RawSyntaxCertificate.packClause x.data.width head++suffix))
    (hpos : x.pos=pre.length) (hcount : head.length ≤ x.data.limit)
    (hcode : code x.data=Encodable.encode (head::tail)) :
    (next word x).1=true ∧
      (next word x).2.pos=pre.length+(RawSyntaxCertificate.packClause x.data.width head).length ∧
      code (next word x).2.data=Encodable.encode tail := by
  have hz : code x.data≠0 := by
    rw [hcode,Encodable.encode_list_cons]
    exact Nat.succ_ne_zero _
  have hc : headCode x.data=Encodable.encode head := by
    unfold headCode
    rw [hcode,Encodable.encode_list_cons,Nat.succ_sub_one]
    change (Nat.unpair (Nat.pair (Encodable.encode head) (Encodable.encode tail))).1=_
    rw [Nat.unpair_pair]
  let rest := head.flatMap (RawSyntaxCertificate.packLiteral x.data.width)++suffix
  have hparse : readCount x.data.limit (word.drop x.pos)=some (head.length,rest) := by
    rw [hword,hpos,List.drop_left]
    simpa only [RawSyntaxCertificate.packClause,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,rest] using
      readCount_pack x.data.limit head.length hcount rest
  have hcheck : clauseAnswer (prepared x.data head.length)=true := by
    rw [prepared_answer x.data head.length hz,hc,RawShape.clause_complete]
    rfl
  have ha : (next word x).1=true := by
    change answer x.data word x.pos=true
    rw [answer,if_neg (show RadixSemantics.value x.data.outer.bits≠0 from hz),hparse]
    exact hcheck
  refine ⟨ha,?_,?_⟩
  · change nextPos word x=_
    rw [nextPos,hparse,hpos,RawSyntaxCertificate.pack_clause_length]
    ring
  · have hy : (next word x).2.data=output x.data head.length := body_output_some x.data word x.pos head.length rest hparse
    rw [hy,output_tail x.data head.length hz,hcode,Encodable.encode_list_cons,Nat.succ_sub_one]
    change (Nat.unpair (Nat.pair (Encodable.encode head) (Encodable.encode tail))).2=_
    rw [Nat.unpair_pair]

end NearCubicWires.RepairOrdinary.RecoveryRawViewLoop
