import Proof.Amplification.RecoveryClauseEvaluationBadTags

/-! The complete three-literal block handles every natural tag and agrees
with the source clause predicate on the reader's literal words. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem block_total (s : State) (e : Extra) (words : Fin 3→List Bool) (word : List Bool)
    (table : FiniteValuation.Table) (tail : List Bool)
    (hs : s.Valid) (he : e.Valid s word) (ha : e.aggregate=false)
    (hl : ∀ i,(words i).length=s.bits.length) (hf : ∀ i,s.fields i=frame (words i))
    (hparse : readList e.cap (readEntry s.bits.length) word=some (table,tail)) :
    ∃ n output,n ≤ 1048576*(s.bits.length+1)^2 ∧
      output 27=[blockCheck (value e.committed) (value e.binaryCount) table words] ∧
      Timed machine n
        (controlConfig (RecoveryCalls.code sizes (decodeNode 0))
          (initialConfiguration (programs (decodeNode 0)) (tapes s e)))
        (RecoveryCalls.stopped sizes (fun _=>0) output) ∧
      (blockCheck (value e.committed) (value e.binaryCount) table words=true →
        ∃ out : BlockResult s e words word table,output=tapes out.state out.extra) := by
  by_cases htags : ∀ i,(Nat.unpair (value (words i))).1 ≤ 1
  · obtain ⟨n,out,hn,h⟩ := block_success s e words word table tail hs he ha hl hf htags hparse
    refine ⟨n,tapes out.state out.extra,hn,?_,h,by intro _; exact ⟨out,rfl⟩⟩
    rw [tapes_answer,out.answer]
    simp [blockCheck,(tags_valid_iff words).mpr htags]
  · obtain ⟨n,output,hn,hresult,h⟩ := block_bad_tags s e words word table tail hs he hl hf htags hparse
    have ht : tagsValid words=false := Bool.eq_false_iff.mpr (by
      intro htrue
      exact htags ((tags_valid_iff words).mp htrue))
    refine ⟨n,output,hn,?_,h,?_⟩
    · simpa [blockCheck,ht] using hresult
    · simp [blockCheck,ht]

theorem block_check_three (s : State) (committed count : Nat) (table : FiniteValuation.Table)
    (hs : CompactCertificate.shapeThree (value s.bits)=true) :
    blockCheck committed count table (RecoveryThreeCellReader.literalWords s)=
      CompactCertificate.checkThree committed count table (value s.bits) := by
  have he : (RecoveryThreeCellReader.endState s).result=true :=
    (RecoveryThreeCellReader.result_shape s).trans hs
  have h0 : value (RecoveryThreeCellReader.literalWords s 0)=(CompactCertificate.cell (value s.bits)).1 :=
    (RecoveryThreeCellReader.success_values s he 0).2
  have h1 : value (RecoveryThreeCellReader.literalWords s 1)=
      (CompactCertificate.cell (CompactCertificate.cell (value s.bits)).2).1 :=
    (RecoveryThreeCellReader.success_values s he 1).2
  have h2 : value (RecoveryThreeCellReader.literalWords s 2)=
      (CompactCertificate.cell (CompactCertificate.cell (CompactCertificate.cell (value s.bits)).2).2).1 :=
    (RecoveryThreeCellReader.success_values s he 2).2
  simp [blockCheck,tagsValid,projectedWords,CompactCertificate.checkThree,hs,
    CompactCertificate.rawThree,RawSyntaxCertificate.projectClause,h0,h1,h2,Bool.and_assoc]

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
