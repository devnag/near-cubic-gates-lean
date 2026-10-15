import Proof.Amplification.RecoveryClauseEvaluationNodes

/-! One complete successful literal segment of the fixed clause controller,
including all three calls and returns, preserves the next literal's inputs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
open RepairSource.VerifierDecoding RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure LiteralResult (s : State) (e : Extra) (which : Fin 3) (literal word : List Bool)
    (table : FiniteValuation.Table) where
  state : State
  extra : Extra
  stateValid : state.Valid
  extraValid : extra.Valid state word
  bits : state.bits=s.bits
  fields : ∀ j,j≠which → state.fields j=s.fields j
  count : extra.binaryCount=e.binaryCount
  committed : extra.committed=e.committed
  cap : extra.cap=e.cap
  aggregate : extra.aggregate=(e.aggregate ||
    TseitinCNF.literalEval (FiniteValuation.assignment (value e.committed) (value e.binaryCount) table)
      (RawSyntaxCertificate.projectLiteral (Nat.unpair (value literal))))

theorem literal_success (s : State) (e : Extra) (which : Fin 3) (literal word : List Bool)
    (table : FiniteValuation.Table) (tail : List Bool)
    (hs : s.Valid) (he : e.Valid s word) (hl : literal.length=s.bits.length)
    (hf : s.fields which=frame literal) (htag : (Nat.unpair (value literal)).1 ≤ 1)
    (hparse : readList e.cap (readEntry s.bits.length) word=some (table,tail)) :
    ∃ n, ∃ out : LiteralResult s e which literal word table,n ≤ 262144*(s.bits.length+1)^2 ∧
      Timed machine n
        (controlConfig (RecoveryCalls.code sizes (decodeNode which))
          (initialConfiguration (programs (decodeNode which)) (tapes s e)))
        (controlConfig (RecoveryCalls.code sizes (continuationNode which))
          (initialConfiguration (programs (continuationNode which)) (tapes out.state out.extra))) := by
  let ds := RecoveryCheckedLiteral.checkedState s which literal
  let index := RecoveryChildSelection.word false literal
  have hds : ds.Valid := RecoveryCheckedLiteral.checked_valid s which literal hs hl
  have hde : e.Valid ds word := checked_extra_valid s e which literal word he
  have hil : index.length=ds.bits.length := (RecoveryChildSelection.word_length false literal).trans hl
  have hfield : ds.fields which=frame index := checked_variable s which literal
  have ht : ds.result=true := by
    change (RecoveryCheckedLiteral.checkedState s which literal).result=true
    rw [checked_tag]
    exact decide_eq_true htag
  obtain ⟨m,output,hm,hlookup,h27,h41,h34,hout⟩ := lookup_ready ds e which index word hds hde hil hfield
  obtain ⟨count,row,guard,hcount,hlen,hvalid,hvalue,hsv,hev,houtput⟩ := hout table tail hparse
  let as := assignedState ds which row
  let ae := assignedExtra e ds count row guard
  have hfinal := truth_valid as ae word hsv hev
  have hag : (truthExtra as ae).aggregate=(e.aggregate ||
      TseitinCNF.literalEval (FiniteValuation.assignment (value e.committed) (value e.binaryCount) table)
        (RawSyntaxCertificate.projectLiteral (Nat.unpair (value literal)))) := by
    change (if RecoveryLiteralTruth.accepted ds.result row.valid then
      e.aggregate || RecoveryLiteralTruth.value ds.flag row.value else false)=_
    rw [ht,hvalid]
    simp only [RecoveryLiteralTruth.accepted,Bool.true_and,↓reduceIte]
    have hv : row.value=FiniteValuation.assignment (value e.committed) (value e.binaryCount) table
        (Nat.unpair (value literal)).2 := by
      simpa only [index,variable_value] using hvalue
    rw [hv]
    change (e.aggregate || RecoveryLiteralTruth.value
      (RecoveryCheckedLiteral.checkedState s which literal).flag
      (FiniteValuation.assignment (value e.committed) (value e.binaryCount) table (Nat.unpair (value literal)).2))=_
    rw [checked_sign,natural_literal_truth _ _ _ htag]
  let result : LiteralResult s e which literal word table :=
    { state := truthState as ae
      extra := truthExtra as ae
      stateValid := hfinal.1
      extraValid := hfinal.2
      bits := rfl
      fields := by
        intro j hj
        simp [truthState,as,assignedState,ds,RecoveryCheckedLiteral.checkedState,
          RecoveryLiteralDecode.decodedState,hj]
      count := rfl
      committed := rfl
      cap := rfl
      aggregate := hag }
  have hd := (decode_program_ready which s e literal hs hl hf).call sizes programs 0 next
    (decodeNode which) (lookupNode which) (by
      intro q
      rw [decode_next]
      have hp : tapes ds e 27=[ds.result] := rfl
      change some (if readTapeBit (tapes ds e 27) 0 then lookupNode which else 12)=some (lookupNode which)
      simp [hp,ht,readTapeBit])
  rw [houtput] at hlookup
  have hlu := (lookup_program_ready which m (tapes ds e) (tapes as ae) hlookup).call sizes programs 0 next
    (lookupNode which) (truthNode which) (by
      intro q
      rw [lookup_next]
      have hp : tapes as ae 34=[row.valid] := rfl
      simp [hp,hvalid,readTapeBit])
  have htr := (truth_program_ready which as ae).call sizes programs 0 next
    (truthNode which) (continuationNode which) (by intro q; exact truth_next which q _)
  refine ⟨(RecoveryCheckedLiteral.time literal+1)+(m+1)+(1+1),result,?_,(hd.trans hlu).trans htr⟩
  have hdBound := RecoveryCheckedLiteral.time_bound literal
  change RecoveryCheckedLiteral.time literal ≤ 131072*(literal.length+1)^2 at hdBound
  change m ≤ 32768*(s.bits.length+1)^2 at hm
  rw [hl] at hdBound
  have hp : 0<(s.bits.length+1)^2 := by positivity
  nlinarith only [hdBound,hm,hp]

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
