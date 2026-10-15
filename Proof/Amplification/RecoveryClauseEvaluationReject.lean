import Proof.Amplification.RecoveryClauseEvaluationLiteral

/-! Malformed natural tags and valuation tables reach the actual reject
node. No successful-workspace invariant is required after rejection. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
open RepairSource.VerifierDecoding RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reject_tail (input : Fin 42→List Bool) (oldResult oldAggregate : Bool)
    (hr : input 27=[oldResult]) (ha : input 41=[oldAggregate]) :
    Timed machine 2 (controlConfig (RecoveryCalls.code sizes 12) (initialConfiguration (programs 12) input))
      (RecoveryCalls.stopped sizes (fun _=>0) (boundaryOutput 2 input)) :=
  (boundary_ready 2 input oldResult oldAggregate hr ha).stop sizes programs 0 next 12 (by intro q; rfl)

theorem finish_tail (input : Fin 42→List Bool) (oldResult oldAggregate : Bool)
    (hr : input 27=[oldResult]) (ha : input 41=[oldAggregate]) :
    Timed machine 2 (controlConfig (RecoveryCalls.code sizes 11) (initialConfiguration (programs 11) input))
      (RecoveryCalls.stopped sizes (fun _=>0) (boundaryOutput 1 input)) :=
  (boundary_ready 1 input oldResult oldAggregate hr ha).stop sizes programs 0 next 11 (by intro q; rfl)

theorem literal_bad_tag (s : State) (e : Extra) (which : Fin 3) (literal : List Bool)
    (hs : s.Valid) (hl : literal.length=s.bits.length) (hf : s.fields which=frame literal)
    (htag : ¬(Nat.unpair (value literal)).1 ≤ 1) :
    ∃ n output,n ≤ 262144*(s.bits.length+1)^2 ∧ output 27=[false] ∧
      Timed machine n
        (controlConfig (RecoveryCalls.code sizes (decodeNode which))
          (initialConfiguration (programs (decodeNode which)) (tapes s e)))
        (RecoveryCalls.stopped sizes (fun _=>0) output) := by
  let ds := RecoveryCheckedLiteral.checkedState s which literal
  have ht : ds.result=false := by
    change (RecoveryCheckedLiteral.checkedState s which literal).result=false
    rw [checked_tag]
    simp [htag]
  have hd := (decode_program_ready which s e literal hs hl hf).call sizes programs 0 next
    (decodeNode which) 12 (by
      intro q
      rw [decode_next]
      have hp : tapes ds e 27=[ds.result] := rfl
      change some (if readTapeBit (tapes ds e 27) 0 then lookupNode which else 12)=some 12
      simp [hp,ht,readTapeBit])
  have hr := reject_tail (tapes ds e) ds.result e.aggregate rfl rfl
  refine ⟨(RecoveryCheckedLiteral.time literal+1)+2,boundaryOutput 2 (tapes ds e),?_,by simp,(hd.trans hr)⟩
  have hb := RecoveryCheckedLiteral.time_bound literal
  change RecoveryCheckedLiteral.time literal ≤ 131072*(literal.length+1)^2 at hb
  rw [hl] at hb
  have hp : 0<(s.bits.length+1)^2 := by positivity
  nlinarith only [hb,hp]

theorem literal_bad_table (s : State) (e : Extra) (which : Fin 3) (literal word : List Bool)
    (hs : s.Valid) (he : e.Valid s word) (hl : literal.length=s.bits.length)
    (hf : s.fields which=frame literal) (htag : (Nat.unpair (value literal)).1 ≤ 1)
    (hparse : readList e.cap (readEntry s.bits.length) word=none) :
    ∃ n output,n ≤ 262144*(s.bits.length+1)^2 ∧ output 27=[false] ∧
      Timed machine n
        (controlConfig (RecoveryCalls.code sizes (decodeNode which))
          (initialConfiguration (programs (decodeNode which)) (tapes s e)))
        (RecoveryCalls.stopped sizes (fun _=>0) output) := by
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
  obtain ⟨m,output,hm,hlookup,h27,h41,h34,_⟩ := lookup_ready ds e which index word hds hde hil hfield
  have hd := (decode_program_ready which s e literal hs hl hf).call sizes programs 0 next
    (decodeNode which) (lookupNode which) (by
      intro q
      rw [decode_next]
      have hp : tapes ds e 27=[ds.result] := rfl
      change some (if readTapeBit (tapes ds e 27) 0 then lookupNode which else 12)=some (lookupNode which)
      simp [hp,ht,readTapeBit])
  have hlu := (lookup_program_ready which m (tapes ds e) output hlookup).call sizes programs 0 next
    (lookupNode which) 12 (by
      intro q
      rw [lookup_next]
      have hp : output 34=[false] := by simpa [ds,RecoveryCheckedLiteral.checkedState,hparse] using h34
      simp [hp,readTapeBit])
  have hr := reject_tail output ds.result e.aggregate h27 h41
  refine ⟨(RecoveryCheckedLiteral.time literal+1)+(m+1)+2,boundaryOutput 2 output,?_,by simp,
    (hd.trans hlu).trans hr⟩
  have hb := RecoveryCheckedLiteral.time_bound literal
  change RecoveryCheckedLiteral.time literal ≤ 131072*(literal.length+1)^2 at hb
  change m ≤ 32768*(s.bits.length+1)^2 at hm
  rw [hl] at hb
  have hp : 0<(s.bits.length+1)^2 := by positivity
  nlinarith only [hb,hm,hp]

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
