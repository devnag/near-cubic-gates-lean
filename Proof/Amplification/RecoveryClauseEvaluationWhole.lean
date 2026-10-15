import Proof.Amplification.RecoveryClauseEvaluationAllTags

/-! Whole ordinary clause checker from the reusable physical entry. All
codes and malformed table prefixes are covered; every accepting return
supplies the actual state for the next clause. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clauseWordCheck (s : State) (e : Extra) (word : List Bool) : Bool :=
  (readList e.cap (readEntry s.bits.length) word).any (fun pair=>
    CompactCertificate.clausePredicate (value e.committed) (value e.binaryCount) pair.1 (value s.bits))

structure ClauseResult (s : State) (e : Extra) (word : List Bool) where
  state : State
  extra : Extra
  stateValid : state.Valid
  extraValid : extra.Valid state word
  width : state.bits.length=s.bits.length
  count : extra.binaryCount=e.binaryCount
  committed : extra.committed=e.committed
  cap : extra.cap=e.cap
  answer : state.result=clauseWordCheck s e word

theorem clause_time_bound (width reader body : Nat)
    (hr : reader ≤ 2097152*(width+1)^2) (hb : body ≤ 1048576*(width+1)^2) :
    2+(reader+1)+body ≤ 4194304*(width+1)^2 := by
  have hp : 0<(width+1)^2 := by positivity
  nlinarith only [hr,hb,hp]

theorem clause_trace (s : State) (e : Extra) (word : List Bool) (hs : s.Valid) (he : e.Valid s word) :
    ∃ n output,n ≤ 4194304*(s.bits.length+1)^2 ∧ output 27=[clauseWordCheck s e word] ∧
      Timed machine n (initialConfiguration machine (tapes s e))
        (RecoveryCalls.stopped sizes (fun _=>0) output) ∧
      (clauseWordCheck s e word=true → ∃ out : ClauseResult s e word,output=tapes out.state out.extra) := by
  let cs := boundaryState 0 s e
  let ce := boundaryExtra 0 e
  have hc := boundary_valid 0 s e word hs he
  let rs := RecoveryThreeCellReader.endState cs
  have hp := reader_properties cs hc.1
  have her : ce.Valid rs word := extra_transport cs rs ce word hc.2 hp.2.1 hp.2.2
  have hclear : Timed machine 2 (initialConfiguration machine (tapes s e))
      (controlConfig (RecoveryCalls.code sizes 1) (initialConfiguration (programs 1) (tapes cs ce))) :=
    (boundary_ready_state 0 s e).call sizes programs 0 next 0 1 (by intro q; rfl)
  have hr := reader_ready cs ce hc.1
  have hreader : RecoveryThreeCellReader.time cs ≤ 2097152*(s.bits.length+1)^2 :=
    RecoveryThreeCellReader.time_bound cs
  have hwidth : rs.bits.length=s.bits.length := hp.2.1
  have hshapeResult : rs.result=CompactCertificate.shapeThree (value s.bits) :=
    RecoveryThreeCellReader.result_shape cs
  by_cases hshape : CompactCertificate.shapeThree (value s.bits)=true
  · have hrt : rs.result=true := hshapeResult.trans hshape
    have hread := hr.call sizes programs 0 next 1 2 (by
      intro q
      change some (if readTapeBit (tapes rs ce 27) 0 then 2 else 12)=some 2
      simp [tapes_answer,hrt,readTapeBit])
    have hprefix := hclear.trans hread
    let words := RecoveryThreeCellReader.literalWords cs
    have hfields : ∀ i,rs.fields i=frame (words i) := RecoveryThreeCellReader.success_fields cs hrt
    have hlengths : ∀ i,(words i).length=rs.bits.length := by
      intro i
      exact (RecoveryThreeCellReader.success_values cs hrt i).1.trans hp.2.1.symm
    cases hparse : readList e.cap (readEntry s.bits.length) word with
    | none =>
      have hpr : readList ce.cap (readEntry rs.bits.length) word=none := by
        change readList e.cap (readEntry rs.bits.length) word=none
        rw [hwidth]
        exact hparse
      obtain ⟨n,output,hn,hout,hbody⟩ := block_bad_table rs ce words word hp.1 her hlengths hfields hpr
      have hcheck : clauseWordCheck s e word=false := by simp [clauseWordCheck,hparse]
      refine ⟨2+(RecoveryThreeCellReader.time cs+1)+n,output,?_,?_,hprefix.trans hbody,?_⟩
      · rw [hwidth] at hn
        exact clause_time_bound _ _ _ hreader hn
      · simpa [hcheck] using hout
      · simp [hcheck]
    | some pair =>
      rcases pair with ⟨table,tail⟩
      have hpr : readList ce.cap (readEntry rs.bits.length) word=some (table,tail) := by
        change readList e.cap (readEntry rs.bits.length) word=some (table,tail)
        rw [hwidth]
        exact hparse
      obtain ⟨n,output,hn,hout,hbody,hreturn⟩ := block_total rs ce words word table tail hp.1 her rfl hlengths hfields hpr
      have hsem : blockCheck (value ce.committed) (value ce.binaryCount) table words=clauseWordCheck s e word := by
        calc
          _ = CompactCertificate.checkThree (value e.committed) (value e.binaryCount) table (value s.bits) :=
            block_check_three cs _ _ table hshape
          _ = CompactCertificate.clausePredicate (value e.committed) (value e.binaryCount) table (value s.bits) :=
            (CompactCertificate.clausePredicate_eq_checkThree _ _ _ _).symm
          _ = clauseWordCheck s e word := by simp [clauseWordCheck,hparse]
      have hanswer : output 27=[clauseWordCheck s e word] := hout.trans (congrArg List.singleton hsem)
      refine ⟨2+(RecoveryThreeCellReader.time cs+1)+n,output,?_,hanswer,hprefix.trans hbody,?_⟩
      · rw [hwidth] at hn
        exact clause_time_bound _ _ _ hreader hn
      · intro htrue
        obtain ⟨out,heq⟩ := hreturn (hsem.trans htrue)
        have ha : out.state.result=clauseWordCheck s e word := by
          rw [heq,tapes_answer] at hanswer
          exact List.singleton_inj.mp hanswer
        let final : ClauseResult s e word :=
          { state := out.state
            extra := out.extra
            stateValid := out.stateValid
            extraValid := out.extraValid
            width := (congrArg List.length out.bits).trans hwidth
            count := out.count
            committed := out.committed
            cap := out.cap
            answer := ha }
        exact ⟨final,heq⟩
  · have hrf : rs.result=false := hshapeResult.trans (Bool.eq_false_iff.mpr hshape)
    have hread := hr.call sizes programs 0 next 1 12 (by
      intro q
      change some (if readTapeBit (tapes rs ce 27) 0 then 2 else 12)=some 12
      simp [tapes_answer,hrf,readTapeBit])
    have hreject := reject_tail (tapes rs ce) rs.result ce.aggregate rfl rfl
    have hcheck : clauseWordCheck s e word=false := by
      have hsf : CompactCertificate.shapeThree (value s.bits)=false := Bool.eq_false_iff.mpr hshape
      unfold clauseWordCheck
      cases ht : readList e.cap (readEntry s.bits.length) word with
      | none => rfl
      | some pair =>
        rcases pair with ⟨table,tail⟩
        simp [CompactCertificate.clausePredicate_eq_checkThree,CompactCertificate.checkThree,hsf]
    refine ⟨2+(RecoveryThreeCellReader.time cs+1)+2,boundaryOutput 2 (tapes rs ce),?_,?_,
      (hclear.trans hread).trans hreject,?_⟩
    · apply clause_time_bound _ _ _ hreader
      have hpos : 0<(s.bits.length+1)^2 := by positivity
      omega
    · simp [hcheck]
    · simp [hcheck]

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
