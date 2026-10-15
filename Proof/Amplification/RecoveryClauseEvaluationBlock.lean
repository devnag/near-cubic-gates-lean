import Proof.Amplification.RecoveryClauseEvaluationBoundaryState

/-! All three actual literal segments are composed on their returned tapes,
followed by the physical final-answer write. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
open RepairSource.VerifierDecoding RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def projectedWords (words : Fin 3→List Bool) : List (Bool×Nat) :=
  [RawSyntaxCertificate.projectLiteral (Nat.unpair (value (words 0))),
    RawSyntaxCertificate.projectLiteral (Nat.unpair (value (words 1))),
    RawSyntaxCertificate.projectLiteral (Nat.unpair (value (words 2)))]

structure BlockResult (s : State) (e : Extra) (words : Fin 3→List Bool) (word : List Bool)
    (table : FiniteValuation.Table) where
  state : State
  extra : Extra
  stateValid : state.Valid
  extraValid : extra.Valid state word
  bits : state.bits=s.bits
  count : extra.binaryCount=e.binaryCount
  committed : extra.committed=e.committed
  cap : extra.cap=e.cap
  answer : state.result=TseitinCNF.clauseEval
    (FiniteValuation.assignment (value e.committed) (value e.binaryCount) table) (projectedWords words)

theorem block_success (s : State) (e : Extra) (words : Fin 3→List Bool) (word : List Bool)
    (table : FiniteValuation.Table) (tail : List Bool)
    (hs : s.Valid) (he : e.Valid s word) (ha : e.aggregate=false)
    (hl : ∀ i,(words i).length=s.bits.length) (hf : ∀ i,s.fields i=frame (words i))
    (htags : ∀ i,(Nat.unpair (value (words i))).1 ≤ 1)
    (hparse : readList e.cap (readEntry s.bits.length) word=some (table,tail)) :
    ∃ n, ∃ out : BlockResult s e words word table,n ≤ 1048576*(s.bits.length+1)^2 ∧
      Timed machine n
        (controlConfig (RecoveryCalls.code sizes (decodeNode 0))
          (initialConfiguration (programs (decodeNode 0)) (tapes s e)))
        (RecoveryCalls.stopped sizes (fun _=>0) (tapes out.state out.extra)) := by
  obtain ⟨n0,o0,hn0,h0⟩ := literal_success s e 0 (words 0) word table tail hs he (hl 0) (hf 0) (htags 0) hparse
  have hl1 : (words 1).length=o0.state.bits.length := (hl 1).trans (congrArg List.length o0.bits).symm
  have hf1 : o0.state.fields 1=frame (words 1) := (o0.fields 1 (by decide)).trans (hf 1)
  have hp1 : readList o0.extra.cap (readEntry o0.state.bits.length) word=some (table,tail) := by
    rw [o0.cap,o0.bits]
    exact hparse
  obtain ⟨n1,o1,hn1,h1⟩ := literal_success o0.state o0.extra 1 (words 1) word table tail
    o0.stateValid o0.extraValid hl1 hf1 (htags 1) hp1
  have hb1 : o1.state.bits=s.bits := o1.bits.trans o0.bits
  have hl2 : (words 2).length=o1.state.bits.length := (hl 2).trans (congrArg List.length hb1).symm
  have hf2 : o1.state.fields 2=frame (words 2) :=
    (o1.fields 2 (by decide)).trans ((o0.fields 2 (by decide)).trans (hf 2))
  have hp2 : readList o1.extra.cap (readEntry o1.state.bits.length) word=some (table,tail) := by
    rw [o1.cap,o0.cap,hb1]
    exact hparse
  obtain ⟨n2,o2,hn2,h2⟩ := literal_success o1.state o1.extra 2 (words 2) word table tail
    o1.stateValid o1.extraValid hl2 hf2 (htags 2) hp2
  have hag : o2.extra.aggregate=TseitinCNF.clauseEval
      (FiniteValuation.assignment (value e.committed) (value e.binaryCount) table) (projectedWords words) := by
    rw [o2.aggregate,o1.aggregate,o0.aggregate,o1.committed,o1.count,o0.committed,o0.count]
    simp [ha,projectedWords,TseitinCNF.clauseEval,Bool.or_assoc]
  have hv := boundary_valid 1 o2.state o2.extra word o2.stateValid o2.extraValid
  let result : BlockResult s e words word table :=
    { state := boundaryState 1 o2.state o2.extra
      extra := boundaryExtra 1 o2.extra
      stateValid := hv.1
      extraValid := hv.2
      bits := o2.bits.trans hb1
      count := o2.count.trans (o1.count.trans o0.count)
      committed := o2.committed.trans (o1.committed.trans o0.committed)
      cap := o2.cap.trans (o1.cap.trans o0.cap)
      answer := hag }
  have hfinish := finish_tail (tapes o2.state o2.extra) o2.state.result o2.extra.aggregate rfl rfl
  rw [boundary_layout] at hfinish
  refine ⟨((n0+n1)+n2)+2,result,?_,((h0.trans h1).trans h2).trans hfinish⟩
  rw [o0.bits] at hn1
  rw [hb1] at hn2
  have hp : 0<(s.bits.length+1)^2 := by positivity
  nlinarith only [hn0,hn1,hn2,hp]

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
