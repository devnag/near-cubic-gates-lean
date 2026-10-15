import Proof.Amplification.RecoveryClauseEvaluationBlock

/-! Every first invalid literal tag is rejected by the same finite clause
graph, after exactly the earlier successful literal segments. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tagsValid (words : Fin 3→List Bool) : Bool :=
  decide ((Nat.unpair (value (words 0))).1 ≤ 1) &&
    decide ((Nat.unpair (value (words 1))).1 ≤ 1) && decide ((Nat.unpair (value (words 2))).1 ≤ 1)
def blockCheck (committed count : Nat) (table : FiniteValuation.Table) (words : Fin 3→List Bool) : Bool :=
  tagsValid words && TseitinCNF.clauseEval (FiniteValuation.assignment committed count table) (projectedWords words)

theorem tags_valid_iff (words : Fin 3→List Bool) :
    tagsValid words=true ↔ ∀ i,(Nat.unpair (value (words i))).1 ≤ 1 := by
  simp only [tagsValid,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h0,h1⟩,h2⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨h 0,h 1⟩,h 2⟩

theorem block_bad_tags (s : State) (e : Extra) (words : Fin 3→List Bool) (word : List Bool)
    (table : FiniteValuation.Table) (tail : List Bool)
    (hs : s.Valid) (he : e.Valid s word)
    (hl : ∀ i,(words i).length=s.bits.length) (hf : ∀ i,s.fields i=frame (words i))
    (hbad : ¬∀ i,(Nat.unpair (value (words i))).1 ≤ 1)
    (hparse : readList e.cap (readEntry s.bits.length) word=some (table,tail)) :
    ∃ n output,n ≤ 1048576*(s.bits.length+1)^2 ∧ output 27=[false] ∧
      Timed machine n
        (controlConfig (RecoveryCalls.code sizes (decodeNode 0))
          (initialConfiguration (programs (decodeNode 0)) (tapes s e)))
        (RecoveryCalls.stopped sizes (fun _=>0) output) := by
  by_cases htag0 : (Nat.unpair (value (words 0))).1 ≤ 1
  · obtain ⟨n0,o0,hn0,h0⟩ := literal_success s e 0 (words 0) word table tail hs he (hl 0) (hf 0) htag0 hparse
    have hl1 : (words 1).length=o0.state.bits.length := (hl 1).trans (congrArg List.length o0.bits).symm
    have hf1 : o0.state.fields 1=frame (words 1) := (o0.fields 1 (by decide)).trans (hf 1)
    by_cases htag1 : (Nat.unpair (value (words 1))).1 ≤ 1
    · have hp1 : readList o0.extra.cap (readEntry o0.state.bits.length) word=some (table,tail) := by
        rw [o0.cap,o0.bits]
        exact hparse
      obtain ⟨n1,o1,hn1,h1⟩ := literal_success o0.state o0.extra 1 (words 1) word table tail
        o0.stateValid o0.extraValid hl1 hf1 htag1 hp1
      have hb1 : o1.state.bits=s.bits := o1.bits.trans o0.bits
      have hl2 : (words 2).length=o1.state.bits.length := (hl 2).trans (congrArg List.length hb1).symm
      have hf2 : o1.state.fields 2=frame (words 2) :=
        (o1.fields 2 (by decide)).trans ((o0.fields 2 (by decide)).trans (hf 2))
      have htag2 : ¬(Nat.unpair (value (words 2))).1 ≤ 1 := by
        intro h
        apply hbad
        intro i
        fin_cases i <;> assumption
      obtain ⟨n2,output,hn2,hout,h2⟩ := literal_bad_tag o1.state o1.extra 2 (words 2)
        o1.stateValid hl2 hf2 htag2
      refine ⟨(n0+n1)+n2,output,?_,hout,(h0.trans h1).trans h2⟩
      rw [o0.bits] at hn1
      rw [hb1] at hn2
      nlinarith only [hn0,hn1,hn2]
    · obtain ⟨n1,output,hn1,hout,h1⟩ := literal_bad_tag o0.state o0.extra 1 (words 1)
        o0.stateValid hl1 hf1 htag1
      refine ⟨n0+n1,output,?_,hout,h0.trans h1⟩
      rw [o0.bits] at hn1
      nlinarith only [hn0,hn1]
  · obtain ⟨n,output,hn,hout,h⟩ := literal_bad_tag s e 0 (words 0) hs (hl 0) (hf 0) htag0
    exact ⟨n,output,hn.trans (by omega),hout,h⟩

theorem block_bad_table (s : State) (e : Extra) (words : Fin 3→List Bool) (word : List Bool)
    (hs : s.Valid) (he : e.Valid s word)
    (hl : ∀ i,(words i).length=s.bits.length) (hf : ∀ i,s.fields i=frame (words i))
    (hparse : readList e.cap (readEntry s.bits.length) word=none) :
    ∃ n output,n ≤ 1048576*(s.bits.length+1)^2 ∧ output 27=[false] ∧
      Timed machine n
        (controlConfig (RecoveryCalls.code sizes (decodeNode 0))
          (initialConfiguration (programs (decodeNode 0)) (tapes s e)))
        (RecoveryCalls.stopped sizes (fun _=>0) output) := by
  by_cases htag : (Nat.unpair (value (words 0))).1 ≤ 1
  · obtain ⟨n,output,hn,hout,h⟩ := literal_bad_table s e 0 (words 0) word hs he (hl 0) (hf 0) htag hparse
    exact ⟨n,output,hn.trans (by omega),hout,h⟩
  · obtain ⟨n,output,hn,hout,h⟩ := literal_bad_tag s e 0 (words 0) hs (hl 0) (hf 0) htag
    exact ⟨n,output,hn.trans (by omega),hout,h⟩

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
