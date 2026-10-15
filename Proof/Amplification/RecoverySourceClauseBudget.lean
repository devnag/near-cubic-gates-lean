import Proof.Amplification.RecoverySourceClauseCode

namespace NearCubicWires.RepairSource.RecoverySourceClauseCode
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cell_length (left right : List Bool) :
    (RecoverySourceListCell.word left right).length≤2*(left.length+right.length+1)+1 := by
  have h := (ClockIncrement.next_length (RecoverySourceListCell.pairedWord left right)).2
  simpa only [RecoverySourceListCell.word,RecoverySourceListCell.pairedWord,binary_length,PCPPair.width] using h

theorem cell_budget (left right : List Bool) :
    RecoverySourceListCell.budget left right≤2048*(left.length+right.length+1)^2 := by
  have hp := PCPPairCold.budget_quadratic left right
  have hw := ClockIncrement.work_bound (RecoverySourceListCell.pairedWord left right)
  simp only [RecoverySourceListCell.pairedWord,binary_length,PCPPair.width] at hw
  change ClockIncrement.work (RecoverySourceListCell.pairedWord left right)≤2*(2*(left.length+right.length+1))+3 at hw
  unfold RecoverySourceListCell.budget
  nlinarith [Nat.zero_le (left.length*right.length)]

theorem cells_budget (ws : Fin 3→List Bool) (R : Nat) (hw : ∀ i,(ws i).length=2*R+4) :
    RecoverySourceClauseCells.budget ws≤67108864*(R+1)^2 := by
  have hTail := cell_length (ws 2) []
  have hMid := cell_length (ws 1) (RecoverySourceClauseCells.tailWord ws)
  change (RecoverySourceClauseCells.tailWord ws).length≤2*((ws 2).length+[].length+1)+1 at hTail
  change (RecoverySourceClauseCells.midWord ws).length≤2*((ws 1).length+(RecoverySourceClauseCells.tailWord ws).length+1)+1 at hMid
  simp only [hw,List.length_nil] at hTail hMid
  have ht : (RecoverySourceClauseCells.tailWord ws).length≤4*R+11 := by omega
  have hm : (RecoverySourceClauseCells.midWord ws).length≤12*R+33 := by omega
  have hb0 := cell_budget (ws 2) []
  have hb1 := cell_budget (ws 1) (RecoverySourceClauseCells.tailWord ws)
  have hb2 := cell_budget (ws 0) (RecoverySourceClauseCells.midWord ws)
  simp only [hw,List.length_nil,Nat.add_zero] at hb0 hb1 hb2
  have h1 : ((2*R+4)+(RecoverySourceClauseCells.tailWord ws).length+1)^2≤(6*R+16)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h2 : ((2*R+4)+(RecoverySourceClauseCells.midWord ws).length+1)^2≤(14*R+38)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hb : RecoverySourceClauseCells.budget ws≤
      5+2048*(2*R+5)^2+2048*(6*R+16)^2+2048*(14*R+38)^2 := by
    unfold RecoverySourceClauseCells.budget
    nlinarith
  apply hb.trans
  nlinarith

def uniformBudget (Q R : Nat) := 268435456*(Q+R+1)^2

theorem budget_bound {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (clause : Fin 3→Literal (pcp.queryCount n)) :
    budget pcp x randomness clause≤uniformBudget (pcp.queryCount n) (pcp.nativeWidth n) := by
  have hc := cells_budget (words pcp x randomness clause) (pcp.nativeWidth n) (by
    intro i
    simp only [words,RecoverySourceLiteralMeaning.word,RecoverySourceLiteralCode.word,binary_length,
      PCPPair.width,List.length_singleton,RecoverySourceLiteralMeaning.addressBits,List.length_ofFn]
    ring)
  unfold budget uniformBudget RecoverySourceLiteralMeaning.uniformBudget
  nlinarith [Nat.zero_le (pcp.queryCount n*pcp.nativeWidth n)]

theorem bounded_clause_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (clause : Fin 3→Literal (pcp.queryCount n)) : ∃ out,
    ClockJoin.ReadyRun machine (uniformBudget (pcp.queryCount n) (pcp.nativeWidth n))
      (input (fun i=>(literalCode (clause i)).bits) (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))) out ∧
      out 262=RepairOrdinary.frame (word pcp x randomness clause) ∧
      out 159=FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness) ∧
      value (word pcp x randomness clause)=Encodable.encode (CanonicalRecoveryLanguage.outerProofClause pcp x randomness clause) := by
  obtain ⟨out,hr,hout,hsource⟩ := clause_run pcp x randomness clause
  exact ⟨out,ClockJoin.enlarge _ _ _ _ _ hr (budget_bound pcp x randomness clause),hout,hsource,word_value pcp x randomness clause⟩

end NearCubicWires.RepairSource.RecoverySourceClauseCode
