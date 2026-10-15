import Proof.Amplification.RecoverySourceClauseLoad

namespace NearCubicWires.RepairSource.RecoverySourceClauseLoad
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem literal_bits_bound {Q : Nat} (literal : Literal Q) : (literalCode literal).bits.length≤2*Q+1 := by
  have hb := RecoveryProjectionRows.bits_le_value (literalCode literal)
  cases literal with
  | positive j=>change (2*j.val).bits.length≤2*Q+1; change (2*j.val).bits.length≤2*j.val at hb; have hj:=j.isLt; omega
  | negative j=>change (2*j.val+1).bits.length≤2*Q+1; change (2*j.val+1).bits.length≤2*j.val+1 at hb; have hj:=j.isLt; omega

def uniformBudget (Q R : Nat) := 536870912*(Q+R+1)^2

theorem budget_bound {Q : Nat} (clause : Fin 3→Literal Q) (R : Nat) :
    budget (fun i=>(literalCode (clause i)).bits) Q R≤uniformBudget Q R := by
  have h0:=literal_bits_bound (clause 0)
  have h1:=literal_bits_bound (clause 1)
  have h2:=literal_bits_bound (clause 2)
  unfold budget RecoverySourceClauseRead.budget RecoverySourceClauseCode.uniformBudget uniformBudget
  nlinarith [Nat.zero_le (Q*R)]

theorem bounded_clause_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n))
    (clause : Fin 3→Literal (pcp.queryCount n)) (pre suffix : List Bool) : ∃ r,
    runFrom machine (uniformBudget (pcp.queryCount n) (pcp.nativeWidth n))
      ⟨machine.start,heads pre,input pre (fun i=>(literalCode (clause i)).bits) suffix
        (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))⟩=some r ∧
      r.final.tapes 262=RepairOrdinary.frame (RecoverySourceClauseCode.word pcp x randomness clause) ∧
      r.final.tapes 159=FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness) ∧
      r.final.tapes 272=RecoverySourceClauseRead.source pre (fun i=>(literalCode (clause i)).bits) suffix ∧
      r.final.heads 272=(pre++RecoverySourceClauseRead.prefixes (fun i=>(literalCode (clause i)).bits) 3).length ∧
      (∀ i : Fin 276,i≠272 → r.final.heads i=0) ∧
      r.steps≤uniformBudget (pcp.queryCount n) (pcp.nativeWidth n) := by
  obtain ⟨r,hr,hw,ha,hsource,hpos,hh,hs⟩ := clause_run pcp x randomness clause pre suffix
  have hb := budget_bound clause (pcp.nativeWidth n)
  have hm := runFrom_moreFuel machine _ (uniformBudget (pcp.queryCount n) (pcp.nativeWidth n)-
    budget (fun i=>(literalCode (clause i)).bits) (pcp.queryCount n) (pcp.nativeWidth n)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r,hm,hw,ha,hsource,hpos,hh,hs.trans hb⟩

end NearCubicWires.RepairSource.RecoverySourceClauseLoad
