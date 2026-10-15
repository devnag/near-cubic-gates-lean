import Proof.Amplification.RecoveryValuationBound

/-! Successful valuation scanning retains the actual suffix and cursor.
This is the byte-address bridge needed by the next raw-view reader. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationTable
open LocalBitMultitape RecoveryValuationStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem iterate_cursor (count : Nat) (x : Cursor) (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readMany (readEntry x.data.width) count x.rest=some (table,rest)) :
    rest=x.rest.drop (count*(x.data.width+1)) ∧
      (RepeatMachine.iterate next count x).2.rest=rest ∧
      (RepeatMachine.iterate next count x).2.data.pos=x.data.pos+2*count*(x.data.width+1) := by
  induction count generalizing x table rest with
  | zero=>
    have he : ([],x.rest)=(table,rest) := Option.some.inj hp
    have hr : rest=x.rest := (congrArg Prod.snd he).symm
    subst rest
    simp [RepeatMachine.iterate]
  | succ count ih=>
    cases hentry : readEntry x.data.width x.rest with
    | none=>
      rw [readMany_head_none _ count x.rest hentry] at hp
      contradiction
    | some pair=>
      rcases pair with ⟨entry,tail⟩
      obtain ⟨_,ht⟩ := readEntry_some x.data.width x.rest entry tail hentry
      cases htail : readMany (readEntry x.data.width) count tail with
      | none=>
        rw [readMany_head_some _ count x.rest entry tail hentry,htail] at hp
        contradiction
      | some pair=>
        rcases pair with ⟨entries,finish⟩
        have hresult : (entry::entries,finish)=(table,rest) := by
          rw [readMany_head_some _ count x.rest entry tail hentry,htail] at hp
          exact Option.some.inj hp
        have hfinish : finish=rest := congrArg Prod.snd hresult
        have htail' : readMany (readEntry (advance x).data.width) count (advance x).rest=some (entries,finish) := by
          simpa only [advance,Data.done,Data.afterRow,Data.afterMatch,Data.afterField,ht] using htail
        have h := ih (advance x) entries finish htail'
        have hlong : x.data.width+1≤x.rest.length := by
          have he := congrArg Option.isSome hentry
          rw [readEntry_isSome] at he
          exact of_decide_eq_true he
        have hkey : (readKey x.data x.rest).length=x.data.width := by
          simp [readKey,List.length_take,show x.data.width≤x.rest.length by omega]
        have hpos : (advance x).data.pos=x.data.pos+2*(x.data.width+1) := by
          change x.data.pos+2*(readKey x.data x.rest++[readValue x.data x.rest]).length=_
          simp [hkey]
        rw [←hfinish]
        simp only [RepeatMachine.iterate,next,hentry,Option.isSome_some,↓reduceIte]
        refine ⟨?_,h.2.1,?_⟩
        · have ha : x.data.width+1+count*(x.data.width+1)=(count+1)*(x.data.width+1) := by ring
          simpa only [advance,Data.done,Data.afterRow,Data.afterMatch,Data.afterField,List.drop_drop,ha] using h.1
        · calc
            _ = (advance x).data.pos+2*count*((advance x).data.width+1) := h.2.2
            _ = x.data.pos+2*(x.data.width+1)+2*count*(x.data.width+1) := by rw [hpos]; rfl
            _ = x.data.pos+2*(count+1)*(x.data.width+1) := by ring

end NearCubicWires.RepairOrdinary.RecoveryValuationTable
