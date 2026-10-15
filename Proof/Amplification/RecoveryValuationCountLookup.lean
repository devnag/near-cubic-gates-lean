import Proof.Amplification.RecoveryValuationCountScan

/-! Exact finite-valuation lookup for the complete capped-list machine,
including the physically parsed count and all malformed witness suffixes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationCount
open LocalBitMultitape RadixSemantics RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem readList_some (width cap : Nat) (word : List Bool) (table : FiniteValuation.Table) (tail : List Bool)
    (h : readList cap (readEntry width) word=some (table,tail)) :
    ∃ count rest,readCount cap word=some (count,rest) ∧
      readMany (readEntry width) count rest=some (table,tail) := by
  cases hc : readCount cap word with
  | none => rw [readList_count_none width cap word hc] at h; contradiction
  | some pair =>
    rcases pair with ⟨count,rest⟩
    exact ⟨count,rest,rfl,by rwa [readList_count_some width cap count word rest hc] at h⟩

theorem valuation_list_run (d : Data) (pre word : List Bool) (cap : Nat)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1)
    (hfound : d.found=false) (hvalue : d.value=false) :
    ∃ r,runFrom machine (limit d.width cap) (cfg d 0 cap machine.start)=some r ∧
      r.steps≤limit d.width cap ∧ r.final.heads 7=0 ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ table tail,readList cap (readEntry d.width) word=some (table,tail) →
        r.final.heads 5=0 ∧ r.final.tapes 5=[FiniteValuation.lookup table (value d.index)] := by
  obtain ⟨r,hr,ht,hh,hvalid,hout⟩ := bounded_list d pre word cap hs hp hi hb
  refine ⟨r,hr,ht,hh,hvalid,?_⟩
  intro table tail hparse
  obtain ⟨count,rest,hcount,hrows⟩ := readList_some d.width cap word table tail hparse
  have ha : (readMany (readEntry d.width) count rest).isSome=true := by rw [hrows]; rfl
  rw [hout count rest hcount ha]
  refine ⟨rfl,?_⟩
  change [(RepeatMachine.iterate RecoveryValuationTable.next count
    (⟨counted d count,rest⟩ : RecoveryValuationTable.Cursor)).2.data.value]=_
  have hv := congrArg Prod.snd (RecoveryValuationTable.iterate_accumulator count
    (⟨counted d count,rest⟩ : RecoveryValuationTable.Cursor) table tail hrows)
  rw [RecoveryValuationTable.fold_selected] at hv
  change (RepeatMachine.iterate RecoveryValuationTable.next count
    (⟨counted d count,rest⟩ : RecoveryValuationTable.Cursor)).2.data.value=
      (if d.found then d.value else RecoveryValuationTable.lookupOr table (value d.index) d.value) at hv
  rw [hfound,hvalue] at hv
  simp only [Bool.false_eq_true,↓reduceIte,RecoveryValuationTable.lookupOr_false] at hv
  exact congrArg List.singleton hv

end NearCubicWires.RepairOrdinary.RecoveryValuationCount
