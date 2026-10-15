import Proof.Amplification.RecoverySourceClauseLoadBudget
import Proof.Circuits.DecompositionSourceBounds

/-! The exact source-stream clause machine executes from bounded blank
workspace. Actual one-tape write growth bounds every scratch tape, while
source and address tapes remain unpadded and retained. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseLoad
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def work (i : Fin 276) : Prop := i≠159 ∧ i≠272
instance (i : Fin 276) : Decidable (work i) := inferInstanceAs (Decidable (i≠159 ∧ i≠272))
def caps (cap : Nat) (i : Fin 276) := if work i then cap else 0

theorem scratch_support (pre : List Bool) (codes : Fin 3→List Bool) (suffix address : List Bool)
    (fuel cap : Nat) (r : ExecutionReceipt 276 _)
    (hr : runFrom machine fuel ⟨machine.start,heads pre,input pre codes suffix address⟩=some r)
    (hcap : r.steps≤cap) : ∀ i,work i → (r.final.tapes i).length≤cap := by
  intro i hi
  have h159 : i.val≠159 := fun he=>hi.1 (Fin.ext he)
  have h272 : i.val≠272 := fun he=>hi.2 (Fin.ext he)
  have h := DecompositionSource.one_tape_support machine fuel _ r i 0 hr
    (by simp only [heads,h272,ite_false,Nat.le_refl])
    (by simp only [input,h159,h272,ite_false,List.length_nil,Nat.le_refl])
  simpa only [Nat.zero_add] using h.trans (by simpa only [Nat.zero_add] using hcap)

theorem padded_clause_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n))
    (clause : Fin 3→Literal (pcp.queryCount n)) (pre suffix : List Bool) (cap : Nat)
    (hcap : uniformBudget (pcp.queryCount n) (pcp.nativeWidth n)≤cap) : ∃ r,
    runFrom machine (uniformBudget (pcp.queryCount n) (pcp.nativeWidth n))
      (ZeroPadding.config (caps cap)
        ⟨machine.start,heads pre,input pre (fun i=>(literalCode (clause i)).bits) suffix
          (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))⟩)=some r ∧
      r.final.tapes 262=ZeroPadding.pad cap (RepairOrdinary.frame (RecoverySourceClauseCode.word pcp x randomness clause)) ∧
      r.final.tapes 159=FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness) ∧
      r.final.tapes 272=RecoverySourceClauseRead.source pre (fun i=>(literalCode (clause i)).bits) suffix ∧
      r.final.heads 272=(pre++RecoverySourceClauseRead.prefixes (fun i=>(literalCode (clause i)).bits) 3).length ∧
      (∀ i : Fin 276,i≠272 → r.final.heads i=0) ∧
      (∀ i,work i → (r.final.tapes i).length≤cap) ∧
      r.steps≤uniformBudget (pcp.queryCount n) (pcp.nativeWidth n) := by
  obtain ⟨base,hbase,bword,baddress,bsource,bpos,bheads,bs⟩ := bounded_clause_run pcp x randomness clause pre suffix
  have support := scratch_support pre (fun i=>(literalCode (clause i)).bits) suffix
    (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)) _ cap base hbase (bs.trans hcap)
  obtain ⟨r,hr,rf,rs,_peak⟩ := ZeroPadding.run_config machine (caps cap) _ _ base hbase
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,rs.trans_le bs⟩
  · rw [rf]
    change ZeroPadding.pad cap (base.final.tapes 262)=_
    rw [bword]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 159)=_
    rw [ZeroPadding.pad_zero,baddress]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 272)=_
    rw [ZeroPadding.pad_zero,bsource]
  · rw [rf]
    exact bpos
  · intro i hi
    rw [rf]
    exact bheads i hi
  · intro i hi
    rw [rf]
    change (ZeroPadding.pad (caps cap i) (base.final.tapes i)).length≤cap
    rw [caps,if_pos hi,ZeroPadding.pad_length]
    exact max_le le_rfl (support i hi)

end NearCubicWires.RepairSource.RecoverySourceClauseLoad
