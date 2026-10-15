import Proof.CaseAnalysis.WitnessFamilyLoopData
import Proof.CaseAnalysis.WitnessFamilyCount

/-! The same canonical outer list produces the actual V driver and the
ordered original sum fields. The already-produced source V is retained
without charging its magnitude as raw parsing scratch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFields
open LocalBitMultitape RecoveryRootRound PCPPNativeCanonicalWalk PCPPNativeCanonicalTree
open RepairSource.VerifierDecoding RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (H : ℕ) (i : Fin 177):=if i.val=172 then 1 else if i.val=174 then 0 else H
def input (H V : ℕ) (bits : List Bool) (i : Fin 177):=
  ZeroPadding.pad (capacity H i) (FamilyCount.input bits V i)
def words (bits : List Bool):=Reencode.fields bits
def tail (H : ℕ) (bits : List Bool):=List.replicate (H-((words bits).flatMap frame).length) false

theorem words_count (bits : List Bool) : (words bits).length=FamilyCount.count bits := by
  simp only [words,Reencode.fields,List.length_map,FamilyCount.count]

theorem words_stream (bits : List Bool) :
    (words bits).flatMap frame=atomStream bits.length (tree (value bits)).atoms := by
  simp only [words,Reencode.fields,List.flatMap_map,atomStream]

theorem header_run (H V : ℕ) (bits : List Bool) (hraw : 2*bits.length+1 ≤ H)
    (hbudget : FamilyCount.budget bits V+1 ≤ H) :
    ∃ output,ClockJoin.ReadyRun FamilyCount.machine (FamilyCount.budget bits V) (input H V bits) output ∧
      output 174=List.replicate V true ∧ output 30=(words bits).flatMap frame++tail H bits ∧
      output 41=ZeroPadding.pad H (CompareMachine.word (FamilyCount.count bits)) ∧
      output 172=[FamilyCount.accepted bits V] ∧
      (∀ i : Fin 177,i≠174 → (output i).length ≤ H) := by
  obtain ⟨out,⟨base,hr,bt,bh,bs⟩,_raw,actual,stream,count,flag⟩:=FamilyCount.count_run bits V
  have support (i : Fin 177) (hi : i≠174) : (base.final.tapes i).length ≤ H := by
    have initial : (FamilyCount.input bits V i).length ≤ H := by
      unfold FamilyCount.input
      split_ifs with hz
      · simpa only [frame_length] using hraw
      · exact (hi (Fin.ext ‹i.val=174›)).elim
      · simp
    have bound:=PCPSerializerReuse.tape_support FamilyCount.machine _ _ base hr i H 0 (by rfl)
      (initial.trans (Nat.le_max_left _ _))
    have steps:base.steps+1 ≤ H:=by omega
    simpa only [Nat.zero_add,max_eq_left steps] using bound
  obtain ⟨r,run,rf,rs,_⟩:=ZeroPadding.run_config FamilyCount.machine (capacity H) _ _ base hr
  have fields (i : Fin 177) : r.final.tapes i=ZeroPadding.pad (capacity H i) (out i) := by
    rw [rf]
    change ZeroPadding.pad _ (base.final.tapes i)=_
    rw [bt]
  refine ⟨r.final.tapes,⟨r,run,rfl,?_,rs.trans_le bs⟩,?_,?_,?_,?_,?_⟩
  · intro i;rw [rf];exact bh i
  · rw [fields,actual];exact ZeroPadding.pad_zero _
  · rw [fields,stream,←words_stream];rfl
  · rw [fields,count];rfl
  · rw [fields,flag]
    change ZeroPadding.pad 1 [FamilyCount.accepted bits V]=[FamilyCount.accepted bits V]
    simp only [ZeroPadding.pad,List.length_singleton,Nat.sub_self,List.replicate_zero,List.append_nil]
  · intro i hi
    rw [rf]
    change (ZeroPadding.pad (capacity H i) (base.final.tapes i)).length ≤ H
    rw [ZeroPadding.pad_length]
    apply max_le _ (support i hi)
    unfold capacity
    split_ifs <;> omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFields
