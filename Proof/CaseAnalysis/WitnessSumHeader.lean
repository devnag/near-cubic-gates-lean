import Proof.CaseAnalysis.WitnessSumCountStream
import Proof.PCP.PCPSerializerTapeSupport

/-! The all-raw sum header uses one reusable allocated bank. Its exact
term fields and actual count feed the existing loop directly. The source
arity and cap ports are retained without imposing a workspace bound on them. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumHeader
open LocalBitMultitape RecoveryRootRound PCPPNativeCanonicalWalk RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def capacity (H : ℕ) (i : Fin 510) :=
  if i.val=499 then 1 else if i.val=501 ∨ i.val=502 then 0 else H
def input (H : ℕ) (bits arityBits : List Bool) (T : ℕ) (i : Fin 510) :=
  ZeroPadding.pad (capacity H i) (SumGuard.input bits arityBits T i)
def flag (bits arityBits : List Bool) (T : ℕ) : Bool := by
  classical
  exact decide (SumGuard.Passes bits arityBits T)
def words (bits : List Bool) := Reencode.fields (SumFields.listCode bits)
def tail (H : ℕ) (bits : List Bool) :=
  List.replicate (H-((words bits).flatMap frame).length) false

theorem words_count (bits : List Bool) : (words bits).length=SumFields.count bits := by
  simp only [words,Reencode.fields,List.length_map,SumFields.count,SumFields.atoms]
theorem words_stream (bits : List Bool) :
    (words bits).flatMap frame=atomStream (SumFields.listCode bits).length (SumFields.atoms bits) := by
  simp only [words,Reencode.fields,List.flatMap_map,SumFields.atoms,atomStream]

theorem header_run (H T : ℕ) (bits arityBits : List Bool)
    (hraw : 2*bits.length+1 ≤ H) (hbudget : SumGuard.budget bits arityBits T+1 ≤ H) :
    ∃ output,ClockJoin.ReadyRun SumGuard.machine (SumGuard.budget bits arityBits T)
      (input H bits arityBits T) output ∧
      output 501=frame arityBits ∧ output 502=List.replicate T true ∧
      output 357=(words bits).flatMap frame++tail H bits ∧
      output 368=ZeroPadding.pad H (CompareMachine.word (SumFields.count bits)) ∧
      output 504=ZeroPadding.pad H (List.replicate (SumFields.count bits) true) ∧
      output 499=[flag bits arityBits T] ∧
      (∀ i : Fin 510,i≠501 → i≠502 → (output i).length ≤ H) := by
  classical
  obtain ⟨out,⟨base,hr,ht,hh,hs⟩,arity,cap,stream,count,rawCount,verdict⟩ := SumGuard.guard_run bits arityBits T
  have bound (i : Fin 510) (h501 : i≠501) (h502 : i≠502) : (base.final.tapes i).length ≤ H := by
    have hi : (SumGuard.input bits arityBits T i).length ≤ H := by
      unfold SumGuard.input
      split_ifs with h1
      · simpa only [frame_length] using hraw
      · exact (h501 (Fin.ext ‹i.val=501›)).elim
      · exact (h502 (Fin.ext ‹i.val=502›)).elim
      · simp
    have h := PCPSerializerReuse.tape_support SumGuard.machine _ _ base hr i H 0 (by rfl)
      (hi.trans (Nat.le_max_left _ _))
    have hs' : base.steps+1 ≤ H := by omega
    simpa only [Nat.zero_add,max_eq_left hs'] using h
  obtain ⟨r,run,rf,rs,_⟩ := ZeroPadding.run_config SumGuard.machine (capacity H) _ _ base hr
  have fields (i : Fin 510) : r.final.tapes i=ZeroPadding.pad (capacity H i) (out i) := by
    rw [rf]
    change ZeroPadding.pad _ (base.final.tapes i)=_
    rw [ht]
  refine ⟨r.final.tapes,⟨r,run,rfl,?_,rs.trans_le hs⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i;rw [rf];exact hh i
  · rw [fields,arity];exact ZeroPadding.pad_zero _
  · rw [fields,cap];exact ZeroPadding.pad_zero _
  · rw [fields,stream,←words_stream]
    rfl
  · rw [fields,count];rfl
  · rw [fields,rawCount];rfl
  · rw [fields,verdict]
    change ZeroPadding.pad 1 [decide (SumGuard.Passes bits arityBits T)]=[flag bits arityBits T]
    simp only [ZeroPadding.pad,List.length_singleton,Nat.sub_self,List.replicate_zero,List.append_nil,flag]
  · intro i h501 h502
    rw [rf]
    change (ZeroPadding.pad (capacity H i) (base.final.tapes i)).length ≤ H
    rw [ZeroPadding.pad_length]
    apply max_le _ (bound i h501 h502)
    unfold capacity
    split_ifs <;> omega

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumHeader
