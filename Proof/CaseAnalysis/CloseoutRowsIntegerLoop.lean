import Proof.CaseAnalysis.RowsIntegerRound
import Proof.CaseAnalysis.RowsFamilyLoop

/-! The literal field-count driver consumes the same canonical integer
stream once, retaining its native word prefix and aggregate codec verdict. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerLoop
open LocalBitMultitape RadixSemantics CloseoutRowsFamilyLoop
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def validity (flag : Bool) (words : List (List Bool)) (j : ℕ) : Bool:=
  flag && (List.range j).all (fun k=>CloseoutRowsIntegerRound.passes (words.getD k []))
theorem validity_succ (flag : Bool) (words : List (List Bool)) (j : ℕ) :
    validity flag words (j+1)=
      (validity flag words j && CloseoutRowsIntegerRound.passes (words.getD j [])):=by
  simp [validity,List.range_succ,Bool.and_assoc]
theorem validity_true (words : List (List Bool)) :
    validity true words words.length=true ↔
      ∀ bits∈words,(CanonicalBinary.decodeInt (value bits)).isSome:=by
  simp only [validity,Bool.true_and,List.all_eq_true,CloseoutRowsIntegerRound.passes,List.mem_range]
  constructor
  · intro h bits hb
    obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hb
    subst bits
    simpa only [List.getD_eq_getElem words [] hi] using h i hi
  · intro h i hi
    rw [List.getD_eq_getElem words [] hi]
    exact h _ (List.getElem_mem hi)

noncomputable def machine:=CloseoutRowsDegreeLoop.machine CloseoutRowsIntegerRound.machine
noncomputable def entry (w : ℕ) (flag : Bool) (words : List (List Bool))
    (pre tail : List Bool) (j : ℕ) (out : List Bool):=
  CloseoutRowsIntegerRound.cfg CloseoutRowsIntegerRound.machine.start (CloseoutRowsIntegerReady.capacity w)
    (pre.length+((words.take j).flatMap frame).length) [] out
    (pre++words.flatMap frame++tail) (validity flag words j)
def budget (w count : ℕ):=count*(5*CloseoutRowsIntegerReady.capacity w+3)+3

theorem integers_run (w : ℕ) (flag : Bool) (words : List (List Bool)) (out pre tail : List Bool)
    (hw : ∀ bits∈words,bits.length≤w) :
    ∃ actual,runFrom machine (budget w words.length)
      (RepeatMachine.cfg 0 (entry w flag words pre tail 0 out) words.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry w flag words pre tail words.length (out++words.flatMap CloseoutRowsCheckedInteger.produced)) words.length 1 ∧
      actual.steps≤budget w words.length:=by
  let emit:=fun j=>CloseoutRowsCheckedInteger.produced (words.getD j [])
  have supplier:∀ j<words.length,∀ acc,∃ actual,
      runFrom CloseoutRowsIntegerRound.machine (5*CloseoutRowsIntegerReady.capacity w)
        (entry w flag words pre tail j acc)=some actual ∧
      actual.final.heads=(entry w flag words pre tail (j+1) (acc++emit j)).heads ∧
      actual.final.tapes=(entry w flag words pre tail (j+1) (acc++emit j)).tapes ∧
      actual.steps≤5*CloseoutRowsIntegerReady.capacity w:=by
    intro j hj acc
    have hmem:words.getD j []∈words:=by
      rw [List.getD_eq_getElem words [] hj]
      exact List.getElem_mem hj
    let fieldPre:=pre++(words.take j).flatMap frame
    let fieldTail:=(words.drop (j+1)).flatMap frame++tail
    obtain ⟨a,ha,asteps,ah,atape⟩:=CloseoutRowsIntegerRound.round_run w (words.getD j []) acc
      fieldPre fieldTail (validity flag words j) (hw _ hmem)
    have hs:fieldPre++frame (words.getD j [])++fieldTail=pre++words.flatMap frame++tail:=by
      rw [split_word words [] frame j hj]
      simp only [fieldPre,fieldTail,List.append_assoc]
    have hinput:CloseoutRowsIntegerRound.cfg CloseoutRowsIntegerRound.machine.start (CloseoutRowsIntegerReady.capacity w) fieldPre.length [] acc
        (fieldPre++frame (words.getD j [])++fieldTail) (validity flag words j)=
        entry w flag words pre tail j acc:=by
      rw [hs]
      apply configuration_ext
      · rfl
      · simp only [fieldPre,List.length_append,entry,CloseoutRowsIntegerRound.cfg]
      · rfl
    rw [hinput] at ha
    have hb:=CloseoutRowsIntegerRound.budget_bound w (words.getD j []) (hw _ hmem)
    have more:=runFrom_moreFuel CloseoutRowsIntegerRound.machine _
      (5*CloseoutRowsIntegerReady.capacity w-CloseoutRowsIntegerRound.budget w (words.getD j [])) _ a ha
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨a,more,?_,?_,asteps.trans hb⟩
    · rw [ah]
      change CloseoutRowsIntegerRound.heads (acc++emit j) (fieldPre.length+2*(words.getD j []).length+1)=
        CloseoutRowsIntegerRound.heads (acc++emit j) (pre.length+((words.take (j+1)).flatMap frame).length)
      rw [next_word words [] frame j hj]
      simp only [fieldPre,List.length_append,frame_length,Nat.add_assoc]
    · rw [atape]
      change CloseoutRowsIntegerRound.data (CloseoutRowsIntegerReady.capacity w) [] (acc++emit j)
        (fieldPre++frame (words.getD j [])++fieldTail)
        (validity flag words j && CloseoutRowsIntegerRound.passes (words.getD j []))=_
      rw [hs,←validity_succ]
      rfl
  obtain ⟨actual,ha,hf,ht⟩:=CloseoutRowsDegreeLoop.loop_run CloseoutRowsIntegerRound.machine
    (entry w flag words pre tail) emit (5*CloseoutRowsIntegerReady.capacity w) words.length
    (by intro j hj acc;rfl) supplier out
  have hout:(List.range words.length).flatMap emit=words.flatMap CloseoutRowsCheckedInteger.produced:=
    flatMap_index words [] CloseoutRowsCheckedInteger.produced
  rw [hout] at hf
  exact ⟨actual,ha,hf,ht⟩

theorem produced_eq (bits : List Bool) (z : ℤ)
    (hz : CanonicalBinary.decodeInt (value bits)=some z) :
    CloseoutRowsCheckedInteger.produced bits=RepairRepresentation.intWord z:=by
  obtain ⟨r,_,_,rt,_,_,_,_,typed⟩:=CloseoutRowsCheckedInteger.native_run bits [] []
  exact (List.nil_append _).symm.trans (rt.symm.trans ((typed z hz).trans (List.nil_append _)))

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerLoop
