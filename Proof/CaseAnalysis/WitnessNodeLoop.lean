import Proof.CaseAnalysis.WitnessNodeRound
import Proof.CaseAnalysis.WitnessDAGMeaning
import Proof.CaseAnalysis.RowsFamilyLoop

/-! Reuse the accepted counted loop on the actual canonical node-field
stream. Each round retains its source cursor and growing native descriptor;
exhaustion includes the physical rewind of the literal count driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeLoop
open LocalBitMultitape RadixSemantics SignedSortKey CloseoutRowsFamilyLoop
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def validity (n : ℕ) (flag : Bool) (words : List (List Bool)) (j : ℕ) : Bool:=
  flag && (List.range j).all (fun k=>NodeRound.passes n k (words.getD k []))

theorem validity_succ (n : ℕ) (flag : Bool) (words : List (List Bool)) (j : ℕ) :
    validity n flag words (j+1)=
      (validity n flag words j && NodeRound.passes n j (words.getD j [])):=by
  simp [validity,List.range_succ,Bool.and_assoc]

theorem validity_true (n : ℕ) (words : List (List Bool)) :
    validity n true words words.length=true ↔
      ∀ i : Fin words.length,NodeMeaning.valid n i.val (words.get i):=by
  classical
  simp only [validity,Bool.true_and,List.all_eq_true,NodeRound.passes,decide_eq_true_eq,
    List.mem_range]
  constructor
  · intro h i
    simpa only [List.getD_eq_getElem words [] i.isLt,List.get_eq_getElem] using h i.val i.isLt
  · intro h i hi
    simpa only [List.getD_eq_getElem words [] hi,List.get_eq_getElem] using h ⟨i,hi⟩

noncomputable def machine:=CloseoutRowsDegreeLoop.machine NodeRound.machine
noncomputable def entry (w : ℕ) (left : List Bool) (flag : Bool)
    (words : List (List Bool)) (pre tail : List Bool) (j : ℕ) (out : List Bool):=
  NodeRound.cfg NodeRound.machine.start (NodeReady.capacity w) w
    (pre.length+((words.take j).flatMap frame).length) left (binary w j) [] out
    (pre++words.flatMap frame++tail) (validity (value left) flag words j)
def budget (w count : ℕ):=count*(5*NodeReady.capacity w+3)+3

theorem nodes_run (w : ℕ) (left : List Bool) (flag : Bool)
    (words : List (List Bool)) (out pre tail : List Bool)
    (hl : left.length=w) (hw : ∀ bits∈words,bits.length+1≤w)
    (hcount : words.length<2^w) :
    ∃ actual,runFrom machine (budget w words.length)
      (RepeatMachine.cfg 0 (entry w left flag words pre tail 0 out) words.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry w left flag words pre tail words.length (out++words.flatMap DAGMeaning.emitted)) words.length 1 ∧
      actual.steps≤budget w words.length:=by
  let emit:=fun j=>DAGMeaning.emitted (words.getD j [])
  have supplier:∀ j<words.length,∀ acc,∃ actual,
      runFrom NodeRound.machine (5*NodeReady.capacity w)
        (entry w left flag words pre tail j acc)=some actual ∧
      actual.final.heads=(entry w left flag words pre tail (j+1) (acc++emit j)).heads ∧
      actual.final.tapes=(entry w left flag words pre tail (j+1) (acc++emit j)).tapes ∧
      actual.steps≤5*NodeReady.capacity w:=by
    intro j hj acc
    have hmem:words.getD j []∈words:=by
      rw [List.getD_eq_getElem words [] hj]
      exact List.getElem_mem hj
    let nodePre:=pre++(words.take j).flatMap frame
    let nodeTail:=(words.drop (j+1)).flatMap frame++tail
    obtain ⟨a,ha,asteps,ah,atape⟩:=NodeRound.round_run w j left (words.getD j []) acc nodePre nodeTail
      (validity (value left) flag words j) hl (hw _ hmem) (by omega)
    have hs:nodePre++frame (words.getD j [])++nodeTail=pre++words.flatMap frame++tail:=by
      rw [split_word words [] frame j hj]
      simp only [nodePre,nodeTail,List.append_assoc]
    have hinput:NodeRound.cfg NodeRound.machine.start (NodeReady.capacity w) w nodePre.length
        left (binary w j) [] acc (nodePre++frame (words.getD j [])++nodeTail)
        (validity (value left) flag words j)=entry w left flag words pre tail j acc:=by
      rw [hs]
      apply configuration_ext
      · rfl
      · simp only [nodePre,List.length_append,entry,NodeRound.cfg]
      · rfl
    rw [hinput] at ha
    have hb:=NodeRound.budget_bound w (words.getD j []) (hw _ hmem)
    have more:=runFrom_moreFuel NodeRound.machine _
      (5*NodeReady.capacity w-NodeRound.budget w (words.getD j [])) _ a ha
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨a,more,?_,?_,asteps.trans hb⟩
    · rw [ah]
      change NodeRound.heads (acc++emit j) (nodePre.length+2*(words.getD j []).length+1)=
        NodeRound.heads (acc++emit j) (pre.length+((words.take (j+1)).flatMap frame).length)
      rw [next_word words [] frame j hj]
      simp only [nodePre,List.length_append,frame_length,Nat.add_assoc]
    · rw [atape]
      change NodeRound.data (NodeReady.capacity w) w left (binary w (j+1)) [] (acc++emit j)
        (nodePre++frame (words.getD j [])++nodeTail)
        (validity (value left) flag words j && NodeRound.passes (value left) j (words.getD j []))=_
      rw [hs,←validity_succ]
      rfl
  obtain ⟨actual,ha,hf,ht⟩:=CloseoutRowsDegreeLoop.loop_run NodeRound.machine
    (entry w left flag words pre tail) emit (5*NodeReady.capacity w) words.length
    (by intro j hj acc;rfl) supplier out
  have hout:(List.range words.length).flatMap emit=words.flatMap DAGMeaning.emitted:=
    flatMap_index words [] DAGMeaning.emitted
  rw [hout] at hf
  exact ⟨actual,ha,hf,ht⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeLoop
