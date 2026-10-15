import Proof.CaseAnalysis.RowsCircuitBottomRound
import Proof.CaseAnalysis.RowsFamilyLoop

/-! The actual serialized bottom count drives the complete reusable worker.
Every original field is parsed once; only retained fields emit native words,
and the source, membership, output and resource cursors remain explicit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomLoop
open LocalBitMultitape RadixSemantics CloseoutRowsCircuitBottom CloseoutRowsFamilyLoop
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def total (cost : ℕ→ℕ) (initial j : ℕ):=initial+((List.range j).map cost).sum
theorem total_succ (cost : ℕ→ℕ) (initial j : ℕ) :
    total cost initial (j+1)=total cost initial j+cost j:=by
  simp [total,List.range_succ,Nat.add_assoc]
def validity (core : ℕ) (flag : Bool) (words : List (List Bool)) (j : ℕ):=
  flag && (List.range j).all (fun k=>passed core (words.getD k []))
theorem validity_succ (core : ℕ) (flag : Bool) (words : List (List Bool)) (j : ℕ) :
    validity core flag words (j+1)=(validity core flag words j && passed core (words.getD j [])):=by
  simp [validity,List.range_succ,Bool.and_assoc]
def choose (threshold : Bool) (membership : List Bool) (memberPos j : ℕ):=
  kept threshold membership (memberPos+2*j)
def outputs (threshold : Bool) (core memberPos : ℕ) (membership : List Bool)
    (words : List (List Bool)) (j : ℕ):=
  emitted core (choose threshold membership memberPos j) (words.getD j [])
def descriptions (core : ℕ) (words : List (List Bool)) (initial j : ℕ):=
  total (fun k=>descriptionCost core (words.getD k [])) initial j
def wires (threshold : Bool) (core memberPos : ℕ) (membership : List Bool)
    (words : List (List Bool)) (initial j : ℕ):=
  total (fun k=>wireCost core (choose threshold membership memberPos k) (words.getD k [])) initial j
noncomputable def machine (threshold : Bool):=CloseoutRowsDegreeLoop.machine (round threshold)
noncomputable def entry (threshold : Bool) (cap core memberPos : ℕ) (flag : Bool)
    (words : List (List Bool)) (pre tail membership : List Bool) (description wireCount j : ℕ)
    (out : List Bool):=
  cfg (round threshold).start cap core (pre.length+((words.take j).flatMap frame).length) (memberPos+2*j) [] out
    (pre++words.flatMap frame++tail) membership (descriptions core words description j)
    (wires threshold core memberPos membership words wireCount j) (validity core flag words j)
def budget (cap count : ℕ):=count*(12*cap+33)+3

theorem bottoms_run (threshold : Bool) (cap core memberPos : ℕ) (flag : Bool)
    (words : List (List Bool)) (out pre tail membership : List Bool) (description wireCount : ℕ)
    (hin : ∀ bits∈words,2*bits.length+1 ≤ cap)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4 ≤ cap) :
    ∃ actual,runFrom (machine threshold) (budget cap words.length)
      (RepeatMachine.cfg 0 (entry threshold cap core memberPos flag words pre tail membership description wireCount 0 out)
        words.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry threshold cap core memberPos flag words pre tail membership description wireCount words.length
          (out++(List.range words.length).flatMap (outputs threshold core memberPos membership words))) words.length 1 ∧
      actual.steps ≤ budget cap words.length:=by
  let emit:=outputs threshold core memberPos membership words
  have supplier:∀ j<words.length,∀ acc,∃ actual,
      runFrom (round threshold) (12*cap+30)
        (entry threshold cap core memberPos flag words pre tail membership description wireCount j acc)=some actual ∧
      actual.final.heads=(entry threshold cap core memberPos flag words pre tail membership description wireCount
        (j+1) (acc++emit j)).heads ∧
      actual.final.tapes=(entry threshold cap core memberPos flag words pre tail membership description wireCount
        (j+1) (acc++emit j)).tapes ∧ actual.steps ≤ 12*cap+30:=by
    intro j hj acc
    have hmem:words.getD j []∈words:=by
      rw [List.getD_eq_getElem words [] hj]
      exact List.getElem_mem hj
    let fieldPre:=pre++(words.take j).flatMap frame
    let fieldTail:=(words.drop (j+1)).flatMap frame++tail
    obtain ⟨a,ha,asteps,ah,atape⟩:=round_run threshold cap core (memberPos+2*j) (words.getD j []) acc
      fieldPre fieldTail membership (descriptions core words description j)
      (wires threshold core memberPos membership words wireCount j) (validity core flag words j)
      (hin _ hmem) (hcap _ hmem)
    have hs:fieldPre++frame (words.getD j [])++fieldTail=pre++words.flatMap frame++tail:=by
      rw [split_word words [] frame j hj]
      simp only [fieldPre,fieldTail,List.append_assoc]
    have hinput:cfg (round threshold).start cap core fieldPre.length (memberPos+2*j) [] acc
        (fieldPre++frame (words.getD j [])++fieldTail) membership (descriptions core words description j)
        (wires threshold core memberPos membership words wireCount j) (validity core flag words j)=
        entry threshold cap core memberPos flag words pre tail membership description wireCount j acc:=by
      rw [hs]
      simp only [fieldPre,List.length_append,entry]
    rw [hinput] at ha
    refine ⟨a,ha,?_,?_,asteps⟩
    · rw [ah]
      change heads (fieldPre.length+2*(words.getD j []).length+1) (memberPos+2*j+2) (acc++emit j)
        (descriptions core words description j+descriptionCost core (words.getD j []))
        (wires threshold core memberPos membership words wireCount j+
          wireCost core (choose threshold membership memberPos j) (words.getD j []))=_
      simp only [entry,cfg,descriptions,wires,total_succ,next_word words [] frame j hj,
        fieldPre,List.length_append,frame_length,Nat.mul_add,Nat.mul_one,Nat.add_assoc]
    · rw [atape]
      change data cap core [] (acc++emit j) (fieldPre++frame (words.getD j [])++fieldTail) membership
        (descriptions core words description j+descriptionCost core (words.getD j []))
        (wires threshold core memberPos membership words wireCount j+
          wireCost core (choose threshold membership memberPos j) (words.getD j []))
        (validity core flag words j && passed core (words.getD j []))=_
      rw [hs]
      simp only [entry,cfg,descriptions,wires,total_succ,validity_succ]
  exact CloseoutRowsDegreeLoop.loop_run (round threshold)
    (entry threshold cap core memberPos flag words pre tail membership description wireCount)
    emit (12*cap+30) words.length (by intro j hj acc;rfl) supplier out

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomLoop
