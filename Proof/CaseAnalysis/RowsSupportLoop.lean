import Proof.CaseAnalysis.RowsSupportRound
import Proof.CaseAnalysis.RowsCircuitBottomLoop

/-! The original serialized bottom count drives the support-retaining round.
Both streams follow the same decoded original occurrence order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape RadixSemantics ExtDecompositionBatch
open CloseoutRowsCircuitBottom CloseoutRowsCircuitBottomLoop CloseoutRowsFamilyLoop
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def supportOutput (threshold : Bool) (core memberPos : ℕ) (membership : List Bool)
    (words : List (List Bool)) (j : ℕ):=
  supportEmitted core (choose threshold membership memberPos j) (words.getD j [])
def supportPrefix (threshold : Bool) (core memberPos : ℕ) (membership : List Bool)
    (words : List (List Bool)) (initial : List Bool) (j : ℕ):=
  initial++(List.range j).flatMap (supportOutput threshold core memberPos membership words)
theorem supportPrefix_succ (threshold : Bool) (core memberPos : ℕ) (membership : List Bool)
    (words : List (List Bool)) (initial : List Bool) (j : ℕ) :
    supportPrefix threshold core memberPos membership words initial (j+1)=
      supportPrefix threshold core memberPos membership words initial j++
        supportOutput threshold core memberPos membership words j:=by
  simp [supportPrefix,List.range_succ,List.append_assoc]

noncomputable def loop (threshold : Bool):=CloseoutRowsDegreeLoop.machine (round threshold)
def budget (cap core count : ℕ):=count*(12*cap+4*core+43)+3
noncomputable def entry (threshold : Bool) (cap core memberPos : ℕ) (flag : Bool)
    (words : List (List Bool)) (supports pre tail membership : List Bool)
    (description wireCount j : ℕ) (out : List Bool):=
  (⟨(round threshold).start,
    extend (heads (pre.length+((words.take j).flatMap frame).length) (memberPos+2*j) out
      (descriptions core words description j) (wires threshold core memberPos membership words wireCount j))
      (supportPrefix threshold core memberPos membership words supports j).length,
    extend (data cap core [] out (pre++words.flatMap frame++tail) membership
      (descriptions core words description j) (wires threshold core memberPos membership words wireCount j)
      (validity core flag words j))
      (supportPrefix threshold core memberPos membership words supports j)⟩ : Configuration 1060 _)

theorem loop_run (threshold : Bool) (cap core memberPos : ℕ) (flag : Bool)
    (words : List (List Bool)) (out supports pre tail membership : List Bool) (description wireCount : ℕ)
    (hin : ∀ bits∈words,2*bits.length+1≤cap)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4≤cap) :
    ∃ actual,runFrom (loop threshold) (budget cap core words.length)
      (RepeatMachine.cfg 0
        (entry threshold cap core memberPos flag words supports pre tail membership description wireCount 0 out)
        words.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry threshold cap core memberPos flag words supports pre tail membership description wireCount words.length
          (out++(List.range words.length).flatMap (outputs threshold core memberPos membership words))) words.length 1 ∧
      actual.steps≤budget cap core words.length := by
  let emit:=outputs threshold core memberPos membership words
  have supplier:∀ j<words.length,∀ acc,∃ actual,
      runFrom (round threshold) (12*cap+4*core+40)
        (entry threshold cap core memberPos flag words supports pre tail membership description wireCount j acc)=some actual ∧
      actual.final.heads=(entry threshold cap core memberPos flag words supports pre tail membership
        description wireCount (j+1) (acc++emit j)).heads ∧
      actual.final.tapes=(entry threshold cap core memberPos flag words supports pre tail membership
        description wireCount (j+1) (acc++emit j)).tapes ∧ actual.steps≤12*cap+4*core+40:=by
    intro j hj acc
    have hmem:words.getD j []∈words:=by
      rw [List.getD_eq_getElem words [] hj]
      exact List.getElem_mem hj
    let fieldPre:=pre++(words.take j).flatMap frame
    let fieldTail:=(words.drop (j+1)).flatMap frame++tail
    obtain ⟨a,ha,ah,atape,asteps⟩:=round_run threshold cap core (memberPos+2*j)
      (words.getD j []) acc (supportPrefix threshold core memberPos membership words supports j)
      fieldPre fieldTail membership (descriptions core words description j)
      (wires threshold core memberPos membership words wireCount j) (validity core flag words j)
      (hin _ hmem) (hcap _ hmem)
    have hs:fieldPre++frame (words.getD j [])++fieldTail=pre++words.flatMap frame++tail:=by
      rw [split_word words [] frame j hj]
      simp only [fieldPre,fieldTail,List.append_assoc]
    have hinput:(⟨(round threshold).start,
        extend (heads fieldPre.length (memberPos+2*j) acc (descriptions core words description j)
          (wires threshold core memberPos membership words wireCount j))
          (supportPrefix threshold core memberPos membership words supports j).length,
        extend (data cap core [] acc (fieldPre++frame (words.getD j [])++fieldTail) membership
          (descriptions core words description j) (wires threshold core memberPos membership words wireCount j)
          (validity core flag words j)) (supportPrefix threshold core memberPos membership words supports j)⟩ :
          Configuration 1060 _)=
        entry threshold cap core memberPos flag words supports pre tail membership description wireCount j acc:=by
      rw [hs]
      simp only [fieldPre,List.length_append,entry]
    rw [hinput] at ha
    refine ⟨a,ha,?_,?_,asteps⟩
    · rw [ah]
      simp only [entry,descriptions,CloseoutRowsCircuitBottomLoop.wires,total_succ,next_word words [] frame j hj,
        fieldPre,List.length_append,frame_length,Nat.mul_add,Nat.mul_one,Nat.add_assoc,
        supportPrefix_succ,supportOutput,choose,emit,outputs]
    · rw [atape,hs]
      simp only [entry,descriptions,CloseoutRowsCircuitBottomLoop.wires,total_succ,validity_succ,
        supportPrefix_succ,supportOutput,choose,emit,outputs]
  exact CloseoutRowsDegreeLoop.loop_run (round threshold)
    (entry threshold cap core memberPos flag words supports pre tail membership description wireCount)
    emit (12*cap+4*core+40) words.length (by intro j hj acc;rfl) supplier out

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
