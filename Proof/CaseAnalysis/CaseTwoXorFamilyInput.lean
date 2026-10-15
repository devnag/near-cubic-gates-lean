import Proof.CaseAnalysis.CaseTwoFixedFoldRun

/-! The restored complete block and the fixed-fold ABI have exactly the
same three framed input words and one accumulator cell. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def wordInput {t : ℕ} (words : Fin 3→List Bool) (j : Fin t) : List Bool:=
  if h : j.val<3 then words ⟨j.val,h⟩ else []
theorem extend_words {t e : ℕ} (ht : 3≤t) (words : Fin 3→List Bool) :
    (Fin.addCases (wordInput (t:=t) words) (fun _ : Fin e=>[]))=wordInput (t:=t+e) words:=by
  funext j
  refine Fin.addCases (motive:=fun j=>(Fin.addCases (m:=t) (n:=e) (motive:=fun _=>List Bool)
      (wordInput (t:=t) words) (fun _ : Fin e=>[])) j=
      wordInput words j) (fun j=>?_) (fun j=>?_) j
  · simp only [Fin.addCases_left,wordInput,Fin.val_castAdd]
  · simp only [Fin.addCases_right,wordInput,Fin.val_natAdd]
    rw [dif_neg (by omega)]
theorem extend_accumulator {t : ℕ} (ht : 3≤t) (words : Fin 3→List Bool) (parity : Bool) :
    XorBody.input (wordInput (t:=t) words) parity=FixedFold.bodyInput (Fin.last t) words parity:=by
  funext j
  refine Fin.addCases (motive:=fun j=>XorBody.input (wordInput (t:=t) words) parity j=
      FixedFold.bodyInput (Fin.last t) words parity j) (fun j=>?_) (fun j : Fin 1=>?_) j
  · have hj : j.val≠t:=Nat.ne_of_lt j.isLt
    simp only [XorBody.input,Fin.addCases_left,wordInput,FixedFold.bodyInput,Fin.val_castAdd,Fin.val_last,hj,if_false]
  · have hj : j.val=0:=by have hb:=j.isLt;omega
    simp only [XorBody.input,Fin.addCases_right,FixedFold.bodyInput,Fin.val_natAdd,Fin.val_last,hj,Nat.add_zero]
    rw [dif_neg (by omega)]
    rfl

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
def words (hierarchy descriptor address : List Bool) : Fin 3→List Bool:=
  ![frame hierarchy,frame descriptor,frame address]
theorem source_input (k : ℕ) (hierarchy descriptor address : List Bool) :
    SourceBlock.input source a k hierarchy descriptor address=wordInput (words hierarchy descriptor address):=by
  funext j
  by_cases hj : j.val<3
  · let i : Fin 3:=⟨j.val,hj⟩
    have small (i : Fin 3) : (if i.val=0 then frame hierarchy else if i.val=1 then frame descriptor
        else if i.val=2 then frame address else [])=words hierarchy descriptor address i:=by
      fin_cases i <;>rfl
    unfold wordInput
    rw [dif_pos hj]
    exact small i
  · simp only [SourceBlock.input,wordInput,dif_neg hj]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
theorem reset_input (k D : ℕ) (hierarchy descriptor address : List Bool) :
    WholeBlock.resetInput source a k D hierarchy descriptor address=
      wordInput (words hierarchy descriptor address):=by
  have hs : 3≤SourceBlock.tapes source a k:=by unfold SourceBlock.tapes;omega
  have hw : 3≤WholeBlock.tapes source a k D:=by unfold WholeBlock.tapes;omega
  have hwhole : WholeBlock.input source a k D hierarchy descriptor address=
      wordInput (t:=WholeBlock.tapes source a k D) (words hierarchy descriptor address):=by
    unfold WholeBlock.input
    rw [source_input]
    exact extend_words hs _
  unfold WholeBlock.resetInput
  rw [hwhole]
  exact extend_words hw _
def tapes (k D : ℕ):=WholeBlock.tapes source a k D+1+1
def accumulator (k D : ℕ) : Fin (tapes source a k D):=Fin.last (WholeBlock.tapes source a k D+1)
theorem accumulator_lower (k D : ℕ) : 3≤(accumulator source a k D).val:=by
  have hs : 3≤SourceBlock.tapes source a k:=by unfold SourceBlock.tapes;omega
  change 3≤WholeBlock.tapes source a k D+1
  unfold WholeBlock.tapes
  omega
theorem body_input (k D : ℕ) (hierarchy descriptor address : List Bool) (parity : Bool) :
    XorBody.input (WholeBlock.resetInput source a k D hierarchy descriptor address) parity=
      FixedFold.bodyInput (accumulator source a k D) (words hierarchy descriptor address) parity:=by
  rw [reset_input]
  exact extend_accumulator (accumulator_lower source a k D) _ parity

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorFamily
