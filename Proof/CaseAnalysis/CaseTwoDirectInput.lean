import Proof.CaseAnalysis.CaseTwoSelectedOutput

/-! The selected Case2 machine has exactly five cold input words. All
capacity, tag, counter and log initialization is already paid inside Cold. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.DirectInput
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)

def tapes (k D copies : ℕ):=SelectedOutput.tapes source a k D copies
def ports (k D copies : ℕ) (j : Fin 5) : Fin (tapes source a k D copies):=
  SelectedOutput.old source a k D copies (Execution.old source a k D copies (j.castAdd 135))
def hierarchyPort (k D copies : ℕ):=ports source a k D copies 0
def descriptionPort (k D copies : ℕ):=ports source a k D copies 1
def addressPort (k D copies : ℕ):=ports source a k D copies 2
def rPort (k D copies : ℕ):=ports source a k D copies 3
def boundPort (k D copies : ℕ):=ports source a k D copies 4
def outputPort (k D copies : ℕ):=SelectedOutput.fresh source a k D copies 0
def words (hierarchy description address : List Bool) (R B : ℕ) : Fin 5→List Bool:=
  ![hierarchy,description,address,List.replicate R true,List.replicate B true]
def input (k D copies : ℕ) (hierarchy description address : List Bool) (R B : ℕ):=
  SelectedOutput.input source a k D copies
    (Execution.input source a k D copies hierarchy description address R B)

theorem port_value (k D copies : ℕ) (j : Fin 5) : (ports source a k D copies j).val=j.val:=rfl
theorem ports_injective (k D copies : ℕ) : Function.Injective (ports source a k D copies):=by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin (tapes source a k D copies)=>z.val) h)
theorem output_outside (k D copies : ℕ) (j : Fin 5) : ports source a k D copies j≠outputPort source a k D copies:=by
  intro h
  have hj:=j.isLt
  have hv:=congrArg Fin.val h
  change j.val=140+Execution.foldTapes source a k D copies at hv
  omega

theorem input_port (k D copies : ℕ) (hierarchy description address : List Bool) (R B : ℕ) (j : Fin 5) :
    input source a k D copies hierarchy description address R B (ports source a k D copies j)=
      words hierarchy description address R B j:=by
  have hp : (j.castAdd 135 : Fin 140)=(j.castAdd 130).castAdd 5:=rfl
  simp only [input,ports,SelectedOutput.old,SelectedOutput.input,Execution.old,
    Execution.input,Fin.addCases_left,hp,PreparedFrames.input,Fin.addCases_left]
  fin_cases j <;>simp [Cold.input,words]

theorem input_empty (k D copies : ℕ) (hierarchy description address : List Bool) (R B : ℕ)
    (i : Fin (tapes source a k D copies)) (hi : 5 ≤ i.val) :
    input source a k D copies hierarchy description address R B i=[]:=by
  revert hi
  refine Fin.addCases (m:=Execution.tapes source a k D copies) (n:=2) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=140) (n:=Execution.foldTapes source a k D copies) (fun z=>?_) (fun z=>?_) j
    · refine Fin.addCases (m:=135) (n:=5) (fun t=>?_) (fun t=>?_) z
      · intro ht
        change 5 ≤ t.val at ht
        have hn (q : Fin 135) (hq : q.val < 5) : t≠q:=by
          intro h
          have hv:=congrArg Fin.val h
          omega
        simp only [input,SelectedOutput.input,Execution.input,PreparedFrames.input,Fin.addCases_left,
          Cold.input,if_neg (hn 0 (by decide)),if_neg (hn 1 (by decide)),
          if_neg (hn 2 (by decide)),if_neg (hn 3 (by decide)),if_neg (hn 4 (by decide))]
      · intro _
        simp only [input,SelectedOutput.input,Execution.input,PreparedFrames.input,Fin.addCases_left,Fin.addCases_right]
    · intro _
      simp only [input,SelectedOutput.input,Execution.input,Fin.addCases_left,Fin.addCases_right]
  · intro _
    simp only [input,SelectedOutput.input,Fin.addCases_right]

theorem input_characterization (k D copies : ℕ) (hierarchy description address : List Bool) (R B : ℕ)
    (i : Fin (tapes source a k D copies)) :
    input source a k D copies hierarchy description address R B i=
      if h : i.val < 5 then words hierarchy description address R B ⟨i.val,h⟩ else []:=by
  by_cases hi : i.val < 5
  · rw [dif_pos hi]
    have he : i=ports source a k D copies ⟨i.val,hi⟩:=Fin.ext rfl
    exact (congrArg (input source a k D copies hierarchy description address R B) he).trans
      (input_port source a k D copies hierarchy description address R B _)
  · rw [dif_neg hi]
    exact input_empty source a k D copies hierarchy description address R B i (by omega)

theorem entry_eq (k D copies : ℕ) (hierarchy description address : List Bool) (R B : ℕ)
    (bank : Fin (tapes source a k D copies)→List Bool)
    (hfields : ∀ j,bank (ports source a k D copies j)=words hierarchy description address R B j)
    (hwork : ∀ i,5 ≤ i.val → bank i=[]) :
    bank=input source a k D copies hierarchy description address R B:=by
  funext i
  by_cases hi : i.val < 5
  · have he : i=ports source a k D copies ⟨i.val,hi⟩:=Fin.ext rfl
    rw [he,hfields,input_port]
  · exact (hwork i (by omega)).trans (input_empty source a k D copies hierarchy description address R B i (by omega)).symm

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.DirectInput
