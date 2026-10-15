import Proof.MachineModel.OrdinaryMatrixScoreShiftedArithmetic

/-! Actual linear-size score capacity producer. Two existing field printers
supply C=4W+18 and preserve raw W; no runtime arithmetic is a free operation. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreCapacity
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (w : ℕ) := 4*w+18
def slots : Fin 6 → Fin 11 := ![3,6,7,8,9,10]
def first : Machine 11 14 := TapeEmbedding.machine 5 ClockFields.machine
noncomputable def last : Machine 11 14 := RecoveryFocus.machine slots ClockFields.machine
noncomputable def machine := Composition.machine first last
def input (w : ℕ) : Fin 11 → List Bool := fun i => if i.val=0 then List.replicate w true else []

theorem capacity_run (w : ℕ) :
    ∃ actual : ExecutionReceipt 11 28,
      run machine (12*w+69) (input w)=some actual ∧
      actual.final.tapes 0=List.replicate w true ∧
      actual.final.tapes 1=frame (List.replicate w false++[true]) ∧
      actual.final.tapes 8=List.replicate (capacity w) true ∧
      (∀ i,actual.final.heads i=0) ∧ actual.steps=12*w+69 := by
  obtain ⟨base,hb,b0,b1,_,b3,_,_,bh,bs⟩ := ClockFields.fields_run w
  have he := TapeEmbedding.run_embed ClockFields.machine (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base
  have ph : ∀ i,prepared.final.heads i=0 := by
    intro i
    fin_cases i <;> simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bh]
  obtain ⟨expanded,hx,_,_,_,x3,_,_,xh,xs⟩ := ClockFields.fields_run (2*(w+3))
  have capEq : 2*(2*(w+3)+3)=capacity w := by unfold capacity; omega
  rw [capEq] at x3
  let entry := initialConfiguration ClockFields.machine
    (Fin.addCases (m := 5) (n := 1) (motive := fun _ => List Bool)
      ![List.replicate (2*(w+3)) true,[],[],[],[]] (fun _ => []))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simp [ph,entry,initialConfiguration]
    · intro i
      fin_cases i
      · exact b3
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) ClockFields.machine
    prepared.final.heads prepared.final.tapes _ entry expanded hx
  rw [hi] at hf
  have hj := Composition.run_join first last (4*w+22) (4*(2*(w+3))+22) _ prepared focused he hf
  have hin : Composition.leftConfig 14 (TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => [])
      (initialConfiguration ClockFields.machine
        (Fin.addCases (m := 5) (n := 1) (motive := fun _ => List Bool)
          ![List.replicate w true,[],[],[],[]] (fun _ => []))))=
      initialConfiguration machine (input w) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,initialConfiguration,input]
  rw [hin] at hj
  have htime : (4*w+22)+1+(4*(2*(w+3))+22)=12*w+69 := by omega
  rw [htime] at hj
  have other (i : Fin 6) (hn : RecoveryFocus.pick slots (i.castAdd 5)=none) :
      focused.final.tapes (i.castAdd 5)=base.final.tapes i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  refine ⟨Composition.joinedReceipt prepared focused,hj,(other 0 (by decide)).trans b0,
    (other 1 (by decide)).trans b1,?_,?_,?_⟩
  · change focused.final.tapes (slots 3)=_
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
    exact x3
  · intro i
    change focused.final.heads i=0
    rw [hff]
    cases h : RecoveryFocus.pick slots i <;> simp [RecoveryFocus.config,h,ph,xh]
  · change base.steps+1+focused.steps=_
    rw [bs,hfs,xs]
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreCapacity
