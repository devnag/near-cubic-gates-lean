import Proof.MachineModel.OrdinaryMatrixScoreRecord

/-! The record copier also traverses M-bit ids. Its common capacity is
therefore physically printed from W+M, covering arithmetic and record work. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreCommonCapacity
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 11 → Fin 14 := ![2,4,5,6,7,8,9,10,11,12,13]
noncomputable def first := TapeEmbedding.machine 10 ClockUnarySum.machine
noncomputable def last := RecoveryFocus.machine slots MatrixScoreCapacity.machine
noncomputable def machine := Composition.machine first last
def input (w m : ℕ) : Fin 14 → List Bool :=
  ![List.replicate w true,List.replicate m true,[],[],[],[],[],[],[],[],[],[],[],[]]
def capacity (w m : ℕ) := MatrixScoreCapacity.capacity (w+m)

theorem capacity_run (w m : ℕ) :
    ∃ actual,run machine (14*(w+m)+76) (input w m)=some actual ∧
      actual.final.tapes 0=List.replicate w true ∧
      actual.final.tapes 1=List.replicate m true ∧
      actual.final.tapes 2=List.replicate (w+m) true ∧
      actual.final.tapes 11=List.replicate (capacity w m) true ∧
      (∀ i,actual.final.heads i=0) ∧ actual.steps≤14*(w+m)+76 := by
  obtain ⟨sum,hs,st,sh,ss⟩ := ClockUnarySum.sum_ready w m
  have he := TapeEmbedding.run_embed ClockUnarySum.machine (fun _ : Fin 10 => 0)
    (fun _ : Fin 10 => []) _ _ sum hs
  let expanded := TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) sum
  have eh : ∀ i,expanded.final.heads i=0 := by
    intro i; fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,sh]
  obtain ⟨cap,hc,c0,_,c8,ch,cs⟩ := MatrixScoreCapacity.capacity_run (w+m)
  let localInput := initialConfiguration MatrixScoreCapacity.machine (MatrixScoreCapacity.input (w+m))
  have hi : RecoveryFocus.config slots expanded.final.heads expanded.final.tapes localInput=
      Composition.restart expanded.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simp [eh,localInput,initialConfiguration]
    · intro i
      fin_cases i
      · change sum.final.tapes 2=List.replicate (w+m) true
        rw [st]
        rfl
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixScoreCapacity.machine
    expanded.final.heads expanded.final.tapes _ localInput cap hc
  rw [hi] at hf
  have joined := Composition.run_join first last (2*(w+m)+6) (12*(w+m)+69) _ expanded focused he hf
  have hin : Composition.leftConfig 28 (TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => [])
      (initialConfiguration ClockUnarySum.machine ![List.replicate w true,List.replicate m true,[],[]]))=
      initialConfiguration machine (input w m) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have ht : (2*(w+m)+6)+1+(12*(w+m)+69)=14*(w+m)+76 := by omega
  rw [ht] at joined
  refine ⟨Composition.joinedReceipt expanded focused,joined,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [hff]
    simp [RecoveryFocus.config,show RecoveryFocus.pick slots 0=none by decide,
      expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,st]
  · change focused.final.tapes 1=_
    rw [hff]
    simp [RecoveryFocus.config,show RecoveryFocus.pick slots 1=none by decide,
      expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,st]
  · change focused.final.tapes (slots 0)=_
    rw [hff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)] using c0
  · change focused.final.tapes (slots 8)=_
    rw [hff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide),capacity] using c8
  · intro i
    change focused.final.heads i=0
    rw [hff]
    cases h : RecoveryFocus.pick slots i <;> simp [RecoveryFocus.config,h,eh,ch]
  · change sum.steps+1+focused.steps≤_
    rw [hfs,cs]
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreCommonCapacity
