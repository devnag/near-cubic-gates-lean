import Proof.MachineModel.OrdinaryMatrixScoreWidth

/-! The score width is now part of the actual cold raw-header execution.
Its local reset retains the raw cut cursor and the head1 assignment driver. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWidthEntry
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev H := (MatrixScoreDimensions.H+10)+MatrixScoreDimensions.P
def slots : Fin 13 → Fin 51 := ![22,40,41,42,43,3,44,45,46,47,48,49,50]
noncomputable def first : Machine 51 H := TapeEmbedding.machine 11 MatrixScoreDimensions.machine
noncomputable def last : Machine 51 29 := RecoveryFocus.machine slots MatrixScoreWidth.machine
noncomputable def machine := Composition.machine first last
def input (word : List Bool) : Fin 51 → List Bool := fun i => if i.val=0 then frame word else []
def budget (d p : ℕ) (suffix : List Bool) := MatrixScoreDimensions.budget d p suffix+6*p+6*natBitLength d+51

theorem entry_run (d p : ℕ) (suffix : List Bool) :
    ∃ actual : ExecutionReceipt 51 (H+29),
      run machine (budget d p suffix) (input (natWord d++natWord p++suffix))=some actual ∧
      actual.final.tapes 0=frame (natWord d++natWord p++suffix) ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 1=natWord d++natWord p++suffix ∧
      actual.final.heads 1=2*natBitLength d+1+(2*natBitLength p+1) ∧
      actual.final.tapes 3=List.replicate (natBitLength d) true ∧ actual.final.heads 3=0 ∧
      actual.final.tapes 22=UnaryTemplate.tape p ∧ actual.final.heads 22=0 ∧
      actual.final.tapes 23=List.replicate d true ∧ actual.final.heads 23=0 ∧
      actual.final.tapes 28=List.replicate (d+3) true ∧ actual.final.heads 28=0 ∧
      actual.final.tapes 32=frame (binary (d+3) (2^d)) ∧ actual.final.heads 32=0 ∧
      actual.final.tapes 39=UnaryTemplate.tape (2^d) ∧ actual.final.heads 39=1 ∧
      actual.final.tapes 40=List.replicate p true ∧ actual.final.heads 40=0 ∧
      actual.final.tapes 49=List.replicate (p+natBitLength d+3) true ∧ actual.final.heads 49=0 ∧
      actual.steps≤budget d p suffix := by
  obtain ⟨base,hb,b0,h0,b1,h1,b3,h3,_,_,_,_,_,_,b22,h22,b23,h23,b28,h28,b32,h32,b39,h39,bs⟩ :=
    MatrixScoreDimensions.dimensions_run d p suffix
  have he := TapeEmbedding.run_embed MatrixScoreDimensions.machine (fun _ : Fin 11 => 0)
    (fun _ : Fin 11 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 11 => 0) (fun _ : Fin 11 => []) base
  obtain ⟨width,hw,w0,w1,w5,_,w11,wh,ws⟩ := MatrixScoreWidth.width_run p (natBitLength d)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes (MatrixScoreWidth.input p (natBitLength d))=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · exact h22
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h3
      all_goals rfl
    · intro i
      fin_cases i
      · exact b22
      · rfl
      · rfl
      · rfl
      · rfl
      · exact b3
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixScoreWidth.machine
    prepared.final.heads prepared.final.tapes _ (MatrixScoreWidth.input p (natBitLength d)) width hw
  rw [hi] at hf
  have hj := Composition.run_join first last (MatrixScoreDimensions.budget d p suffix)
    (6*p+6*natBitLength d+50) _ prepared focused he hf
  have hin : Composition.leftConfig 29 (TapeEmbedding.config (fun _ : Fin 11 => 0) (fun _ : Fin 11 => [])
      (initialConfiguration MatrixScoreDimensions.machine (MatrixScoreDimensions.input (natWord d++natWord p++suffix))))=
      initialConfiguration machine (input (natWord d++natWord p++suffix)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        initialConfiguration,input,MatrixScoreDimensions.input]
  rw [hin] at hj
  have htime : MatrixScoreDimensions.budget d p suffix+1+(6*p+6*natBitLength d+50)=budget d p suffix := by
    unfold budget; omega
  rw [htime] at hj
  have otherT (i : Fin 40) (hn : RecoveryFocus.pick slots (i.castAdd 11)=none) :
      focused.final.tapes (i.castAdd 11)=base.final.tapes i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have otherH (i : Fin 40) (hn : RecoveryFocus.pick slots (i.castAdd 11)=none) :
      focused.final.heads (i.castAdd 11)=base.final.heads i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have localT (i : Fin 13) : focused.final.tapes (slots i)=width.final.tapes i := by
    rw [hff]; simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have localH (i : Fin 13) : focused.final.heads (slots i)=0 := by
    rw [hff]; simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide),wh]
  refine ⟨Composition.joinedReceipt prepared focused,hj,
    (otherT 0 (by decide)).trans b0,(otherH 0 (by decide)).trans h0,
    (otherT 1 (by decide)).trans b1,(otherH 1 (by decide)).trans h1,
    (localT 5).trans w5,localH 5,(localT 0).trans w0,localH 0,
    (otherT 23 (by decide)).trans b23,(otherH 23 (by decide)).trans h23,
    (otherT 28 (by decide)).trans b28,(otherH 28 (by decide)).trans h28,
    (otherT 32 (by decide)).trans b32,(otherH 32 (by decide)).trans h32,
    (otherT 39 (by decide)).trans b39,(otherH 39 (by decide)).trans h39,
    (localT 1).trans w1,localH 1,(localT 11).trans w11,localH 11,?_⟩
  change base.steps+1+focused.steps≤_
  rw [hfs]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreWidthEntry
