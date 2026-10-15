import Proof.MachineModel.OrdinaryMatrixScoreCommonCapacity

/-! Cold raw-header setup with the common scalar/record capacity. Every
runtime driver and native accumulator constant in this interface is produced
by the same actual run; the cut cursor remains positioned after the headers. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreSetup
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev H := MatrixScoreConstantsEntry.H+43
def slots : Fin 14 → Fin 80 := ![49,28,68,69,70,71,72,73,74,75,76,77,78,79]
noncomputable def first : Machine 80 H := TapeEmbedding.machine 12 MatrixScoreConstantsEntry.machine
noncomputable def last : Machine 80 33 := RecoveryFocus.machine slots MatrixScoreCommonCapacity.machine
noncomputable def machine := Composition.machine first last
def input (word : List Bool) : Fin 80 → List Bool := fun i => if i.val=0 then frame word else []
def width (d p : ℕ) := MatrixScoreConstantsEntry.width d p
def capacity (d p : ℕ) := MatrixScoreCommonCapacity.capacity (width d p) (d+3)
def budget (d p : ℕ) (suffix : List Bool) := MatrixScoreConstantsEntry.budget d p suffix+14*(width d p+(d+3))+77

theorem setup_run (d p : ℕ) (suffix : List Bool) :
    ∃ actual : ExecutionReceipt 80 (H+33),
      run machine (budget d p suffix) (input (natWord d++natWord p++suffix))=some actual ∧
      actual.final.tapes 0=frame (natWord d++natWord p++suffix) ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 1=natWord d++natWord p++suffix ∧
      actual.final.heads 1=2*natBitLength d+1+(2*natBitLength p+1) ∧
      actual.final.tapes 23=List.replicate d true ∧ actual.final.heads 23=0 ∧
      actual.final.tapes 28=List.replicate (d+3) true ∧ actual.final.heads 28=0 ∧
      actual.final.tapes 32=frame (binary (d+3) (2^d)) ∧ actual.final.heads 32=0 ∧
      actual.final.tapes 39=UnaryTemplate.tape (2^d) ∧ actual.final.heads 39=1 ∧
      actual.final.tapes 40=List.replicate p true ∧ actual.final.heads 40=0 ∧
      actual.final.tapes 49=List.replicate (width d p) true ∧ actual.final.heads 49=0 ∧
      actual.final.tapes 61=frame (binary (width d p) (2^(p+natBitLength d+2))) ∧ actual.final.heads 61=0 ∧
      actual.final.tapes 65=frame (binary (width d p) 0) ∧ actual.final.heads 65=0 ∧
      actual.final.tapes 77=List.replicate (capacity d p) true ∧ actual.final.heads 77=0 ∧
      actual.steps≤budget d p suffix := by
  obtain ⟨base,hb,b0,h0,b1,h1,b23,h23,b28,h28,b32,h32,b39,h39,b40,h40,b49,h49,_,_,b61,h61,b65,h65,bs⟩ :=
    MatrixScoreConstantsEntry.entry_run d p suffix
  have he := TapeEmbedding.run_embed MatrixScoreConstantsEntry.machine (fun _ : Fin 12 => 0)
    (fun _ : Fin 12 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 12 => 0) (fun _ : Fin 12 => []) base
  obtain ⟨cap,hc,c0,c1,_,c11,ch,cs⟩ := MatrixScoreCommonCapacity.capacity_run (width d p) (d+3)
  let localInput := initialConfiguration MatrixScoreCommonCapacity.machine (MatrixScoreCommonCapacity.input (width d p) (d+3))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes localInput=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · exact h49
      · exact h28
      all_goals rfl
    · intro i
      fin_cases i
      · exact b49
      · exact b28
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixScoreCommonCapacity.machine
    prepared.final.heads prepared.final.tapes _ localInput cap hc
  rw [hi] at hf
  have hj := Composition.run_join first last (MatrixScoreConstantsEntry.budget d p suffix)
    (14*(width d p+(d+3))+76) _ prepared focused he hf
  have hin : Composition.leftConfig 33 (TapeEmbedding.config (fun _ : Fin 12 => 0) (fun _ : Fin 12 => [])
      (initialConfiguration MatrixScoreConstantsEntry.machine (MatrixScoreConstantsEntry.input (natWord d++natWord p++suffix))))=
      initialConfiguration machine (input (natWord d++natWord p++suffix)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        initialConfiguration,input,MatrixScoreConstantsEntry.input]
  rw [hin] at hj
  have htime : MatrixScoreConstantsEntry.budget d p suffix+1+(14*(width d p+(d+3))+76)=budget d p suffix := by
    unfold budget; omega
  rw [htime] at hj
  have otherT (i : Fin 68) (hn : RecoveryFocus.pick slots (i.castAdd 12)=none) :
      focused.final.tapes (i.castAdd 12)=base.final.tapes i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have otherH (i : Fin 68) (hn : RecoveryFocus.pick slots (i.castAdd 12)=none) :
      focused.final.heads (i.castAdd 12)=base.final.heads i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have localT (i : Fin 14) : focused.final.tapes (slots i)=cap.final.tapes i := by
    rw [hff]; simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have localH (i : Fin 14) : focused.final.heads (slots i)=0 := by
    rw [hff]; simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide),ch]
  refine ⟨Composition.joinedReceipt prepared focused,hj,
    (otherT 0 (by decide)).trans b0,(otherH 0 (by decide)).trans h0,
    (otherT 1 (by decide)).trans b1,(otherH 1 (by decide)).trans h1,
    (otherT 23 (by decide)).trans b23,(otherH 23 (by decide)).trans h23,
    (localT 1).trans c1,localH 1,
    (otherT 32 (by decide)).trans b32,(otherH 32 (by decide)).trans h32,
    (otherT 39 (by decide)).trans b39,(otherH 39 (by decide)).trans h39,
    (otherT 40 (by decide)).trans b40,(otherH 40 (by decide)).trans h40,
    (localT 0).trans c0,localH 0,
    (otherT 61 (by decide)).trans b61,(otherH 61 (by decide)).trans h61,
    (otherT 65 (by decide)).trans b65,(otherH 65 (by decide)).trans h65,
    (localT 11).trans c11,localH 11,?_⟩
  change base.steps+1+focused.steps≤_
  rw [hfs]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreSetup
