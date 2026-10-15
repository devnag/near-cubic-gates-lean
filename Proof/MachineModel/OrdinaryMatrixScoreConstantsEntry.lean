import Proof.MachineModel.OrdinaryMatrixScoreConstants
import Proof.MachineModel.OrdinaryMatrixScoreWidthEntry

/-! The raw header parser now supplies the actual reusable scalar constants.
The cut cursor and the assignment driver are retained by focused calls. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreConstantsEntry
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev H := MatrixScoreWidthEntry.H+29
def slots : Fin 18 → Fin 68 := ![49,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67]
noncomputable def first : Machine 68 H := TapeEmbedding.machine 17 MatrixScoreWidthEntry.machine
noncomputable def last : Machine 68 43 := RecoveryFocus.machine slots MatrixScoreConstants.machine
noncomputable def machine := Composition.machine first last
def input (word : List Bool) : Fin 68 → List Bool := fun i => if i.val=0 then frame word else []
def width (d p : ℕ) := p+natBitLength d+3
def budget (d p : ℕ) (suffix : List Bool) := MatrixScoreWidthEntry.budget d p suffix+24*width d p+90

theorem entry_run (d p : ℕ) (suffix : List Bool) :
    ∃ actual : ExecutionReceipt 68 (H+43),
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
      actual.final.tapes 58=List.replicate (MatrixScoreCapacity.capacity (width d p)) true ∧ actual.final.heads 58=0 ∧
      actual.final.tapes 61=frame (binary (width d p) (2^(p+natBitLength d+2))) ∧ actual.final.heads 61=0 ∧
      actual.final.tapes 65=frame (binary (width d p) 0) ∧ actual.final.heads 65=0 ∧
      actual.steps≤budget d p suffix := by
  obtain ⟨base,hb,b0,h0,b1,h1,_,_,_,_,b23,h23,b28,h28,b32,h32,b39,h39,b40,h40,b49,h49,bs⟩ :=
    MatrixScoreWidthEntry.entry_run d p suffix
  have he := TapeEmbedding.run_embed MatrixScoreWidthEntry.machine (fun _ : Fin 17 => 0)
    (fun _ : Fin 17 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 17 => 0) (fun _ : Fin 17 => []) base
  obtain ⟨constants,hc,c0,c8,c11,c15,ch,cs⟩ := MatrixScoreConstants.constants_run (p+natBitLength d+2)
  have hw : p+natBitLength d+2+1=width d p := by unfold width; omega
  rw [hw] at hc c0 c8 c11 c15 cs
  let localInput := initialConfiguration MatrixScoreConstants.machine (MatrixScoreConstants.input (width d p))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes localInput=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · exact h49
      all_goals rfl
    · intro i
      fin_cases i
      · exact b49
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixScoreConstants.machine
    prepared.final.heads prepared.final.tapes _ localInput constants hc
  rw [hi] at hf
  have hj := Composition.run_join first last (MatrixScoreWidthEntry.budget d p suffix)
    (24*width d p+89) _ prepared focused he hf
  have hin : Composition.leftConfig 43 (TapeEmbedding.config (fun _ : Fin 17 => 0) (fun _ : Fin 17 => [])
      (initialConfiguration MatrixScoreWidthEntry.machine (MatrixScoreWidthEntry.input (natWord d++natWord p++suffix))))=
      initialConfiguration machine (input (natWord d++natWord p++suffix)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        initialConfiguration,input,MatrixScoreWidthEntry.input]
  rw [hin] at hj
  have htime : MatrixScoreWidthEntry.budget d p suffix+1+(24*width d p+89)=budget d p suffix := by
    unfold budget; omega
  rw [htime] at hj
  have otherT (i : Fin 51) (hn : RecoveryFocus.pick slots (i.castAdd 17)=none) :
      focused.final.tapes (i.castAdd 17)=base.final.tapes i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have otherH (i : Fin 51) (hn : RecoveryFocus.pick slots (i.castAdd 17)=none) :
      focused.final.heads (i.castAdd 17)=base.final.heads i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have localT (i : Fin 18) : focused.final.tapes (slots i)=constants.final.tapes i := by
    rw [hff]; simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have localH (i : Fin 18) : focused.final.heads (slots i)=0 := by
    rw [hff]; simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide),ch]
  refine ⟨Composition.joinedReceipt prepared focused,hj,
    (otherT 0 (by decide)).trans b0,(otherH 0 (by decide)).trans h0,
    (otherT 1 (by decide)).trans b1,(otherH 1 (by decide)).trans h1,
    (otherT 23 (by decide)).trans b23,(otherH 23 (by decide)).trans h23,
    (otherT 28 (by decide)).trans b28,(otherH 28 (by decide)).trans h28,
    (otherT 32 (by decide)).trans b32,(otherH 32 (by decide)).trans h32,
    (otherT 39 (by decide)).trans b39,(otherH 39 (by decide)).trans h39,
    (otherT 40 (by decide)).trans b40,(otherH 40 (by decide)).trans h40,
    (localT 0).trans c0,localH 0,(localT 8).trans c8,localH 8,
    (localT 11).trans c11,localH 11,(localT 15).trans c15,localH 15,?_⟩
  change base.steps+1+focused.steps≤_
  rw [hfs]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreConstantsEntry
