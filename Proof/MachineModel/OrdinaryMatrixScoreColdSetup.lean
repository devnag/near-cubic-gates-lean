import Proof.MachineModel.OrdinaryMatrixScoreFields
import Proof.MachineModel.OrdinaryMatrixScoreSetup

/-! The original raw headers now physically produce every native initial
field and counter needed by the all-2U score traversal. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreColdSetup
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 21 → Fin 98 := ![23,80,81,82,83,28,84,85,86,87,77,88,89,90,91,92,93,94,95,96,97]
noncomputable def first := TapeEmbedding.machine 18 MatrixScoreSetup.machine
noncomputable def last := RecoveryFocus.machine slots MatrixScoreColdFields.machine
noncomputable def machine := Composition.machine first last
def input (word : List Bool) : Fin 98 → List Bool := fun i => if i=0 then frame word else []
def budget (d p : ℕ) (suffix : List Bool) := MatrixScoreSetup.budget d p suffix+1+
  MatrixScoreColdFields.budget d (d+3) (MatrixScoreSetup.capacity d p)

theorem setup_run (d p : ℕ) (suffix : List Bool) :
    ∃ actual,run machine (budget d p suffix) (input (natWord d++natWord p++suffix))=some actual ∧
      actual.final.tapes 0=frame (natWord d++natWord p++suffix) ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 1=natWord d++natWord p++suffix ∧ actual.final.heads 1=2*natBitLength d+1+(2*natBitLength p+1) ∧
      actual.final.tapes 32=frame (binary (d+3) (2^d)) ∧ actual.final.heads 32=0 ∧
      actual.final.tapes 39=UnaryTemplate.tape (2^d) ∧ actual.final.heads 39=1 ∧
      actual.final.tapes 49=List.replicate (MatrixScoreSetup.width d p) true ∧ actual.final.heads 49=0 ∧
      actual.final.tapes 61=frame (binary (MatrixScoreSetup.width d p) (2^(p+natBitLength d+2))) ∧ actual.final.heads 61=0 ∧
      actual.final.tapes 65=frame (binary (MatrixScoreSetup.width d p) 0) ∧ actual.final.heads 65=0 ∧
      actual.final.tapes 77=List.replicate (MatrixScoreSetup.capacity d p) true ∧ actual.final.heads 77=0 ∧
      actual.final.tapes 82=UnaryTemplate.tape d ∧ actual.final.heads 82=0 ∧
      actual.final.tapes 85=frame (binary d 0) ∧ actual.final.heads 85=0 ∧
      actual.final.tapes 89=frame (binary d 0) ∧ actual.final.heads 89=0 ∧
      actual.final.tapes 93=frame (binary (d+3) 0) ∧ actual.final.heads 93=0 ∧
      actual.final.tapes 96=List.replicate (MatrixScoreSetup.capacity d p) false ∧ actual.final.heads 96=0 ∧
      actual.final.tapes 97=List.replicate (MatrixScoreSetup.capacity d p+1) false ∧ actual.final.heads 97=0 ∧
      actual.steps≤budget d p suffix := by
  obtain ⟨base,hb,b0,h0,b1,h1,b23,h23,b28,h28,b32,h32,b39,h39,b40,h40,b49,h49,b61,h61,b65,h65,b77,h77,bs⟩ :=
    MatrixScoreSetup.setup_run d p suffix
  have he := TapeEmbedding.run_embed MatrixScoreSetup.machine (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) base
  obtain ⟨fields,hf,fh,f3,f7,f12,f16,f10,f19,f20,fs⟩ := MatrixScoreColdFields.fields_run d (d+3) (MatrixScoreSetup.capacity d p)
  let entry := initialConfiguration MatrixScoreColdFields.machine (MatrixScoreColdFields.input d (d+3) (MatrixScoreSetup.capacity d p))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · exact h23
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h28
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h77
      all_goals rfl
    · intro i
      fin_cases i
      · exact b23
      · rfl
      · rfl
      · rfl
      · rfl
      · exact b28
      · rfl
      · rfl
      · rfl
      · rfl
      · exact b77
      all_goals rfl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixScoreColdFields.machine
    prepared.final.heads prepared.final.tapes _ entry fields hf
  rw [hi] at hfocus
  have joined := Composition.run_join first last _ _ _ prepared focused he hfocus
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 18 => 0) (fun _ : Fin 18 => [])
      (initialConfiguration MatrixScoreSetup.machine (MatrixScoreSetup.input (natWord d++natWord p++suffix))))=
      initialConfiguration machine (input (natWord d++natWord p++suffix)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have otherT (i : Fin 80) (hn : RecoveryFocus.pick slots (i.castAdd 18)=none) : focused.final.tapes (i.castAdd 18)=base.final.tapes i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have otherH (i : Fin 80) (hn : RecoveryFocus.pick slots (i.castAdd 18)=none) : focused.final.heads (i.castAdd 18)=base.final.heads i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have localT (i : Fin 21) : focused.final.tapes (slots i)=fields.final.tapes i := by
    rw [hff]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have localH (i : Fin 21) : focused.final.heads (slots i)=0 := by
    rw [hff]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide),fh]
  refine ⟨Composition.joinedReceipt prepared focused,joined,
    (otherT 0 (by decide)).trans b0,(otherH 0 (by decide)).trans h0,
    (otherT 1 (by decide)).trans b1,(otherH 1 (by decide)).trans h1,
    (otherT 32 (by decide)).trans b32,(otherH 32 (by decide)).trans h32,
    (otherT 39 (by decide)).trans b39,(otherH 39 (by decide)).trans h39,
    (otherT 49 (by decide)).trans b49,(otherH 49 (by decide)).trans h49,
    (otherT 61 (by decide)).trans b61,(otherH 61 (by decide)).trans h61,
    (otherT 65 (by decide)).trans b65,(otherH 65 (by decide)).trans h65,
    (localT 10).trans f10,localH 10,
    (localT 3).trans f3,localH 3,(localT 7).trans f7,localH 7,
    (localT 12).trans f12,localH 12,(localT 16).trans f16,localH 16,
    (localT 19).trans f19,localH 19,(localT 20).trans f20,localH 20,?_⟩
  change base.steps+1+focused.steps≤_
  rw [hfs]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreColdSetup
