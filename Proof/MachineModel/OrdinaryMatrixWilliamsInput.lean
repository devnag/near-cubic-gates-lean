import Proof.MachineModel.OrdinaryMatrixWilliamsDimensions
import Proof.MachineModel.OrdinaryMatrixWilliamsFrame

/-! The original raw cut request now physically supplies the exact framed
input of the corrected Williams wrapper for its first signed Boolean plane. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsInput
open LocalBitMultitape MatrixScoreBatch RepairRepresentation WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 7 → Fin 424 := ![410,409,420,407,394,422,423]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 2 MatrixWilliamsDimensions.machine
noncomputable def last := RecoveryFocus.machine slots MatrixWilliamsFrame.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 424 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def word (r : Request) := natWord r.U++MatrixSignedPlane.plane r false 0++MatrixRightPlaneNative.plane r
noncomputable def budget (r : Request) := MatrixWilliamsDimensions.budget r+1+(6*(2*r.d+3)+12*(r.U*r.Capacity)+38)

theorem header_length (r : Request) : (natWord r.U).length=2*r.d+3 := by
  change (natWord (2^r.d)).length=_
  rw [←MatrixPowerHeader.word_eq]
  exact MatrixPowerHeader.word_length r.d

theorem left_length (r : Request) (negative : Bool) (bit : ℕ) :
    (MatrixSignedPlane.plane r negative bit).length=r.U*r.Capacity := by
  simp [MatrixSignedPlane.plane,rowMajorBitMatrix,List.length_flatten,List.map_ofFn,Function.comp_def]

theorem right_length (r : Request) : (MatrixRightPlaneNative.plane r).length=r.U*r.Capacity := by
  simp [MatrixRightPlaneNative.plane,rowMajorBitMatrix,List.length_flatten,List.map_ofFn,Function.comp_def,Nat.mul_comm]

theorem raw_run (r : Request) (hp : 0<r.p) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 422=frame (word r) ∧ actual.final.heads 422=0 ∧
    (∀ j,actual.final.tapes ((MatrixWilliamsDimensions.selected j).castAdd 2)=MatrixWilliamsDimensions.values r j) ∧
    (∀ j,actual.final.heads ((MatrixWilliamsDimensions.selected j).castAdd 2)=0) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,bs⟩ := MatrixWilliamsDimensions.raw_run r hp
  have hemb := TapeEmbedding.run_embed MatrixWilliamsDimensions.machine (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base
  obtain ⟨body,hr,bodyT,bodyH,bodyS⟩ := MatrixWilliamsFrame.frame_run (natWord r.U)
    (MatrixSignedPlane.plane r false 0) (MatrixRightPlaneNative.plane r) (r.U*r.Capacity)
    (left_length r false 0) (right_length r)
  rw [header_length] at hr bodyS
  let entry := initialConfiguration MatrixWilliamsFrame.machine (MatrixWilliamsFrame.resetInput (natWord r.U)
    (MatrixSignedPlane.plane r false 0) (MatrixRightPlaneNative.plane r) (r.U*r.Capacity))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j
      · exact bh 5
      · exact bh 4
      · exact bh 6
      · exact bh 2
      · exact bh 3
      · rfl
      · rfl
    · intro j; fin_cases j
      · change base.final.tapes 410=UnaryTemplate.tape (natWord r.U).length
        rw [header_length]
        exact bt 5
      · exact bt 4
      · exact bt 6
      · exact bt 2
      · exact bt 3
      · rfl
      · rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixWilliamsFrame.machine
    prepared.final.heads prepared.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused hemb hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => [])
      (initialConfiguration MatrixWilliamsDimensions.machine (MatrixWilliamsDimensions.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have localT (j : Fin 7) : focused.final.tapes (slots j)=body.final.tapes j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 7) : focused.final.heads (slots j)=body.final.heads j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have retained (i : Fin 422) (hn : RecoveryFocus.pick slots (i.castAdd 2)=none) :
      focused.final.tapes (i.castAdd 2)=base.final.tapes i ∧ focused.final.heads (i.castAdd 2)=base.final.heads i := by
    rw [ff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  refine ⟨Composition.joinedReceipt prepared focused,hj,(localT 5).trans (bodyT 5),(localH 5).trans (bodyH 5),?_,?_,?_⟩
  · intro j; fin_cases j
    · exact (retained 400 (by decide)).1.trans (bt 0)
    · exact (retained 200 (by decide)).1.trans (bt 1)
    · exact (localT 3).trans (bodyT 3)
    · exact (localT 4).trans (bodyT 4)
    · exact (localT 1).trans (bodyT 1)
    · have ht := (localT 0).trans (bodyT 0)
      change focused.final.tapes 410=UnaryTemplate.tape (natWord r.U).length at ht
      rw [header_length] at ht
      exact ht
    · exact (localT 2).trans (bodyT 2)
  · intro j; fin_cases j
    · exact (retained 400 (by decide)).2.trans (bh 0)
    · exact (retained 200 (by decide)).2.trans (bh 1)
    · exact (localH 3).trans (bodyH 3)
    · exact (localH 4).trans (bodyH 4)
    · exact (localH 1).trans (bodyH 1)
    · exact (localH 0).trans (bodyH 0)
    · exact (localH 2).trans (bodyH 2)
  · change base.steps+1+focused.steps≤budget r
    rw [fs,bodyS]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixWilliamsInput
