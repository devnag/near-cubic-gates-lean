import Proof.MachineModel.OrdinaryMatrixBatchRightPlaneFields

/-! Both Boolean matrices now come from a single original framed Request
and blank work. The right producer pays its actual pad driver and every
transpose/sort/select/pad/rewind step while retaining the left matrix. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRightPlane
open LocalBitMultitape MatrixScoreBatch
open MatrixRightPlaneBank (slots slots_injective)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 4 MatrixBatchRightPadDriver.machine
noncomputable def last := RecoveryFocus.machine slots MatrixRightPlaneNative.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 362 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixBatchRightPadDriver.budget r+1+MatrixRightPlaneNative.budget r

theorem plane_run (r : Request) (base : ExecutionReceipt 358 _)
    (hb : run MatrixBatchRightPadDriver.machine (MatrixBatchRightPadDriver.budget r) (MatrixBatchRightPadDriver.input r)=some base)
    (bt : ∀ j,(TapeEmbedding.config (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) base.final).tapes (slots j)=
      MatrixRightPlaneNative.input r j)
    (bh : ∀ j,(TapeEmbedding.config (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) base.final).heads (slots j)=0)
    (bs : base.steps≤MatrixBatchRightPadDriver.budget r) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 360=MatrixRightPlaneNative.plane r ∧ actual.final.heads 360=0 ∧
    (∀ j,actual.final.heads (slots j)=0) ∧
    (∀ i : Fin 358,(∀ j,slots j≠i.castAdd 4) → actual.final.tapes (i.castAdd 4)=base.final.tapes i ∧
      actual.final.heads (i.castAdd 4)=base.final.heads i) ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchRightPadDriver.machine (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) base
  obtain ⟨body,hr,rt,rh,rs⟩ := MatrixRightPlaneNative.plane_run r
  let entry := initialConfiguration MatrixRightPlaneNative.machine (MatrixRightPlaneNative.input r)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · exact bh
    · exact bt
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixRightPlaneNative.machine
    prepared.final.heads prepared.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 4 => 0) (fun _ : Fin 4 => [])
      (initialConfiguration MatrixBatchRightPadDriver.machine (MatrixBatchRightPadDriver.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have localH (j : Fin 24) : focused.final.heads (slots j)=0 := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,rh]
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,localH 19,localH,?_,?_⟩
  · change focused.final.tapes (slots 19)=_
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact rt
  · intro i hi
    change focused.final.tapes (i.castAdd 4)=_ ∧ focused.final.heads (i.castAdd 4)=_
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hi,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps≤budget r
    rw [fs]
    change base.steps+1+body.steps≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) : ∃ base : ExecutionReceipt 358 _,∃ actual,
    run MatrixBatchRightPadDriver.machine (MatrixBatchRightPadDriver.budget r) (MatrixBatchRightPadDriver.input r)=some base ∧
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 360=MatrixRightPlaneNative.plane r ∧ actual.final.heads 360=0 ∧
    actual.final.tapes 342=MatrixBucketLeftPlane.plane r ∧ actual.final.heads 342=0 ∧
    (∀ j,actual.final.heads (slots j)=0) ∧
    (∀ i : Fin 358,(∀ j,slots j≠i.castAdd 4) → actual.final.tapes (i.castAdd 4)=base.final.tapes i ∧
      actual.final.heads (i.castAdd 4)=base.final.heads i) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,leftT,leftH,bs⟩ := MatrixBatchRightPlaneFields.source_fields r
  obtain ⟨actual,ha,outT,outH,ah,old,steps⟩ := plane_run r base hb bt bh bs
  have hl := old 342 (by decide)
  exact ⟨base,actual,hb,ha,outT,outH,hl.1.trans leftT,hl.2.trans leftH,ah,old,steps⟩

end NearCubicWires.RepairOrdinary.MatrixBatchRightPlane
