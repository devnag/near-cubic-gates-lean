import Proof.MachineModel.OrdinaryMatrixBucketCoordinateSort

/-! Original framed Request through the complete bucket producer, followed
by the actual coordinate sort and paid rewind on the same output tape. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchCoordinateSort
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 7 → Fin 342 := ![314,336,337,338,339,340,341]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 6 MatrixBatchBucketPass.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBucketCoordinateSort.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 342 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixBatchBucketPass.budget r+1+MatrixBucketCoordinateSort.budget r

theorem sort_run (r : Request) (base : ExecutionReceipt 336 _)
    (hb : run MatrixBatchBucketPass.machine (MatrixBatchBucketPass.budget r) (MatrixBatchBucketPass.input r)=some base)
    (bt : base.final.tapes 314=MatrixBatchBucketPass.output r) (bh : base.final.heads 314=0)
    (bs : base.steps≤MatrixBatchBucketPass.budget r) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 314=MatrixBucketCoordinateSort.output r ∧ actual.final.heads 314=0 ∧
    (∀ j,actual.final.heads (slots j)=0) ∧
    (∀ i : Fin 336,i≠314 → actual.final.tapes (i.castAdd 6)=base.final.tapes i ∧
      actual.final.heads (i.castAdd 6)=base.final.heads i) ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchBucketPass.machine (fun _ : Fin 6 => 0) (fun _ : Fin 6 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 6 => 0) (fun _ : Fin 6 => []) base
  obtain ⟨body,hr,rt,rh,rs⟩ := MatrixBucketCoordinateSort.sort_run r
  let entry := initialConfiguration MatrixBucketCoordinateSort.machine (MatrixBucketCoordinateSort.input r)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j
      · exact bh
      all_goals rfl
    · intro j
      fin_cases j
      · exact bt
      all_goals rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBucketCoordinateSort.machine
    prepared.final.heads prepared.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 6 => 0) (fun _ : Fin 6 => [])
      (initialConfiguration MatrixBatchBucketPass.machine (MatrixBatchBucketPass.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have localH (j : Fin 7) : focused.final.heads (slots j)=0 := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact rh j
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,localH 0,localH,?_,?_⟩
  · change focused.final.tapes (slots 0)=_
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact rt
  · intro i hi
    have hn : ∀ j,slots j≠i.castAdd 6 := by
      intro j
      have hil := i.isLt
      have hiv : i.val≠314 := fun h => hi (Fin.ext h)
      fin_cases j <;> simp [slots,Fin.ext_iff] <;> omega
    change focused.final.tapes (i.castAdd 6)=_ ∧ focused.final.heads (i.castAdd 6)=_
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps≤budget r
    rw [fs]
    change base.steps+1+body.steps≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) : ∃ base : ExecutionReceipt 336 _,∃ actual,
    run MatrixBatchBucketPass.machine (MatrixBatchBucketPass.budget r) (MatrixBatchBucketPass.input r)=some base ∧
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 314=MatrixBucketCoordinateSort.output r ∧ actual.final.heads 314=0 ∧
    (∀ j,actual.final.heads (slots j)=0) ∧
    (∀ i : Fin 336,i≠314 → actual.final.tapes (i.castAdd 6)=base.final.tapes i ∧
      actual.final.heads (i.castAdd 6)=base.final.heads i) ∧ actual.steps≤budget r := by
  obtain ⟨_,_,_,base,_,hb,bt,bh,_,_,_,bs⟩ := MatrixBatchBucketPass.raw_run r
  obtain ⟨actual,ha,outputT,ah,heads,old,steps⟩ := sort_run r base hb bt bh bs
  exact ⟨base,actual,hb,ha,outputT,ah,heads,old,steps⟩

end NearCubicWires.RepairOrdinary.MatrixBatchCoordinateSort
