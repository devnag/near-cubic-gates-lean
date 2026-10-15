import Proof.MachineModel.OrdinaryMatrixBatchBucketPassFields

/-! The original framed Request and blank work now produce the complete
terminated all-gate keyed bucket stream at head0. This execution includes
all raw score/rank/dimension/bank preparation and one final output rewind. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchBucketPass
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketPassFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 MatrixBatchBucketBank.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBucketGatePass.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 336 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchBucketBank.budget r+1+MatrixBucketGatePass.budget r
noncomputable def output (r : Request) :=
  ZeroPadding.pad (MatrixScoreReusableRanks.D r) (MatrixBucketGateNativeLoop.output r++[false])

theorem pass_run (r : Request) (unused : Fin 3 → List Bool) (base : ExecutionReceipt 335 _)
    (hb : run MatrixBatchBucketBank.machine (MatrixBatchBucketBank.budget r) (MatrixBatchBucketBank.input r)=some base)
    (bt : ∀ j,(TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base.final).tapes (slots j)=
      MatrixBucketGatePass.input r unused j)
    (bh : ∀ j,(TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base.final).heads (slots j)=0)
    (bs : base.steps≤MatrixBatchBucketBank.budget r) :
    ∃ store : MatrixBucketGateLoop.Store r,∃ actual,
      run machine (budget r) (input r)=some actual ∧
      actual.final.tapes 314=output r ∧ actual.final.heads 314=0 ∧
      (∀ j : Fin 36,actual.final.tapes (slots (j.castAdd 1))=(MatrixBucketGateFinish.final r unused store).tapes j) ∧
      (∀ j : Fin 36,actual.final.heads (slots (j.castAdd 1))=
        if j=8 then 0 else (MatrixBucketGateFinish.final r unused store).heads j) ∧
      (∀ i : Fin 335,(∀ j,slots j≠i.castAdd 1) → actual.final.tapes (i.castAdd 1)=base.final.tapes i ∧
        actual.final.heads (i.castAdd 1)=base.final.heads i) ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchBucketBank.machine (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base
  obtain ⟨store,body,hbody,bodyH,bodyT,_,_,bodyS⟩ := MatrixBucketGatePass.pass_run r unused
  let entry := initialConfiguration MatrixBucketGatePass.machine (MatrixBucketGatePass.input r unused)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · exact bh
    · exact bt
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBucketGatePass.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [])
      (initialConfiguration MatrixBatchBucketBank.machine (MatrixBatchBucketBank.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (j : Fin 36) : focused.final.tapes (slots (j.castAdd 1))=(MatrixBucketGateFinish.final r unused store).tapes j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact bodyT j
  have localH (j : Fin 36) : focused.final.heads (slots (j.castAdd 1))=
      if j=8 then 0 else (MatrixBucketGateFinish.final r unused store).heads j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact bodyH j
  refine ⟨store,Composition.joinedReceipt prepared focused,joined,?_,localH 8,localT,localH,?_,?_⟩
  · change focused.final.tapes 314=output r
    have h := localT 8
    simp only [MatrixBucketGateFinish.final,Function.update_self] at h
    exact h
  · intro i hi
    change focused.final.tapes (i.castAdd 1)=_ ∧ focused.final.heads (i.castAdd 1)=_
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hi,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps≤budget r
    rw [fs]
    change base.steps+1+body.steps≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) :
    ∃ unused : Fin 3 → List Bool,∃ store : MatrixBucketGateLoop.Store r,∃ base : ExecutionReceipt 335 _,∃ actual,
      run MatrixBatchBucketBank.machine (MatrixBatchBucketBank.budget r) (MatrixBatchBucketBank.input r)=some base ∧
      run machine (budget r) (input r)=some actual ∧
      actual.final.tapes 314=output r ∧ actual.final.heads 314=0 ∧
      (∀ j : Fin 36,actual.final.tapes (slots (j.castAdd 1))=(MatrixBucketGateFinish.final r unused store).tapes j) ∧
      (∀ j : Fin 36,actual.final.heads (slots (j.castAdd 1))=
        if j=8 then 0 else (MatrixBucketGateFinish.final r unused store).heads j) ∧
      (∀ i : Fin 335,(∀ j,slots j≠i.castAdd 1) → actual.final.tapes (i.castAdd 1)=base.final.tapes i ∧
        actual.final.heads (i.castAdd 1)=base.final.heads i) ∧ actual.steps≤budget r := by
  obtain ⟨unused,base,hb,bt,bh,bs⟩ := source_fields r
  obtain ⟨store,actual,ha,h314,t314,atapes,ah,old,as⟩ := pass_run r unused base hb bt bh bs
  exact ⟨unused,store,base,actual,hb,ha,h314,t314,atapes,ah,old,as⟩

end NearCubicWires.RepairOrdinary.MatrixBatchBucketPass
