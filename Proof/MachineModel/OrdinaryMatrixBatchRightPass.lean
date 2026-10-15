import Proof.MachineModel.OrdinaryMatrixBatchRightPassFields

/-! The original framed Request and blank work now produce the complete
terminated right key stream at head zero while retaining the actual left
matrix. Every score/rank/dimension/bank step and the right output rewind
belong to this single ordinary execution. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRightPass
open LocalBitMultitape MatrixScoreBatch MatrixBatchRightPassFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 MatrixBatchRightBank.machine
noncomputable def last := RecoveryFocus.machine slots MatrixRightGatePass.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 348 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixBatchRightBank.budget r+1+MatrixRightGatePass.budget r
noncomputable def output (r : Request) :=
  ZeroPadding.pad (MatrixScoreReusableRanks.D r) (MatrixRightGateNativeLoop.output r++[false])

theorem pass_run (r : Request) (unused : Fin 3 → List Bool) (initialStore : MatrixBucketGateLoop.Store r) (base : ExecutionReceipt 347 _)
    (hb : run MatrixBatchRightBank.machine (MatrixBatchRightBank.budget r) (MatrixBatchRightBank.input r)=some base)
    (bt : ∀ j,(TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base.final).tapes (slots j)=
      (MatrixRightGatePass.input r unused initialStore).tapes j)
    (bh : ∀ j,(TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base.final).heads (slots j)=(MatrixRightGatePass.input r unused initialStore).heads j)
    (bs : base.steps≤MatrixBatchRightBank.budget r) :
    ∃ store : MatrixBucketGateLoop.Store r,∃ actual,
      run machine (budget r) (input r)=some actual ∧
      actual.final.tapes 344=output r ∧ actual.final.heads 344=0 ∧
      (∀ j : Fin 38,actual.final.tapes (slots (j.castAdd 1))=(MatrixRightGateFinish.final r unused store).tapes j) ∧
      (∀ j : Fin 38,actual.final.heads (slots (j.castAdd 1))=
        if j=8 then 0 else (MatrixRightGateFinish.final r unused store).heads j) ∧
      (∀ i : Fin 347,(∀ j,slots j≠i.castAdd 1) → actual.final.tapes (i.castAdd 1)=base.final.tapes i ∧
        actual.final.heads (i.castAdd 1)=base.final.heads i) ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchRightBank.machine (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base
  obtain ⟨store,body,hbody,bodyH,bodyT,_,_,bodyS⟩ := MatrixRightGatePass.pass_run r unused initialStore
  let entry := MatrixRightGatePass.input r unused initialStore
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · exact bh
    · exact bt
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixRightGatePass.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [])
      (initialConfiguration MatrixBatchRightBank.machine (MatrixBatchRightBank.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (j : Fin 38) : focused.final.tapes (slots (j.castAdd 1))=(MatrixRightGateFinish.final r unused store).tapes j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact bodyT j
  have localH (j : Fin 38) : focused.final.heads (slots (j.castAdd 1))=
      if j=8 then 0 else (MatrixRightGateFinish.final r unused store).heads j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact bodyH j
  refine ⟨store,Composition.joinedReceipt prepared focused,joined,?_,localH 8,localT,localH,?_,?_⟩
  · change focused.final.tapes 344=output r
    have h := localT 8
    simp only [MatrixRightGateFinish.final,Function.update_self] at h
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
    ∃ unused : Fin 3 → List Bool,∃ store : MatrixBucketGateLoop.Store r,∃ base : ExecutionReceipt 347 _,∃ actual,
      run MatrixBatchRightBank.machine (MatrixBatchRightBank.budget r) (MatrixBatchRightBank.input r)=some base ∧
      run machine (budget r) (input r)=some actual ∧
      actual.final.tapes 344=output r ∧ actual.final.heads 344=0 ∧
      actual.final.tapes 342=MatrixBucketLeftPlane.plane r ∧ actual.final.heads 342=0 ∧
      (∀ j : Fin 38,actual.final.tapes (slots (j.castAdd 1))=(MatrixRightGateFinish.final r unused store).tapes j) ∧
      (∀ j : Fin 38,actual.final.heads (slots (j.castAdd 1))=
        if j=8 then 0 else (MatrixRightGateFinish.final r unused store).heads j) ∧
      (∀ i : Fin 347,(∀ j,slots j≠i.castAdd 1) → actual.final.tapes (i.castAdd 1)=base.final.tapes i ∧
        actual.final.heads (i.castAdd 1)=base.final.heads i) ∧ actual.steps≤budget r := by
  obtain ⟨unused,initialStore,base,hb,bt,bh,leftT,leftH,bs⟩ := source_fields r
  obtain ⟨store,actual,ha,outT,outH,atapes,ah,old,as⟩ := pass_run r unused initialStore base hb bt bh bs
  have hl := old 342 (by decide)
  exact ⟨unused,store,base,actual,hb,ha,outT,outH,hl.1.trans leftT,hl.2.trans leftH,atapes,ah,old,as⟩

end NearCubicWires.RepairOrdinary.MatrixBatchRightPass
