import Proof.MachineModel.OrdinaryMatrixBatchRightBankFields

/-! The original-request execution physically allocates its new right
output/scratch and resets the reused inner coordinate before the gate pass. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRightBank
open LocalBitMultitape MatrixScoreBatch MatrixBatchRightBankFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 3 MatrixBatchRightReturn.machine
noncomputable def last := RecoveryFocus.machine slots MatrixRightBankEntry.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 347 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixBatchRightReturn.budget r+1+MatrixRightBankEntry.budget r

theorem bank_run (r : Request) (base : ExecutionReceipt 344 _)
    (hb : run MatrixBatchRightReturn.machine (MatrixBatchRightReturn.budget r) (MatrixBatchRightReturn.input r)=some base)
    (bt : ∀ j,(TapeEmbedding.config (fun _ : Fin 3 => 0) (fun _ : Fin 3 => []) base.final).tapes (slots j)=
      MatrixRightBankEntry.input r r.Used j)
    (bh : ∀ j,(TapeEmbedding.config (fun _ : Fin 3 => 0) (fun _ : Fin 3 => []) base.final).heads (slots j)=0)
    (bs : base.steps≤MatrixBatchRightReturn.budget r) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    (∀ j,actual.final.tapes (slots j)=MatrixRightBankEntry.output r j) ∧
    (∀ j,actual.final.heads (slots j)=0) ∧
    (∀ i : Fin 344,i≠323 → actual.final.tapes (i.castAdd 3)=base.final.tapes i) ∧
    (∀ i : Fin 344,actual.final.heads (i.castAdd 3)=base.final.heads i) ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchRightReturn.machine (fun _ : Fin 3 => 0) (fun _ : Fin 3 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 3 => 0) (fun _ : Fin 3 => []) base
  obtain ⟨body,hr,rt,rh,rs⟩ := MatrixRightBankEntry.entry_ready r r.Used
  let entry := initialConfiguration MatrixRightBankEntry.machine (MatrixRightBankEntry.input r r.Used)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · exact bh
    · exact bt
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixRightBankEntry.machine
    prepared.final.heads prepared.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 3 => 0) (fun _ : Fin 3 => [])
      (initialConfiguration MatrixBatchRightReturn.machine (MatrixBatchRightReturn.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have localT (j : Fin 9) : focused.final.tapes (slots j)=MatrixRightBankEntry.output r j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,rt]
  have localH (j : Fin 9) : focused.final.heads (slots j)=0 := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,rh]
  refine ⟨Composition.joinedReceipt prepared focused,hj,localT,localH,?_,?_,?_⟩
  · intro i hi323
    change focused.final.tapes (i.castAdd 3)=_
    rw [ff]
    cases hx : RecoveryFocus.pick slots (i.castAdd 3) with
    | none => simp [RecoveryFocus.config,hx,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hx
      have j0 : j≠0 := by intro h; subst j; have hv := congrArg Fin.val hj; change 344=i.val at hv; omega
      have j1 : j≠1 := by intro h; subst j; have hv := congrArg Fin.val hj; change 345=i.val at hv; omega
      have j2 : j≠2 := by intro h; subst j; have hv := congrArg Fin.val hj; change 346=i.val at hv; omega
      have j3 : j≠3 := by intro h; subst j; apply hi323; exact Fin.ext (congrArg Fin.val hj).symm
      have same : MatrixRightBankEntry.output r j=MatrixRightBankEntry.input r r.Used j := by
        fin_cases j <;> first | exact (j0 rfl).elim | exact (j1 rfl).elim | exact (j2 rfl).elim | exact (j3 rfl).elim | rfl
      simp only [RecoveryFocus.config,hx,rt]
      have t := (bt j).symm
      rw [hj] at t
      apply same.trans
      simpa only [TapeEmbedding.config,Fin.addCases_left] using t
  · intro i
    change focused.final.heads (i.castAdd 3)=_
    rw [ff]
    cases hx : RecoveryFocus.pick slots (i.castAdd 3) with
    | none => simp [RecoveryFocus.config,hx,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hx
      simp only [RecoveryFocus.config,hx,rh]
      have h := (bh j).symm
      rw [hj] at h
      simpa only [TapeEmbedding.config,Fin.addCases_left] using h
  · change prepared.steps+1+focused.steps≤budget r
    rw [fs]
    change base.steps+1+body.steps≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) : ∃ base : ExecutionReceipt 344 _,∃ actual,
    run MatrixBatchRightReturn.machine (MatrixBatchRightReturn.budget r) (MatrixBatchRightReturn.input r)=some base ∧
    run machine (budget r) (input r)=some actual ∧
    (∀ j,actual.final.tapes (slots j)=MatrixRightBankEntry.output r j) ∧
    (∀ j,actual.final.heads (slots j)=0) ∧
    (∀ i : Fin 344,i≠323 → actual.final.tapes (i.castAdd 3)=base.final.tapes i) ∧
    (∀ i : Fin 344,actual.final.heads (i.castAdd 3)=base.final.heads i) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,bs⟩ := source_fields r
  obtain ⟨actual,ha,outputT,ah,oldT,oldH,steps⟩ := bank_run r base hb bt bh bs
  exact ⟨base,actual,hb,ha,outputT,ah,oldT,oldH,steps⟩

end NearCubicWires.RepairOrdinary.MatrixBatchRightBank
