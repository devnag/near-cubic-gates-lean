import Proof.MachineModel.OrdinaryMatrixBatchBucketBankFields

/-! Original Request plus blank work reaches a fully allocated and
initialized bucket-scanner bank. Every old source and cursor is retained. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchBucketBank
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 34 → Fin 335 := ![306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,130,295,291,299,222,329,330,331,332,333,334]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 29 MatrixBatchRankReverse.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBucketTemplate.bank
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 335 → List Bool := fun i => if i=0 then physicalInput r else []
def bankBudget (r : Request) := MatrixBucketTemplate.budget (MatrixScoreReusableRanks.D r) (H r) r.M r.Buckets
def budget (r : Request) := MatrixBatchRankReverse.budget r+1+bankBudget r

theorem bank_run (r : Request) (base : ExecutionReceipt 306 _)
    (hb : run MatrixBatchRankReverse.machine (MatrixBatchRankReverse.budget r) (MatrixBatchRankReverse.input r)=some base)
    (bt : ∀ j,base.final.tapes (MatrixBatchBucketBankFields.slots j)=MatrixBatchBucketBankFields.fields r j)
    (bh : ∀ j,base.final.heads (MatrixBatchBucketBankFields.slots j)=0)
    (bs : base.steps ≤ MatrixBatchRankReverse.budget r) :
    ∃ bankOut : Fin 34 → List Bool,
      (∀ i : Fin 34,i≠22 → i≠28 → i≠29 → i≠30 → bankOut i=
        MatrixBucketScalars.data (MatrixScoreReusableRanks.D r) (H r) r.M (r.bucketSize+1) r.Buckets 6 i) ∧
      bankOut 22=ZeroPadding.pad (MatrixScoreReusableRanks.D r) (UnaryTemplate.tape r.Buckets) ∧
      ∃ actual,run machine (budget r) (input r)=some actual ∧
        (∀ i : Fin 306,actual.final.tapes (i.castAdd 29)=base.final.tapes i) ∧
        (∀ i : Fin 306,actual.final.heads (i.castAdd 29)=base.final.heads i) ∧
        (∀ j,actual.final.tapes (slots j)=bankOut j) ∧
        (∀ j,actual.final.heads (slots j)=0) ∧ actual.steps ≤ budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchRankReverse.machine (fun _ : Fin 29 => 0)
    (fun _ : Fin 29 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 29 => 0) (fun _ : Fin 29 => []) base
  obtain ⟨hH,hM⟩ := MatrixBatchBucketBankFields.capacity_fit r
  obtain ⟨out,ready,old,o22⟩ := MatrixBucketTemplate.bank_ready (MatrixScoreReusableRanks.D r)
    (H r) r.M (r.bucketSize+1) r.Buckets hH hM
  obtain ⟨body,hbody,bodyT,bodyH,bodyS⟩ := ready
  let entry := initialConfiguration MatrixBucketTemplate.bank
    (MatrixBucketWorkspace.input (MatrixScoreReusableRanks.D r) (H r) r.M (r.bucketSize+1) r.Buckets)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j
      all_goals first | exact bh 0 | exact bh 1 | exact bh 2 | exact bh 3 | exact bh 4 | rfl
    · intro j
      fin_cases j
      all_goals first | exact bt 0 | exact bt 1 | exact bt 2 | exact bt 3 | exact bt 4 | rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBucketTemplate.bank
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 29 => 0) (fun _ : Fin 29 => [])
      (initialConfiguration MatrixBatchRankReverse.machine (MatrixBatchRankReverse.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (j : Fin 34) : focused.final.tapes (slots j)=out j := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bodyT]
  have localH (j : Fin 34) : focused.final.heads (slots j)=0 := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bodyH]
  have stableT (j : Fin 5) : out ⟨23+j.val,by omega⟩=MatrixBatchBucketBankFields.fields r j := by
    fin_cases j
    · exact old 23 (by decide) (by decide) (by decide) (by decide)
    · exact old 24 (by decide) (by decide) (by decide) (by decide)
    · exact old 25 (by decide) (by decide) (by decide) (by decide)
    · exact old 26 (by decide) (by decide) (by decide) (by decide)
    · exact old 27 (by decide) (by decide) (by decide) (by decide)
  have old_or_new (j : Fin 34) : (slots j).val<306 → ∃ k : Fin 5,j=⟨23+k.val,by omega⟩ := by
    intro hj
    fin_cases j
    all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩ | simp [slots] at hj
  refine ⟨out,old,o22,Composition.joinedReceipt prepared focused,joined,?_,?_,localT,localH,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 29)=_
    rw [hff]
    cases hp : RecoveryFocus.pick slots (i.castAdd 29) with
    | none => simp [RecoveryFocus.config,hp,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hp
      obtain ⟨k,hk⟩ := old_or_new j (by rw [hj]; exact i.isLt)
      subst j
      have hi : MatrixBatchBucketBankFields.slots k=i := by
        apply Fin.ext
        have hv := congrArg Fin.val hj
        fin_cases k <;> exact hv
      simp only [RecoveryFocus.config,hp,bodyT]
      exact (stableT k).trans ((bt k).symm.trans (congrArg base.final.tapes hi))
  · intro i
    change focused.final.heads (i.castAdd 29)=_
    rw [hff]
    cases hp : RecoveryFocus.pick slots (i.castAdd 29) with
    | none => simp [RecoveryFocus.config,hp,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hp
      obtain ⟨k,hk⟩ := old_or_new j (by rw [hj]; exact i.isLt)
      subst j
      have hi : MatrixBatchBucketBankFields.slots k=i := by
        apply Fin.ext
        have hv := congrArg Fin.val hj
        fin_cases k <;> exact hv
      simp only [RecoveryFocus.config,hp,bodyH]
      exact (bh k).symm.trans (congrArg base.final.heads hi)
  · change prepared.steps+1+focused.steps ≤ budget r
    rw [hfs]
    change base.steps+1+body.steps ≤ budget r
    unfold budget bankBudget
    omega

theorem raw_run (r : Request) :
    ∃ base : ExecutionReceipt 306 _,∃ bankOut : Fin 34 → List Bool,∃ actual,
      run MatrixBatchRankReverse.machine (MatrixBatchRankReverse.budget r) (MatrixBatchRankReverse.input r)=some base ∧
      run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 306,actual.final.tapes (i.castAdd 29)=base.final.tapes i) ∧
      (∀ i : Fin 306,actual.final.heads (i.castAdd 29)=base.final.heads i) ∧
      (∀ j,actual.final.tapes (slots j)=bankOut j) ∧
      (∀ j,actual.final.heads (slots j)=0) ∧
      (∀ i : Fin 34,i≠22 → i≠28 → i≠29 → i≠30 → bankOut i=
        MatrixBucketScalars.data (MatrixScoreReusableRanks.D r) (H r) r.M (r.bucketSize+1) r.Buckets 6 i) ∧
      bankOut 22=ZeroPadding.pad (MatrixScoreReusableRanks.D r) (UnaryTemplate.tape r.Buckets) ∧
      actual.steps ≤ budget r := by
  obtain ⟨base,hb,bt,bh,bs⟩ := MatrixBatchBucketBankFields.source_fields r
  obtain ⟨bankOut,fields,counter,actual,ha,atapes,ah,localT,localH,as⟩ := bank_run r base hb bt bh bs
  exact ⟨base,bankOut,actual,hb,ha,atapes,ah,localT,localH,fields,counter,as⟩

end NearCubicWires.RepairOrdinary.MatrixBatchBucketBank
