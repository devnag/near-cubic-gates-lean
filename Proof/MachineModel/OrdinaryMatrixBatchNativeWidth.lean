import Proof.MachineModel.OrdinaryMatrixNativeWidth

/-! Recover the common width at the literal original-request endpoint.
The width scan preserves all earlier tapes and streaming cursors. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchNativeWidth
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_u (r : Request) (state : MatrixBatchGateStore.Store r) :
    (MatrixBatchGateNativeLoop.cfg r 3 (word r) (word r).length (MatrixBatchGateNativeLoop.output r) state).tapes 23=
      frame (binary r.M r.U) := by
  rw [MatrixBatchGateNativeLoop.cfg_tapes]
  simp [Fin.addCases,MatrixBatchGateClear.tapes,install,MatrixBatchGateClear.pick_scratch,
    MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable]

theorem word_run (r : Request) :
    ∃ actual,run MatrixBatchBucketSizes.machine (MatrixBatchBucketSizes.budget r) (MatrixBatchBucketSizes.input r)=some actual ∧
      actual.final.tapes 32=frame (binary r.M r.U) ∧ actual.final.heads 32=0 ∧
      actual.steps≤MatrixBatchBucketSizes.budget r := by
  obtain ⟨state,base,hb,bh,bt,_,_,_,_,_,_,_,_,_,_,bs⟩ := MatrixBatchAllRanks.all_run r
  have b32 : base.final.tapes 32=frame (binary r.M r.U) := (bt 23).trans (native_u r state)
  have h32 : base.final.heads 32=0 := bh 23
  have b39 : base.final.tapes 39=UnaryTemplate.tape r.U := (bt 27).trans (MatrixBatchRootCapacity.native_u r state)
  have h39 : base.final.heads 39=1 := bh 27
  have b130 : base.final.tapes 130=List.replicate (MatrixScoreReusableRanks.D r) true := (bt 44).trans (MatrixBatchRootCapacity.native_d r state)
  have h130 : base.final.heads 130=0 := bh 44
  have b89 : base.final.tapes 89=UnaryTemplate.tape r.Gates := by
    change base.final.tapes (MatrixBatchGateLayout.slots 48)=_
    rw [bt,MatrixBatchGateNativeLoop.cfg_tapes]
    rfl
  have h89 : base.final.heads 89=1 := bh 48
  obtain ⟨root,hr,rt,rh,r166,h166,rs⟩ := MatrixBatchRootCapacity.capacity_run r base hb b39 h39 b130 h130 bs
  obtain ⟨funded,hf,ft,fh,f196,h196,fs⟩ := MatrixBatchBucketBudget.budget_run r root hr r166 h166
    ((rt 89).trans b89) ((rh 89).trans h89) rs
  have f39 : funded.final.tapes 39=UnaryTemplate.tape r.U := (ft 39).trans ((rt 39).trans b39)
  have h39' : funded.final.heads 39=0 := (fh 39).trans (rh 39)
  obtain ⟨actual,ha,atapes,ah,_,_,_,_,_,_,_,_,as⟩ := MatrixBatchBucketSizes.sizes_run r funded hf f39 h39' f196 h196 fs
  exact ⟨actual,ha,(atapes 32 (by decide)).trans ((ft 32).trans ((rt 32).trans b32)),
    (ah 32).trans ((fh 32).trans ((rh 32).trans h32)),as⟩

def slots : Fin 6 → Fin 229 := ![32,224,225,226,227,228]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_old (i : Fin 224) (h32 : i≠32) : RecoveryFocus.pick slots (i.castAdd 5)=none := by
  fin_cases i <;> first | contradiction | decide
noncomputable def first := TapeEmbedding.machine 5 MatrixBatchBucketSizes.machine
noncomputable def last := RecoveryFocus.machine slots MatrixNativeWidth.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 229 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchBucketSizes.budget r+1+(8*r.M+18)

theorem width_run (r : Request) (base : ExecutionReceipt 224 _)
    (hb : run MatrixBatchBucketSizes.machine (MatrixBatchBucketSizes.budget r) (MatrixBatchBucketSizes.input r)=some base)
    (b32 : base.final.tapes 32=frame (binary r.M r.U)) (h32 : base.final.heads 32=0)
    (bs : base.steps≤MatrixBatchBucketSizes.budget r) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 224,actual.final.tapes (i.castAdd 5)=base.final.tapes i) ∧
      (∀ i : Fin 224,actual.final.heads (i.castAdd 5)=base.final.heads i) ∧
      actual.final.tapes 225=List.replicate r.M true ∧ actual.final.heads 225=0 ∧
      actual.final.tapes 226=List.replicate r.M true ∧ actual.final.heads 226=0 ∧
      actual.final.tapes 227=UnaryTemplate.tape r.M ∧ actual.final.heads 227=0 ∧
      actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchBucketSizes.machine (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base
  obtain ⟨out,ready,o0,o2,o3,o4⟩ := MatrixNativeWidth.width_run (binary r.M r.U)
  have hlen : (binary r.M r.U).length=r.M := by simp
  simp only [hlen] at o2 o3 o4
  obtain ⟨body,hbody,bt,bh,bsteps⟩ := ready
  have hbudget : MatrixNativeWidth.budget (binary r.M r.U)=8*r.M+18 := by simp [MatrixNativeWidth.budget]
  rw [hbudget] at hbody bsteps
  let entry := initialConfiguration MatrixNativeWidth.machine (MatrixNativeWidth.input (binary r.M r.U))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact h32
      all_goals rfl
    · intro i; fin_cases i
      · exact b32
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixNativeWidth.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => [])
      (initialConfiguration MatrixBatchBucketSizes.machine (MatrixBatchBucketSizes.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (i : Fin 6) : focused.final.tapes (slots i)=out i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bt]
  have localH (i : Fin 6) : focused.final.heads (slots i)=0 := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bh]
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_,(localT 2).trans o2,localH 2,
    (localT 3).trans o3,localH 3,(localT 4).trans o4,localH 4,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 5)=_
    by_cases hi32 : i=32
    · subst i; exact (localT 0).trans (o0.trans b32.symm)
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi32]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · intro i
    change focused.final.heads (i.castAdd 5)=_
    by_cases hi32 : i=32
    · subst i; exact (localH 0).trans h32.symm
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi32]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps≤budget r
    rw [hfs]
    change base.steps+1+body.steps≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) :
    ∃ base : ExecutionReceipt 224 _,∃ actual,
      run MatrixBatchBucketSizes.machine (MatrixBatchBucketSizes.budget r) (MatrixBatchBucketSizes.input r)=some base ∧
      run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 224,actual.final.tapes (i.castAdd 5)=base.final.tapes i) ∧
      (∀ i : Fin 224,actual.final.heads (i.castAdd 5)=base.final.heads i) ∧
      actual.final.tapes 225=List.replicate r.M true ∧ actual.final.heads 225=0 ∧
      actual.final.tapes 226=List.replicate r.M true ∧ actual.final.heads 226=0 ∧
      actual.final.tapes 227=UnaryTemplate.tape r.M ∧ actual.final.heads 227=0 ∧
      actual.steps≤budget r := by
  obtain ⟨base,hb,b32,h32,bs⟩ := word_run r
  obtain ⟨actual,ha,atapes,ah,a225,h225,a226,h226,a227,h227,as⟩ := width_run r base hb b32 h32 bs
  exact ⟨base,actual,hb,ha,atapes,ah,a225,h225,a226,h226,a227,h227,as⟩

end NearCubicWires.RepairOrdinary.MatrixBatchNativeWidth
