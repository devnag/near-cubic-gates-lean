import Proof.MachineModel.OrdinaryMatrixBucketBudget

namespace NearCubicWires.RepairOrdinary.MatrixBatchBucketBudget
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem root_fields (r : Request) :
    ∃ actual,run MatrixBatchRootCapacity.machine (MatrixBatchRootCapacity.budget r) (MatrixBatchRootCapacity.input r)=some actual ∧
      actual.final.tapes 166=UnaryTemplate.tape (MatrixBucketDimensions.capacity r.U) ∧ actual.final.heads 166=0 ∧
      actual.final.tapes 89=UnaryTemplate.tape r.Gates ∧ actual.final.heads 89=1 ∧
      actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 162=MatrixBatchGateNativeLoop.output r ∧ actual.final.heads 162=(MatrixBatchGateNativeLoop.output r).length ∧
      actual.steps≤MatrixBatchRootCapacity.budget r := by
  obtain ⟨state,base,hb,bh,bt,b162,h162,b0,h0,_,_,_,_,_,_,bs⟩ := MatrixBatchAllRanks.all_run r
  have b39 : base.final.tapes 39=UnaryTemplate.tape r.U := (bt 27).trans (MatrixBatchRootCapacity.native_u r state)
  have h39 : base.final.heads 39=1 := bh 27
  have b130 : base.final.tapes 130=List.replicate (MatrixScoreReusableRanks.D r) true := (bt 44).trans (MatrixBatchRootCapacity.native_d r state)
  have h130 : base.final.heads 130=0 := bh 44
  have b89 : base.final.tapes 89=UnaryTemplate.tape r.Gates := by
    change base.final.tapes (MatrixBatchGateLayout.slots 48)=_
    rw [bt,MatrixBatchGateNativeLoop.cfg_tapes]
    rfl
  have h89 : base.final.heads 89=1 := bh 48
  obtain ⟨actual,ha,atapes,ah,a166,h166,as⟩ := MatrixBatchRootCapacity.capacity_run r base hb b39 h39 b130 h130 bs
  exact ⟨actual,ha,a166,h166,(atapes 89).trans b89,(ah 89).trans h89,
    (atapes 0).trans b0,(ah 0).trans h0,(atapes 162).trans b162,(ah 162).trans h162,as⟩

def slots : Fin 9 → Fin 198 := ![166,89,191,192,193,194,195,196,197]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_old (i : Fin 191) (h89 : i≠89) (h166 : i≠166) :
    RecoveryFocus.pick slots (i.castAdd 7)=none := by
  fin_cases i <;> first | contradiction | decide
def shifted (heads : Fin 198 → ℕ) (i : Fin 198) := if i=89 then heads i-1 else heads i
def retreat : Machine 198 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=89 then .left else .stay⟩ else none
theorem retreat_run (heads : Fin 198 → ℕ) (tapes : Fin 198 → List Bool) :
    ∃ actual,runFrom retreat 1 ⟨0,heads,tapes⟩=some actual ∧
      actual.final=⟨1,shifted heads,tapes⟩ ∧ actual.steps=1 := by
  have hs : step retreat ⟨0,heads,tapes⟩=some ⟨1,shifted heads,tapes⟩ := by
    simp only [step,retreat,Fin.val_zero,ite_true,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=89 <;> simp [applyAction,shifted,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

noncomputable def first := TapeEmbedding.machine 7 MatrixBatchRootCapacity.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBucketBudget.machine
noncomputable def tail := Composition.machine retreat last
noncomputable def machine := Composition.machine first tail
def input (r : Request) : Fin 198 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchRootCapacity.budget r+1+(1+1+MatrixBucketBudget.budget (MatrixBucketDimensions.capacity r.U))

theorem budget_run (r : Request) (base : ExecutionReceipt 191 _)
    (hb : run MatrixBatchRootCapacity.machine (MatrixBatchRootCapacity.budget r) (MatrixBatchRootCapacity.input r)=some base)
    (b166 : base.final.tapes 166=UnaryTemplate.tape (MatrixBucketDimensions.capacity r.U)) (h166 : base.final.heads 166=0)
    (b89 : base.final.tapes 89=UnaryTemplate.tape r.Gates) (h89 : base.final.heads 89=1)
    (bs : base.steps≤MatrixBatchRootCapacity.budget r) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 191,actual.final.tapes (i.castAdd 7)=base.final.tapes i) ∧
      (∀ i : Fin 191,actual.final.heads (i.castAdd 7)=if i=89 then 0 else base.final.heads i) ∧
      actual.final.tapes 196=List.replicate (MatrixBucketDimensions.bucketBudget r.U r.Gates) true ∧
      actual.final.heads 196=0 ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchRootCapacity.machine (fun _ : Fin 7 => 0) (fun _ : Fin 7 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 7 => 0) (fun _ : Fin 7 => []) base
  obtain ⟨moved,hm,mf,ms⟩ := retreat_run prepared.final.heads prepared.final.tapes
  obtain ⟨body,hbody,b0,b1,b7,bh,bsteps⟩ := MatrixBucketBudget.budget_run (MatrixBucketDimensions.capacity r.U) r.Gates
  let entry := initialConfiguration MatrixBucketBudget.machine
    (MatrixBucketBudgetPrepare.input (MatrixBucketDimensions.capacity r.U) r.Gates)
  have hi : RecoveryFocus.config slots moved.final.heads moved.final.tapes entry=
      Composition.restart moved.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [mf]
      fin_cases i
      · exact h166
      · change base.final.heads 89-1=0
        omega
      all_goals rfl
    · intro i
      rw [mf]
      fin_cases i
      · exact b166
      · exact b89
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBucketBudget.machine
    moved.final.heads moved.final.tapes _ entry body hbody
  rw [hi] at hf
  have joinedTail := Composition.run_join retreat last _ _ _ moved focused hm hf
  have hmid : Composition.leftConfig _ ⟨0,prepared.final.heads,prepared.final.tapes⟩=
      Composition.restart prepared.final tail.start := rfl
  rw [hmid] at joinedTail
  have joined := Composition.run_join first tail _ _ _ prepared (Composition.joinedReceipt moved focused) he joinedTail
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 7 => 0) (fun _ : Fin 7 => [])
      (initialConfiguration MatrixBatchRootCapacity.machine (MatrixBatchRootCapacity.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (i : Fin 9) : focused.final.tapes (slots i)=body.final.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (i : Fin 9) : focused.final.heads (slots i)=0 := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bh]
  refine ⟨Composition.joinedReceipt prepared (Composition.joinedReceipt moved focused),joined,?_,?_,
    (localT 7).trans b7,localH 7,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 7)=_
    by_cases hi89 : i=89
    · subst i; exact (localT 1).trans (b1.trans b89.symm)
    by_cases hi166 : i=166
    · subst i; exact (localT 0).trans (b0.trans b166.symm)
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi89 hi166]
    rw [mf]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · intro i
    change focused.final.heads (i.castAdd 7)=_
    by_cases hi89 : i=89
    · subst i; exact localH 1
    by_cases hi166 : i=166
    · subst i; exact (localH 0).trans h166.symm
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi89 hi166]
    rw [mf]
    have hh : (i.castAdd 7 : Fin 198)≠89 := by
      intro heq
      apply hi89
      exact Fin.ext (congrArg (fun a : Fin 198 => a.val) heq)
    simp only [shifted,hh,hi89,ite_false]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+(moved.steps+1+focused.steps)≤_
    rw [ms,hfs]
    change base.steps+1+(1+1+body.steps)≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 162=MatrixBatchGateNativeLoop.output r ∧ actual.final.heads 162=(MatrixBatchGateNativeLoop.output r).length ∧
      actual.final.tapes 166=UnaryTemplate.tape (MatrixBucketDimensions.capacity r.U) ∧ actual.final.heads 166=0 ∧
      actual.final.tapes 196=List.replicate (MatrixBucketDimensions.bucketBudget r.U r.Gates) true ∧
      actual.final.heads 196=0 ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,b166,h166,b89,h89,b0,h0,b162,h162,bs⟩ := root_fields r
  obtain ⟨actual,ha,atapes,ah,a196,h196,as⟩ := budget_run r base hb b166 h166 b89 h89 bs
  exact ⟨actual,ha,(atapes 0).trans b0,(ah 0).trans h0,(atapes 162).trans b162,(ah 162).trans h162,
    (atapes 166).trans b166,(ah 166).trans h166,a196,h196,as⟩

end NearCubicWires.RepairOrdinary.MatrixBatchBucketBudget
