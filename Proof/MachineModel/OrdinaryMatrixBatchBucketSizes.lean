import Proof.MachineModel.OrdinaryMatrixBucketSizes

/-! The canonical B/Buckets supplier is docked to the actual original
request producer. All earlier tapes except the consumed raw budget are
retained, including the ranked stream and actual U driver. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchBucketSizes
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_fields (r : Request) :
    ∃ actual,run MatrixBatchBucketBudget.machine (MatrixBatchBucketBudget.budget r) (MatrixBatchBucketBudget.input r)=some actual ∧
      actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 162=MatrixBatchGateNativeLoop.output r ∧ actual.final.heads 162=(MatrixBatchGateNativeLoop.output r).length ∧
      actual.final.tapes 166=UnaryTemplate.tape (MatrixBucketDimensions.capacity r.U) ∧ actual.final.heads 166=0 ∧
      actual.final.tapes 39=UnaryTemplate.tape r.U ∧ actual.final.heads 39=0 ∧
      actual.final.tapes 196=List.replicate (MatrixBucketDimensions.bucketBudget r.U r.Gates) true ∧
      actual.final.heads 196=0 ∧ actual.steps≤MatrixBatchBucketBudget.budget r := by
  obtain ⟨root,hr,r166,h166,r89,h89,r0,h0,r162,h162,rs⟩ := MatrixBatchBucketBudget.root_fields r
  obtain ⟨same,hs,_,_,_,_,_,_,s39,sh39,_,_,_⟩ := MatrixBatchRootCapacity.raw_run r
  have heq : same=root := Option.some.inj (hs.symm.trans hr)
  subst same
  obtain ⟨actual,ha,atapes,ah,a196,h196,as⟩ := MatrixBatchBucketBudget.budget_run r root hr r166 h166 r89 h89 rs
  exact ⟨actual,ha,(atapes 0).trans r0,(ah 0).trans h0,(atapes 162).trans r162,(ah 162).trans h162,
    (atapes 166).trans r166,(ah 166).trans h166,(atapes 39).trans s39,(ah 39).trans sh39,a196,h196,as⟩

def slots : Fin 28 → Fin 224 :=
  ![39,198,199,200,201,202,203,204,205,206,196,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_old (i : Fin 198) (h39 : i≠39) (h196 : i≠196) :
    RecoveryFocus.pick slots (i.castAdd 26)=none := by
  fin_cases i <;> first | contradiction | decide
noncomputable def first := TapeEmbedding.machine 26 MatrixBatchBucketBudget.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBucketSizes.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 224 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchBucketBudget.budget r+1+
  MatrixBucketSizes.budget r.U (MatrixBucketDimensions.bucketBudget r.U r.Gates)

theorem sizes_run (r : Request) (base : ExecutionReceipt 198 _)
    (hb : run MatrixBatchBucketBudget.machine (MatrixBatchBucketBudget.budget r) (MatrixBatchBucketBudget.input r)=some base)
    (b39 : base.final.tapes 39=UnaryTemplate.tape r.U) (h39 : base.final.heads 39=0)
    (b196 : base.final.tapes 196=List.replicate (MatrixBucketDimensions.bucketBudget r.U r.Gates) true)
    (h196 : base.final.heads 196=0) (bs : base.steps≤MatrixBatchBucketBudget.budget r) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 198,i≠196 → actual.final.tapes (i.castAdd 26)=base.final.tapes i) ∧
      (∀ i : Fin 198,actual.final.heads (i.castAdd 26)=base.final.heads i) ∧
      actual.final.tapes 207=List.replicate (MatrixBucketDimensions.bucketBudget r.U r.Gates) true ∧ actual.final.heads 207=0 ∧
      actual.final.tapes 214=List.replicate (MatrixBucketDimensions.bucketSize r.U r.Gates) true ∧ actual.final.heads 214=0 ∧
      actual.final.tapes 216=UnaryTemplate.tape (MatrixBucketDimensions.width r.U r.Gates) ∧ actual.final.heads 216=0 ∧
      actual.final.tapes 222=UnaryTemplate.tape (MatrixBucketDimensions.buckets r.U r.Gates) ∧ actual.final.heads 222=0 ∧
      actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchBucketBudget.machine (fun _ : Fin 26 => 0) (fun _ : Fin 26 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 26 => 0) (fun _ : Fin 26 => []) base
  have hpositive : 0<MatrixBucketDimensions.bucketBudget r.U r.Gates := by
    have h := MatrixBucketDimensions.budget_positive r.U r.Gates r.gateSquare
    omega
  obtain ⟨out,ready,o0,_,_,o11,_,_,o18,_,o20,_,_,o26⟩ :=
    MatrixBucketSizes.sizes_run r.U (MatrixBucketDimensions.bucketBudget r.U r.Gates) hpositive
  obtain ⟨body,hbody,bt,bh,bsteps⟩ := ready
  let entry := initialConfiguration MatrixBucketSizes.machine
    (MatrixBucketSizePrepare.input r.U (MatrixBucketDimensions.bucketBudget r.U r.Gates))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact h39
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h196
      all_goals rfl
    · intro i; fin_cases i
      · exact b39
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact b196
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBucketSizes.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 26 => 0) (fun _ : Fin 26 => [])
      (initialConfiguration MatrixBatchBucketBudget.machine (MatrixBatchBucketBudget.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (i : Fin 28) : focused.final.tapes (slots i)=out i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bt]
  have localH (i : Fin 28) : focused.final.heads (slots i)=0 := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bh]
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_,(localT 11).trans o11,localH 11,
    (localT 18).trans (o18.trans (congrArg (fun n => List.replicate n true) (MatrixBucketSizes.size_eq r.U r.Gates))),localH 18,
    (localT 20).trans (o20.trans (congrArg UnaryTemplate.tape (MatrixBucketSizes.width_eq r.U r.Gates))),localH 20,
    (localT 26).trans (o26.trans (congrArg UnaryTemplate.tape (MatrixBucketSizes.count_eq r.U r.Gates))),localH 26,?_⟩
  · intro i hi196
    change focused.final.tapes (i.castAdd 26)=_
    by_cases hi39 : i=39
    · subst i; exact (localT 0).trans (o0.trans b39.symm)
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi39 hi196]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · intro i
    change focused.final.heads (i.castAdd 26)=_
    by_cases hi39 : i=39
    · subst i; exact (localH 0).trans h39.symm
    by_cases hi196 : i=196
    · subst i; exact (localH 10).trans h196.symm
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi39 hi196]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps≤budget r
    rw [hfs]
    change base.steps+1+body.steps≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 162=MatrixBatchGateNativeLoop.output r ∧ actual.final.heads 162=(MatrixBatchGateNativeLoop.output r).length ∧
      actual.final.tapes 166=UnaryTemplate.tape (MatrixBucketDimensions.capacity r.U) ∧ actual.final.heads 166=0 ∧
      actual.final.tapes 39=UnaryTemplate.tape r.U ∧ actual.final.heads 39=0 ∧
      actual.final.tapes 207=List.replicate (MatrixBucketDimensions.bucketBudget r.U r.Gates) true ∧ actual.final.heads 207=0 ∧
      actual.final.tapes 214=List.replicate (MatrixBucketDimensions.bucketSize r.U r.Gates) true ∧ actual.final.heads 214=0 ∧
      actual.final.tapes 216=UnaryTemplate.tape (MatrixBucketDimensions.width r.U r.Gates) ∧ actual.final.heads 216=0 ∧
      actual.final.tapes 222=UnaryTemplate.tape (MatrixBucketDimensions.buckets r.U r.Gates) ∧ actual.final.heads 222=0 ∧
      actual.steps≤budget r := by
  obtain ⟨base,hb,b0,h0,b162,h162,b166,h166,b39,h39,b196,h196,bs⟩ := budget_fields r
  obtain ⟨actual,ha,atapes,ah,a207,h207,a214,h214,a216,h216,a222,h222,as⟩ := sizes_run r base hb b39 h39 b196 h196 bs
  exact ⟨actual,ha,(atapes 0 (by decide)).trans b0,(ah 0).trans h0,(atapes 162 (by decide)).trans b162,(ah 162).trans h162,
    (atapes 166 (by decide)).trans b166,(ah 166).trans h166,(atapes 39 (by decide)).trans b39,(ah 39).trans h39,
    a207,h207,a214,h214,a216,h216,a222,h222,as⟩

end NearCubicWires.RepairOrdinary.MatrixBatchBucketSizes
