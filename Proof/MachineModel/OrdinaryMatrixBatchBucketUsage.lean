import Proof.MachineModel.OrdinaryMatrixBucketUsage

/-! Whole original-request producer of the actual used-coordinate and
padding templates, retaining every earlier rank and dimension field. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchBucketUsage
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem gate_field (r : Request) :
    ∃ actual,run MatrixBatchNativeWidth.machine (MatrixBatchNativeWidth.budget r) (MatrixBatchNativeWidth.input r)=some actual ∧
      actual.final.tapes 89=UnaryTemplate.tape r.Gates ∧ actual.final.heads 89=0 := by
  obtain ⟨root,hr,r166,h166,r89,h89,_,_,_,_,rs⟩ := MatrixBatchBucketBudget.root_fields r
  obtain ⟨funded,hf,ft,fh,f196,h196,fs⟩ := MatrixBatchBucketBudget.budget_run r root hr r166 h166 r89 h89 rs
  obtain ⟨same,hs,_,_,_,_,_,_,s39,h39,_,_,_⟩ := MatrixBatchBucketSizes.budget_fields r
  have heq : same=funded := Option.some.inj (hs.symm.trans hf)
  subst same
  obtain ⟨sized,hz,zt,zh,_,_,_,_,_,_,_,_,zs⟩ := MatrixBatchBucketSizes.sizes_run r funded hf s39 h39 f196 h196 fs
  obtain ⟨same,hs,s32,h32,_⟩ := MatrixBatchNativeWidth.word_run r
  have heq : same=sized := Option.some.inj (hs.symm.trans hz)
  subst same
  obtain ⟨actual,ha,atapes,ah,_,_,_,_,_,_,_⟩ := MatrixBatchNativeWidth.width_run r sized hz s32 h32 zs
  exact ⟨actual,ha,(atapes 89).trans ((zt 89 (by decide)).trans ((ft 89).trans r89)),
    (ah 89).trans ((zh 89).trans (fh 89))⟩

theorem source_fields (r : Request) :
    ∃ actual,run MatrixBatchNativeDimensions.machine (MatrixBatchNativeDimensions.budget r) (MatrixBatchNativeDimensions.input r)=some actual ∧
      actual.final.tapes 89=UnaryTemplate.tape r.Gates ∧ actual.final.heads 89=0 ∧
      actual.final.tapes 222=UnaryTemplate.tape r.Buckets ∧ actual.final.heads 222=0 ∧
      actual.final.tapes 166=UnaryTemplate.tape r.Capacity ∧ actual.final.heads 166=0 ∧
      actual.steps≤MatrixBatchNativeDimensions.budget r := by
  obtain ⟨base,actual,hb,ha,atapes,ah,_,_,_,_,_,_,as⟩ := MatrixBatchNativeDimensions.raw_run r
  obtain ⟨same,hs,s89,h89⟩ := gate_field r
  have heq : same=base := Option.some.inj (hs.symm.trans hb)
  subst same
  obtain ⟨same,hs,_,_,s166,h166,_,_,s222,h222,_⟩ := MatrixBatchNativeDimensions.source_fields r
  have heq : same=base := Option.some.inj (hs.symm.trans hb)
  subst same
  exact ⟨actual,ha,(atapes 89).trans s89,(ah 89).trans h89,
    (atapes 222).trans s222,(ah 222).trans h222,(atapes 166).trans s166,(ah 166).trans h166,as⟩

def slots : Fin 15 → Fin 289 := ![89,277,278,279,280,222,281,282,283,284,285,286,166,287,288]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_old (i : Fin 277) (h89 : i≠89) (h166 : i≠166) (h222 : i≠222) :
    RecoveryFocus.pick slots (i.castAdd 12)=none := by
  fin_cases i <;> first | contradiction | decide
noncomputable def first := TapeEmbedding.machine 12 MatrixBatchNativeDimensions.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBucketUsage.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 289 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchNativeDimensions.budget r+1+MatrixBucketUsage.budget r.Gates r.Buckets r.Capacity

theorem usage_run (r : Request) (base : ExecutionReceipt 277 _)
    (hb : run MatrixBatchNativeDimensions.machine (MatrixBatchNativeDimensions.budget r) (MatrixBatchNativeDimensions.input r)=some base)
    (b89 : base.final.tapes 89=UnaryTemplate.tape r.Gates) (h89 : base.final.heads 89=0)
    (b222 : base.final.tapes 222=UnaryTemplate.tape r.Buckets) (h222 : base.final.heads 222=0)
    (b166 : base.final.tapes 166=UnaryTemplate.tape r.Capacity) (h166 : base.final.heads 166=0)
    (bs : base.steps≤MatrixBatchNativeDimensions.budget r) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 277,actual.final.tapes (i.castAdd 12)=base.final.tapes i) ∧
      (∀ i : Fin 277,actual.final.heads (i.castAdd 12)=base.final.heads i) ∧
      actual.final.tapes 285=UnaryTemplate.tape r.Used ∧ actual.final.heads 285=0 ∧
      actual.final.tapes 287=UnaryTemplate.tape (r.Capacity-r.Used) ∧ actual.final.heads 287=0 ∧
      actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchNativeDimensions.machine (fun _ : Fin 12 => 0) (fun _ : Fin 12 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 12 => 0) (fun _ : Fin 12 => []) base
  obtain ⟨out,ready,o0,o5,o12,o10,o13⟩ := MatrixBucketUsage.usage_run r.Gates r.Buckets r.Capacity (capacity r)
  obtain ⟨body,hbody,bt,bh,bsteps⟩ := ready
  let entry := initialConfiguration MatrixBucketUsage.machine (MatrixBucketUsage.input r.Gates r.Buckets r.Capacity)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact h89
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h222
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h166
      all_goals rfl
    · intro i; fin_cases i
      · exact b89
      · rfl
      · rfl
      · rfl
      · rfl
      · exact b222
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact b166
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBucketUsage.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 12 => 0) (fun _ : Fin 12 => [])
      (initialConfiguration MatrixBatchNativeDimensions.machine (MatrixBatchNativeDimensions.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (i : Fin 15) : focused.final.tapes (slots i)=out i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bt]
  have localH (i : Fin 15) : focused.final.heads (slots i)=0 := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bh]
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_,(localT 10).trans o10,localH 10,
    (localT 13).trans o13,localH 13,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 12)=_
    by_cases hi89 : i=89
    · subst i; exact (localT 0).trans (o0.trans b89.symm)
    by_cases hi166 : i=166
    · subst i; exact (localT 12).trans (o12.trans b166.symm)
    by_cases hi222 : i=222
    · subst i; exact (localT 5).trans (o5.trans b222.symm)
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi89 hi166 hi222]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · intro i
    change focused.final.heads (i.castAdd 12)=_
    by_cases hi89 : i=89
    · subst i; exact (localH 0).trans h89.symm
    by_cases hi166 : i=166
    · subst i; exact (localH 12).trans h166.symm
    by_cases hi222 : i=222
    · subst i; exact (localH 5).trans h222.symm
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi89 hi166 hi222]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps≤budget r
    rw [hfs]
    change base.steps+1+body.steps≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) :
    ∃ base : ExecutionReceipt 277 _,∃ actual,
      run MatrixBatchNativeDimensions.machine (MatrixBatchNativeDimensions.budget r) (MatrixBatchNativeDimensions.input r)=some base ∧
      run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 277,actual.final.tapes (i.castAdd 12)=base.final.tapes i) ∧
      (∀ i : Fin 277,actual.final.heads (i.castAdd 12)=base.final.heads i) ∧
      actual.final.tapes 285=UnaryTemplate.tape r.Used ∧ actual.final.heads 285=0 ∧
      actual.final.tapes 287=UnaryTemplate.tape (r.Capacity-r.Used) ∧ actual.final.heads 287=0 ∧
      actual.steps≤budget r := by
  obtain ⟨base,hb,b89,h89,b222,h222,b166,h166,bs⟩ := source_fields r
  obtain ⟨actual,ha,atapes,ah,a285,h285,a287,h287,as⟩ := usage_run r base hb b89 h89 b222 h222 b166 h166 bs
  exact ⟨base,actual,hb,ha,atapes,ah,a285,h285,a287,h287,as⟩

end NearCubicWires.RepairOrdinary.MatrixBatchBucketUsage
