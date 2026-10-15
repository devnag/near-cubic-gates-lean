import Proof.MachineModel.OrdinaryMatrixBucketEndpoints

/-! Exact key-width/endpoint supplier at the full original-request
boundary. All existing data and streaming cursors are retained. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchBucketEndpoints
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def H (r : Request) := r.M+r.S+1
theorem native_w (r : Request) (state : MatrixBatchGateStore.Store r) :
    (MatrixBatchGateNativeLoop.cfg r 3 (word r) (word r).length (MatrixBatchGateNativeLoop.output r) state).tapes 6=
      List.replicate (r.S+1) true := by
  rw [MatrixBatchGateNativeLoop.cfg_tapes]
  simp [Fin.addCases,MatrixBatchGateClear.tapes,install,MatrixBatchGateClear.pick_scratch,
    MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable]

theorem new_fields (r : Request) :
    ∃ actual,run MatrixBatchBucketUsage.machine (MatrixBatchBucketUsage.budget r) (MatrixBatchBucketUsage.input r)=some actual ∧
      actual.final.tapes 225=List.replicate r.M true ∧ actual.final.heads 225=0 ∧
      actual.final.tapes 258=frame (binary r.M (r.bucketSize+1)) ∧ actual.final.heads 258=0 := by
  obtain ⟨base,native,hb,hn,nt,nh,_,_,n258,h258,_,_,ns⟩ := MatrixBatchNativeDimensions.raw_run r
  obtain ⟨same,hs,s225,h225,_,_,_,_,_,_,_⟩ := MatrixBatchNativeDimensions.source_fields r
  have heq : same=base := Option.some.inj (hs.symm.trans hb)
  subst same
  obtain ⟨same,hs,s89,h89,s222,h222,s166,h166,_⟩ := MatrixBatchBucketUsage.source_fields r
  have heq : same=native := Option.some.inj (hs.symm.trans hn)
  subst same
  obtain ⟨actual,ha,atapes,ah,_,_,_,_,_⟩ := MatrixBatchBucketUsage.usage_run r native hn s89 h89 s222 h222 s166 h166 ns
  exact ⟨actual,ha,(atapes 225).trans ((nt 225).trans s225),(ah 225).trans ((nh 225).trans h225),
    (atapes 258).trans n258,(ah 258).trans h258⟩

theorem source_fields (r : Request) :
    ∃ actual,run MatrixBatchBucketUsage.machine (MatrixBatchBucketUsage.budget r) (MatrixBatchBucketUsage.input r)=some actual ∧
      actual.final.tapes 49=List.replicate (r.S+1) true ∧ actual.final.heads 49=0 ∧
      actual.final.tapes 225=List.replicate r.M true ∧ actual.final.heads 225=0 ∧
      actual.final.tapes 258=frame (binary r.M (r.bucketSize+1)) ∧ actual.final.heads 258=0 ∧
      actual.steps≤MatrixBatchBucketUsage.budget r := by
  obtain ⟨state,ranked,actual,_,rt,rh,ha,atapes,ah,_,_,_,_,_,_,_,_,_,_,as⟩ := MatrixBatchRetainedFields.retained_run r
  obtain ⟨same,hs,s225,h225,s258,h258⟩ := new_fields r
  have heq : same=actual := Option.some.inj (hs.symm.trans ha)
  subst same
  exact ⟨actual,ha,(atapes 49).trans ((rt 6).trans (native_w r state)),(ah 49).trans (rh 6),
    s225,h225,s258,h258,as⟩

def slots : Fin 16 → Fin 302 := ![49,225,258,289,290,291,292,293,294,295,296,297,298,299,300,301]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_old (i : Fin 289) (h49 : i≠49) (h225 : i≠225) (h258 : i≠258) :
    RecoveryFocus.pick slots (i.castAdd 13)=none := by
  fin_cases i <;> first | contradiction | decide
noncomputable def first := TapeEmbedding.machine 13 MatrixBatchBucketUsage.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBucketEndpoints.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 302 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchBucketUsage.budget r+1+MatrixBucketEndpoints.budget (r.S+1) r.M

theorem endpoints_run (r : Request) (base : ExecutionReceipt 289 _)
    (hb : run MatrixBatchBucketUsage.machine (MatrixBatchBucketUsage.budget r) (MatrixBatchBucketUsage.input r)=some base)
    (b49 : base.final.tapes 49=List.replicate (r.S+1) true) (h49 : base.final.heads 49=0)
    (b225 : base.final.tapes 225=List.replicate r.M true) (h225 : base.final.heads 225=0)
    (b258 : base.final.tapes 258=frame (binary r.M (r.bucketSize+1))) (h258 : base.final.heads 258=0)
    (bs : base.steps≤MatrixBatchBucketUsage.budget r) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 289,actual.final.tapes (i.castAdd 13)=base.final.tapes i) ∧
      (∀ i : Fin 289,actual.final.heads (i.castAdd 13)=base.final.heads i) ∧
      actual.final.tapes 289=List.replicate (H r) true ∧ actual.final.heads 289=0 ∧
      actual.final.tapes 291=frame (binary (H r) (r.bucketSize+1)) ∧ actual.final.heads 291=0 ∧
      actual.final.tapes 295=frame (binary (H r) 0) ∧ actual.final.heads 295=0 ∧
      actual.final.tapes 299=frame (binary r.M 0) ∧ actual.final.heads 299=0 ∧
      actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchBucketUsage.machine (fun _ : Fin 13 => 0) (fun _ : Fin 13 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 13 => 0) (fun _ : Fin 13 => []) base
  have hfit : r.bucketSize+1<2^r.M := MatrixBatchNativeDimensions.dimensions_fit r 1
  obtain ⟨out,ready,o0,o1,o2,o3,o5,o9,o13⟩ := MatrixBucketEndpoints.endpoints_run (r.S+1) r.M (r.bucketSize+1) hfit
  have hH : (r.S+1)+r.M=H r := by unfold H; omega
  rw [hH] at o3 o5 o9
  obtain ⟨body,hbody,bt,bh,bsteps⟩ := ready
  let entry := initialConfiguration MatrixBucketEndpoints.machine (MatrixBucketEndpoints.input (r.S+1) r.M (r.bucketSize+1))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact h49
      · exact h225
      · exact h258
      all_goals rfl
    · intro i; fin_cases i
      · exact b49
      · exact b225
      · exact b258
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBucketEndpoints.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 13 => 0) (fun _ : Fin 13 => [])
      (initialConfiguration MatrixBatchBucketUsage.machine (MatrixBatchBucketUsage.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (i : Fin 16) : focused.final.tapes (slots i)=out i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bt]
  have localH (i : Fin 16) : focused.final.heads (slots i)=0 := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bh]
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_,(localT 3).trans o3,localH 3,
    (localT 5).trans o5,localH 5,(localT 9).trans o9,localH 9,(localT 13).trans o13,localH 13,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 13)=_
    by_cases hi49 : i=49
    · subst i; exact (localT 0).trans (o0.trans b49.symm)
    by_cases hi225 : i=225
    · subst i; exact (localT 1).trans (o1.trans b225.symm)
    by_cases hi258 : i=258
    · subst i; exact (localT 2).trans (o2.trans b258.symm)
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi49 hi225 hi258]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · intro i
    change focused.final.heads (i.castAdd 13)=_
    by_cases hi49 : i=49
    · subst i; exact (localH 0).trans h49.symm
    by_cases hi225 : i=225
    · subst i; exact (localH 1).trans h225.symm
    by_cases hi258 : i=258
    · subst i; exact (localH 2).trans h258.symm
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi49 hi225 hi258]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps≤budget r
    rw [hfs]
    change base.steps+1+body.steps≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) :
    ∃ base : ExecutionReceipt 289 _,∃ actual,
      run MatrixBatchBucketUsage.machine (MatrixBatchBucketUsage.budget r) (MatrixBatchBucketUsage.input r)=some base ∧
      run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 289,actual.final.tapes (i.castAdd 13)=base.final.tapes i) ∧
      (∀ i : Fin 289,actual.final.heads (i.castAdd 13)=base.final.heads i) ∧
      actual.final.tapes 289=List.replicate (H r) true ∧ actual.final.heads 289=0 ∧
      actual.final.tapes 291=frame (binary (H r) (r.bucketSize+1)) ∧ actual.final.heads 291=0 ∧
      actual.final.tapes 295=frame (binary (H r) 0) ∧ actual.final.heads 295=0 ∧
      actual.final.tapes 299=frame (binary r.M 0) ∧ actual.final.heads 299=0 ∧
      actual.steps≤budget r := by
  obtain ⟨base,hb,b49,h49,b225,h225,b258,h258,bs⟩ := source_fields r
  obtain ⟨actual,ha,atapes,ah,a289,h289,a291,h291,a295,h295,a299,h299,as⟩ :=
    endpoints_run r base hb b49 h49 b225 h225 b258 h258 bs
  exact ⟨base,actual,hb,ha,atapes,ah,a289,h289,a291,h291,a295,h295,a299,h299,as⟩

end NearCubicWires.RepairOrdinary.MatrixBatchBucketEndpoints
