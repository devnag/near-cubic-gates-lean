import Proof.MachineModel.OrdinaryMatrixBucketRoot

namespace NearCubicWires.RepairOrdinary.MatrixBatchRootCapacity
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open MatrixScoreReusableRanks (D)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 27 → Fin 191 := ![166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,39,188,189,130,190]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_old (i : Fin 166) (h39 : i≠39) (h130 : i≠130) :
    RecoveryFocus.pick slots (i.castAdd 25)=none := by
  fin_cases i <;> first | contradiction | decide
def shifted (heads : Fin 191 → ℕ) (i : Fin 191) := if i=39 then heads i-1 else heads i
def retreat : Machine 191 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=39 then .left else .stay⟩ else none
theorem retreat_run (heads : Fin 191 → ℕ) (tapes : Fin 191 → List Bool) :
    ∃ actual,runFrom retreat 1 ⟨0,heads,tapes⟩=some actual ∧
      actual.final=⟨1,shifted heads,tapes⟩ ∧ actual.steps=1 := by
  have hs : step retreat ⟨0,heads,tapes⟩=some ⟨1,shifted heads,tapes⟩ := by
    simp only [step,retreat,Fin.val_zero,ite_true,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=39 <;> simp [applyAction,shifted,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

noncomputable def first := TapeEmbedding.machine 25 MatrixBatchAllRanks.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBucketRootCold.machine
noncomputable def tail := Composition.machine retreat last
noncomputable def machine := Composition.machine first tail
def input (r : Request) : Fin 191 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchAllRanks.budget r+1+(1+1+MatrixBucketRootCold.budget r)

theorem capacity_run (r : Request) (base : ExecutionReceipt 166 _)
    (hb : run MatrixBatchAllRanks.machine (MatrixBatchAllRanks.budget r) (MatrixBatchGateColdEntry.input r)=some base)
    (b39 : base.final.tapes 39=UnaryTemplate.tape r.U) (h39 : base.final.heads 39=1)
    (b130 : base.final.tapes 130=List.replicate (D r) true) (h130 : base.final.heads 130=0)
    (bs : base.steps≤MatrixBatchAllRanks.budget r) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 166,actual.final.tapes (i.castAdd 25)=base.final.tapes i) ∧
      (∀ i : Fin 166,actual.final.heads (i.castAdd 25)=if i=39 then 0 else base.final.heads i) ∧
      actual.final.tapes 166=UnaryTemplate.tape (MatrixBucketDimensions.capacity r.U) ∧
      actual.final.heads 166=0 ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchAllRanks.machine (fun _ : Fin 25 => 0) (fun _ : Fin 25 => [])
    _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 25 => 0) (fun _ : Fin 25 => []) base
  obtain ⟨moved,hm,mf,ms⟩ := retreat_run prepared.final.heads prepared.final.tapes
  obtain ⟨work,_,body,hbody,bh,bt,bsteps⟩ := MatrixBucketRootCold.root_run r
  let entry := initialConfiguration MatrixBucketRootCold.machine (MatrixBucketRootCold.input r)
  have hi : RecoveryFocus.config slots moved.final.heads moved.final.tapes entry=
      Composition.restart moved.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [mf]
      fin_cases i
      all_goals first | (change base.final.heads 39-1=0; omega) | exact h130 | rfl
    · intro i
      rw [mf]
      fin_cases i
      all_goals first | exact b39 | exact b130 | rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBucketRootCold.machine
    moved.final.heads moved.final.tapes _ entry body hbody
  rw [hi] at hf
  have joinedTail := Composition.run_join retreat last _ _ _ moved focused hm hf
  have hmid : Composition.leftConfig _ ⟨0,prepared.final.heads,prepared.final.tapes⟩=
      Composition.restart prepared.final tail.start := rfl
  rw [hmid] at joinedTail
  have joined := Composition.run_join first tail _ _ _ prepared
    (Composition.joinedReceipt moved focused) he joinedTail
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 25 => 0) (fun _ : Fin 25 => [])
      (initialConfiguration MatrixBatchAllRanks.machine (MatrixBatchGateColdEntry.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (i : Fin 27) : focused.final.tapes (slots i)=
      MatrixBucketRootClear.tapes r (MatrixBucketDimensions.capacity r.U) (D r+1) work i := by
    rw [hff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using congrFun bt i
  have localH (i : Fin 27) : focused.final.heads (slots i)=0 := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bh]
  refine ⟨Composition.joinedReceipt prepared (Composition.joinedReceipt moved focused),joined,?_,?_,
    localT 0,localH 0,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 25)=_
    by_cases hi39 : i=39
    · subst i
      exact (localT 22).trans b39.symm
    by_cases hi130 : i=130
    · subst i
      exact (localT 25).trans b130.symm
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi39 hi130]
    rw [mf]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · intro i
    change focused.final.heads (i.castAdd 25)=_
    by_cases hi39 : i=39
    · subst i
      exact localH 22
    by_cases hi130 : i=130
    · subst i
      exact (localH 25).trans h130.symm
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi39 hi130]
    rw [mf]
    have hh : (i.castAdd 25 : Fin 191)≠39 := by
      intro heq
      apply hi39
      exact Fin.ext (congrArg (fun a : Fin 191 => a.val) heq)
    simp only [shifted,hh,hi39,ite_false]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+(moved.steps+1+focused.steps)≤_
    rw [ms,hfs]
    change base.steps+1+(1+1+body.steps)≤budget r
    unfold budget
    omega

theorem native_u (r : Request) (state : MatrixBatchGateStore.Store r) :
    (MatrixBatchGateNativeLoop.cfg r 3 (word r) (word r).length (MatrixBatchGateNativeLoop.output r) state).tapes 27=
      UnaryTemplate.tape r.U := by
  rw [MatrixBatchGateNativeLoop.cfg_tapes]
  simp [Fin.addCases,MatrixBatchGateClear.tapes,RecoveryRootRound.install,MatrixBatchGateClear.pick_scratch,
    MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable]
theorem native_d (r : Request) (state : MatrixBatchGateStore.Store r) :
    (MatrixBatchGateNativeLoop.cfg r 3 (word r) (word r).length (MatrixBatchGateNativeLoop.output r) state).tapes 44=
      List.replicate (D r) true := by
  rw [MatrixBatchGateNativeLoop.cfg_tapes]
  simp [Fin.addCases,MatrixBatchGateClear.tapes,RecoveryRootRound.install,MatrixBatchGateClear.pick_scratch,
    MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable]

theorem raw_run (r : Request) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 162=MatrixBatchGateNativeLoop.output r ∧
      actual.final.heads 162=(MatrixBatchGateNativeLoop.output r).length ∧
      actual.final.tapes 166=UnaryTemplate.tape (MatrixBucketDimensions.capacity r.U) ∧
      actual.final.heads 166=0 ∧ actual.final.tapes 39=UnaryTemplate.tape r.U ∧
      actual.final.heads 39=0 ∧ actual.final.tapes 130=List.replicate (D r) true ∧
      actual.final.heads 130=0 ∧ actual.steps≤budget r := by
  obtain ⟨state,base,hb,bh,bt,b162,h162,b0,h0,_,_,_,_,_,_,bs⟩ := MatrixBatchAllRanks.all_run r
  have b39 : base.final.tapes 39=UnaryTemplate.tape r.U := (bt 27).trans (native_u r state)
  have h39 : base.final.heads 39=1 := bh 27
  have b130 : base.final.tapes 130=List.replicate (D r) true := (bt 44).trans (native_d r state)
  have h130 : base.final.heads 130=0 := bh 44
  obtain ⟨actual,ha,atapes,ah,a166,h166,as⟩ := capacity_run r base hb b39 h39 b130 h130 bs
  exact ⟨actual,ha,(atapes 0).trans b0,(ah 0).trans h0,(atapes 162).trans b162,(ah 162).trans h162,
    a166,h166,(atapes 39).trans b39,ah 39,(atapes 130).trans b130,(ah 130).trans h130,as⟩

end NearCubicWires.RepairOrdinary.MatrixBatchRootCapacity
