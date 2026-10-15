import Proof.MachineModel.OrdinaryMatrixBatchCapacity

/-! The shared storage driver is constructed from the actual cold batch
prefix. The U sentinel's entry adjustment is an executed transition. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchWorkspace
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 26 → Fin 132 := ![77,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,39,126,127,128,129,130,131]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_old (i : Fin 108) (h77 : i≠77) (h39 : i≠39) :
    RecoveryFocus.pick slots (i.castAdd 24)=none := by
  fin_cases i <;> first | contradiction | decide
def shifted (heads : Fin 132 → ℕ) (i : Fin 132) := if i=39 then heads i-1 else heads i
def retreat : Machine 132 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=39 then .left else .stay⟩ else none
theorem retreat_run (heads : Fin 132 → ℕ) (tapes : Fin 132 → List Bool) :
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

noncomputable def first := TapeEmbedding.machine 24 MatrixBatchNativeFields.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBatchCapacity.machine
noncomputable def tail := Composition.machine retreat last
noncomputable def machine := Composition.machine first tail
def input (r : Request) : Fin 132 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchNativeFields.budget r+1+
  (1+1+MatrixBatchCapacity.budget (MatrixScoreLeftLoop.C r) r.U)

theorem workspace_run (r : Request) (base : ExecutionReceipt 108 _)
    (hb : run MatrixBatchNativeFields.machine (MatrixBatchNativeFields.budget r)
      (MatrixBatchNativeFields.input r)=some base)
    (b77 : base.final.tapes 77=List.replicate (MatrixScoreLeftLoop.C r) true)
    (h77 : base.final.heads 77=0)
    (b39 : base.final.tapes 39=UnaryTemplate.tape r.U) (h39 : base.final.heads 39=1)
    (bs : base.steps≤MatrixBatchNativeFields.budget r) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 108,actual.final.tapes (i.castAdd 24)=base.final.tapes i) ∧
      (∀ i : Fin 108,actual.final.heads (i.castAdd 24)=if i=39 then 0 else base.final.heads i) ∧
      actual.final.tapes 130=List.replicate (MatrixBatchCapacity.capacity (MatrixScoreLeftLoop.C r) r.U) true ∧
      actual.final.heads 130=0 ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchNativeFields.machine
    (fun _ : Fin 24 => 0) (fun _ : Fin 24 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 24 => 0) (fun _ : Fin 24 => []) base
  obtain ⟨moved,hm,mf,ms⟩ := retreat_run prepared.final.heads prepared.final.tapes
  obtain ⟨out,hready,c0,c19,c24⟩ :=
    MatrixBatchCapacity.capacity_run (MatrixScoreLeftLoop.C r) r.U
  obtain ⟨body,hbdy,bt,bh,bsteps⟩ := hready
  let entry := initialConfiguration MatrixBatchCapacity.machine
    (MatrixBatchCapacity.input (MatrixScoreLeftLoop.C r) r.U)
  have hi : RecoveryFocus.config slots moved.final.heads moved.final.tapes entry=
      Composition.restart moved.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [mf]
      fin_cases i
      · exact h77
      all_goals first | (change base.final.heads 39-1=0; omega) | rfl
    · intro i
      rw [mf]
      fin_cases i
      · exact b77
      all_goals first | exact b39 | rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBatchCapacity.machine
    moved.final.heads moved.final.tapes _ entry body hbdy
  rw [hi] at hf
  have joinedTail := Composition.run_join retreat last _ _ _ moved focused hm hf
  have hmid : Composition.leftConfig _ ⟨0,prepared.final.heads,prepared.final.tapes⟩=
      Composition.restart prepared.final tail.start := rfl
  rw [hmid] at joinedTail
  have joined := Composition.run_join first tail _ _ _ prepared
    (Composition.joinedReceipt moved focused) he joinedTail
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 24 => 0) (fun _ : Fin 24 => [])
      (initialConfiguration MatrixBatchNativeFields.machine (MatrixBatchNativeFields.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (i : Fin 26) : focused.final.tapes (slots i)=out i := by
    rw [hff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using congrFun bt i
  have localH (i : Fin 26) : focused.final.heads (slots i)=0 := by
    rw [hff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using bh i
  refine ⟨Composition.joinedReceipt prepared (Composition.joinedReceipt moved focused),joined,?_,?_,
    (localT 24).trans c24,localH 24,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 24)=_
    by_cases hi77 : i=77
    · subst i
      exact (localT 0).trans (c0.trans b77.symm)
    by_cases hi39 : i=39
    · subst i
      exact (localT 19).trans (c19.trans b39.symm)
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi77 hi39]
    rw [mf]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · intro i
    change focused.final.heads (i.castAdd 24)=_
    by_cases hi77 : i=77
    · subst i
      exact (localH 0).trans h77.symm
    by_cases hi39 : i=39
    · subst i
      exact localH 19
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi77 hi39]
    rw [mf]
    have hh : (i.castAdd 24 : Fin 132)≠39 := by
      intro heq
      apply hi39
      exact Fin.ext (congrArg (fun a : Fin 132 => a.val) heq)
    simp only [shifted,hh,hi39,ite_false]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+(moved.steps+1+focused.steps)≤_
    rw [ms,hfs]
    change base.steps+1+(1+1+body.steps)≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) : ∃ actual,run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 130=List.replicate (MatrixBatchCapacity.capacity (MatrixScoreLeftLoop.C r) r.U) true ∧
    actual.final.heads 130=0 ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,b0,h0,_,_,_,_,b39,h39,_,_,_,_,_,_,_,_,b77,h77,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bs⟩ :=
    MatrixBatchNativeFields.setup_run r
  obtain ⟨actual,ha,hta,ah,a130,h130,hsteps⟩ := workspace_run r base hb b77 h77 b39 h39 bs
  exact ⟨actual,ha,(hta 0).trans b0,(ah 0).trans h0,a130,h130,hsteps⟩

end NearCubicWires.RepairOrdinary.MatrixBatchWorkspace
