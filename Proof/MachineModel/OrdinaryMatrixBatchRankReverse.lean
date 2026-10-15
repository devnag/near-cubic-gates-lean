import Proof.MachineModel.OrdinaryMatrixBatchRankReverseFields

/-! The original raw Request now reaches a rank stream at head0 with the
canonical bucket dimensions retained. The H sentinel and every rewind step
are produced by the executed enclosing program. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRankReverse
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 8 → Fin 306 := ![162,289,39,89,302,303,304,305]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_old (i : Fin 302) (h162 : i≠162) (h289 : i≠289) (h39 : i≠39) (h89 : i≠89) :
    RecoveryFocus.pick slots (i.castAdd 4)=none := by
  fin_cases i <;> first | contradiction | decide
noncomputable def first := TapeEmbedding.machine 4 MatrixBatchBucketEndpoints.machine
noncomputable def last : Machine 306 (6+(2+(MatrixRankStreamReverse.loopStates+2))) :=
  RecoveryFocus.machine slots MatrixRankReverseEntry.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 306 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchBucketEndpoints.budget r+1+MatrixRankReverseEntry.budget (H r) r.U r.Gates

theorem reverse_run (r : Request) (base : ExecutionReceipt 302 _)
    (hb : run MatrixBatchBucketEndpoints.machine (MatrixBatchBucketEndpoints.budget r)
      (MatrixBatchBucketEndpoints.input r)=some base)
    (b162 : base.final.tapes 162=MatrixBatchGateNativeLoop.output r)
    (h162 : base.final.heads 162=(MatrixBatchGateNativeLoop.output r).length)
    (b289 : base.final.tapes 289=List.replicate (H r) true) (h289 : base.final.heads 289=0)
    (b39 : base.final.tapes 39=UnaryTemplate.tape r.U) (h39 : base.final.heads 39=0)
    (b89 : base.final.tapes 89=UnaryTemplate.tape r.Gates) (h89 : base.final.heads 89=0)
    (bs : base.steps ≤ MatrixBatchBucketEndpoints.budget r) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 302,i≠289 → actual.final.tapes (i.castAdd 4)=base.final.tapes i) ∧
      (∀ i : Fin 302,actual.final.heads (i.castAdd 4)=if i=162 then 0 else base.final.heads i) ∧
      actual.final.tapes 302=List.replicate (H r) true ∧ actual.final.heads 302=0 ∧
      actual.final.tapes 303=List.replicate (H r) true ∧ actual.final.heads 303=0 ∧
      actual.final.tapes 304=UnaryTemplate.tape (H r) ∧ actual.final.heads 304=0 ∧
      actual.steps ≤ budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchBucketEndpoints.machine (fun _ : Fin 4 => 0)
    (fun _ : Fin 4 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) base
  obtain ⟨body,hbody,bsteps,bheads,b0,b2,b3,b4,b5,b6⟩ := MatrixRankReverseEntry.entry_run
    (MatrixBatchGateNativeLoop.output r) (H r) r.U r.Gates (MatrixBatchGateNativeLoop.output r).length
  have bh : ∀ i,body.final.heads i=0 := by
    intro i
    rw [bheads,MatrixBatchRankReverseFields.output_length,Nat.sub_self]
    fin_cases i <;> rfl
  let entry := MatrixRankReverseEntry.cfg (MatrixBatchGateNativeLoop.output r) (H r) r.U r.Gates
    (MatrixBatchGateNativeLoop.output r).length
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact h162
      · exact h289
      · exact h39
      · exact h89
      all_goals rfl
    · intro i; fin_cases i
      · exact b162
      · exact b289
      · exact b39
      · exact b89
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config
    (s := 6+(2+(MatrixRankStreamReverse.loopStates+2))) slots slots_injective MatrixRankReverseEntry.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 4 => 0) (fun _ : Fin 4 => [])
      (initialConfiguration MatrixBatchBucketEndpoints.machine (MatrixBatchBucketEndpoints.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (i : Fin 8) : focused.final.tapes (slots i)=body.final.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (i : Fin 8) : focused.final.heads (slots i)=0 := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bh]
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_,(localT 4).trans b4,localH 4,
    (localT 5).trans b5,localH 5,(localT 6).trans b6,localH 6,?_⟩
  · intro i hi289
    change focused.final.tapes (i.castAdd 4)=_
    by_cases hi162 : i=162
    · subst i; exact (localT 0).trans (b0.trans b162.symm)
    by_cases hi39 : i=39
    · subst i; exact (localT 2).trans (b2.trans b39.symm)
    by_cases hi89 : i=89
    · subst i; exact (localT 3).trans (b3.trans b89.symm)
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi162 hi289 hi39 hi89]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · intro i
    change focused.final.heads (i.castAdd 4)=_
    by_cases hi162 : i=162
    · subst i
      change focused.final.heads (slots 0)=0
      exact localH 0
    simp only [hi162,ite_false]
    by_cases hi289 : i=289
    · subst i; exact (localH 1).trans h289.symm
    by_cases hi39 : i=39
    · subst i; exact (localH 2).trans h39.symm
    by_cases hi89 : i=89
    · subst i; exact (localH 3).trans h89.symm
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi162 hi289 hi39 hi89]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps ≤ budget r
    rw [hfs]
    change base.steps+1+body.steps ≤ budget r
    unfold budget
    omega

theorem raw_run (r : Request) :
    ∃ base : ExecutionReceipt 302 _,∃ actual,
      run MatrixBatchBucketEndpoints.machine (MatrixBatchBucketEndpoints.budget r) (MatrixBatchBucketEndpoints.input r)=some base ∧
      run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 302,i≠289 → actual.final.tapes (i.castAdd 4)=base.final.tapes i) ∧
      (∀ i : Fin 302,actual.final.heads (i.castAdd 4)=if i=162 then 0 else base.final.heads i) ∧
      actual.final.tapes 162=MatrixBatchGateNativeLoop.output r ∧ actual.final.heads 162=0 ∧
      actual.final.tapes 39=UnaryTemplate.tape r.U ∧ actual.final.heads 39=0 ∧
      actual.final.tapes 89=UnaryTemplate.tape r.Gates ∧ actual.final.heads 89=0 ∧
      actual.final.tapes 302=List.replicate (H r) true ∧ actual.final.heads 302=0 ∧
      actual.final.tapes 303=List.replicate (H r) true ∧ actual.final.heads 303=0 ∧
      actual.final.tapes 304=UnaryTemplate.tape (H r) ∧ actual.final.heads 304=0 ∧
      actual.steps ≤ budget r := by
  obtain ⟨base,hb,b162,h162,b289,h289,b39,h39,b89,h89,bs⟩ := MatrixBatchRankReverseFields.source_fields r
  obtain ⟨actual,ha,atapes,ah,a302,h302,a303,h303,a304,h304,as⟩ :=
    reverse_run r base hb b162 h162 b289 h289 b39 h39 b89 h89 bs
  refine ⟨base,actual,hb,ha,atapes,ah,(atapes 162 (by decide)).trans b162,?_,
    (atapes 39 (by decide)).trans b39,?_,(atapes 89 (by decide)).trans b89,?_,a302,h302,a303,h303,a304,h304,as⟩
  · simpa using ah 162
  · exact (ah 39).trans (by simpa using h39)
  · exact (ah 89).trans (by simpa using h89)

end NearCubicWires.RepairOrdinary.MatrixBatchRankReverse
