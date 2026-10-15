import Proof.MachineModel.OrdinaryMatrixBucketGateFinish

/-! Whole cold bucket pass: write the mask/cursor offsets, execute all
ordered gates, append the aggregate terminator, then rewind only the key
output once using the physically recorded whole-pass log. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketGatePass
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def traversal := Composition.machine MatrixBucketGateBootstrap.machine MatrixBucketGateLoop.machine
noncomputable def forward := Composition.machine traversal MatrixBucketGateFinish.machine
def selected (i : Fin 36) : Bool := decide (i=8)
noncomputable def machine := MaskedReset.machine forward selected
def forwardBudget (r : Request) := (1+1+MatrixBucketGateNativeLoop.budget r)+1+1
def budget (r : Request) := 2*forwardBudget r+2
noncomputable def input (r : Request) (unused : Fin 3 → List Bool) :=
  Fin.addCases (m := 36) (n := 1) (motive := fun _ => List Bool)
    (MatrixBucketGateBootstrap.input r unused) (fun _ => [])

theorem traversal_run (r : Request) (unused : Fin 3 → List Bool) :
    ∃ store : MatrixBucketGateLoop.Store r,∃ actual,
      run traversal (1+1+MatrixBucketGateNativeLoop.budget r) (MatrixBucketGateBootstrap.input r unused)=some actual ∧
      actual.final=Composition.rightConfig 2 (MatrixBucketGateFinish.before r unused store) ∧
      actual.steps≤1+1+MatrixBucketGateNativeLoop.budget r := by
  obtain ⟨boot,hb,bh,bt,bs⟩ := MatrixBucketGateBootstrap.boot_run r unused
  obtain ⟨store,loop,hl,lf,ls⟩ := MatrixBucketGateNativeLoop.all_run r (MatrixBucketGateNativeLoop.cold r) [] unused
  simp only [List.nil_append] at lf
  have hi : Composition.restart boot.final MatrixBucketGateLoop.machine.start=MatrixBucketGateBootstrap.target r unused := by
    apply configuration_ext
    · rfl
    · exact bh
    · exact bt
  change runFrom MatrixBucketGateLoop.machine (MatrixBucketGateNativeLoop.budget r)
    (MatrixBucketGateBootstrap.target r unused)=some loop at hl
  rw [←hi] at hl
  have joined := Composition.run_join MatrixBucketGateBootstrap.machine MatrixBucketGateLoop.machine _ _ _ boot loop hb hl
  refine ⟨store,Composition.joinedReceipt boot loop,joined,?_,?_⟩
  · change Composition.rightConfig 2 loop.final=_
    rw [lf]
    rfl
  · change boot.steps+1+loop.steps≤_
    omega

theorem forward_run (r : Request) (unused : Fin 3 → List Bool) :
    ∃ store : MatrixBucketGateLoop.Store r,∃ actual,
      run forward (forwardBudget r) (MatrixBucketGateBootstrap.input r unused)=some actual ∧
      actual.final.heads=(MatrixBucketGateFinish.final r unused store).heads ∧
      actual.final.tapes=(MatrixBucketGateFinish.final r unused store).tapes ∧
      actual.steps≤forwardBudget r := by
  obtain ⟨store,base,hb,bf,bs⟩ := traversal_run r unused
  obtain ⟨last,hl,lf,ls⟩ := MatrixBucketGateFinish.finish_run r unused store
  have hi : Composition.restart base.final MatrixBucketGateFinish.machine.start=
      Composition.restart (MatrixBucketGateFinish.before r unused store) MatrixBucketGateFinish.machine.start := by
    rw [bf]
    rfl
  rw [←hi] at hl
  have joined := Composition.run_join traversal MatrixBucketGateFinish.machine _ _ _ base last hb hl
  refine ⟨store,Composition.joinedReceipt base last,joined,?_,?_,?_⟩
  · change last.final.heads=_
    rw [lf]
  · change last.final.tapes=_
    rw [lf]
  · change base.steps+1+last.steps≤forwardBudget r
    unfold forwardBudget
    omega

theorem pass_run (r : Request) (unused : Fin 3 → List Bool) :
    ∃ store : MatrixBucketGateLoop.Store r,∃ actual,
      run machine (budget r) (input r unused)=some actual ∧
      (∀ i : Fin 36,actual.final.heads (i.castAdd 1)=
        if i=8 then 0 else (MatrixBucketGateFinish.final r unused store).heads i) ∧
      (∀ i : Fin 36,actual.final.tapes (i.castAdd 1)=(MatrixBucketGateFinish.final r unused store).tapes i) ∧
      actual.final.heads 36=0 ∧ (∃ n,actual.final.tapes 36=List.replicate n false ∧ n≤forwardBudget r) ∧
      actual.steps≤budget r := by
  obtain ⟨store,base,hb,bh,bt,bs⟩ := forward_run r unused
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i _
    obtain ⟨hp,_⟩ := prefix_of_run forward (forwardBudget r)
      (initialConfiguration forward (MatrixBucketGateBootstrap.input r unused)) base hb
    have h := SelectiveReset.prefix_head hp i
    simpa only [initialConfiguration,Nat.zero_add] using h
  obtain ⟨actual,ha,hf,hs,_⟩ := MaskedReset.reset_run forward selected _ _ base hb hh
  have hsmall : 2*base.steps+2≤budget r := by unfold budget; omega
  have he := runFrom_moreFuel machine _ (budget r-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hsmall] at he
  have hin : Rewind.recording (initialConfiguration forward (MatrixBucketGateBootstrap.input r unused)) 0=
      initialConfiguration machine (input r unused) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hin] at he
  refine ⟨store,actual,he,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hf,bh]
    simp [SelectiveReset.finished,Rewind.config,Fin.addCases_left,selected]
  · intro i
    rw [hf,bt]
    simp [SelectiveReset.finished,Rewind.config,Fin.addCases_left]
  · rw [hf]
    rfl
  · refine ⟨base.steps,?_,bs⟩
    rw [hf]
    rfl
  · omega

end NearCubicWires.RepairOrdinary.MatrixBucketGatePass
