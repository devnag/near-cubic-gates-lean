import Proof.MachineModel.OrdinaryMatrixRightGateFinish

/-! The whole right pass advances the actual Gates cursor, executes all
ordered gates, appends the aggregate terminator, then rewinds only the key
output once using the physically recorded whole-pass log. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGatePass
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def traversal := Composition.machine MatrixRightGateBootstrap.machine MatrixRightGateLoop.machine
noncomputable def forward := Composition.machine traversal MatrixRightGateFinish.machine
def selected (i : Fin 38) : Bool := decide (i=8)
noncomputable def machine := MaskedReset.machine forward selected
def forwardBudget (r : Request) := (1+1+MatrixRightGateNativeLoop.budget r)+1+1
def budget (r : Request) := 2*forwardBudget r+2
noncomputable def input (r : Request) (unused : Fin 3 → List Bool) (s : MatrixBucketGateLoop.Store r) :=
  Rewind.recording (MatrixRightGateBootstrap.input forward.start r unused s) 0

theorem traversal_run (r : Request) (unused : Fin 3 → List Bool) (s : MatrixBucketGateLoop.Store r) :
    ∃ store : MatrixBucketGateLoop.Store r,∃ actual,
      runFrom traversal (1+1+MatrixRightGateNativeLoop.budget r) (MatrixRightGateBootstrap.input traversal.start r unused s)=some actual ∧
      actual.final=Composition.rightConfig 2 (MatrixRightGateFinish.before r unused store) ∧
      actual.steps≤1+1+MatrixRightGateNativeLoop.budget r := by
  obtain ⟨boot,hb,bh,bt,bs⟩ := MatrixRightGateBootstrap.boot_run r unused s
  obtain ⟨store,loop,hl,lf,ls⟩ := MatrixRightGateNativeLoop.all_run r s [] unused
  simp only [List.nil_append] at lf
  have hi : Composition.restart boot.final MatrixRightGateLoop.machine.start=MatrixRightGateBootstrap.target r unused s := by
    apply configuration_ext
    · rfl
    · exact bh
    · exact bt
  change runFrom MatrixRightGateLoop.machine (MatrixRightGateNativeLoop.budget r)
    (MatrixRightGateBootstrap.target r unused s)=some loop at hl
  rw [←hi] at hl
  have joined := Composition.run_join MatrixRightGateBootstrap.machine MatrixRightGateLoop.machine _ _ _ boot loop hb hl
  refine ⟨store,Composition.joinedReceipt boot loop,joined,?_,?_⟩
  · change Composition.rightConfig 2 loop.final=_
    rw [lf]
    rfl
  · change boot.steps+1+loop.steps≤_
    omega

theorem forward_run (r : Request) (unused : Fin 3 → List Bool) (s : MatrixBucketGateLoop.Store r) :
    ∃ store : MatrixBucketGateLoop.Store r,∃ actual,
      runFrom forward (forwardBudget r) (MatrixRightGateBootstrap.input forward.start r unused s)=some actual ∧
      actual.final.heads=(MatrixRightGateFinish.final r unused store).heads ∧
      actual.final.tapes=(MatrixRightGateFinish.final r unused store).tapes ∧
      actual.steps≤forwardBudget r := by
  obtain ⟨store,base,hb,bf,bs⟩ := traversal_run r unused s
  obtain ⟨last,hl,lf,ls⟩ := MatrixRightGateFinish.finish_run r unused store
  have hi : Composition.restart base.final MatrixRightGateFinish.machine.start=
      Composition.restart (MatrixRightGateFinish.before r unused store) MatrixRightGateFinish.machine.start := by
    rw [bf]
    rfl
  rw [←hi] at hl
  have joined := Composition.run_join traversal MatrixRightGateFinish.machine _ _ _ base last hb hl
  refine ⟨store,Composition.joinedReceipt base last,joined,?_,?_,?_⟩
  · change last.final.heads=_
    rw [lf]
  · change last.final.tapes=_
    rw [lf]
  · change base.steps+1+last.steps≤forwardBudget r
    unfold forwardBudget
    omega

theorem pass_run (r : Request) (unused : Fin 3 → List Bool) (s : MatrixBucketGateLoop.Store r) :
    ∃ store : MatrixBucketGateLoop.Store r,∃ actual,
      runFrom machine (budget r) (input r unused s)=some actual ∧
      (∀ i : Fin 38,actual.final.heads (i.castAdd 1)=
        if i=8 then 0 else (MatrixRightGateFinish.final r unused store).heads i) ∧
      (∀ i : Fin 38,actual.final.tapes (i.castAdd 1)=(MatrixRightGateFinish.final r unused store).tapes i) ∧
      actual.final.heads 38=0 ∧ (∃ n,actual.final.tapes 38=List.replicate n false ∧ n≤forwardBudget r) ∧
      actual.steps≤budget r := by
  obtain ⟨store,base,hb,bh,bt,bs⟩ := forward_run r unused s
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have hi8 : i=8 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    obtain ⟨hp,_⟩ := prefix_of_run forward (forwardBudget r)
      (MatrixRightGateBootstrap.input forward.start r unused s) base hb
    have h := SelectiveReset.prefix_head hp 8
    have hz : (MatrixRightGateBootstrap.input forward.start r unused s).heads 8=0 := by
      simp [MatrixRightGateBootstrap.input,MatrixRightGateBootstrap.target,MatrixRightGateNativeLoop.cfg_heads]
      rfl
    rw [hz,Nat.zero_add] at h
    exact h
  obtain ⟨actual,ha,hf,hs,_⟩ := MaskedReset.reset_run forward selected _ _ base hb hh
  have hsmall : 2*base.steps+2≤budget r := by unfold budget; omega
  have he := runFrom_moreFuel machine _ (budget r-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hsmall] at he
  change runFrom machine (budget r) (input r unused s)=some actual at he
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

end NearCubicWires.RepairOrdinary.MatrixRightGatePass
