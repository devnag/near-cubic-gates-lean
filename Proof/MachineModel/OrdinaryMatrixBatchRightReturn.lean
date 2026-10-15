import Proof.MachineModel.OrdinaryMatrixBatchLeftRetained

/-! The actual original-request left producer enters its right-plane phase
by rewinding the retained rank stream, preserving all tape contents. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRightReturn
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 344 := ![162,304,39,89]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def last := RecoveryFocus.machine slots MatrixRightRankReturn.machine
noncomputable def machine := Composition.machine MatrixBatchLeftPlane.machine last
def input := MatrixBatchLeftPlane.input
noncomputable def budget (r : Request) := MatrixBatchLeftPlane.budget r+1+MatrixRightRankReturn.budget r

theorem return_run (r : Request) (base : ExecutionReceipt 344 _)
    (hb : run MatrixBatchLeftPlane.machine (MatrixBatchLeftPlane.budget r) (input r)=some base)
    (bt : ∀ j,base.final.tapes (slots j)=MatrixRightRankReturn.tapes r j)
    (bh : ∀ j,base.final.heads (slots j)=MatrixRightRankReturn.heads r j)
    (bs : base.steps≤MatrixBatchLeftPlane.budget r) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧ actual.final.tapes=base.final.tapes ∧
    (∀ j,actual.final.heads (slots j)=0) ∧
    (∀ i,(∀ j,slots j≠i) → actual.final.heads i=base.final.heads i) ∧ actual.steps≤budget r := by
  obtain ⟨body,hr,rt,rh,rs⟩ := MatrixRightRankReturn.return_run r
  let entry := MatrixRightRankReturn.input r
  have hi : RecoveryFocus.config slots base.final.heads base.final.tapes entry=
      Composition.restart base.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · exact bh
    · exact bt
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config
    (s := 2+(2+(MatrixRankStreamReverse.loopStates+2))) slots slots_injective MatrixRightRankReturn.machine
    base.final.heads base.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join MatrixBatchLeftPlane.machine last _ _ _ base focused hb hf
  have localH (j : Fin 4) : focused.final.heads (slots j)=0 := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact rh j
  refine ⟨Composition.joinedReceipt base focused,hj,?_,localH,?_,?_⟩
  · change focused.final.tapes=base.final.tapes
    rw [ff]
    funext i
    cases hx : RecoveryFocus.pick slots i with
    | none => simp only [RecoveryFocus.config,hx]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hx
      simp only [RecoveryFocus.config,hx,rt]
      rw [← hj]
      exact (bt j).symm
  · intro i hi
    change focused.final.heads i=base.final.heads i
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hi]
  · change base.steps+1+focused.steps≤budget r
    rw [fs]
    unfold budget
    omega

theorem raw_run (r : Request) : ∃ unused : Fin 3 → List Bool,∃ store : MatrixBucketGateLoop.Store r,
    ∃ base : ExecutionReceipt 344 _,∃ actual,
    run MatrixBatchLeftPlane.machine (MatrixBatchLeftPlane.budget r) (input r)=some base ∧
    run machine (budget r) (input r)=some actual ∧ actual.final.tapes=base.final.tapes ∧
    actual.final.tapes 342=MatrixBucketLeftPlane.plane r ∧ actual.final.heads 342=0 ∧
    (∀ j : Fin 36,j≠8 → actual.final.tapes (MatrixBatchLeftRetained.nativeSlot j)=
      (MatrixBucketGateFinish.final r unused store).tapes j) ∧
    (∀ j,actual.final.heads (slots j)=0) ∧
    (∀ i,(∀ j,slots j≠i) → actual.final.heads i=base.final.heads i) ∧ actual.steps≤budget r := by
  obtain ⟨unused,store,base,hb,outT,outH,nt,nh,h304,hh304,u39,hu39,bs⟩ := MatrixBatchLeftRetained.retained_run r
  have bt : ∀ j,base.final.tapes (slots j)=MatrixRightRankReturn.tapes r j := by
    intro j
    fin_cases j
    · apply (nt 34 (by decide)).trans
      simp [MatrixBucketGateFinish.final,MatrixBucketGateFinish.before,MatrixBucketGateNativeLoop.cfg_tapes,
        MatrixBucketGatePrepare.data,MatrixBucketGatePrepare.extra,Fin.addCases,MatrixRightRankReturn.tapes]
    · exact h304
    · exact u39
    · apply (nt 35 (by decide)).trans
      simp [MatrixBucketGateFinish.final,MatrixBucketGateFinish.before,MatrixBucketGateNativeLoop.cfg_tapes,
        Fin.addCases,MatrixRightRankReturn.tapes]
  have bh : ∀ j,base.final.heads (slots j)=MatrixRightRankReturn.heads r j := by
    intro j
    fin_cases j
    · exact (nh 34 (by decide)).trans (by rfl)
    · exact hh304
    · exact hu39
    · exact (nh 35 (by decide)).trans (by rfl)
  obtain ⟨actual,ha,atapes,ah,old,steps⟩ := return_run r base hb bt bh bs
  refine ⟨unused,store,base,actual,hb,ha,atapes,(congrFun atapes 342).trans outT,
    (old 342 (by decide)).trans outH,?_,ah,old,steps⟩
  intro j hj
  exact (congrFun atapes _).trans (nt j hj)

end NearCubicWires.RepairOrdinary.MatrixBatchRightReturn
