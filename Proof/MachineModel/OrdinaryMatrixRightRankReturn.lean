import Proof.MachineModel.OrdinaryMatrixBatchLeftPlaneBounds

/-! The existing rank rewind consumes retained H/U/Gates templates.
After the left-bucket pass the Gates head is one; this real entry first
retreats it and then restores the entire ranked packet stream. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightRankReturn
open LocalBitMultitape RecoveryExecution MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (r : Request) : Fin 4 → List Bool :=
  ![MatrixBatchGateNativeLoop.output r,UnaryTemplate.tape (H r),UnaryTemplate.tape r.U,UnaryTemplate.tape r.Gates]
noncomputable def heads (r : Request) : Fin 4 → ℕ := ![(MatrixBatchGateNativeLoop.output r).length,0,0,1]
def boot : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,![.stay,.stay,.stay,.left]⟩
noncomputable def machine := Composition.machine boot MatrixRankStreamReverse.machine
def budget (r : Request) := 1+1+MatrixRankStreamReverse.budget (H r) r.U r.Gates
noncomputable def input (r : Request) := Composition.leftConfig (2+(MatrixRankStreamReverse.loopStates+2))
  (⟨boot.start,heads r,tapes r⟩ : Configuration 4 2)

theorem return_run (r : Request) : ∃ actual,
    runFrom machine (budget r) (input r)=some actual ∧
    actual.final.tapes=tapes r ∧ (∀ i,actual.final.heads i=0) ∧ actual.steps≤budget r := by
  let final : Configuration 4 2 := ⟨1,![(MatrixBatchGateNativeLoop.output r).length,0,0,0],tapes r⟩
  have hs : step boot ⟨boot.start,heads r,tapes r⟩=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨prepared,hp,pf,ps⟩ := (Timed.single (by rfl) hs).run (by rfl)
  obtain ⟨body,hb,bs,bh,bt⟩ := MatrixRankStreamReverse.reverse_run (MatrixBatchGateNativeLoop.output r)
    (H r) r.U r.Gates (MatrixBatchGateNativeLoop.output r).length
  have hi : Composition.restart prepared.final MatrixRankStreamReverse.machine.start=
      MatrixRankStreamReverse.cfg (MatrixBatchGateNativeLoop.output r) (H r) r.U r.Gates
        (MatrixBatchGateNativeLoop.output r).length := by
    rw [pf]
    rfl
  have hn : runFrom MatrixRankStreamReverse.machine (MatrixRankStreamReverse.budget (H r) r.U r.Gates)
      (Composition.restart prepared.final MatrixRankStreamReverse.machine.start)=some body := by
    rw [hi]
    exact hb
  have hj := Composition.run_join boot MatrixRankStreamReverse.machine 1 _ _ prepared body hp hn
  refine ⟨Composition.joinedReceipt prepared body,hj,bt,?_,?_⟩
  · intro i
    change body.final.heads i=0
    rw [bh,MatrixBatchRankReverseFields.output_length,Nat.sub_self]
    fin_cases i <;> rfl
  · change prepared.steps+1+body.steps≤budget r
    rw [ps]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixRightRankReturn
