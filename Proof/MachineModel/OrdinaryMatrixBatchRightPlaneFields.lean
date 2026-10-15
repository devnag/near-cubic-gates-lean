import Proof.MachineModel.OrdinaryMatrixRightPlaneBank

/-! Every right-plane field comes from the same original-request execution:
ranked output, retained zero bank, native words and U/Used/padding templates.
Four fresh blank tapes are precisely the output and rewind tapes. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRightPlaneFields
open LocalBitMultitape
open MatrixScoreBatch (Request)
open MatrixRightPlaneBank (slots native fields)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem classify (i : Fin 24) : i=7 ∨ i=10 ∨ i=12 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ ∃ j,fields j=i := by
  revert i
  decide

theorem source_fields (r : Request) : ∃ base,
    run MatrixBatchRightPadDriver.machine (MatrixBatchRightPadDriver.budget r) (MatrixBatchRightPadDriver.input r)=some base ∧
    (∀ j,(TapeEmbedding.config (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) base.final).tapes (slots j)=
      MatrixRightPlaneNative.input r j) ∧
    (∀ j,(TapeEmbedding.config (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) base.final).heads (slots j)=0) ∧
    base.final.tapes 342=MatrixBucketLeftPlane.plane r ∧ base.final.heads 342=0 ∧
    base.steps≤MatrixBatchRightPadDriver.budget r := by
  obtain ⟨pass,base,hpass,hb,padT,padH,old,bs⟩ := MatrixBatchRightPadDriver.raw_run r
  obtain ⟨unused,store,_,same,_,hs,outT,outH,leftT,leftH,nt,nh,_,_⟩ := MatrixBatchRightPass.raw_run r
  have he : same=pass := Option.some.inj (hs.symm.trans hpass)
  subst same
  obtain ⟨same,hs,dt,dh,_⟩ := MatrixRightDimensions.source_fields r
  have he : same=pass := Option.some.inj (hs.symm.trans hpass)
  subst same
  let actual := TapeEmbedding.config (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) base.final
  have reusedT (j : Fin 16) : actual.tapes (slots (fields j))=MatrixRightPlaneNative.input r (fields j) := by
    rw [MatrixRightPlaneBank.slots_native]
    simp only [actual,TapeEmbedding.config,Fin.addCases_left]
    exact (old _).1.trans ((nt (native j)).trans (MatrixRightPlaneBank.reused_tapes r unused store j))
  have reusedH (j : Fin 16) : actual.heads (slots (fields j))=0 := by
    rw [MatrixRightPlaneBank.slots_native]
    simp only [actual,TapeEmbedding.config,Fin.addCases_left]
    exact (old _).2.trans ((nh (native j)).trans (MatrixRightPlaneBank.reused_heads r unused store j))
  have uT : actual.tapes 39=UnaryTemplate.tape r.U := (old 39).1.trans (dt 2)
  have uH : actual.heads 39=0 := (old 39).2.trans (dh 2)
  have usedT : actual.tapes 285=UnaryTemplate.tape r.Used := (old 285).1.trans (dt 0)
  have usedH : actual.heads 285=0 := (old 285).2.trans (dh 0)
  have sourceT : actual.tapes 344=MatrixBatchRightPass.output r := (old 344).1.trans outT
  have sourceH : actual.heads 344=0 := (old 344).2.trans outH
  refine ⟨base,hb,?_,?_,(old 342).1.trans leftT,(old 342).2.trans leftH,bs⟩
  · intro i
    rcases classify i with h | h | h | h | h | h | h | h | ⟨j,hj⟩
    · subst i; exact sourceT
    · subst i; rfl
    · subst i; rfl
    · subst i; rfl
    · subst i; exact uT
    · subst i; exact usedT
    · subst i; exact padT
    · subst i; rfl
    · rw [←hj]; exact reusedT j
  · intro i
    rcases classify i with h | h | h | h | h | h | h | h | ⟨j,hj⟩
    · subst i; exact sourceH
    · subst i; rfl
    · subst i; rfl
    · subst i; rfl
    · subst i; exact uH
    · subst i; exact usedH
    · subst i; exact padH
    · subst i; rfl
    · rw [←hj]; exact reusedH j

end NearCubicWires.RepairOrdinary.MatrixBatchRightPlaneFields
