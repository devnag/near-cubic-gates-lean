import Proof.MachineModel.OrdinaryMatrixRightRankReturn

/-! The actual left-plane endpoint still contains the executed native
bucket bank and original rank stream, apart from the sorted key output.
These fields are exposed for its right-plane consumer, from the same run. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchLeftRetained
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlot (j : Fin 36) : Fin 344 :=
  ⟨(MatrixBatchBucketPassFields.slots (j.castAdd 1)).val,by omega⟩

theorem retained_run (r : Request) : ∃ unused : Fin 3 → List Bool,∃ store : MatrixBucketGateLoop.Store r,∃ actual,
    run MatrixBatchLeftPlane.machine (MatrixBatchLeftPlane.budget r) (MatrixBatchLeftPlane.input r)=some actual ∧
    actual.final.tapes 342=MatrixBucketLeftPlane.plane r ∧ actual.final.heads 342=0 ∧
    (∀ j : Fin 36,j≠8 → actual.final.tapes (nativeSlot j)=(MatrixBucketGateFinish.final r unused store).tapes j) ∧
    (∀ j : Fin 36,j≠8 → actual.final.heads (nativeSlot j)=(MatrixBucketGateFinish.final r unused store).heads j) ∧
    actual.final.tapes 304=UnaryTemplate.tape (H r) ∧ actual.final.heads 304=0 ∧
    actual.final.tapes 39=UnaryTemplate.tape r.U ∧ actual.final.heads 39=0 ∧
    actual.steps≤MatrixBatchLeftPlane.budget r := by
  obtain ⟨sorted,actual,hs,ha,outputT,outputH,leftOld,steps⟩ := MatrixBatchLeftPlane.raw_run r
  obtain ⟨pre,same,hpre,hss,_,_,_,sortOld,_⟩ := MatrixBatchCoordinateSort.raw_run r
  have he : same=sorted := Option.some.inj (hss.symm.trans hs)
  subst same
  obtain ⟨unused,store,bank,same,hbank,hpp,_,_,nativeT,nativeH,preOld,_⟩ := MatrixBatchBucketPass.raw_run r
  have he : same=pre := Option.some.inj (hpp.symm.trans hpre)
  subst same
  obtain ⟨reversed,_,same,hr,hb,bankT,bankH,_,_,_,_,_⟩ := MatrixBatchBucketBank.raw_run r
  have he : same=bank := Option.some.inj (hb.symm.trans hbank)
  subst same
  obtain ⟨_,same,_,hrr,_,_,_,_,_,_,_,_,_,_,_,_,r304,h304,_⟩ := MatrixBatchRankReverse.raw_run r
  have he : same=reversed := Option.some.inj (hrr.symm.trans hr)
  subst same
  obtain ⟨same,hss,_,_,_,_,_,_,u39,h39,_⟩ := MatrixBatchLeftFields.source_fields r
  have he : same=sorted := Option.some.inj (hss.symm.trans hs)
  subst same
  have old (i : Fin 336) (hi : i≠314) : actual.final.tapes (i.castAdd 8)=pre.final.tapes i ∧
      actual.final.heads (i.castAdd 8)=pre.final.heads i :=
    ⟨(leftOld (i.castAdd 6)).1.trans (sortOld i hi).1,(leftOld (i.castAdd 6)).2.trans (sortOld i hi).2⟩
  have keep304 := preOld 304 (by decide)
  refine ⟨unused,store,actual,ha,outputT,outputH,?_,?_,?_,?_,
    (leftOld 39).1.trans u39,(leftOld 39).2.trans h39,steps⟩
  · intro j hj
    have hk : MatrixBatchBucketPassFields.slots (j.castAdd 1)≠314 := by
      fin_cases j <;> first | exact (hj rfl).elim | decide
    exact (old _ hk).1.trans (nativeT j)
  · intro j hj
    have hk : MatrixBatchBucketPassFields.slots (j.castAdd 1)≠314 := by
      fin_cases j <;> first | exact (hj rfl).elim | decide
    have h := nativeH j
    simp only [hj,ite_false] at h
    exact (old _ hk).2.trans h
  · exact (old 304 (by decide)).1.trans (keep304.1.trans ((bankT 304).trans r304))
  · exact (old 304 (by decide)).2.trans (keep304.2.trans ((bankH 304).trans h304))

end NearCubicWires.RepairOrdinary.MatrixBatchLeftRetained
