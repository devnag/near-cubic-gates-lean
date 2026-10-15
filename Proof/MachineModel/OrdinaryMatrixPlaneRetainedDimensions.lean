import Proof.MachineModel.OrdinaryMatrixPlaneDimensions

/-! The original-request right producer retains the exact dimension fields
needed by the signed-plane scheduler. Both matrices remain the same actual
ones, and no dimension is installed from its mathematical value. -/
namespace NearCubicWires.RepairOrdinary.MatrixPlaneRetainedDimensions
open LocalBitMultitape MatrixScoreBatch
open MatrixPlaneDimensions (slots values)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem right_fields (r : Request) : ∃ actual,
    run MatrixBatchRightPass.machine (MatrixBatchRightPass.budget r) (MatrixBatchRightPass.input r)=some actual ∧
    (∀ j,actual.final.tapes ((slots j).castAdd 59)=values r j) ∧
    (∀ j,actual.final.heads ((slots j).castAdd 59)=0) ∧
    actual.final.tapes 222=UnaryTemplate.tape r.Buckets ∧ actual.final.heads 222=0 := by
  obtain ⟨unused,store,bank,actual,hbank,ha,_,_,_,_,nt,nh,passOld,_⟩ := MatrixBatchRightPass.raw_run r
  obtain ⟨ret,same,hret,hs,_,_,bankT,bankH,_⟩ := MatrixBatchRightBank.raw_run r
  have he : same=bank := Option.some.inj (hs.symm.trans hbank)
  subst same
  obtain ⟨_,_,left,same,hleft,hs,retT,_,_,_,_,retOld,_⟩ := MatrixBatchRightReturn.raw_run r
  have he : same=ret := Option.some.inj (hs.symm.trans hret)
  subst same
  obtain ⟨sorted,same,hsort,hs,_,_,leftOld,_⟩ := MatrixBatchLeftPlane.raw_run r
  have he : same=left := Option.some.inj (hs.symm.trans hleft)
  subst same
  obtain ⟨same,hs,dt,dh⟩ := MatrixPlaneDimensions.coordinate_fields r
  have he : same=sorted := Option.some.inj (hs.symm.trans hsort)
  subst same
  have retained (j : Fin 4) : actual.final.tapes ((slots j).castAdd 59)=values r j ∧
      actual.final.heads ((slots j).castAdd 59)=0 := by
    obtain ⟨pT,pH⟩ := passOld ((slots j).castAdd 58) (by fin_cases j <;> decide)
    have bT := bankT ((slots j).castAdd 55) (by fin_cases j <;> decide)
    have bH := bankH ((slots j).castAdd 55)
    have l := leftOld ((slots j).castAdd 53)
    have rh := retOld ((slots j).castAdd 55) (by fin_cases j <;> decide)
    exact ⟨pT.trans (bT.trans ((congrFun retT _).trans (l.1.trans (dt j)))),
      pH.trans (bH.trans (rh.trans (l.2.trans (dh j))))⟩
  refine ⟨actual,ha,fun j => (retained j).1,fun j => (retained j).2,?_,?_⟩
  · change actual.final.tapes (MatrixBatchRightPassFields.slots ((27 : Fin 38).castAdd 1))=_
    rw [nt]
    simp [MatrixRightGateFinish.final,MatrixRightGateFinish.before,MatrixRightGateNativeLoop.cfg_tapes,
      MatrixRightGateLayout.data,MatrixRightGateLoop.state,MatrixBucketGatePrepare.data,MatrixBucketGatePrepare.extra,Fin.addCases]
  · exact nh 27

theorem plane_fields (r : Request) : ∃ actual,
    run MatrixBatchRightPlane.machine (MatrixBatchRightPlane.budget r) (MatrixBatchRightPlane.input r)=some actual ∧
    (∀ j,actual.final.tapes ((slots j).castAdd 73)=values r j) ∧
    (∀ j,actual.final.heads ((slots j).castAdd 73)=0) ∧
    actual.final.tapes 222=UnaryTemplate.tape r.Buckets ∧ actual.final.heads 222=0 := by
  obtain ⟨pad,actual,hpad,ha,_,_,_,_,_,old,_⟩ := MatrixBatchRightPlane.raw_run r
  obtain ⟨pass,same,hpass,hs,_,_,padOld,_⟩ := MatrixBatchRightPadDriver.raw_run r
  have he : same=pad := Option.some.inj (hs.symm.trans hpad)
  subst same
  obtain ⟨same,hs,dt,dh,bt,bh⟩ := right_fields r
  have he : same=pass := Option.some.inj (hs.symm.trans hpass)
  subst same
  have retained (j : Fin 4) : actual.final.tapes ((slots j).castAdd 73)=values r j ∧
      actual.final.heads ((slots j).castAdd 73)=0 := by
    have h := old ((slots j).castAdd 69) (by fin_cases j <;> decide)
    have hp := padOld ((slots j).castAdd 59)
    exact ⟨h.1.trans (hp.1.trans (dt j)),h.2.trans (hp.2.trans (dh j))⟩
  have bucket := old 222 (by decide)
  exact ⟨actual,ha,fun j => (retained j).1,fun j => (retained j).2,
    bucket.1.trans ((padOld 222).1.trans bt),bucket.2.trans ((padOld 222).2.trans bh)⟩

end NearCubicWires.RepairOrdinary.MatrixPlaneRetainedDimensions
