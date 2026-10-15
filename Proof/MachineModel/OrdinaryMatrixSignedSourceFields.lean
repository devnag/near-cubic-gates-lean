import Proof.MachineModel.OrdinaryMatrixPlaneRetainedDimensions

/-! The eleven literal scheduler fields come from the same complete
original-request computation. The signed-plane caller can now select these
tapes and pay its head bootstrap without assuming precomputed values. -/
namespace NearCubicWires.RepairOrdinary.MatrixSignedSourceFields
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 11 → Fin 396 := ![12,22,32,33,200,256,321,259,66,376,394]
noncomputable def values (r : Request) : Fin 11 → List Bool :=
  ![UnaryTemplate.tape r.d,UnaryTemplate.tape r.p,UnaryTemplate.tape r.Gates,
    MatrixCoefficientLoop.output r.p r.cuts,UnaryTemplate.tape r.Capacity,UnaryTemplate.tape r.Buckets,
    UnaryTemplate.tape (r.Capacity-r.Used),List.replicate r.M true,frame (SignedSortKey.binary r.M r.U),
    MatrixBucketLeftPlane.plane r,MatrixRightPlaneNative.plane r]

theorem source_fields (r : Request) : ∃ actual,
    run MatrixBatchCoefficientPlanes.machine (MatrixBatchCoefficientPlanes.budget r) (MatrixBatchCoefficientPlanes.input r)=some actual ∧
    (∀ j,actual.final.tapes (slots j)=values r j) ∧
    (∀ j,actual.final.heads (slots j)=0) ∧ actual.steps≤MatrixBatchCoefficientPlanes.budget r := by
  obtain ⟨cold,body,actual,hcold,hbody,ha,native,leftT,leftH,rightT,rightH,bankT,bankH,old,steps⟩ :=
    MatrixCoefficientPlaneFields.retained_run r
  obtain ⟨same,hs,_,_,dT,pT,gT,_,_⟩ := MatrixCoefficientRetainedCold.cold_fields r
  have he : same=cold := Option.some.inj (hs.symm.trans hcold)
  subst same
  obtain ⟨same,hs,dt,dh,bT,bH⟩ := MatrixPlaneRetainedDimensions.plane_fields r
  have he : same=body := Option.some.inj (hs.symm.trans hbody)
  subst same
  refine ⟨actual,ha,?_,?_,steps⟩
  · intro j; fin_cases j
    · exact (old 12 (by decide)).1.trans dT
    · exact (old 22 (by decide)).1.trans pT
    · exact (old 32 (by decide)).1.trans gT
    · exact bankT
    · exact (native 166).1.trans (dt 0)
    · exact (native 222).1.trans bT
    · exact (native 287).1.trans (dt 3)
    · exact (native 225).1.trans (dt 1)
    · exact (native 32).1.trans (dt 2)
    · exact leftT
    · exact rightT
  · intro j; fin_cases j
    · exact (old 12 (by decide)).2
    · exact (old 22 (by decide)).2
    · exact (old 32 (by decide)).2
    · exact bankH
    · exact (native 166).2.trans (dh 0)
    · exact (native 222).2.trans bH
    · exact (native 287).2.trans (dh 3)
    · exact (native 225).2.trans (dh 1)
    · exact (native 32).2.trans (dh 2)
    · exact leftH
    · exact rightH

end NearCubicWires.RepairOrdinary.MatrixSignedSourceFields
