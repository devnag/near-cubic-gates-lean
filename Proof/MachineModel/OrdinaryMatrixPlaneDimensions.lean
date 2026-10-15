import Proof.MachineModel.OrdinaryMatrixCoefficientPlaneFields

/-! Physical dimensions retained through the actual coordinate producer.
These are projections of its original request execution, with deterministic
receipt equality connecting the earlier paid canonical dimensions. -/
namespace NearCubicWires.RepairOrdinary.MatrixPlaneDimensions
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 289 := ![166,225,32,287]
def values (r : Request) : Fin 4 → List Bool :=
  ![UnaryTemplate.tape r.Capacity,List.replicate r.M true,
    frame (SignedSortKey.binary r.M r.U),UnaryTemplate.tape (r.Capacity-r.Used)]

theorem usage_fields (r : Request) : ∃ actual,
    run MatrixBatchBucketUsage.machine (MatrixBatchBucketUsage.budget r) (MatrixBatchBucketUsage.input r)=some actual ∧
    (∀ j,actual.final.tapes (slots j)=values r j) ∧
    (∀ j,actual.final.heads (slots j)=0) := by
  obtain ⟨native,hn,n89,h89,n222,h222,n166,h166,ns⟩ := MatrixBatchBucketUsage.source_fields r
  obtain ⟨actual,ha,atapes,ah,_,_,padT,padH,_⟩ := MatrixBatchBucketUsage.usage_run r native hn
    n89 h89 n222 h222 n166 h166 ns
  obtain ⟨same,hs,mT,mH,_,_⟩ := MatrixBatchBucketEndpoints.new_fields r
  have he : same=actual := Option.some.inj (hs.symm.trans ha)
  subst same
  obtain ⟨state,ranked,same,_,rt,rh,hs,ut,uh,_,_,_,_,_,_,_,_,_,_,_⟩ := MatrixBatchRetainedFields.retained_run r
  have he : same=actual := Option.some.inj (hs.symm.trans ha)
  subst same
  have uT : actual.final.tapes 32=frame (SignedSortKey.binary r.M r.U) :=
    (ut 32).trans ((rt 23).trans (MatrixBatchNativeWidth.native_u r state))
  have uH : actual.final.heads 32=0 := (uh 32).trans (by exact rh 23)
  refine ⟨actual,ha,?_,?_⟩
  · intro j; fin_cases j
    · exact (atapes 166).trans n166
    · exact mT
    · exact uT
    · exact padT
  · intro j; fin_cases j
    · exact (ah 166).trans h166
    · exact mH
    · exact uH
    · exact padH

theorem coordinate_fields (r : Request) : ∃ actual,
    run MatrixBatchCoordinateSort.machine (MatrixBatchCoordinateSort.budget r) (MatrixBatchCoordinateSort.input r)=some actual ∧
    (∀ j,actual.final.tapes ((slots j).castAdd 53)=values r j) ∧
    (∀ j,actual.final.heads ((slots j).castAdd 53)=0) := by
  obtain ⟨pre,actual,hpre,ha,_,_,_,old,_⟩ := MatrixBatchCoordinateSort.raw_run r
  obtain ⟨_,_,bank,same,hbank,hsame,_,_,_,_,preOld,_⟩ := MatrixBatchBucketPass.raw_run r
  have he : same=pre := Option.some.inj (hsame.symm.trans hpre)
  subst same
  obtain ⟨reversed,_,same,hr,hb,bankT,bankH,_,_,_,_,_⟩ := MatrixBatchBucketBank.raw_run r
  have he : same=bank := Option.some.inj (hb.symm.trans hbank)
  subst same
  obtain ⟨endpoints,same,hep,hrr,revT,revH,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := MatrixBatchRankReverse.raw_run r
  have he : same=reversed := Option.some.inj (hrr.symm.trans hr)
  subst same
  obtain ⟨usage,same,hu,hepp,epT,epH,_,_,_,_,_,_,_,_,_⟩ := MatrixBatchBucketEndpoints.raw_run r
  have he : same=endpoints := Option.some.inj (hepp.symm.trans hep)
  subst same
  obtain ⟨same,hs,vt,vh⟩ := usage_fields r
  have he : same=usage := Option.some.inj (hs.symm.trans hu)
  subst same
  have retained (j : Fin 4) : actual.final.tapes ((slots j).castAdd 53)=usage.final.tapes (slots j) ∧
      actual.final.heads ((slots j).castAdd 53)=usage.final.heads (slots j) := by
    let i : Fin 306 := (slots j).castAdd 17
    obtain ⟨pT,pH⟩ := preOld (i.castAdd 29) (by fin_cases j <;> decide)
    obtain ⟨aT,aH⟩ := old (i.castAdd 30) (by fin_cases j <;> decide)
    have rT := revT ((slots j).castAdd 13) (by fin_cases j <;> decide)
    have rH := revH ((slots j).castAdd 13)
    have he : ((slots j).castAdd 13 : Fin 302)≠162 := by fin_cases j <;> decide
    simp only [he,ite_false] at rH
    exact ⟨aT.trans (pT.trans ((bankT i).trans (rT.trans (epT (slots j))))),
      aH.trans (pH.trans ((bankH i).trans (rH.trans (epH (slots j)))))⟩
  exact ⟨actual,ha,fun j => (retained j).1.trans (vt j),fun j => (retained j).2.trans (vh j)⟩

end NearCubicWires.RepairOrdinary.MatrixPlaneDimensions
