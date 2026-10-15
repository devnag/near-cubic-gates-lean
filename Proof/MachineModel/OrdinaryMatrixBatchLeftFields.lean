import Proof.MachineModel.OrdinaryMatrixBucketLeftPlane

/-! The exact U/Used/pad fields at the actual coordinate-sort endpoint.
Determinism connects the retained fields to their original cold executions. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchLeftFields
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_fields (r : Request) : ∃ actual,
    run MatrixBatchCoordinateSort.machine (MatrixBatchCoordinateSort.budget r) (MatrixBatchCoordinateSort.input r)=some actual ∧
    actual.final.tapes 314=MatrixBucketCoordinateSort.output r ∧ actual.final.heads 314=0 ∧
    actual.final.tapes 285=UnaryTemplate.tape r.Used ∧ actual.final.heads 285=0 ∧
    actual.final.tapes 287=UnaryTemplate.tape (r.Capacity-r.Used) ∧ actual.final.heads 287=0 ∧
    actual.final.tapes 39=UnaryTemplate.tape r.U ∧ actual.final.heads 39=0 ∧
    actual.steps≤MatrixBatchCoordinateSort.budget r := by
  obtain ⟨pre,actual,hpre,ha,a314,h314,_,old,steps⟩ := MatrixBatchCoordinateSort.raw_run r
  obtain ⟨_,_,bank,same,hbank,hsame,_,_,_,_,preOld,_⟩ := MatrixBatchBucketPass.raw_run r
  have he : same=pre := Option.some.inj (hsame.symm.trans hpre)
  subst same
  obtain ⟨reversed,_,same,hr,hb,bankT,bankH,_,_,_,_,_⟩ := MatrixBatchBucketBank.raw_run r
  have he : same=bank := Option.some.inj (hb.symm.trans hbank)
  subst same
  obtain ⟨endpoints,same,hep,hrr,revT,revH,_,_,u39,hu39,_,_,_,_,_,_,_,_,_⟩ := MatrixBatchRankReverse.raw_run r
  have he : same=reversed := Option.some.inj (hrr.symm.trans hr)
  subst same
  obtain ⟨usage,same,hu,hepp,epT,epH,_,_,_,_,_,_,_,_,_⟩ := MatrixBatchBucketEndpoints.raw_run r
  have he : same=endpoints := Option.some.inj (hepp.symm.trans hep)
  subst same
  obtain ⟨_,same,_,huu,_,_,u285,hu285,u287,hu287,_⟩ := MatrixBatchBucketUsage.raw_run r
  have he : same=usage := Option.some.inj (huu.symm.trans hu)
  subst same
  have retained (i : Fin 306) (hselected : ∀ j,MatrixBatchBucketPassFields.slots j≠
      (i.castAdd 29).castAdd 1) (h314 : (i.castAdd 30 : Fin 336)≠314) :
      actual.final.tapes (i.castAdd 36)=reversed.final.tapes i ∧
      actual.final.heads (i.castAdd 36)=reversed.final.heads i := by
    obtain ⟨pT,pH⟩ := preOld (i.castAdd 29) hselected
    obtain ⟨aT,aH⟩ := old (i.castAdd 30) h314
    exact ⟨aT.trans (pT.trans (bankT i)),aH.trans (pH.trans (bankH i))⟩
  have h285 := retained 285 (by decide) (by decide)
  have h287 := retained 287 (by decide) (by decide)
  have h39 := retained 39 (by decide) (by decide)
  refine ⟨actual,ha,a314,h314,?_,?_,?_,?_,h39.1.trans u39,h39.2.trans hu39,steps⟩
  · exact h285.1.trans ((revT 285 (by decide)).trans ((epT 285).trans u285))
  · exact h285.2.trans ((revH 285).trans ((epH 285).trans hu285))
  · exact h287.1.trans ((revT 287 (by decide)).trans ((epT 287).trans u287))
  · exact h287.2.trans ((revH 287).trans ((epH 287).trans hu287))

end NearCubicWires.RepairOrdinary.MatrixBatchLeftFields
