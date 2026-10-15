import Proof.Hierarchy.CompetitorCountBanksLayout

/-! Execute the complete same-bucket producer beside the prepared Williams
packets. Every old tape is retained exactly; the new bank has the canonical
state encoding already required by the final count-table machine. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountBanks
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def same (p : Program) := RecoveryFocus.machine (sameSlots p) CompetitorSameBucketColdDense.machine
noncomputable def sameWord (r : Request) := CompetitorPlaneStream.oldWords (CompetitorSameBucketColdDense.width r)
  (CompetitorPlaneTable.canonical (CompetitorSameBucketState.state r))

theorem same_run (p : Program) (r : Request) (ambient : Fin (CompetitorCrossScheduler.tapes p) → List Bool)
    (h0 : ambient (CompetitorCrossScheduler.fieldSlots p 0)=MatrixScoreBatch.physicalInput r)
    (hw : ambient (CompetitorCrossScheduler.fieldSlots p 52)=List.replicate (CompetitorSameBucketColdDense.width r) true) :
    ∃ out,ClockJoin.ReadyRun (same p) (CompetitorSameBucketColdDense.budget r) (extend p ambient) out ∧
      (∀ i,out (native p i)=ambient i) ∧ out (bank p)=sameWord r := by
  obtain ⟨localRun,hr,h2,hret,hh,hs⟩ := CompetitorSameBucketColdDense.cold_run r
  have ready : ClockJoin.ReadyRun CompetitorSameBucketColdDense.machine (CompetitorSameBucketColdDense.budget r)
      (CompetitorSameBucketColdDense.input r) localRun.final.tapes := ⟨localRun,hr,rfl,hh,hs⟩
  have focused := bounded_focus (sameSlots p) (same_injective p) _ _ _ ready (extend p ambient)
    (same_input p r ambient h0 hw)
  let out := install (sameSlots p) (extend p ambient) localRun.final.tapes
  refine ⟨out,focused,same_fields p r ambient localRun.final.tapes h0 hw (hret 0) (hret 1),?_⟩
  change install (sameSlots p) (extend p ambient) localRun.final.tapes (sameSlots p 2)=_
  rw [install_slot _ (same_injective p),h2]
  exact (CompetitorSameBucketState.dense_word r (CompetitorSameBucketColdDense.width r)).symm

end NearCubicWires.RepairOrdinary.CompetitorCountBanks
