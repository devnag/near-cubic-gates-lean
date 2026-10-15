import Proof.MachineModel.OrdinaryMatrixRankReverseEntry

/-! The literal ranked packet length, and the actual retained counters
at the cold batch rewind call. No stream-length driver is assumed. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRankReverseFields
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem packet_length (r : Request) (gate : Fin r.Gates) :
    (MatrixScoreRawRanks.output r gate).length=MatrixRankPacketReverse.distance (H r) r.U := by
  have hp := MatrixBatchRankedGate.packet_budget r gate
  unfold MatrixBatchRankAppend.packetBudget at hp
  rw [MatrixBatchRankedGate.words_length] at hp
  rw [←MatrixBatchRankedGate.stream_eq]
  simp only [MatrixBatchRankAppend.stream,List.length_append,List.length_singleton]
  unfold MatrixRankPacketReverse.distance MatrixRankFieldReverse.distance H
  nlinarith

theorem packets_length (r : Request) (gs : List (Fin r.Gates)) :
    (MatrixBatchGateLoop.packets r gs).length=gs.length*MatrixRankPacketReverse.distance (H r) r.U := by
  induction gs with
  | nil => simp [MatrixBatchGateLoop.packets]
  | cons gate gs ih =>
    simp only [MatrixBatchGateLoop.packets_cons,List.length_append,packet_length,ih,List.length_cons,Nat.succ_mul]
    omega

theorem output_length (r : Request) :
    (MatrixBatchGateNativeLoop.output r).length=r.Gates*MatrixRankPacketReverse.distance (H r) r.U := by
  simp only [MatrixBatchGateNativeLoop.output,packets_length,List.length_finRange]

theorem source_fields (r : Request) :
    ∃ actual,run MatrixBatchBucketEndpoints.machine (MatrixBatchBucketEndpoints.budget r)
      (MatrixBatchBucketEndpoints.input r)=some actual ∧
      actual.final.tapes 162=MatrixBatchGateNativeLoop.output r ∧
      actual.final.heads 162=(MatrixBatchGateNativeLoop.output r).length ∧
      actual.final.tapes 289=List.replicate (H r) true ∧ actual.final.heads 289=0 ∧
      actual.final.tapes 39=UnaryTemplate.tape r.U ∧ actual.final.heads 39=0 ∧
      actual.final.tapes 89=UnaryTemplate.tape r.Gates ∧ actual.final.heads 89=0 ∧
      actual.steps ≤ MatrixBatchBucketEndpoints.budget r := by
  obtain ⟨state,ranked,used,_,rt,_,hu,ut,uh,_,_,r162,h162,_,_,_,_,_,_,_⟩ := MatrixBatchRetainedFields.retained_run r
  obtain ⟨same,actual,hs,ha,atapes,ah,a289,h289,_,_,_,_,_,_,as⟩ := MatrixBatchBucketEndpoints.raw_run r
  have heq : same=used := Option.some.inj (hs.symm.trans hu)
  subst same
  have u39 : used.final.tapes 39=UnaryTemplate.tape r.U :=
    (ut 39).trans ((rt 27).trans (MatrixBatchRootCapacity.native_u r state))
  have u89 : used.final.tapes 89=UnaryTemplate.tape r.Gates := by
    apply (ut 89).trans
    change ranked.final.tapes (MatrixBatchGateLayout.slots 48)=_
    rw [rt,MatrixBatchGateNativeLoop.cfg_tapes]
    rfl
  refine ⟨actual,ha,(atapes 162).trans ((ut 162).trans r162),?_,a289,h289,
    (atapes 39).trans u39,?_,(atapes 89).trans u89,?_,as⟩
  · exact (ah 162).trans ((uh 162).trans (by simpa using h162))
  · exact (ah 39).trans (by simpa using uh 39)
  · exact (ah 89).trans (by simpa using uh 89)

end NearCubicWires.RepairOrdinary.MatrixBatchRankReverseFields
