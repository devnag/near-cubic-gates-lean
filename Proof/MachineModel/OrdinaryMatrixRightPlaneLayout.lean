import Proof.MachineModel.OrdinaryMatrixRightRecords

/-! Native right-plane entry uses the completed raw key stream and already
paid zero bank, two retained native zero words, and the actual dimension
templates. Zero padding changes only finite tape representation. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightPlaneLayout
open LocalBitMultitape MatrixScoreBatch MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def caps (r : Request) (i : Fin 23) :=
  if i=7 then max (MatrixScoreReusableRanks.D r) ((MatrixCoordinateTranspose.stream r.M (MatrixRightRecords.records r)).length+1)
  else if i=21 then r.Used+2
  else if i=10 ∨ i=12 ∨ i=19 ∨ i=20 ∨ i=22 then 0 else MatrixScoreReusableRanks.D r
noncomputable def target (r : Request) := ZeroPadding.config (caps r)
  (MatrixRightHandoff.input r.M (2*r.M) (MatrixRightRecords.records r) [] r.U r.Used ((r.Capacity-r.Used)*r.U))
noncomputable def input (r : Request) : Fin 23 → List Bool :=
  let D := MatrixScoreReusableRanks.D r
  ![zeros D,zeros D,zeros D,zeros D,zeros D,zeros D,zeros D,MatrixBatchRightPass.output r,
    scalar D r.M 0,scalar D r.M 0,[],zeros D,[],zeros D,zeros D,zeros D,zeros D,zeros D,zeros D,[],
    UnaryTemplate.tape r.U,UnaryTemplate.tape r.Used,UnaryTemplate.tape ((r.Capacity-r.Used)*r.U)]

theorem pad_false (D : ℕ) (bits : List Bool) :
    ZeroPadding.pad D (bits++[false])=ZeroPadding.pad (max D (bits.length+1)) bits := by
  unfold ZeroPadding.pad
  simp only [List.length_append,List.length_singleton,List.append_assoc]
  congr 1
  change List.replicate 1 false++List.replicate (D-(bits.length+1)) false=_
  rw [← List.replicate_add]
  congr 1
  omega

theorem target_tapes (r : Request) : (target r).tapes=input r := by
  have hb := MatrixBucketCallBounds.workspace_fit r
  unfold MatrixBatchBucketEndpoints.H at hb
  have h4 : 4*r.M+1≤MatrixScoreReusableRanks.D r := by omega
  have h8 : 8*r.M+3≤MatrixScoreReusableRanks.D r := by omega
  have h2 : 2*r.M+1≤MatrixScoreReusableRanks.D r := by omega
  have h24 : 24*r.M+14≤MatrixScoreReusableRanks.D r := by omega
  have hc : 2*r.M≤MatrixScoreReusableRanks.D r := by omega
  funext i
  by_cases h7 : i=7
  · subst i
    change ZeroPadding.pad (max (MatrixScoreReusableRanks.D r)
      ((MatrixCoordinateTranspose.stream r.M (MatrixRightRecords.records r)).length+1))
      (MatrixCoordinateTranspose.stream r.M (MatrixRightRecords.records r))=MatrixBatchRightPass.output r
    rw [MatrixBatchRightPass.output,MatrixRightRecords.output_stream,pad_false]
  fin_cases i
  all_goals first
    | exact (h7 rfl).elim
    | simp [target,ZeroPadding.config,caps,input,MatrixRightHandoff.input,Composition.leftConfig,TapeEmbedding.config,
    MatrixRightHandoff.tapes,MatrixCoordinateTranspose.resetInput,Rewind.recording,Rewind.config,
    MatrixCoordinateTranspose.cfg,Fin.addCases,MatrixBatchRightPass.output,MatrixRightRecords.output_stream,
    scalar,RankCarrier.binary_zero,zeros,ZeroPadding.pad,UnaryTemplate.tape,
    RepairSource.VerifierDecoding.CompareMachine.word,
    Nat.add_sub_of_le h4,Nat.add_sub_of_le h8,Nat.add_sub_of_le h2,Nat.add_sub_of_le h24,Nat.add_sub_of_le hc]

theorem target_heads (r : Request) : (target r).heads=fun i => if i=20 ∨ i=21 ∨ i=22 then 1 else 0 := by
  funext i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.MatrixRightPlaneLayout
