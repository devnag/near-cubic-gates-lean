import Proof.MachineModel.OrdinaryMatrixBucketKeyRecords

/-! The actual coordinate sorter consumes the native padded all-bucket
stream. Its paid rewind returns every selected head to zero. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketCoordinateSort
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 7 88 := Rewind.machine SortCarrier.machine
noncomputable def budget (r : Request) := 2*SortCarrier.budget (MatrixBucketKeyRecords.records r)+2
noncomputable def input (r : Request) : Fin 7 → List Bool :=
  fun i => if i=0 then MatrixBatchBucketPass.output r else []
def caps (r : Request) : Fin 7 → ℕ := fun i => if i=0 then MatrixScoreReusableRanks.D r else 0
noncomputable def output (r : Request) := ZeroPadding.pad (MatrixScoreReusableRanks.D r)
  (StablePartition.stream (SortCarrier.sorted (MatrixBucketKeyRecords.request r)))

theorem sort_run (r : Request) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 0=output r ∧ (∀ i,actual.final.heads i=0) ∧ actual.steps≤budget r := by
  let req := MatrixBucketKeyRecords.request r
  obtain ⟨source,_,_,hs,ht,hsteps,_⟩ := Classical.choose_spec (SortCarrier.raw_sort req.records req.uniform)
  obtain ⟨reset,hr,rt,rh,rs,_⟩ := Rewind.reset_run SortCarrier.machine _ _ source hs
  obtain ⟨padded,hp,pf,ps,_⟩ := ZeroPadding.run_config machine (caps r) _ _ reset hr
  have hi : ZeroPadding.config (caps r)
      (initialConfiguration machine (Fin.addCases (motive := fun _ : Fin (6+1) => List Bool) (SourceHandoff.sourceTapes (t := 6) (StablePartition.stream req.records))
        (fun _ : Fin 1 => [])))=initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,caps,input,SourceHandoff.sourceTapes,Fin.addCases,
        MatrixBucketKeyRecords.input_stream,req,initialConfiguration]
  change runFrom machine (2*source.steps+2)
    (ZeroPadding.config (caps r) (initialConfiguration machine
      (Fin.addCases (motive := fun _ : Fin (6+1) => List Bool)
        (SourceHandoff.sourceTapes (t := 6) (StablePartition.stream req.records)) (fun _ : Fin 1 => []))))=some padded at hp
  rw [hi] at hp
  have hb : 2*source.steps+2≤budget r := by
    change 2*source.steps+2≤2*SortCarrier.budget req.records+2
    omega
  have hm := runFrom_moreFuel machine (2*source.steps+2) (budget r-(2*source.steps+2)) _ _ hp
  rw [Nat.add_sub_of_le hb] at hm
  refine ⟨padded,hm,?_,?_,?_⟩
  · rw [pf]
    change ZeroPadding.pad (MatrixScoreReusableRanks.D r) (reset.final.tapes 0)=_
    exact congrArg (ZeroPadding.pad (MatrixScoreReusableRanks.D r)) ((rt 0).trans ht)
  · intro i
    rw [pf]
    exact rh i
  · rw [ps,rs]
    exact hb

theorem budget_le (r : Request) : budget r≤256*(r.Used*(r.U+r.U)+1)*(r.M+r.M+2)^2+2 := by
  have h := SortCost.carrier_budget_le (MatrixBucketKeyRecords.request r)
  have hw := MatrixBucketKeyRecords.width_le r
  have hm : (SortPreparation.width (MatrixBucketKeyRecords.records r)+1)^2≤(r.M+r.M+2)^2 := by
    exact Nat.pow_le_pow_left (by omega) 2
  have hb := Nat.mul_le_mul_left (256*(r.Used*(r.U+r.U)+1)) hm
  change 4*_+3+SortCarrier.budget (MatrixBucketKeyRecords.records r)≤
    128*((MatrixBucketKeyRecords.records r).length+1)*(SortPreparation.width (MatrixBucketKeyRecords.records r)+1)^2 at h
  rw [MatrixBucketKeyRecords.count] at h
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixBucketCoordinateSort
