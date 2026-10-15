import Proof.MachineModel.OrdinaryMatrixBucketCallBounds

/-! The existing ordinary bucket traversal consumes the actual padded
native bank. All arithmetic/record bounds come from the unchanged Request;
only the ordinary reusable backing invariant remains as a caller input. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketNativeCall
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (r : Request) (q : Fin s) (inner boundary rank : ℕ)
    (upper record clone source out : List Bool) (head : ℕ) :=
  ZeroPadding.config (fun _ : Fin 23 => MatrixScoreReusableRanks.D r)
    (KeyBucketLoop.config q (H r) boundary (r.bucketSize+1) rank upper record clone true source out
      r.M r.M inner (MatrixScoreReusableRanks.D r) (MatrixScoreReusableRanks.D r) head r.Buckets)
def budget (r : Request) := r.Buckets*(2*MatrixBucketCallBounds.resetBudget r+12*H r+4*r.M+21)+1
noncomputable def output (r : Request) (gate : Fin r.Gates) :=
  KeyBucketLoop.output r.M r.M (gate.val*r.Buckets) 0 (r.bucketSize+1) true
    (MatrixScoreRawRanks.entries r gate) r.Buckets

theorem bucket_run (r : Request) (gate : Fin r.Gates) (rank : ℕ) (upper record clone out : List Bool)
    (hu : upper.length ≤ 2*H r+1) (hr : record.length ≤ 4*H r+1) (hc : clone.length ≤ 4*H r+1) :
    ∃ phase finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2*H r+1 ∧ finalRecord.length ≤ 4*H r+1 ∧ finalClone.length ≤ 4*H r+1 ∧
      ∃ actual,runFrom KeyBucketLoop.machine (budget r)
        (cfg r KeyBucketLoop.machine.start (gate.val*r.Buckets) 0 rank upper record clone
          (MatrixScoreRawRanks.output r gate) out 1)=some actual ∧
        actual.final=cfg r (UnaryController.stop (s := 75) phase) ((gate.val+1)*r.Buckets)
          (r.Buckets*(r.bucketSize+1)) finalRank finalUpper finalRecord finalClone
          (MatrixScoreRawRanks.output r gate) (out++output r gate) (r.Buckets+1) ∧
        actual.steps ≤ budget r := by
  have hkey : 2*r.M ≤ MatrixScoreReusableRanks.D r := by
    have h := (MatrixBatchBucketBankFields.capacity_fit r).2
    omega
  have hreset : (MatrixScoreRawRanks.entries r gate).length*(68*(r.M+r.S+1)+4*(r.M+r.M)+63)+1 ≤
      MatrixScoreReusableRanks.D r := by
    rw [MatrixBucketCallBounds.entries_length]
    have h := MatrixBucketCallBounds.reset_fit r
    unfold MatrixBucketCallBounds.resetBudget H at h
    convert h using 1
    ring
  obtain ⟨phase,finalRank,finalUpper,finalRecord,finalClone,hfu,hfr,hfc,base,hb,hf,hs,_⟩ :=
    KeyBucketLoop.buckets_run r.S r.M r.M (MatrixScoreReusableRanks.D r) (MatrixScoreReusableRanks.D r)
      (r.bucketSize+1) (MatrixScoreRawRanks.entries r gate) true (MatrixBucketCallBounds.ranks_fit r gate)
      hkey hkey hreset r.Buckets (gate.val*r.Buckets) 0 rank upper record clone out
      (MatrixBucketCallBounds.inner_fit r gate) (by simpa only [Nat.zero_add,H] using MatrixBucketCallBounds.boundary_fit r) hu hr hc
  have hbtime : r.Buckets*(2*((MatrixScoreRawRanks.entries r gate).length*(68*(r.M+r.S+1)+4*(r.M+r.M)+63)+1)+
      12*(r.M+r.S+1)+4*r.M+21)+1=budget r := by
    rw [MatrixBucketCallBounds.entries_length]
    unfold budget MatrixBucketCallBounds.resetBudget H
    ring
  rw [hbtime] at hb hs
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config KeyBucketLoop.machine
    (fun _ : Fin 23 => MatrixScoreReusableRanks.D r) _ _ base hb
  refine ⟨phase,finalRank,finalUpper,finalRecord,finalClone,hfu,hfr,hfc,actual,ha,?_,has.trans_le hs⟩
  rw [haf,hf]
  have he : gate.val*r.Buckets+r.Buckets=(gate.val+1)*r.Buckets := by ring
  simp only [Nat.zero_add,he]
  rfl

end NearCubicWires.RepairOrdinary.MatrixBucketNativeCall
