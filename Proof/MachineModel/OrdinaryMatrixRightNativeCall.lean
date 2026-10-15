import Proof.MachineModel.OrdinaryMatrixBatchRightReturn
import Proof.MachineModel.OrdinaryMatrixRightLoop

/-! The right-bucket controller at the original Request's native width.
All rank, endpoint and scratch bounds are derived locally; its finite
sentinel and padded bank match the reusable ordinary caller. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightNativeCall
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ranks_fit (r : Request) (g : Fin r.Gates) :
    ∀ entry∈MatrixScoreRawRanks.entries r g,entry.2.2<2^(H r)-1 := by
  have hs : ∀ entry∈MatrixScoreRawRanks.entries r g,entry.2.2<2^r.M := by
    apply KeyLoop.indexed_fits
    have hl := MatrixBucketCallBounds.entries_length r g
    simp only [MatrixScoreRawRanks.entries,KeyLoop.indexed_length] at hl
    rw [MatrixBucketCallBounds.native_power]
    have hu : 1≤r.U := Nat.one_le_two_pow
    omega
  intro entry he
  have h := hs entry he
  have hp := MatrixBucketCallBounds.header_power r
  have hu : 1≤r.U := Nat.one_le_two_pow
  rw [MatrixBucketCallBounds.native_power] at h
  omega

theorem boundary_fit (r : Request) :
    (r.bucketSize+1)+r.Buckets*(r.bucketSize+1)<2^(H r) := by
  have hb := MatrixBucketCallBounds.boundary_le r
  have hB : r.bucketSize+1≤2*r.U+1 := MatrixBucketDimensions.width_le r.U r.Gates
  have hp := MatrixBucketCallBounds.header_power r
  have hu : 1≤r.U := Nat.one_le_two_pow
  omega

noncomputable def params (r : Request) (g : Fin r.Gates) : MatrixRightBucket.Params where
  S := r.S
  K := r.M
  I := r.M
  B := r.bucketSize+1
  keyCap := MatrixScoreReusableRanks.D r
  resetCap := MatrixScoreReusableRanks.D r
  records := MatrixScoreRawRanks.entries r g
  rankFit := ranks_fit r g
  keyI := by have h := (MatrixBatchBucketBankFields.capacity_fit r).2; omega
  keyK := by have h := (MatrixBatchBucketBankFields.capacity_fit r).2; omega
  resetFit := by
    rw [MatrixBucketCallBounds.entries_length]
    have h := MatrixBucketCallBounds.reset_fit r
    unfold MatrixBucketCallBounds.resetBudget H at h
    convert h using 1
    ring

def driverCaps (r : Request) (i : Fin 26) := if i=25 then r.Buckets+2 else 0
def caps (r : Request) (i : Fin 26) := if i=22 then 0 else MatrixScoreReusableRanks.D r
noncomputable def cfg (r : Request) (g : Fin r.Gates) (phase : Fin 5) (v : MatrixRightAdvance.Store) :=
  ZeroPadding.config (caps r) (ZeroPadding.config (driverCaps r)
    (RepeatMachine.cfg phase (MatrixRightBucket.cfg MatrixRightBucket.machine.start (params r g) v) r.Buckets 1))
def budget (r : Request) := r.Buckets*(2*MatrixBucketCallBounds.resetBudget r+24*H r+4*r.M+36)+3
noncomputable def output (r : Request) (g : Fin r.Gates) :=
  MatrixRightLoop.output (params r g) (r.bucketSize+1) (g.val*r.Buckets) r.Buckets

theorem loop_run (r : Request) (g : Fin r.Gates) (v : MatrixRightAdvance.Store)
    (ha : v.a=r.bucketSize+1) (hi : v.inner=g.val*r.Buckets)
    (hu : v.upper.length≤2*H r+1) (hr : v.record.length≤4*H r+1)
    (hc : v.clone.length≤4*H r+1) :
    ∃ final : MatrixRightAdvance.Store,final.upper.length≤2*H r+1 ∧
      final.record.length≤4*H r+1 ∧ final.clone.length≤4*H r+1 ∧
      final.a=(r.bucketSize+1)+r.Buckets*(r.bucketSize+1) ∧
      final.inner=(g.val+1)*r.Buckets ∧ final.out=v.out++output r g ∧
      ∃ actual,runFrom MatrixRightLoop.machine (budget r) (cfg r g 0 v)=some actual ∧
        actual.final=cfg r g 3 final ∧ actual.steps≤budget r := by
  have hfa : v.a+r.Buckets*(params r g).B<2^MatrixRightBucket.width (params r g) := by
    rw [ha]
    exact boundary_fit r
  have hfi : v.inner+r.Buckets<2^(params r g).I := by
    rw [hi]
    exact MatrixBucketCallBounds.inner_fit r g
  obtain ⟨final,hfu,hfr,hfc,hfa,hfi,hfo,base,hb,bs,bf⟩ :=
    MatrixRightLoop.loop_run (params r g) r.Buckets v hfa hfi hu hr hc
  have ht : r.Buckets*(MatrixRightLoop.cost (params r g)+3)+3=budget r := by
    unfold MatrixRightLoop.cost MatrixRightBucket.fuel MatrixRightBucket.width params
    rw [MatrixBucketCallBounds.entries_length]
    unfold budget MatrixBucketCallBounds.resetBudget H
    ring
  rw [ht] at hb bs
  obtain ⟨native,hn,nf,ns,_⟩ := ZeroPadding.run_config MatrixRightLoop.machine (driverCaps r) _ _ base hb
  obtain ⟨actual,hact,af,actS,_⟩ := ZeroPadding.run_config MatrixRightLoop.machine (caps r) _ _ native hn
  refine ⟨final,hfu,hfr,hfc,?_,?_,?_,actual,hact,?_,actS.trans_le (ns.trans_le bs)⟩
  · simpa only [ha,params] using hfa
  · rw [hi] at hfi
    convert hfi using 1
    ring
  · simpa only [ha,hi,output] using hfo
  · rw [af,nf,bf]
    rfl

end NearCubicWires.RepairOrdinary.MatrixRightNativeCall
