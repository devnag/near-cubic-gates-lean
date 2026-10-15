import Proof.MachineModel.OrdinaryMatrixBatchBucketSizes
import Proof.MachineModel.OrdinaryMatrixBatchAllRanksBounds
import Proof.Hierarchy.CompetitorFinalTableNative

/-! Tight ALL-gate aggregate for the actual capacity-dependent buckets.
This pays even a padded B-by-B scan of every bucket; replacing Gates by
Capacity before this inequality would lose the required exponent. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucket
open LocalBitMultitape SupplierPrinter MatrixScoreBatch SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def blockWidth (u c g : ℕ) := stableCapacityBucketSize u u c g+1

theorem block_width_le (u c g : ℕ) : blockWidth u c g≤2*u+1 := by
  simp only [blockWidth,stableCapacityBucketSize]
  split
  · omega
  · have h := Nat.div_le_self (u+u) (stableCapacityBucketBudget c g-1)
    omega

theorem gate_block_width (u c g : ℕ) (hu : 1≤u) (hs : g*g≤c) (hc : c≤u) :
    g*blockWidth u c g≤5*u := by
  have hg : g≤u := (Nat.le_mul_self g).trans (hs.trans hc)
  by_cases h0 : g=0
  · simp [h0]
  have hgpos : 0<g := by omega
  let q := stableCapacityBucketBudget c g
  have hqeq : q=c/g := by simp [q,stableCapacityBucketBudget,h0]
  have hgq : g≤q := by
    rw [hqeq]
    exact (Nat.le_div_iff_mul_le hgpos).mpr hs
  by_cases h1 : g=1
  · have hb := block_width_le u c g
    nlinarith
  have hq : 1<q := by omega
  let v := (u+u)/(q-1)
  have hdiv : v*(q-1)≤u+u := Nat.div_mul_le_self _ _
  have hqsub : q-1+1=q := Nat.sub_add_cancel (by omega)
  have htwice : g≤2*(q-1) := by omega
  have hv := Nat.mul_le_mul_left v htwice
  have hb : blockWidth u c g=v+1 := by
    unfold blockWidth stableCapacityBucketSize
    change (if q≤1 then u+u else (u+u)/(q-1))+1=v+1
    rw [if_neg (by omega)]
  rw [hb]
  nlinarith

theorem all_bucket_pairs (u c g : ℕ) (hu : 1≤u) (hs : g*g≤c) (hc : c≤u) :
    g*stableDominanceBucketCount u u (stableCapacityBucketSize u u c g)*(blockWidth u c g)^2≤25*u^2 := by
  let b := blockWidth u c g
  have hb : b≤3*u := (block_width_le u c g).trans (by omega)
  have hgb : g*b≤5*u := gate_block_width u c g hu hs hc
  have hcount : stableDominanceBucketCount u u (stableCapacityBucketSize u u c g)*b≤5*u := by
    have hdiv := Nat.div_mul_le_self (u+u) b
    change ((u+u)/b+1)*b≤5*u
    nlinarith
  have hm := Nat.mul_le_mul hgb hcount
  nlinarith

theorem request_gate_block (r : Request) : r.Gates*(r.bucketSize+1)≤5*r.U :=
  gate_block_width r.U r.Capacity r.Gates (dimension_positive r) r.gateSquare (WilliamsPaddedRequest.inner_le r.U)

theorem request_all_pairs (r : Request) : r.Gates*r.Buckets*(r.bucketSize+1)^2≤25*r.U^2 :=
  all_bucket_pairs r.U r.Capacity r.Gates (dimension_positive r) r.gateSquare (WilliamsPaddedRequest.inner_le r.U)

theorem all_same_pairs (r : Request) :
    (∑ gate : Fin r.Gates,stableSameBucketPairCount (bucketSize := r.bucketSize)
      (leftScore r) (rightScore r) gate)≤5*r.U^2 := by
  calc
    _ ≤ ∑ _gate : Fin r.Gates,r.U*(r.bucketSize+1) := by
      apply Finset.sum_le_sum
      intro gate _
      exact stableSameBucketPairCount_le (leftScore r) (rightScore r) gate
    _ = r.Gates*(r.U*(r.bucketSize+1)) := by simp
    _ ≤ 5*r.U^2 := by
      have h := Nat.mul_le_mul_left r.U (request_gate_block r)
      nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucket
