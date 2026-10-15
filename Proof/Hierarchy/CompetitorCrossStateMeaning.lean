import Proof.Hierarchy.CompetitorSameBucketState

/-! The actual positive/negative plane loop reconstructs the canonical
signed-by-Boolean product. Existing supplier reconstruction and padding
theorems identify it with the exact B.3 later-bucket term. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossStateMeaning
open MatrixScoreBatch SupplierPrinter CompetitorPlaneTable CompetitorMatrixPlaneTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def signed {n : ℕ} (state : State n) (i : Fin n) : ℤ := (state.positive i : ℤ)-state.negative i

theorem plane_signed {n : ℕ} (a : Plane n) (s : State n) (i : Fin n) :
    signed (a.apply s) i=signed s i+(2^a.bit : ℤ)*((a.positive i : ℤ)-a.negative i) := by
  simp only [signed,Plane.apply,pairState,advance,CompetitorPlane.nextPositive,
    CompetitorPlane.nextNegative,CompetitorPlaneWidth.factor_value,Bool.false_eq_true,↓reduceIte,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem evaluate_signed {n : ℕ} (planes : List (Plane n)) (s : State n) (i : Fin n) :
    signed (evaluate planes s) i=signed s i+
      (planes.map (fun a=>(2^a.bit : ℤ)*((a.positive i : ℤ)-a.negative i))).sum := by
  induction planes generalizing s with
  | nil => simp [evaluate]
  | cons a planes ih =>
    rw [evaluate,ih,plane_signed]
    simp only [List.map_cons,List.sum_cons]
    ring

theorem sum_range_fin (p : ℕ) (f : ℕ → ℤ) :
    ((List.range p).map f).sum=∑ i : Fin p,f i.val := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [List.range_succ,List.map_append,List.sum_append,ih,Fin.sum_univ_castSucc]
    simp

noncomputable def state (r : Request) := evaluate (planes r) (zero (r.U*r.U))

theorem signed_recombined (r : Request) (i : Fin (r.U*r.U)) :
    signed (state r) i=recombinedSignedProduct (width := r.p) (signedLeft r) (booleanRight r) i.divNat i.modNat := by
  have h:=evaluate_signed (planes r) (zero (r.U*r.U)) i
  simp only [planes,List.map_map,Function.comp_def,plane,signed,zero,Nat.cast_zero,sub_self,zero_add] at h
  change signed (state r) i=((List.range r.p).map
    (fun bit=>(2^bit : ℤ)*((count r false bit i : ℤ)-count r true bit i))).sum at h
  rw [sum_range_fin] at h
  exact h

theorem signedLeft_fit (r : Request) : ∀ row inner,(signedLeft r row inner).natAbs < 2^r.p := by
  intro row inner
  unfold signedLeft padSignedInner
  split
  · unfold reindexedLaterBucketLeft laterBucketLeft
    split
    · exact (r.fits _ (List.get_mem r.cuts _)).2.2
    · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _

theorem signed_product (r : Request) (i : Fin (r.U*r.U)) :
    signed (state r) i=signedBooleanProduct (signedLeft r) (booleanRight r) i.divNat i.modNat := by
  rw [signed_recombined,recombinedSignedProduct_eq _ _ (signedLeft_fit r)]

theorem signed_later (r : Request) (i : Fin (r.U*r.U)) :
    signed (state r) i=laterBucketContribution
      (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize) (weight r) i.divNat i.modNat := by
  rw [signed_product]
  unfold signedLeft booleanRight
  have hc : r.Gates*stableDominanceBucketCount r.U r.U r.bucketSize ≤ r.Capacity := capacity r
  have hp:=signedBooleanProduct_padInner_eq hc
    (reindexedLaterBucketLeft (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize) (weight r))
    (reindexedLaterBucketRight (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize))
  rw [hp,reindexedLaterBucketProduct_eq]

theorem combined_dominance (r : Request) (i : Fin (r.U*r.U)) :
    (((state r).positive i+(CompetitorSameBucketState.state r).positive i : ℕ) : ℤ)-
      ((state r).negative i+(CompetitorSameBucketState.state r).negative i : ℕ)=
      weightedDominance (leftScore r) (rightScore r) (weight r) i.divNat i.modNat := by
  have hs:=CompetitorSameBucketState.signed_meaning r i
  have hc:=signed_later r i
  have ht:=weightedDominance_eq_stable_same_add_later (leftScore r) (rightScore r) r.bucketSize (weight r)
    i.divNat i.modNat
  simp only [signed] at hc
  push_cast
  linear_combination hs+hc-ht

end NearCubicWires.RepairOrdinary.CompetitorCrossStateMeaning
