import Proof.Hierarchy.CompetitorSelectedCountBounds

/-! The odd residual rectangle may use the full U² driver. Its missing
tail consists solely of implicit blank cells with a false selector, so it
changes neither the selected sum nor the paper normalization. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedCount
open CompetitorCountMask SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padded (N : ℕ) (xs : List (Bool × ℕ)) := xs++List.replicate (N-xs.length) (false,0)

theorem padded_length (N : ℕ) (xs : List (Bool × ℕ)) (hn : xs.length≤N) :
    (padded N xs).length=N := by simp [padded];omega

theorem selected_padded (N : ℕ) (xs : List (Bool × ℕ)) :
    selected (padded N xs)=selected xs++List.replicate (N-xs.length) 0 := by
  simp [selected,padded]

theorem padded_sum (N : ℕ) (xs : List (Bool × ℕ)) :
    (selected (padded N xs)).sum=(selected xs).sum := by
  simp [selected_padded]

theorem padded_fit (Q N : ℕ) (xs : List (Bool × ℕ))
    (hx : ∀ x∈selected xs,x<2^Q) : ∀ x∈selected (padded N xs),x<2^Q := by
  intro x h
  rw [selected_padded] at h
  rcases List.mem_append.mp h with h | h
  · exact hx x h
  · have he : x=0 := (List.mem_replicate.mp h).2
    subst x
    positivity

theorem padded_mask (N : ℕ) (xs : List (Bool × ℕ)) :
    mask (padded N xs)=ZeroPadding.pad N (mask xs) := by
  simp [mask,padded,ZeroPadding.pad]

theorem zero_raw (Q N : ℕ) :
    CompetitorCountFold.raw Q (List.replicate N 0)=List.replicate (Q*N) false := by
  induction N with
  | zero => simp [CompetitorCountFold.raw]
  | succ N ih =>
    rw [List.replicate_succ,CompetitorCountFold.raw_cons,RankCarrier.binary_zero,ih,
      ←List.replicate_add]
    congr 1
    ring

theorem padded_counts (Q N : ℕ) (xs : List (Bool × ℕ)) :
    CompetitorCountFold.raw Q (counts (padded N xs))=
      ZeroPadding.pad (Q*N) (CompetitorCountFold.raw Q (counts xs)) := by
  have hc : counts (padded N xs)=counts xs++List.replicate (N-xs.length) 0 := by
    simp [counts,padded]
  rw [hc]
  change (counts xs++List.replicate (N-xs.length) 0).flatMap (binary Q)=_
  rw [List.flatMap_append]
  change CompetitorCountFold.raw Q (counts xs)++CompetitorCountFold.raw Q (List.replicate (N-xs.length) 0)=_
  rw [zero_raw]
  simp only [ZeroPadding.pad,CompetitorCountFold.raw_length,counts_length,Nat.mul_sub_left_distrib]

end NearCubicWires.RepairOrdinary.CompetitorSelectedCount
