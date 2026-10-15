import Proof.MachineModel.OrdinaryMatrixRightInputs

/-! The paid right sorting/selection program at the paper's exact B.3
bucket layout. Rank-labelled generation and its outer handoff stay explicit. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightPaper
open LocalBitMultitape SupplierPrinter CoordinateKey
open WilliamsLoaderForms (rowMajorBitMatrix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def payload {U Gates : ℕ} (bucketSize : ℕ) (leftScore : IntMatrix U Gates) (rightScore : IntMatrix Gates U)
    (index : Fin (Gates*stableDominanceBucketCount U U bucketSize)) (id : Fin (U+U)) : Bool :=
  let p := finProdFinEquiv.symm index
  decide ((p.2.val+1)*(bucketSize+1) ≤
    (stableDominanceRank leftScore rightScore p.1 (finSumFinEquiv.symm id)).val)

theorem right_eq {U Gates : ℕ} (bucketSize : ℕ) (leftScore : IntMatrix U Gates) (rightScore : IntMatrix Gates U) :
    MatrixRightGrid.right (payload bucketSize leftScore rightScore)=
      reindexedLaterBucketRight (stableBucketedDominanceLayout leftScore rightScore bucketSize) := by
  funext index column
  simpa only [MatrixRightGrid.right,payload,reindexedLaterBucketRight,finSumFinEquiv_symm_apply_natAdd] using
    (BucketBoundary.right_cell leftScore rightScore bucketSize
      (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2 column).symm

noncomputable def request {U Gates : ℕ} (S M bucketSize : ℕ)
    (leftScore : IntMatrix U Gates) (rightScore : IntMatrix Gates U) : SortCarrier.Request :=
  MatrixRightInputs.request M (payload bucketSize leftScore rightScore)
    (CrossGrid.order S M bucketSize leftScore rightScore)

theorem paper_run {U Gates Capacity : ℕ} (S M bucketSize : ℕ)
    (leftScore : IntMatrix U Gates) (rightScore : IntMatrix Gates U)
    (hsize : U+U ≤ 2^M)
    (hinner : Gates*stableDominanceBucketCount U U bucketSize ≤ 2^M)
    (hcap : Gates*stableDominanceBucketCount U U bucketSize ≤ Capacity)
    (hlo : ∀ gate copy,-(2^S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ gate copy,stableDominanceCopyScore leftScore rightScore gate copy<(2^S : ℕ)) (out : List Bool) :
    let used := Gates*stableDominanceBucketCount U U bucketSize
    ∃ actual : ExecutionReceipt 11 (88+MatrixRightSort.planeStates),
      runFrom MatrixRightSort.machine (512*(used*(U+U)+Capacity*U+used+1)*(M+M+2)^2)
        (MatrixRightSort.input (request S M bucketSize leftScore rightScore) out U used ((Capacity-used)*U))=some actual ∧
      actual.final.tapes 7=out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity)
        (reindexedLaterBucketRight (stableBucketedDominanceLayout leftScore rightScore bucketSize))) ∧
      actual.final.heads 7=(out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity)
        (reindexedLaterBucketRight (stableBucketedDominanceLayout leftScore rightScore bucketSize)))).length ∧
      actual.steps ≤ 512*(used*(U+U)+Capacity*U+used+1)*(M+M+2)^2 := by
  have ho : ∀ inner,(CrossGrid.order S M bucketSize leftScore rightScore inner).Perm (List.finRange (U+U)) := by
    intro inner
    exact dominance_ids_perm S M leftScore rightScore (finProdFinEquiv.symm inner).1 hsize (hlo _) (hhi _)
  obtain ⟨actual,hr,ht,hh,hs⟩ := MatrixRightInputs.plane_run M (payload bucketSize leftScore rightScore)
    (CrossGrid.order S M bucketSize leftScore rightScore) ho hsize hinner hcap out
  rw [right_eq] at ht hh
  exact ⟨actual,hr,ht,hh,hs⟩

end NearCubicWires.RepairOrdinary.MatrixRightPaper
