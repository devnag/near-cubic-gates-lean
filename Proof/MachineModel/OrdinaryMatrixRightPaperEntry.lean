import Proof.MachineModel.OrdinaryMatrixRightHandoffCost

/-! Literal B.3 right matrix from the original keyed-record order, including
the paid coordinate transposition and all downstream physical work. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightPaper
open LocalBitMultitape SupplierPrinter CoordinateKey
open WilliamsLoaderForms (rowMajorBitMatrix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_run {U Gates Capacity : ℕ} (S M bucketSize : ℕ)
    (leftScore : IntMatrix U Gates) (rightScore : IntMatrix Gates U)
    (hsize : U+U ≤ 2^M)
    (hinner : Gates*stableDominanceBucketCount U U bucketSize ≤ 2^M)
    (hcap : Gates*stableDominanceBucketCount U U bucketSize ≤ Capacity)
    (hlo : ∀ gate copy,-(2^S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ gate copy,stableDominanceCopyScore leftScore rightScore gate copy<(2^S : ℕ)) (out : List Bool) :
    let used := Gates*stableDominanceBucketCount U U bucketSize
    ∃ actual : ExecutionReceipt 23 (40+MatrixRightHandoff.sortStates),
      runFrom MatrixRightHandoff.machine (1024*(used*(U+U)+Capacity*U+used+1)*(M+M+2)^2)
        (MatrixRightHandoff.input M (2*M)
          (MatrixRightInputs.original (payload bucketSize leftScore rightScore)
            (CrossGrid.order S M bucketSize leftScore rightScore))
          out U used ((Capacity-used)*U))=some actual ∧
      actual.final.tapes 19=out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity)
        (reindexedLaterBucketRight (stableBucketedDominanceLayout leftScore rightScore bucketSize))) ∧
      actual.final.heads 19=(out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity)
        (reindexedLaterBucketRight (stableBucketedDominanceLayout leftScore rightScore bucketSize)))).length ∧
      actual.steps ≤ 1024*(used*(U+U)+Capacity*U+used+1)*(M+M+2)^2 := by
  have ho : ∀ inner,(CrossGrid.order S M bucketSize leftScore rightScore inner).Perm
      (List.finRange (U+U)) := by
    intro inner
    exact dominance_ids_perm S M leftScore rightScore (finProdFinEquiv.symm inner).1
      hsize (hlo _) (hhi _)
  obtain ⟨actual,hr,ht,hh,hs⟩ := MatrixRightHandoff.plane_run M (payload bucketSize leftScore rightScore)
    (CrossGrid.order S M bucketSize leftScore rightScore) ho hsize hinner hcap out
  have hl := MatrixRightHandoff.original_length (payload bucketSize leftScore rightScore)
    (CrossGrid.order S M bucketSize leftScore rightScore) ho
  rw [hl] at hr hs
  have hb := MatrixRightHandoff.budget_le M U (Gates*stableDominanceBucketCount U U bucketSize) Capacity
  have hm := runFrom_moreFuel MatrixRightHandoff.machine _
    (1024*(Gates*stableDominanceBucketCount U U bucketSize*(U+U)+Capacity*U+
      Gates*stableDominanceBucketCount U U bucketSize+1)*(M+M+2)^2-
      MatrixRightHandoff.budget M U (Gates*stableDominanceBucketCount U U bucketSize) Capacity
        (Gates*stableDominanceBucketCount U U bucketSize*(U+U))) _ actual hr
  rw [Nat.add_sub_of_le hb] at hm
  rw [right_eq] at ht hh
  exact ⟨actual,hm,ht,hh,hs.trans hb⟩

end NearCubicWires.RepairOrdinary.MatrixRightPaper
