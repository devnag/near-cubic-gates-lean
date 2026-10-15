import Proof.MachineModel.OrdinaryMatrixBucketCount

/-! Whole physical B/Buckets supplier and its canonical arithmetic bridge.
The only inputs are the actual U template and positive raw budget. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketSizes
open LocalBitMultitape SourceInterfaces SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine MatrixBucketSize.machine MatrixBucketCount.machine
def budget (U q : ℕ) := MatrixBucketSize.budget U q+1+
  MatrixBucketCount.budget U (MatrixBucketSizeBranches.value U q+1)

theorem sizes_run (U q : ℕ) (hq : 0<q) : ∃ out,ClockJoin.ReadyRun machine (budget U q)
    (MatrixBucketSizePrepare.input U q) out ∧
    out 0=UnaryTemplate.tape U ∧ out 7=List.replicate (2*U) true ∧ out 8=UnaryTemplate.tape (2*U) ∧
    out 11=List.replicate q true ∧ out 12=UnaryTemplate.tape (q-1) ∧ out 13=UnaryTemplate.tape q ∧
    out 18=List.replicate (MatrixBucketSizeBranches.value U q) true ∧
    out 19=List.replicate (MatrixBucketSizeBranches.value U q) true ∧
    out 20=UnaryTemplate.tape (MatrixBucketSizeBranches.value U q+1) ∧
    out 24=List.replicate ((2*U)/(MatrixBucketSizeBranches.value U q+1)) true ∧
    out 25=List.replicate ((2*U)/(MatrixBucketSizeBranches.value U q+1)) true ∧
    out 26=UnaryTemplate.tape (MatrixBucketCount.value U (MatrixBucketSizeBranches.value U q+1)) := by
  obtain ⟨sized,hs,s0,s7,s8,s11,s12,s13,s18,s19,s20,sfresh⟩ := MatrixBucketSize.size_run U q hq
  obtain ⟨out,hc,old,o24,o25,o26⟩ := MatrixBucketCount.count_run U (MatrixBucketSizeBranches.value U q+1)
    (by omega) sized s7 s20 sfresh
  have whole := ClockJoin.join MatrixBucketSize.machine MatrixBucketCount.machine _ _ _ _ _ hs hc
  exact ⟨out,whole,(old 0).trans s0,(old 7).trans s7,(old 8).trans s8,(old 11).trans s11,
    (old 12).trans s12,(old 13).trans s13,(old 18).trans s18,(old 19).trans s19,
    (old 20).trans s20,o24,o25,o26⟩

theorem size_eq (U G : ℕ) :
    MatrixBucketSizeBranches.value U (MatrixBucketDimensions.bucketBudget U G)=MatrixBucketDimensions.bucketSize U G := by
  simp only [MatrixBucketSizeBranches.value,MatrixBucketDimensions.bucketSize,
    stableCapacityBucketSize,MatrixBucketDimensions.bucketBudget,two_mul]
theorem width_eq (U G : ℕ) :
    MatrixBucketSizeBranches.value U (MatrixBucketDimensions.bucketBudget U G)+1=MatrixBucketDimensions.width U G := by
  rw [size_eq]
  rfl
theorem count_eq (U G : ℕ) :
    MatrixBucketCount.value U (MatrixBucketSizeBranches.value U (MatrixBucketDimensions.bucketBudget U G)+1)=
      MatrixBucketDimensions.buckets U G := by
  rw [size_eq]
  simp only [MatrixBucketCount.value,MatrixBucketDimensions.buckets,stableDominanceBucketCount,two_mul]

theorem budget_le (U q : ℕ) : budget U q≤100*(U+q+1) := by
  have hsize : MatrixBucketSizeBranches.value U q≤2*U := by
    unfold MatrixBucketSizeBranches.value
    split
    · exact Nat.le_refl _
    · exact Nat.div_le_self _ _
  have hcount := Nat.div_le_self (2*U) (MatrixBucketSizeBranches.value U q+1)
  unfold budget MatrixBucketSize.budget MatrixBucketSize.decisionBudget MatrixBucketSizePrepare.budget
    MatrixBucketDouble.budget WilliamsUnaryProduct.budget MatrixBucketCount.budget
  omega

end NearCubicWires.RepairOrdinary.MatrixBucketSizes
