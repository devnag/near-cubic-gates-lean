import Proof.CaseAnalysis.RawRowsChildren

/-! The actual mode row and corrected child source supply the common digit
width. Cut generation is separately added and paid by the strict paper load. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierWalkBridge
open RepairRepresentation RepairOrdinary
open CloseoutRowsRawLogShape CloseoutRowsCacheInput
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def actualWidth {q : ℕ} (gs : List (SupportedNormalizedGate q))
    (L den z ell childBits : ℕ) :=
  rowWidth z (canonicalWalkLength den) (windowSum gs L) (rowDepth gs L) ell childBits

theorem actualWidth_positive {q : ℕ} (gs : List (SupportedNormalizedGate q))
    (L den z ell childBits : ℕ) : 1 ≤ actualWidth gs L den z ell childBits := by
  unfold actualWidth rowWidth
  omega

theorem row_digit_fit {q : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (constant : Fin gs.length → Bool)
    (L den z ell childBits : ℕ) (P : StructuralGF2Polynomial)
    (hcount : P.length ≤ rowCountBase gs L den^z)
    (hdegree : RawMonomialDegreeAtMost (z*coordinateDegree gs L den) P)
    (hell : natBitLength (2*gs.length+1) ≤ ell)
    (hchildren : ∀ i, (occurrenceExactChildren a gs i).length ≤ 2^childBits) :
    (structuralOccurrenceExactPolynomial a gs constant P).length <
      2^actualWidth gs L den z ell childBits := by
  let B := ell+coordinateLog (canonicalWalkLength den) (windowSum gs L) (rowDepth gs L) ell
  have hbase : rowCountBase gs L den ≤ 2^B := by
    have hlt : rowCountBase gs L den < 2^natBitLength (rowCountBase gs L den) := by
      simpa only [natBitLength] using Nat.lt_pow_succ_log_self (b := 2) (by decide) (rowCountBase gs L den)
    exact hlt.le.trans (Nat.pow_le_pow_right (by decide) (rowCount_log gs L den ell hell))
  have hP : P.length ≤ 2^(z*B) := by
    calc
      _ ≤ rowCountBase gs L den^z := hcount
      _ ≤ (2^B)^z := Nat.pow_le_pow_left hbase z
      _ = _ := by rw [←pow_mul,Nat.mul_comm]
  have h := exact_digit_fit a gs constant (z*B) childBits (z*coordinateDegree gs L den)
    P hP hdegree hchildren
  have he : z*B+childBits*(z*coordinateDegree gs L den)+1 ≤ actualWidth gs L den z ell childBits := by
    rw [coordinateDegree_eq]
    unfold actualWidth rowWidth B
    ring_nf
    omega
  exact h.trans_le (Nat.pow_le_pow_right (by decide) he)

theorem raw_cuts_bound {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (K w : ℕ) (bank : List (List (List Bool)))
    (hbank : bank.length ≤ 2^K) (hw : ∀ rows∈bank,rows.length ≤ 2^w) (hpos : 1 ≤ w) :
    (bank.flatMap (CloseoutRowsSharedDigits.cuts gs (K+1) w)).length ≤
      2^(2*(K+w*(K+2))) := by
  have hp := CloseoutRowsSharedDigits.batch_perm gs (K+1) w bank hw
  rw [hp.length_eq,RowPowerBinLift.batch_length]
  have hm : ∀ ms∈family gs bank,ms.length ≤ 2^w := by
    intro ms hms
    obtain ⟨rows,hr,rfl⟩ := List.mem_map.mp hms
    simpa only [polynomial,List.length_map] using hw rows hr
  have hb := RowBinLift.batch_length_bound (K+1) (2^w) (family gs bank) hm
  rw [max_eq_right Nat.one_le_two_pow] at hb
  have hfamily : (family gs bank).length ≤ 2^K := by simpa only [family,List.length_map] using hbank
  have hQ : K+1 ≤ 2^(K+1) := Nat.lt_two_pow_self.le
  calc
    _ ≤ 2^K*2^(K+1)*(2^w)^(K+1) :=
      hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul hfamily hQ))
    _ = 2^(K+(K+1)+w*(K+1)) := by rw [←pow_add,←pow_mul,←pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      nlinarith

theorem raw_cuts_gate {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (K w s : ℕ) (bank : List (List (List Bool)))
    (hbank : bank.length ≤ 2^K) (hw : ∀ rows∈bank,rows.length ≤ 2^w) (hpos : 1 ≤ w)
    (hload : 200*(K+w*(K+2)) ≤ s) :
    (bank.flatMap (CloseoutRowsSharedDigits.cuts gs (K+1) w)).length^100 ≤ 2^s := by
  calc
    _ ≤ (2^(2*(K+w*(K+2))))^100 := Nat.pow_le_pow_left (raw_cuts_bound gs K w bank hbank hw hpos) 100
    _ = 2^(200*(K+w*(K+2))) := by rw [←pow_mul]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hload

theorem actual_digit_margin {q : ℕ} (gs : List (SupportedNormalizedGate q))
    (L den z ell childBits K s : ℕ) (ha : childBits ≤ ell)
    (hload : 200*(K+128*(z+1)*(canonicalWalkLength den+1)*
      (windowSum gs L+rowDepth gs L+1)*(ell+1)*(K+2)) ≤ s) :
    200*(K+actualWidth gs L den z ell childBits*(K+2)) ≤ s := by
  exact (Nat.mul_le_mul_left 200 (digit_load K z (canonicalWalkLength den)
    (windowSum gs L) (rowDepth gs L) ell childBits ha)).trans hload

theorem raw_generation_bound (S K w s N : ℕ) (hQ : K+1 ≤ S) (hN : N ≤ 2^K)
    (hload : 200*(K+w*(K+2)) ≤ s) :
    CloseoutRowsCapacityDriver.budget S (w*(K+2))+
      CloseoutRowsFamilyLoop.budget N (K+1) (4096*S^4*2^(w*(K+2))) ≤
        4000000*2^s*(S+1)^5*(w*(K+2)+1) := by
  apply CloseoutRowsFamilyBudget.bank_bound S _ K s N hQ _ hN
  omega

end
end NearCubicWires.RepairSource.CloseoutRawRows
