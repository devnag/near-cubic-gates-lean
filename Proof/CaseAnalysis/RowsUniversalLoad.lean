import Proof.CaseAnalysis.RowsUniversalResources
import Proof.CaseAnalysis.RawRowsLoad

/-! The original row-count/degree ledger supplies the digit width for the
universal pooled polynomial, using exactly one extra child-count bit. -/
namespace NearCubicWires.RepairSource.CloseoutRowsUniversal
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierWalkBridge
open RepairRepresentation RepairOrdinary CloseoutRawRows
open CloseoutRowsRawLogShape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem row_digit_fit {q : ℕ} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (gs : List (SupportedNormalizedGate q))
    (L den z ell childBits : ℕ) (P : StructuralGF2Polynomial)
    (hcount : P.length ≤ rowCountBase gs L den^z)
    (hdegree : RawMonomialDegreeAtMost (z*coordinateDegree gs L den) P)
    (hell : natBitLength (2*gs.length+1) ≤ ell)
    (hchildren : ∀ i : Fin (pool live gs).length,
      (ExtDecompositionBatch.children a ((pool live gs).get i)).length ≤ 2^childBits) :
    (lower a live gs P).length < 2^actualWidth gs L den z ell (childBits+1) := by
  let B := ell+coordinateLog (canonicalWalkLength den) (windowSum gs L) (rowDepth gs L) ell
  have hbase : rowCountBase gs L den ≤ 2^B := by
    have hlt : rowCountBase gs L den < 2^natBitLength (rowCountBase gs L den) := by
      simpa only [natBitLength] using
        Nat.lt_pow_succ_log_self (b := 2) (by decide) (rowCountBase gs L den)
    exact hlt.le.trans (Nat.pow_le_pow_right (by decide) (rowCount_log gs L den ell hell))
  have hP : P.length ≤ 2^(z*B) := by
    calc
      _ ≤ rowCountBase gs L den^z := hcount
      _ ≤ (2^B)^z := Nat.pow_le_pow_left hbase z
      _ = _ := by rw [←pow_mul,Nat.mul_comm]
  have h := lower_digit_fit a live gs (z*B) childBits (z*coordinateDegree gs L den)
    P hP hdegree hchildren
  have he : z*B+(childBits+1)*(z*coordinateDegree gs L den)+1 ≤
      actualWidth gs L den z ell (childBits+1) := by
    rw [coordinateDegree_eq]
    unfold actualWidth rowWidth B
    ring_nf
    omega
  exact h.trans_le (Nat.pow_le_pow_right (by decide) he)

end
end NearCubicWires.RepairSource.CloseoutRowsUniversal
