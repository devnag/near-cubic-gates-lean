import Proof.MachineModel.TopDownPaidReusableFamily
import Proof.MachineModel.TopDownFamilyAuditContract

/-! Actual binary-order C.10 requests instantiate the reusable callback.
Value bounds and count congruence are the accepted source theorems; the
uniform printed width is the existing family contract's commonWidth. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler SourceInterfaces
open RepairSource CloseoutFinal
attribute [local irreducible] BinaryPool.pool CompactBounds.radix

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2=liveᶜ.card) (w degree : Nat)
  (hs : 67 ≤ s) (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)

noncomputable def binaryDatum (d : P1TopDownFamilyShape.Descriptor a live occ s w degree) (C : Nat) : Datum where
  row:=BinaryRequest.input a live occ s harity d.polynomial w degree hs d.monomials_fit hpos hload d.degree_fit
  C:=C
  Q:=live.card+1
  f:=C10SupplierTable.table a live occ s harity d.polynomial w hs d.monomials_fit hpos hload
  select:=d.select

theorem binary_valid (printer : WilliamsAlgorithm)
    (d : P1TopDownFamilyShape.Descriptor a live occ s w degree) (C B R S : Nat)
    (hC : (Header.stream (binaryDatum a live occ s harity w degree hs hpos hload d C).row).length≤C)
    (hR : P1TopDownPaidReloadCore.fuel printer
      (binaryDatum a live occ s harity w degree hs hpos hload d C).row C (live.card+1)≤R)
    (hB : RowPayload.budget (scalarWidth (EquationRow.request
      (binaryDatum a live occ s harity w degree hs hpos hload d C).row) (live.card+1))≤B)
    (hBR : B+1≤R)
    (hS : P1TopDownPaidReloadCore.budget printer
      (binaryDatum a live occ s harity w degree hs hpos hload d C).row C (live.card+1) B+1≤S)
    (hBS : B≤S) : Valid printer B R S (binaryDatum a live occ s harity w degree hs hpos hload d C) := by
  refine ⟨hC,?_,?_,?_,hR,hB,hBR,hS,hBS⟩
  · change live.card+1 ≤ CompactBounds.radix a live occ*
      ((min degree (BinaryPool.pool a live occ s harity).length)*(live.card+1))+(live.card+1)+1
    omega
  · exact C10SupplierTable.table_lt a live occ s harity d.polynomial w hs d.monomials_fit hpos hload
  · intro i
    exact BinaryRequest.table_modEq a live occ s harity d.polynomial w degree hs d.monomials_fit
      hpos hload d.degree_fit i.divNat i.modNat

theorem binary_emit (d : P1TopDownFamilyShape.Descriptor a live occ s w degree) (C : Nat) :
    (binaryDatum a live occ s harity w degree hs hpos hload d C).emit=
      SignedSortKey.binary (P1TopDownFamilyShape.commonWidth a live occ s harity degree)
        (selected (CompetitorSelectedCells.cells (decide (s%2=1))
          (C10SupplierTable.table a live occ s harity d.polynomial w hs d.monomials_fit hpos hload)
          d.select)).sum := by
  dsimp only [Datum.emit,binaryDatum]
  erw [P1TopDownFamilyShape.width_eq a live occ s harity w degree d.polynomial hs
    d.monomials_fit hpos hload d.degree_fit]
  rfl

end NearCubicWires.P1TopDownPaidReusable
