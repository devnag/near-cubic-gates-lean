import Proof.MachineModel.TopDownPaidReusableReserves
import Proof.MachineModel.TopDownPaidFamilyConsumers
import Proof.MachineModel.ClosureBinaryHeaderCapacity
import Proof.MachineModel.ClosureBinaryPreparedCostLoad
import Proof.MachineModel.ClosureBinaryRowCost

/-! One explicit reserve for every actual binary request in a family. Existing
header production and original-degree driver estimates discharge the capacities.
These arithmetic facts leave the physical source/template production visible. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidBinaryReserves
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler SourceInterfaces
open RepairSource CloseoutFinal P1TopDownPaidReusable P1TopDownPaidReusableReserves
attribute [local irreducible] BinaryPool.pool CompactBounds.radix

def headerCapacity (q s c e : Nat) : Nat :=
  (2^230*(c+5)^88)*(q+1)^((e+1)*88)*2^(s/8)+1
noncomputable def driverCapacity (printer : WilliamsAlgorithm) (q s c e : Nat) : Nat :=
  64*(headerCapacity q s c e+1)+2^21*(c+4)^3*(q+1)^((e+2)*3)*2^(s/32)+
    CompactCost.tableCoefficient printer c*
      (2^s*(q+1)^((e+2)*CompetitorCrossScheduler.exponent printer))

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2=liveᶜ.card) (w degree : Nat)
  (hs : 67  ≤  s) (hpos : 1  ≤  w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)

theorem binary_physical (printer : WilliamsAlgorithm)
    (d : P1TopDownFamilyShape.Descriptor a live occ s w degree) (c e : Nat)
    (hcache : CompactBounds.radix a live occ ≤ c*(q+1)^e) (hdegree : degree ≤ q+1) :
    let V:=driverCapacity printer q s c e
    PhysicalBounds printer (buffer V) (rewind printer V) (workspace printer V)
      (binaryDatum a live occ s harity w degree hs hpos hload d (headerCapacity q s c e)) := by
  dsimp only
  let row:=BinaryRequest.input a live occ s harity d.polynomial w degree hs
    d.monomials_fit hpos hload d.degree_fit
  have hraw:=BinaryPreparedCost.lower_stream_bound a live occ d.polynomial
    (c*(q+1)^e) degree w hcache d.degree_fit d.monomials_fit
  have hheader:=BinaryHeaderCapacity.header_length a live occ s harity d.polynomial
    w degree (BinaryPreparedCost.rawBound (c*(q+1)^e) degree live.card w)
    hs d.monomials_fit hpos hload d.degree_fit hraw
  have hprep:=BinaryPreparedCost.budget_polynomial a live occ s harity d.polynomial
    degree w c e hcache d.degree_fit hdegree d.monomials_fit hload
  have hC : (Header.stream row).length ≤ headerCapacity q s c e :=
    hheader.trans (Nat.add_le_add_right hprep 1)
  have hQ : live.card+1 ≤ (EquationRow.request row).p := by
    change live.card+1 ≤ CompactBounds.radix a live occ*
      (min degree (BinaryPool.pool a live occ s harity).length*(live.card+1))+(live.card+1)+1
    omega
  have hD:=BinaryRowCost.driver_bound a printer live occ s harity d.polynomial w degree
    hs d.monomials_fit hpos hload d.degree_fit (headerCapacity q s c e) c e hcache hdegree
  obtain ⟨hR,hB,hBR,hS,hBS⟩:=capacities printer row (headerCapacity q s c e) (live.card+1)
    (driverCapacity printer q s c e) hC hQ hD
  exact ⟨hC,hR,hB,hBR,hS,hBS⟩

/-- Complete transaction accounting, before external-row multiplication.
The two preparation powers remain additive to the single residual table. -/
theorem row_budget_bound (printer : WilliamsAlgorithm) (q s c e : Nat) :
    (3*P1TopDownPaidPayload.tapes printer+6)*
      (workspace printer (driverCapacity printer q s c e)+1)  ≤ 
    ((3*P1TopDownPaidPayload.tapes printer+6)*(2*coefficient printer+21))*
      (64*(headerCapacity q s c e+1)+
       2^21*(c+4)^3*(q+1)^((e+2)*3)*2^(s/32)+1)+
    (((3*P1TopDownPaidPayload.tapes printer+6)*(2*coefficient printer+21))*
      CompactCost.tableCoefficient printer c)*
      (2^s*(q+1)^((e+2)*CompetitorCrossScheduler.exponent printer)) := by
  unfold workspace driverCapacity
  nlinarith only [Nat.zero_le (64*(headerCapacity q s c e+1)+
    2^21*(c+4)^3*(q+1)^((e+2)*3)*2^(s/32)+
    CompactCost.tableCoefficient printer c*
      (2^s*(q+1)^((e+2)*CompetitorCrossScheduler.exponent printer)))]

end NearCubicWires.P1TopDownPaidBinaryReserves
