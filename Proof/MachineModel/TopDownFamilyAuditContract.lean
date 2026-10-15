import Proof.MachineModel.ClosureBinaryPreparedPayload

/-! Minimal semantic row descriptors and the actual uniform output width.
This defines no encoded source, producer, enumeration, mask or reusable bank.
Those remain the whole transaction's physical obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownFamilyShape
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierEstimator
open RepairSource CloseoutFinal CanonicalFourfoldRowProgram ThresholdCompiler
open CompetitorSelectedCount P1Closure

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2=liveᶜ.card) (w degree : Nat)

/-- Only mathematical row data. None of these fields supplies physical words. -/
structure Descriptor where
  polynomial : StructuralGF2Polynomial
  monomials_fit : (CloseoutRowsUniversal.lower a live occ polynomial).length<2^w
  degree_fit : CloseoutRawRows.RawMonomialDegreeAtMost degree polynomial
  select : Fin (2^((s+1)/2)) → Fin (2^((s+1)/2)) → Bool

noncomputable def commonWidth : Nat :=
  (live.card+1)+(2*((s+1)/2)+
    2*(CompactBounds.radix a live occ*
      (min degree (BinaryPool.pool a live occ s harity).length*(live.card+1))+
      (live.card+1)+1)+4)

attribute [local irreducible] BinaryPool.pool CompactBounds.radix

theorem width_eq (P : StructuralGF2Polynomial) (hs : 67 ≤ s)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length<2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P) :
    scalarWidth (EquationRow.request
      (P1Closure.BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree))
      (live.card+1)=commonWidth a live occ s harity degree := by
  rw [scalarWidth,extraWidth_eq]
  rfl

theorem width_independent (P P' : StructuralGF2Polynomial) (hs : 67 ≤ s)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length<2^w)
    (hmon' : (CloseoutRowsUniversal.lower a live occ P').length<2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P)
    (hdegree' : CloseoutRawRows.RawMonomialDegreeAtMost degree P') :
    scalarWidth (EquationRow.request
      (P1Closure.BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree))
      (live.card+1)=
    scalarWidth (EquationRow.request
      (P1Closure.BinaryRequest.input a live occ s harity P' w degree hs hmon' hpos hload hdegree'))
      (live.card+1) :=
  (width_eq a live occ s harity w degree P hs hmon hpos hload hdegree).trans
    (width_eq a live occ s harity w degree P' hs hmon' hpos hload hdegree').symm

end NearCubicWires.P1TopDownFamilyShape
