import Proof.Hierarchy.HierarchyNormalizedReady
import Proof.Hierarchy.HierarchyEncodeReady

/-! Actual fixed-source normalized-PCP realization and its immediate
separated/outer consumers. Every constructor/resource field is supplied. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalized
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def realization {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) :
    NormalizedPCPRun source H (HierarchyEncode.encode H Cpad)
      (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
      (HierarchyProjection.width_fits source H Cpad hpad) (HierarchyProjection.queries_fit source H Cpad hpad)
      (HierarchyNormalizedBounds.inputExponent source) :=
  HierarchyEncode.normalizedRun source H Cpad hcoeff hpad
    (HierarchyNormalizedBounds.inputExponent source) (HierarchyNormalizedBounds.coefficient source H Cpad)
    (HierarchyNormalizedBounds.logExponent source) (HierarchyNormalizedBounds.coefficient_positive source H Cpad)
    (HierarchyNormalizedBounds.proof_coefficient_le source H Cpad)
    (HierarchyNormalizedBounds.source_coefficient_le source H Cpad)
    (boundedConstructor source H Cpad hcoeff hpad)

def separated {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) :
    SeparatedPCPResult H (HierarchyNormalizedBounds.inputExponent source) :=
  separated_of_normalizedRun source H (HierarchyEncode.encode H Cpad)
    (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
    (HierarchyProjection.width_fits source H Cpad hpad) (HierarchyProjection.queries_fit source H Cpad hpad)
    (HierarchyNormalizedBounds.inputExponent source) (realization source H Cpad hcoeff hpad)

def outer {k : ℕ} (joint : JointOrdinarySource (fun n => n^(k+2)))
    (Cpad : ℕ) (hcoeff : joint.hierarchy.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) :
    ChangedHierarchyOuterPCP joint (separated source joint.hierarchy Cpad hcoeff hpad).degrees :=
  outer_of_normalizedRun source joint (HierarchyEncode.encode joint.hierarchy Cpad)
    (HierarchyProjection.width source joint.hierarchy Cpad) (HierarchyProjection.queries source joint.hierarchy Cpad)
    (HierarchyProjection.width_fits source joint.hierarchy Cpad hpad)
    (HierarchyProjection.queries_fit source joint.hierarchy Cpad hpad)
    (HierarchyNormalizedBounds.inputExponent source) (realization source joint.hierarchy Cpad hcoeff hpad)

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalized
