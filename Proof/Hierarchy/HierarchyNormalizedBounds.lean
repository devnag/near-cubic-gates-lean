import Proof.Hierarchy.HierarchyNormalizedBoundsLedger

/-! The whole literal normalized-PCP budget, including its ordinary input
framing, has one source-fixed input exponent before selecting the hierarchy.
One coefficient covers runtime, proof length and query count simultaneously. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalizedBounds
open RepairOrdinary HierarchySourceScales
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def inputExponent := HierarchyStreamCost.inputExponent source*60
def logExponent := HierarchyStreamCost.logExponent source*60
def coefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  HierarchyStreamCost.coefficient source H Cpad+
    serializerCoefficient*(HierarchyStreamCost.resourceCoefficient source H Cpad+1)^60+
    HierarchyProjection.proofCoefficient source H Cpad+source.coefficient+1

theorem coefficient_positive {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :
    0<coefficient source H Cpad := by unfold coefficient; omega

theorem proof_coefficient_le {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :
    HierarchyProjection.proofCoefficient source H Cpad ≤ coefficient source H Cpad := by
  unfold coefficient
  omega

theorem source_coefficient_le {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :
    source.coefficient ≤ coefficient source H Cpad := by unfold coefficient; omega

theorem budget_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    framedBudget source H Cpad r ≤ coefficient source H Cpad*(r.1+1)^inputExponent source*
      (natBitLength (H.time r.1)+1)^logExponent source := by
  let X := r.1+1
  let Z := natBitLength (H.time r.1)+1
  let a := inputExponent source
  let g := logExponent source
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hZ : 1 ≤ Z := by dsimp [Z]; omega
  have hp := HierarchyStreamCost.budget_bound source H Cpad hcoeff hpad r
  have hm : X^HierarchyStreamCost.inputExponent source*Z^HierarchyStreamCost.logExponent source ≤ X^a*Z^g :=
    monomial_le X Z a g (HierarchyStreamCost.inputExponent source) (HierarchyStreamCost.logExponent source)
      hX hZ (by dsimp [a,inputExponent]; omega) (by dsimp [g,logExponent]; omega)
  have hp' : HierarchyStreamCost.framedBudget source H Cpad r ≤ 
      HierarchyStreamCost.coefficient source H Cpad*X^a*Z^g := by
    exact hp.trans (by simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_left (HierarchyStreamCost.coefficient source H Cpad) hm)
  have hr := HierarchyStreamCost.polynomial_resource_bound source H Cpad hcoeff hpad r serializerCoefficient 60
  have hs := framed_serialization_bound source H Cpad hpad r
  calc
    _ ≤ HierarchyStreamCost.framedBudget source H Cpad r+
        serializerCoefficient*(Streams.resource (source.output (HierarchyEncode.encode H Cpad r))
          (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1)+1)^60 := hs
    _ ≤ HierarchyStreamCost.coefficient source H Cpad*X^a*Z^g+
        (serializerCoefficient*(HierarchyStreamCost.resourceCoefficient source H Cpad+1)^60)*X^a*Z^g :=
      Nat.add_le_add hp' hr
    _=(HierarchyStreamCost.coefficient source H Cpad+
        serializerCoefficient*(HierarchyStreamCost.resourceCoefficient source H Cpad+1)^60)*X^a*Z^g := by ring
    _ ≤ coefficient source H Cpad*X^a*Z^g := by
      gcongr
      unfold coefficient
      omega

theorem raw_budget_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    HierarchyNormalized.budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) ≤ 
      coefficient source H Cpad*(r.1+1)^inputExponent source*(natBitLength (H.time r.1)+1)^logExponent source := by
  have hb := budget_bound source H Cpad hcoeff hpad r
  unfold framedBudget at hb
  omega

theorem proof_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (n : ℕ) :
    2^HierarchyProjection.width source H Cpad n ≤ coefficient source H Cpad*H.time n*
      logScale (H.time n)^(5+source.degrees.proofLog) := by
  exact (HierarchyProjection.proof_bound source H Cpad hcoeff hpad n).trans (by
    gcongr
    exact proof_coefficient_le source H Cpad)

theorem query_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad n : ℕ) :
    HierarchyProjection.queries source H Cpad n ≤ 
      coefficient source H Cpad*(HierarchyProjection.width source H Cpad n+1)^source.degrees.queries := by
  exact (HierarchyProjection.query_bound source H Cpad n).trans (by
    gcongr
    exact source_coefficient_le source H Cpad)

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalizedBounds
