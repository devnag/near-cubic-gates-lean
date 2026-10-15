import Proof.PCP.PCPPSubstitutionRequest
import Proof.Foundations.RecoveryCaseOne

/-! Paper C.10's short witness-family and clause counts. These bounds use
the actual compact substituted circuit and the same pointwise source;
no polynomial in the original hierarchy input is renamed polynomial in q. -/
namespace NearCubicWires.RepairSource.CloseoutSourceCounts
open SourceInterfaces RepairRepresentation RepairOrdinary PCPPSubstitution PCPPRequestBoundary
open RecoveryScheduleEnvelope PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_counts (a : PointwisePCPPAlgorithm) {n r Q : Nat}
    (oracle : BooleanCircuit n) (projections : Fin Q→Fin n→ProjectedRandomBit r)
    (formula : ThreeCNF Q) :
    let p:=a.output (sourceRequest a oracle projections formula)
    p.systematicBits+p.auxiliaryBits ≤ 2*a.coefficient*(requestParameter a r Q oracle.size+1)^a.degree ∧
      2^p.clauseBits ≤ a.coefficient*(requestParameter a r Q oracle.size+1)^a.degree := by
  let request:=sourceRequest a oracle projections formula
  have hsub:=compactSubstituted_size oracle projections formula
  have hsize : request.circuit.size ≤ requestParameter a r Q oracle.size := by
    change (PCPPRequestBoundary.request a (compactSubstituted oracle projections formula)).circuit.size ≤ _
    rw [request_size]
    unfold requestParameter
    omega
  have harity : request.arity ≤ requestParameter a r Q oracle.size := by
    change domain a r ≤ _
    unfold requestParameter
    omega
  have hs:=(a.systematicBound request).trans (Nat.mul_le_mul_left a.coefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right harity 1) a.degree))
  have ha:=(a.auxiliaryBound request).trans (Nat.mul_le_mul_left a.coefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) a.degree))
  have hc:=(a.clauseCountBound request).trans (Nat.mul_le_mul_left a.coefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) a.degree))
  refine ⟨?_,hc⟩
  calc
    _ ≤ a.coefficient*(requestParameter a r Q oracle.size+1)^a.degree+
        a.coefficient*(requestParameter a r Q oracle.size+1)^a.degree := Nat.add_le_add hs ha
    _ = _ := by ring

def shortRequest (a : PointwisePCPPAlgorithm) (queryCoefficient queryDegree oracleDegree q : Nat) :=
  requestParameter a q (queryCoefficient*(q+1)^queryDegree) (oracleSizeBound oracleDegree q)

def shortBound (a : PointwisePCPPAlgorithm) (queryCoefficient queryDegree oracleDegree q : Nat) :=
  2*a.coefficient*(shortRequest a queryCoefficient queryDegree oracleDegree q+1)^a.degree

theorem shortRequest_polynomial (a : PointwisePCPPAlgorithm) (queryCoefficient queryDegree oracleDegree : Nat) :
    PolynomiallyBounded (shortRequest a queryCoefficient queryDegree oracleDegree) := by
  have hone:=polynomiallyBounded_constant 1
  have htwo:=polynomiallyBounded_constant 2
  have hq:=polynomiallyBounded_mul (polynomiallyBounded_constant queryCoefficient)
    (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id hone) queryDegree)
  have ho:=oracleSizeBound_polynomiallyBounded oracleDegree
  have hd:=polynomiallyBounded_max polynomiallyBounded_id (polynomiallyBounded_constant a.minimumArity)
  exact polynomiallyBounded_add
    (polynomiallyBounded_add
      (polynomiallyBounded_add
        (polynomiallyBounded_mul hq (polynomiallyBounded_add (polynomiallyBounded_mul htwo ho) hone))
        (polynomiallyBounded_mul (polynomiallyBounded_constant 3)
          (polynomiallyBounded_pow (polynomiallyBounded_mul htwo hq) 3)))
      (polynomiallyBounded_mul htwo hd))
    (polynomiallyBounded_constant 5)

theorem shortBound_polynomial (a : PointwisePCPPAlgorithm) (queryCoefficient queryDegree oracleDegree : Nat) :
    PolynomiallyBounded (shortBound a queryCoefficient queryDegree oracleDegree) :=
  polynomiallyBounded_mul (polynomiallyBounded_constant (2*a.coefficient))
    (polynomiallyBounded_pow (polynomiallyBounded_add
      (shortRequest_polynomial a queryCoefficient queryDegree oracleDegree)
      (polynomiallyBounded_constant 1)) a.degree)

theorem short_counts (a : PointwisePCPPAlgorithm) {n r Q : Nat}
    (oracle : BooleanCircuit n) (projections : Fin Q→Fin n→ProjectedRandomBit r)
    (formula : ThreeCNF Q) (queryCoefficient queryDegree oracleDegree : Nat)
    (hq : Q ≤ queryCoefficient*(r+1)^queryDegree)
    (ho : oracle.size ≤ oracleSizeBound oracleDegree r) :
    let p:=a.output (sourceRequest a oracle projections formula)
    p.systematicBits+p.auxiliaryBits ≤ shortBound a queryCoefficient queryDegree oracleDegree r ∧
      2^p.clauseBits ≤ shortBound a queryCoefficient queryDegree oracleDegree r := by
  obtain ⟨hv,hc⟩:=source_counts a oracle projections formula
  have hp : requestParameter a r Q oracle.size ≤ shortRequest a queryCoefficient queryDegree oracleDegree r := by
    unfold shortRequest requestParameter
    gcongr
  have hpow:=Nat.pow_le_pow_left (Nat.add_le_add_right hp 1) a.degree
  refine ⟨hv.trans (Nat.mul_le_mul_left (2*a.coefficient) hpow),?_⟩
  have hm:=(hc.trans (Nat.mul_le_mul_left a.coefficient hpow))
  exact hm.trans (Nat.mul_le_mul_right _ (by omega : a.coefficient ≤ 2*a.coefficient))

end NearCubicWires.RepairSource.CloseoutSourceCounts
