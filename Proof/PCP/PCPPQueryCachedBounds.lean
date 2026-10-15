import Proof.PCP.PCPPQuerySupportEndpoint
import Proof.PCP.PCPPQueryClauseEndpoint
import Proof.PCP.PCPPQueryBounds

/-! A single explicit polynomial capacity for repeated local queries on the
same cached PCPP object. The constructor is never called by these readers. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryCachedBounds
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
  RecoveryWitnessPolicy PolynomialSchedule ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def degree (a : PointwisePCPPAlgorithm) := 2*max 10 a.degree
def coefficient (a : PointwisePCPPAlgorithm) := 10000*(a.coefficient+131084)^2+1
def capacity (a : PointwisePCPPAlgorithm) (n : ℕ) := coefficient a*(n+1)^(degree a)
def callBudget (a : PointwisePCPPAlgorithm) (n : ℕ) := 4*capacity a n+7

theorem code_bound (n : ℕ) :
    canonicalBooleanCircuitCodeBitBound (n+1) ≤ 131072*(n+1)^10 := by
  simp only [canonicalBooleanCircuitCodeBitBound,canonicalBooleanNodeCodeBitBound,
    canonicalBalancedCodeBitBound,canonicalNatCodeBitBound,CanonicalBinary.encodeNatBitsBound,taggedListBitBound]
  ring_nf
  omega

theorem majorant_bound (a : PointwisePCPPAlgorithm) (n : ℕ) :
    PCPPQueryBounds.majorant a n+1 ≤ capacity a n := by
  let D := max 10 a.degree
  let X := (n+1)^D
  have hpos : 1≤X := Nat.one_le_pow _ _ (by omega)
  have hn : n+1≤X := by
    have h := Nat.pow_le_pow_right (show 0<n+1 by omega) (show 1≤D by dsimp [D]; omega)
    simpa only [pow_one] using h
  have hcode : canonicalBooleanCircuitCodeBitBound (n+1)≤131072*X :=
    (code_bound n).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (show 10≤D by exact le_max_left _ _)))
  have hsource : a.coefficient*(n+1)^a.degree≤a.coefficient*X :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (show a.degree≤D by exact le_max_right _ _))
  have hs : PCPPQueryBounds.scalar a n+1≤(a.coefficient+131084)*X := by
    unfold PCPPQueryBounds.scalar
    nlinarith
  have hsq := Nat.pow_le_pow_left hs 2
  have hid : ((n+1)^D)^2=(n+1)^(degree a) := by
    rw [← pow_mul]
    congr 1
    dsimp [D,degree]
    omega
  change 10000*(PCPPQueryBounds.scalar a n+1)^2+1≤_
  unfold capacity coefficient
  rw [mul_pow] at hsq
  change _≤(a.coefficient+131084)^2*((n+1)^D)^2 at hsq
  rw [hid] at hsq
  have hx : 1≤(n+1)^(degree a) := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem coefficient_pos (a : PointwisePCPPAlgorithm) : 0<coefficient a := by
  unfold coefficient
  omega

theorem support_capacity (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (a.output r).systematicBits) :
    PCPPQuerySupportReset.cost r (a.output r) i+1≤capacity a (r.circuit.size+r.arity) := by
  have h := PCPPQueryBounds.support_bound a r i
  have hc := majorant_bound a (r.circuit.size+r.arity)
  change PCPPQuerySupport.budget _ _ _ _ _+1≤_
  omega

theorem clause_capacity (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (2^(a.output r).clauseBits)) :
    PCPPQueryClause.queryBudget r (a.output r) i+1≤capacity a (r.circuit.size+r.arity) := by
  have h := PCPPQueryBounds.clause_bound a r i
  have hc := majorant_bound a (r.circuit.size+r.arity)
  omega

end NearCubicWires.RepairOrdinary.PCPPQueryCachedBounds
