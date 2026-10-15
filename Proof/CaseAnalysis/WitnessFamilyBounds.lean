import Proof.CaseAnalysis.WitnessAliases

/-! Every family index comes from the same substituted request. The variable
count is polynomial in its compact size, with no source-word-size factor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness
open RepairRepresentation SourceInterfaces PCPPRequestBoundary
open CanonicalBinary CanonicalWitnessCodec SupplierPipeline RecoveryWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceVariableCount (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :=
  (a.output r).systematicBits + (a.output r).auxiliaryBits

theorem sourceVariableCount_bound (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :
    sourceVariableCount a r ≤ 2*a.coefficient*(r.circuit.size+1)^a.degree := by
  have hs := (a.systematicBound r).trans
    (Nat.mul_le_mul_left a.coefficient (Nat.pow_le_pow_left (Nat.add_le_add_right r.sizeLarge 1) a.degree))
  have ha := a.auxiliaryBound r
  unfold sourceVariableCount
  rw [mul_assoc, two_mul]
  omega

theorem substituted_variable_count (a : PointwisePCPPAlgorithm) {n r q : ℕ}
    (oracle : BooleanCircuit n) (projections : Fin q → Fin n → ProjectedRandomBit r)
    (formula : ThreeCNF q) :
    sourceVariableCount a (PCPPSubstitution.sourceRequest a oracle projections formula) ≤
      2*a.coefficient*(PCPPSubstitution.requestParameter a r q oracle.size+1)^a.degree := by
  apply (sourceVariableCount_bound a _).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have hs := PCPPSubstitution.compactSubstituted_size oracle projections formula
  unfold PCPPSubstitution.sourceRequest
  rw [request_size]
  unfold PCPPSubstitution.requestParameter
  omega

theorem source_family_code_bound {Circuit : SupplierPipeline.CircuitFamily}
    {wires description : {n : ℕ} → Circuit n → ℕ} {limits : LegalSumLimits}
    (codec : CanonicalCircuitCodec Circuit) (a : PointwisePCPPAlgorithm)
    (r : PCPPRequest a.minimumArity)
    (family : SumFamily Circuit wires description limits (sourceVariableCount a r)) (bits : ℕ)
    (hbits : ∀ s ∈ family.sums, natBitLength (s.code codec) ≤ bits) :
    let V := 2*a.coefficient*(r.circuit.size+1)^a.degree
    natBitLength (family.code codec) ≤ 1+2*V^4*(V*bits+1) := by
  dsimp only
  apply (family.code_bits codec bits hbits).trans
  gcongr <;> exact sourceVariableCount_bound a r

end NearCubicWires.RepairOrdinary.CloseoutWitness
