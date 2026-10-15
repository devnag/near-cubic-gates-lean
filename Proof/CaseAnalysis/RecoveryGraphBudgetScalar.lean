import Proof.CaseAnalysis.RecoveryGraphBudgetScalarArithmetic

/-! Scalar C.12 envelopes in the actual paid W. These bounds are later
transported along W≤C*(2^n+1)^E, never along an exponential in refuter N. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
open RepairSource ProjectionNormalization RecoveryTseitinNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def formulaCoefficient : ℕ := 10000000000000000
def serializerCoefficient : ℕ := 6*formulaCoefficient+8+1000000000064*(formulaCoefficient+1)^12

theorem cold_scalar (arity count W : ℕ) (ha : arity ≤ W) (hc : count ≤ W) :
    Cold.budget arity count ≤ formulaCoefficient*(W+1)^4 := by
  have hp3 := Nat.pow_le_pow_left (show arity+count+1 ≤ 2*(W+1) by omega) 3
  have hp4 := Nat.pow_le_pow_left (show arity+count+2 ≤ 2*(W+1) by omega) 4
  norm_num only [Nat.mul_pow,Nat.reducePow] at hp3 hp4
  have hcap : Reuse.capacity arity count ≤ 17592186044416*(W+1)^3 := by
    unfold Reuse.capacity
    omega
  have hcost := DimensionPower.cost_bound 3 2199023255552 (arity+count+1) 3 le_rfl
  change DimensionPower.cost 2199023255552 (arity+count+1) 3 ≤
    2*2199023255552+2+3*(6*2199023255552*(arity+count+2)^4+7) at hcost
  have htaut := RecoveryTseitinTautology.Cold.budget_bound arity
  have htautpow := Nat.pow_le_pow_left (Nat.add_le_add_right ha 1) 3
  have hfold := Nat.mul_le_mul hc (Nat.add_le_add_right (Nat.mul_le_mul_left 6 hcap) 14)
  have hbits : Assertion.bits.length ≤ 100 := by decide
  unfold Cold.budget Cold.wholeBudget Cold.prefixBudget Cold.driversBudget
    PCPSerializerCapacity.Power.budget Counter.budget Cold.tautBudget
    Formula.budget Reuse.stepBudget Assertion.budget formulaCoefficient
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4)]

theorem serializer_scalar {arity : ℕ} (c : BooleanCircuit arity) (W : ℕ)
    (ha : arity ≤ W) (hc : c.nodes.length ≤ W) :
    Serialize.budget c ≤ serializerCoefficient*(W+1)^48 :=
  serializer_arithmetic (Cold.budget arity c.nodes.length) formulaCoefficient (W+1)
    (Serialize.budget c) (by omega) (cold_scalar arity c.nodes.length W ha hc) (serialize_budget c)

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
