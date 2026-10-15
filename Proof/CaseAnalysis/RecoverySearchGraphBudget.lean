import Proof.CaseAnalysis.RecoverySearchGraphDock
import Proof.CaseAnalysis.RecoveryGraphBudgetScalar

/-! Bound the actual search request from the existing serializer's fresh
output tape. No separate encoded-formula size analysis or prepass is used. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearchExecution
open LocalBitMultitape RepairOrdinary BalancedCNFSATEncoding
open RecoveryTseitinNative RecoveryBoundedGraphBudget
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem payload_bits_bound {arity : Nat} (c : BooleanCircuit arity) :
    (balancedCNFPayload (CircuitInputCNF.circuitInputFormula c)).bits.length ≤ Serialize.budget c := by
  obtain ⟨r,hr,ht,hs⟩:=Serialize.serialize_run c
  have h:=DecompositionSource.one_tape_support Serialize.machine _ _ r 1504 0 hr
    (by rfl) (by rfl)
  rw [ht,Nat.zero_add,frame_length] at h
  omega

theorem radius_bound {arity : Nat} (c : BooleanCircuit arity) (W : Nat)
    (ha : arity ≤ W) (hc : c.nodes.length ≤ W) :
    RecoveryPrefixCold.radius (balancedCNFPayload (CircuitInputCNF.circuitInputFormula c)) arity ≤
      (serializerCoefficient+7)*(W+1)^48 := by
  have hp:=(payload_bits_bound c).trans (serializer_scalar c W ha hc)
  have hw : W+1 ≤ (W+1)^48:=Nat.le_self_pow (by decide) (W+1)
  have h1 : 1 ≤ (W+1)^48:=Nat.one_le_pow _ _ (by omega)
  unfold RecoveryPrefixCold.radius
  nlinarith

def graphSearchCoefficient : Nat:=1099511627776*(serializerCoefficient+7)^3

private theorem cubic_product (K W : Nat) :
    1099511627776*((K+7)*(W+1)^48)^3=
      (1099511627776*(K+7)^3)*(W+1)^144 := by
  rw [Nat.mul_pow,←Nat.pow_mul,Nat.mul_assoc]

theorem graph_budget_bound {arity : Nat} (c : BooleanCircuit arity) (W : Nat)
    (ha : arity ≤ W) (hc : c.nodes.length ≤ W) :
    RecoveryBoundedSearch.fullBudget 1073741824
      (balancedCNFPayload (CircuitInputCNF.circuitInputFormula c)) arity ≤
      graphSearchCoefficient*(W+1)^144 := by
  have h:=Nat.mul_le_mul_left 1099511627776 (Nat.pow_le_pow_left (radius_bound c W ha hc) 3)
  have he : 1099511627776*((serializerCoefficient+7)*(W+1)^48)^3=
      graphSearchCoefficient*(W+1)^144 := by
    exact cubic_product serializerCoefficient W
  exact (RecoveryBoundedSearch.full_budget_bound _ _).trans (h.trans_eq he)

end NearCubicWires.RepairSource.RecoveryBoundedSearchExecution
