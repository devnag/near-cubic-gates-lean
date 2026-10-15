import Proof.CaseAnalysis.RecoveryGraphBudgetScalar
import Proof.CaseAnalysis.RecoveryGraphBudgetScalarCount

/-! Add the actual original count compiler and graph serializer, in one
polynomial of the same paid W and original C.12 backing. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
open RepairSource.RecoveryTseitinNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def graphSerializerCoefficient : ℕ := 16*330000000066+2*serializerCoefficient+3
def wholeCoefficient : ℕ := 1000000000*330000000066+1+graphSerializerCoefficient

theorem original_scalar {arity : ℕ} (c : BooleanCircuit arity) (W : ℕ)
    (ha : arity ≤ W) (hc : c.nodes.length ≤ W) :
    RecoveryBoundedGraphSerialize.budget (scalarBacking W) c ≤
      graphSerializerCoefficient*(W+1)^48 := by
  have fits := serializer_fits c W (scalarSupport W) ha hc
  have h := RecoveryBoundedGraphSerialize.budget_le (scalarBacking W) c fits.2.1 fits.2.2
  have hs := serializer_scalar c W ha hc
  have hpow : (W+1)^6 ≤ (W+1)^48 := Nat.pow_le_pow_right (by omega) (by decide)
  have hback := (scalar_backing W).trans (Nat.mul_le_mul_left 330000000066 hpow)
  have hu : 1 ≤ (W+1)^48 := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 16*(scalarBacking W+2)+2*Serialize.budget c+3 := h
    _ ≤ 16*(330000000066*(W+1)^48)+2*(serializerCoefficient*(W+1)^48)+3*(W+1)^48 :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 16 hback) (Nat.mul_le_mul_left 2 hs))
        (by simpa using Nat.mul_le_mul_left 3 hu)
    _ = graphSerializerCoefficient*(W+1)^48 := by unfold graphSerializerCoefficient;ring

theorem whole_scalar {arity : ℕ} (c : BooleanCircuit arity) (W R bound : ℕ)
    (ha : arity ≤ W) (hc : c.nodes.length ≤ W)
    (hR : R ≤ W) (hb : bound ≤ W) (htwo : 2^R ≤ W) :
    RecoveryBoundedCountUniform.compiledBudget (scalarBacking W) W R bound+1+
      RecoveryBoundedGraphSerialize.budget (scalarBacking W) c ≤ wholeCoefficient*(W+1)^48 := by
  have hcount := compiled_paid_scalar W R bound hR hb htwo
  have hpow : (W+1)^10 ≤ (W+1)^48 := Nat.pow_le_pow_right (by omega) (by decide)
  have hs := hcount.trans (Nat.mul_le_mul_left (1000000000*330000000066) hpow)
  have hg := original_scalar c W ha hc
  have hu : 1 ≤ (W+1)^48 := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ (1000000000*330000000066)*(W+1)^48+(W+1)^48+graphSerializerCoefficient*(W+1)^48 :=
      Nat.add_le_add (Nat.add_le_add hs hu) hg
    _ = wholeCoefficient*(W+1)^48 := by unfold wholeCoefficient;ring

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
