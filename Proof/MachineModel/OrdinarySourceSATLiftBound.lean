import Proof.MachineModel.OrdinarySourceSATLiftFinish

/-! A fixed cubic bound for all physical input preparation, source clocking,
query replacement and final framed output. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ledger (input : List Bool) (b : ℕ) :=
  prepareBudget input b+20*capacity b*(b+1)+4*b+7

def budget (input : List Bool) (b : ℕ) := 1099511627776*(b+input.length+1)^3

theorem ledger_bound (input : List Bool) (b : ℕ) : ledger input b ≤ budget input b := by
  let M := b+input.length+1
  let X := M^3
  have hm : 0<M := by dsimp [M]; omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ hm
  have hM : M ≤ X := by
    have h := Nat.pow_le_pow_right hm (by decide : 1 ≤ 3)
    simpa only [pow_one] using h
  have hb : b ≤ X := (show b ≤ M by dsimp [M]; omega).trans hM
  have hn : input.length ≤ X := (show input.length ≤ M by dsimp [M]; omega).trans hM
  have hp : (b+1)^3 ≤ X := Nat.pow_le_pow_left (by dsimp [M]; omega) 3
  have hp2 : (b+2)^3 ≤ 8*X := by
    have h := Nat.pow_le_pow_left (show b+2 ≤ 2*M by dsimp [M]; omega) 3
    simpa only [Nat.mul_pow,show (2 : ℕ)^3=8 from rfl] using h
  have hc := DimensionPower.cost_bound 2 268435456 (b+1) 2 le_rfl
  change DimensionPower.cost 268435456 (b+1) 2 ≤
    2*268435456+2+2*(6*268435456*(b+2)^3+7) at hc
  have hpair := Nat.mul_le_mul_left (12*268435456) hp2
  have hcap : 20*capacity b*(b+1) ≤ 20*268435456*X := by
    calc
      _ = 20*268435456*(b+1)^3 := by unfold capacity; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hp
  have hconst := Nat.mul_le_mul_left (2*268435456+57) hX
  unfold ledger prepareBudget parseBudget PCPSerializerCapacity.Power.budget budget
  rw [boundInput_length]
  change 4*(2*input.length+2*b+2)+4*input.length+8*b+16+
    (2*b+9+DimensionPower.cost 268435456 (b+1) 2)+1+
    20*capacity b*(b+1)+4*b+7 ≤ 1099511627776*X
  omega

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
