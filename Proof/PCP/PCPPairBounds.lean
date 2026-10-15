import Proof.Hierarchy.HierarchyBinaryMultiply
import Proof.Hierarchy.CompetitorSignedDecision

/-! Width for an actual pairing of two binary fields. The factor keeps
its original field length: the multiplier's stronger shifted-input bound
is proved here and is not replaced by mere product-fit. -/
namespace NearCubicWires.RepairOrdinary.PCPPair
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (left right : List Bool) := 2*(left.length+right.length+1)

theorem width_power (left right : List Bool) :
    2^width left right=4*(2^(left.length+right.length))^2 := by
  calc 2^width left right=2^(left.length+right.length+1)*2^(left.length+right.length+1) := by
         rw [←pow_add]
         congr 1
         dsimp [width]
         omega
       _=4*(2^(left.length+right.length))^2 := by rw [pow_succ]; ring

theorem field_bounds (left right : List Bool) :
    value left<2^(left.length+right.length) ∧ value right<2^(left.length+right.length) := by
  exact ⟨(value_lt left).trans_le (Nat.pow_le_pow_right (by decide) (by omega)),
    (value_lt right).trans_le (Nat.pow_le_pow_right (by decide) (by omega))⟩

theorem square_bounds (left right : List Bool) :
    value left*2^left.length<2^width left right ∧
    value right*2^right.length<2^width left right ∧
    value left*value left+value left+value right<2^width left right ∧
    value right*value right+value right+value left<2^width left right := by
  obtain ⟨ha,hb⟩ := field_bounds left right
  have hp : 1≤2^(left.length+right.length) := Nat.one_le_pow _ _ (by decide)
  have hl : 2^left.length≤2^(left.length+right.length) := Nat.pow_le_pow_right (by decide) (by omega)
  have hr : 2^right.length≤2^(left.length+right.length) := Nat.pow_le_pow_right (by decide) (by omega)
  have hla := Nat.mul_le_mul ha.le hl
  have hra := Nat.mul_le_mul hb.le hr
  have hls := Nat.mul_le_mul ha.le ha.le
  have hrs := Nat.mul_le_mul hb.le hb.le
  rw [width_power]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem pair_formula (a b : ℕ) : Nat.pair a b=if b≤a then a*a+a+b else b*b+a := by
  unfold Nat.pair
  split_ifs <;> omega

theorem pair_bound (left right : List Bool) : Nat.pair (value left) (value right)<2^width left right := by
  have h := square_bounds left right
  rw [pair_formula]
  split <;> omega

end NearCubicWires.RepairOrdinary.PCPPair
