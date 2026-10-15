import Proof.PCP.PCPPQueryCapacity

/-! One-time capacity preparation has fixed polynomial bit-time in the same
native size+arity parameter. No source call or row iteration is hidden here. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryCapacity
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def preparationCoefficient (D K : ℕ) := 2*K+22+7*D+6*D*K*2^(D+1)

theorem budget_bound (D K size arity : ℕ) :
    budget D K size arity≤preparationCoefficient D K*(size+arity+1)^(D+1) := by
  let s:=size+arity
  let X:=(s+1)^(D+1)
  have hpos : 1≤X := Nat.one_le_pow _ _ (by omega)
  have hlinear : s+1≤X := by
    have h:=Nat.pow_le_pow_right (show 0<s+1 by omega) (show 1≤D+1 by omega)
    simpa only [pow_one] using h
  have hp : (s+2)^(D+1)≤2^(D+1)*X := by
    have h:=Nat.pow_le_pow_left (show s+2≤2*(s+1) by omega) (D+1)
    simpa only [mul_pow] using h
  have hc:=DimensionPower.cost_bound D K (s+1) D le_rfl
  rw [show s+1+1=s+2 by omega] at hc
  have hmul:=Nat.mul_le_mul_left (6*D*K) hp
  have hconstant:=Nat.mul_le_mul_left (2*K+18+7*D) hpos
  have hinput:=Nat.mul_le_mul_left 4 hlinear
  change 2*s+7+(2*s+9+DimensionPower.cost K (s+1) D)≤preparationCoefficient D K*X
  unfold preparationCoefficient
  nlinarith

theorem source_capacity_run (a : PointwisePCPPAlgorithm) (size arity : ℕ) :
    let D:=PCPPQueryCachedBounds.degree a
    let K:=PCPPQueryCachedBounds.coefficient a
    ∃ out,ClockJoin.ReadyRun (machine D K)
      (preparationCoefficient D K*(size+arity+1)^(D+1)) (input D size arity) out ∧
      out (sumSlots D 0)=List.replicate size true ∧
      out (sumSlots D 1)=List.replicate arity true ∧
      out (outputSlot D)=List.replicate (PCPPQueryCachedBounds.capacity a (size+arity)) true := by
  dsimp only
  obtain ⟨out,hr,hs,ha,hc⟩:=capacity_run (PCPPQueryCachedBounds.degree a) (PCPPQueryCachedBounds.coefficient a) size arity
  exact ⟨out,ClockJoin.enlarge _ _ _ _ _ hr (budget_bound _ _ _ _),hs,ha,hc⟩

end NearCubicWires.RepairOrdinary.PCPPQueryCapacity
