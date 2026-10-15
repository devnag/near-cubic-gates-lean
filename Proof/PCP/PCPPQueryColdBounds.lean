import Proof.PCP.PCPPQueryColdPrepare

/-! Source-fixed polynomial time for the complete cold shared-cache setup,
with every capacity and template prerequisite discharged. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryCold
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient (D K : ℕ) := PCPPQueryCapacity.preparationCoefficient D K+2*K+18

theorem budget_bound (D K size arity : ℕ) :
    budget D K size arity≤coefficient D K*(size+arity+1)^(D+1) := by
  let X:=(size+arity+1)^(D+1)
  have hpos : 1≤X := Nat.one_le_pow _ _ (by omega)
  have hinput : arity+1≤X := by
    have h:=Nat.pow_le_pow_right (show 0<size+arity+1 by omega) (show 1≤D+1 by omega)
    simp only [pow_one] at h
    exact (show arity+1 ≤ size+arity+1 by omega).trans h
  have hp : (size+arity+1)^D≤X := Nat.pow_le_pow_right (by omega) (by omega)
  have hcap:=Nat.mul_le_mul_left (2*K) hp
  have hs:=PCPPQueryCapacity.budget_bound D K size arity
  change PCPPQueryCapacity.budget D K size arity≤PCPPQueryCapacity.preparationCoefficient D K*X at hs
  unfold budget coefficient
  change PCPPQueryCapacity.budget D K size arity+1+2*arity+2*(K*(size+arity+1)^D)+15≤
    (PCPPQueryCapacity.preparationCoefficient D K+2*K+18)*X
  nlinarith

theorem source_cold_run (a : PointwisePCPPAlgorithm) (source : List Bool) (size arity : ℕ) :
    let D:=PCPPQueryCachedBounds.degree a
    let K:=PCPPQueryCachedBounds.coefficient a
    let C:=PCPPQueryCachedBounds.capacity a (size+arity)
    ∃ r,run (machine D K) (coefficient D K*(size+arity+1)^(D+1)) (input D source size arity)=some r ∧
      (∀ j : Fin 19,r.final.tapes (cacheSlots D j)=PCPPQueryIndexPadding.clauseData source arity 0 C [] j) ∧
      (∀ j : Fin 19,r.final.heads (cacheSlots D j)=PCPPQueryClauseReuse.heads j) ∧
      r.final.tapes (sizeSlot D)=List.replicate size true ∧ r.final.heads (sizeSlot D)=0 ∧
      r.steps≤coefficient D K*(size+arity+1)^(D+1) := by
  dsimp only
  let D:=PCPPQueryCachedBounds.degree a
  let K:=PCPPQueryCachedBounds.coefficient a
  have hK : 2≤K := by
    have h:=Nat.one_le_pow 2 (a.coefficient+131084) (by omega)
    dsimp [K,PCPPQueryCachedBounds.coefficient]
    omega
  have hp : 1≤(size+arity+1)^D := Nat.one_le_pow _ _ (by omega)
  have hC : 2≤K*(size+arity+1)^D := hK.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left K hp)
  obtain ⟨r,hr,ht,hh,hs,hsh,hb⟩:=cold_run D K source size arity hC
  have hc:=budget_bound D K size arity
  have hm:=runFrom_moreFuel (machine D K) _
    (coefficient D K*(size+arity+1)^(D+1)-budget D K size arity) _ r hr
  rw [Nat.add_sub_of_le hc] at hm
  exact ⟨r,hm,ht,hh,hs,hsh,hb.trans hc⟩

end NearCubicWires.RepairOrdinary.PCPPQueryCold
