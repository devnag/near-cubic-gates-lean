import Proof.PCP.PCPClauseList

/-! Coarse whole runtime and output-size bounds for the actual two-level
clause serializer. The exponent is fixed before the hierarchy is selected. -/
namespace NearCubicWires.RepairOrdinary.PCPClauseList
open PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient : ℕ := 4000000000000000003+1000000000000*513^12

theorem budget_bound (groups : List (List (List Bool)))
    (hthree : ∀ fs∈groups,fs.length=3) :
    budget groups ≤ coefficient*((PCPTripleLoop.stream groups).length+1)^13 := by
  let B := (PCPTripleLoop.stream groups).length
  have hglobal := PCPTripleGlobal.budget_bound B groups.length (PCPTripleGlobal.group_count_le groups hthree)
  have hm := fields_mass groups hthree
  have hsmall : mass (fields groups)+1 ≤ 513*(B+1) := by omega
  have hp := Nat.pow_le_pow_left hsmall 12
  rw [mul_pow] at hp
  have h12 : (B+1)^12 ≤ (B+1)^13 := pow_le_pow_right₀ (by omega) (by omega)
  have hpos : 1 ≤ (B+1)^13 := Nat.one_le_pow 13 _ (by omega)
  have hserial : PCPTraversal.budget (mass (fields groups)) ≤ 1000000000000*513^12*(B+1)^13 := by
    unfold PCPTraversal.budget
    calc
      _ ≤ 1000000000000*(513^12*(B+1)^12) := Nat.mul_le_mul_left _ hp
      _ ≤ 1000000000000*(513^12*(B+1)^13) := by gcongr
      _ = _ := by ring
  change 2*PCPTripleGlobal.budget B groups.length+3+PCPTraversal.budget (mass (fields groups)) ≤ coefficient*(B+1)^13
  unfold coefficient
  omega

theorem output_bound (groups : List (List (List Bool)))
    (hthree : ∀ fs∈groups,fs.length=3) :
    (PCPTraversal.code (fields groups)).bits.length ≤ 3*513^5*((PCPTripleLoop.stream groups).length+1)^5 := by
  have hm := fields_mass groups hthree
  have hsmall : mass (fields groups)+1 ≤ 513*((PCPTripleLoop.stream groups).length+1) := by omega
  have hb := PCPTraversal.bounded_code (fields groups) (mass (fields groups)) le_rfl
  have hp := Nat.pow_le_pow_left hsmall 5
  rw [mul_pow] at hp
  calc
    _ ≤ 3*(mass (fields groups)+1)^5 := hb
    _ ≤ 3*(513^5*((PCPTripleLoop.stream groups).length+1)^5) := Nat.mul_le_mul_left _ hp
    _ = _ := by ring

end NearCubicWires.RepairOrdinary.PCPClauseList
