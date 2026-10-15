import Proof.Amplification.RecoveryProjectionRowsMeaning

/-! The physical evaluator bank can be allocated from the SAME normalized
width alone. Every original projection code is bounded by that width, so no
additional scan or supplied bound on the full source stream is required. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionRows
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (width : Nat) := 1048576*(width+1)^4

theorem bits_le_value (n : Nat) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem projection_size {width : Nat} (p : ProjectedRandomBit width) :
    (projectionCode p).bits.length ≤ 7*(width+1)^2 := by
  have hp : 1 ≤ (width+1)^2 := Nat.one_le_pow _ _ (by omega)
  apply (bits_le_value _).trans
  cases p with
  | bit i =>
    have h := Nat.pair_lt_max_add_one_sq 0 i.val
    have hm : max 0 i.val ≤ width := max_le (by omega) (by have hi:=i.isLt; omega)
    have hs : (max 0 i.val+1)^2 ≤ (width+1)^2 := by gcongr
    change Nat.pair 0 i.val ≤ _
    omega
  | negatedBit i =>
    have h := Nat.pair_lt_max_add_one_sq 1 i.val
    have hm : max 1 i.val ≤ width := max_le (by have hi:=i.isLt; omega) (by have hi:=i.isLt; omega)
    have hs : (max 1 i.val+1)^2 ≤ (width+1)^2 := by gcongr
    change Nat.pair 1 i.val ≤ _
    omega
  | constant b =>
    cases b <;> change Nat.pair 2 _ ≤ _
    all_goals norm_num [Nat.pair]
    all_goals omega

theorem capacity_covers {width : Nat} (p : ProjectedRandomBit width) (randomness : BitInput width) :
    RecoveryProjectionEval.budget (projectionCode p).bits (List.ofFn randomness)+1 ≤ capacity width := by
  have hsize := projection_size p
  have hlin : width+1 ≤ (width+1)^2 := Nat.le_self_pow (by decide) _
  have hp : 1 ≤ (width+1)^4 := Nat.one_le_pow _ _ (by omega)
  have hrad : (projectionCode p).bits.length+width+1 ≤ 8*(width+1)^2 := by omega
  have hsquare : ((projectionCode p).bits.length+width+1)^2 ≤ (8*(width+1)^2)^2 := by gcongr
  have he : (8*(width+1)^2)^2=64*(width+1)^4 := by ring
  rw [he] at hsquare
  simp only [RecoveryProjectionEval.budget,List.length_ofFn,capacity]
  nlinarith

end NearCubicWires.RepairSource.RecoveryProjectionRows
