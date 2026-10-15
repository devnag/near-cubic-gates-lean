import Proof.Foundations.RecoverySourceSAT
import Proof.PCP.PCPPairReusable

/-! Exact constant-depth legacy marker for the budgeted source-oracle lift.
Four canonical pair calls realize all three apparent successors as well. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift
open RepairOrdinary RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boundInput (input : List Bool) (budget : ℕ) : List Bool :=
  frame input ++ frame (List.replicate budget true)

@[simp] theorem boundInput_length (input : List Bool) (budget : ℕ) :
    (boundInput input budget).length = 2 * input.length + 2 * budget + 2 := by
  simp [boundInput]
  omega

theorem pair_right_one (n : ℕ) (hn : 1 ≤ n) : Nat.pair n 1 = Nat.pair n 0 + 1 := by
  rw [PCPPair.pair_formula, PCPPair.pair_formula]
  simp only [hn, Nat.zero_le, if_true]

theorem pair_left_one (n : ℕ) (hn : 1 < n) : Nat.pair 1 n = Nat.pair 0 n + 1 := by
  rw [PCPPair.pair_formula, PCPPair.pair_formula]
  simp only [show ¬ n ≤ 1 by omega, show ¬ n ≤ 0 by omega, if_false]

def first (c : ℕ) : ℕ := Nat.pair 1 c
def second (c : ℕ) : ℕ := Nat.pair (first c) 1
def third (c : ℕ) : ℕ := Nat.pair (second c) 1
def fourth (c : ℕ) : ℕ := Nat.pair 1 (third c)

theorem first_two (c : ℕ) : 2 ≤ first c := by
  unfold first
  rw [PCPPair.pair_formula]
  split_ifs <;> nlinarith

theorem second_two (c : ℕ) : 2 ≤ second c :=
  (first_two c).trans (Nat.left_le_pair _ _)

theorem third_two (c : ℕ) : 2 ≤ third c :=
  (second_two c).trans (Nat.left_le_pair _ _)

theorem exact_marker (c : ℕ) : fourth c = RecoveryOracle.liftSourceSAT c := by
  have ha := first_two c
  have hb := second_two c
  have hd := third_two c
  change Nat.pair 1 (third c) =
    Nat.pair 0 (Nat.pair (Nat.pair (Nat.pair 1 c) 0 + 1) 0 + 1) + 1
  rw [pair_left_one _ (by omega)]
  have hs : second c = Nat.pair (first c) 0 + 1 := pair_right_one _ (by omega)
  have ht : third c = Nat.pair (second c) 0 + 1 := pair_right_one _ (by omega)
  rw [ht, hs]
  rfl

theorem query_agrees (c : ℕ) : RecoveryOracle.correctedSat (fourth c) = RecoveryOracle.sourceSAT c := by
  rw [exact_marker]
  exact RecoveryOracle.corrected_liftSourceSAT c

theorem intermediate_le (c : ℕ) :
    first c ≤ fourth c ∧ second c ≤ fourth c ∧ third c ≤ fourth c := by
  have h12 : first c ≤ second c := Nat.left_le_pair _ _
  have h23 : second c ≤ third c := Nat.left_le_pair _ _
  have h34 : third c ≤ fourth c := Nat.right_le_pair _ _
  exact ⟨h12.trans (h23.trans h34), h23.trans h34, h34⟩

theorem value_width (bits : List Bool) : natBitLength (value bits) ≤ bits.length + 1 := by
  have hv := value_lt bits
  have hw := Nat.log_mono_right (b := 2) hv.le
  rw [Nat.log_pow (by decide : 1 < 2)] at hw
  exact Nat.add_le_add_right hw 1

theorem lift_width (bits : List Bool) : (fourth (value bits)).bits.length ≤ 23 * (bits.length + 1) := by
  have h := RecoveryOracle.liftSourceSAT_bits (value bits)
  have hv := value_width bits
  have hb := PCPSerializerMass.nat_bits_width (fourth (value bits))
  rw [← exact_marker] at h
  omega

theorem node_width (bits : List Bool) (node : ℕ) (hnode : node ≤ fourth (value bits)) :
    node.bits.length ≤ 23 * (bits.length + 1) := by
  have h := RecoveryOracle.liftSourceSAT_bits (value bits)
  have hv := value_width bits
  have hb := PCPSerializerMass.nat_bits_width node
  have hm : natBitLength node ≤ natBitLength (fourth (value bits)) :=
    Nat.add_le_add_right (Nat.log_mono_right hnode) 1
  rw [← exact_marker] at h
  omega

theorem value_eq_bitsValue (bits : List Bool) : value bits = CanonicalBinary.bitsValue bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp only [value, CanonicalBinary.bitsValue, ih]

def capacity (b : ℕ) : ℕ := 268435456 * (b + 1)^2

theorem capacity_pair (b : ℕ) (left right : List Bool)
    (hl : left.length ≤ 23 * (b + 1)) (hr : right.length ≤ 23 * (b + 1)) :
    PCPPairCanonical.budget left right + 1 ≤ capacity b := by
  have hp := PCPPairCanonical.budget_quadratic left right
  have hs : left.length + right.length + 1 ≤ 47 * (b + 1) := by omega
  have hsq := Nat.pow_le_pow_left hs 2
  have he : (47 * (b + 1))^2 = 2209 * (b + 1)^2 := by ring
  rw [he] at hsq
  have hpos : 1 ≤ (b + 1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold capacity
  omega

end NearCubicWires.RepairSource.OrdinarySourceSATLift
