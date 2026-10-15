import Proof.Amplification.RecoveryQueryLayout

/-! All nine executed nodes fit a single quadratic workspace bound in the
three input bit lengths.  Count remains binary; it is never expanded here. -/
namespace NearCubicWires.RepairSource.RecoveryQuery
open CanonicalBinary BalancedCNFSATEncoding RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bytes (payload committed count : Nat) := payload.bits.length+committed.bits.length+count.bits.length
def capacity (payload committed count : Nat) := 1073741824*(bytes payload committed count+1)^2

theorem values_le (flat : Bool) (payload committed count : Nat) (j : Fin 9) :
    values flat payload committed count j ≤ code flat payload committed count := by
  have h01 : node0 count ≤ node1 count :=
    (Nat.left_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h13 : node1 count ≤ node3 committed count :=
    (Nat.right_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h23 : node2 committed ≤ node3 committed count :=
    (Nat.left_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h34 : node3 committed count ≤ node4 committed count :=
    (Nat.left_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h47 : node4 committed count ≤ node7 flat payload committed count :=
    (Nat.right_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h56 : node5 flat payload ≤ node6 flat payload :=
    (Nat.left_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h67 : node6 flat payload ≤ node7 flat payload committed count :=
    (Nat.left_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h78 : node7 flat payload committed count ≤ node8 flat payload committed count :=
    (Nat.right_le_pair _ _).trans (Nat.le_add_right _ 1)
  rw [←exact_code]
  fin_cases j
  · exact h01.trans (h13.trans (h34.trans (h47.trans h78)))
  · exact h13.trans (h34.trans (h47.trans h78))
  · exact h23.trans (h34.trans (h47.trans h78))
  · exact h34.trans (h47.trans h78)
  · exact h47.trans h78
  · exact h56.trans (h67.trans h78)
  · exact h67.trans h78
  · exact h78
  · exact Nat.le_refl _

theorem arguments_le (flat : Bool) (payload committed count : Nat) (j : Fin 9) :
    lefts flat payload committed count j ≤ code flat payload committed count ∧
      rights flat payload committed count j ≤ code flat payload committed count := by
  have hn := values_le flat payload committed count j
  rw [←node_result] at hn
  have hp : Nat.pair (lefts flat payload committed count j) (rights flat payload committed count j) ≤
      RecoveryQueryCell.result (operations j) (lefts flat payload committed count j)
        (rights flat payload committed count j) := Nat.le_add_right _ _
  exact ⟨(Nat.left_le_pair _ _).trans (hp.trans hn),(Nat.right_le_pair _ _).trans (hp.trans hn)⟩

theorem nat_width (n : Nat) : natBitLength n ≤ n.bits.length+1 := by
  have h := OrdinarySourceSATLift.value_width n.bits
  rw [CanonicalPositiveOutput.nat_bits_value] at h
  exact h

theorem code_width (flat : Bool) (payload committed count : Nat) :
    natBitLength (code flat payload committed count) ≤ 95*(bytes payload committed count+1) := by
  have hp := nat_width payload
  have ha := nat_width committed
  have hc := nat_width count
  have hmax : max 1 (max (natBitLength payload) (max (natBitLength committed) (natBitLength count))) ≤
      bytes payload committed count+1 := by
    unfold bytes
    omega
  have h : natBitLength (code flat payload committed count) ≤
      64*max 1 (max (natBitLength payload) (max (natBitLength committed) (natBitLength count)))+31 := by
    cases flat
    · exact NestedBalancedCNFCodec.encodeNestedBalancedPrefixCNFPayloadMarker_bits_le payload committed count
    · exact encodeBalancedPrefixCNFPayload_bits_le payload committed count
  omega

theorem argument_widths (flat : Bool) (payload committed count : Nat) (j : Fin 9) :
    (lefts flat payload committed count j).bits.length ≤ 95*(bytes payload committed count+1) ∧
      (rights flat payload committed count j).bits.length ≤ 95*(bytes payload committed count+1) := by
  have bound := code_width flat payload committed count
  obtain ⟨hl,hr⟩ := arguments_le flat payload committed count j
  have hleft := PCPSerializerMass.nat_bits_width (lefts flat payload committed count j)
  have hright := PCPSerializerMass.nat_bits_width (rights flat payload committed count j)
  have hmonoL : natBitLength (lefts flat payload committed count j) ≤ natBitLength (code flat payload committed count) :=
    Nat.add_le_add_right (Nat.log_mono_right hl) 1
  have hmonoR : natBitLength (rights flat payload committed count j) ≤ natBitLength (code flat payload committed count) :=
    Nat.add_le_add_right (Nat.log_mono_right hr) 1
  omega

theorem cell_capacity (flat : Bool) (payload committed count : Nat) (j : Fin 9) :
    RecoveryQueryCell.budget (operations j) (lefts flat payload committed count j)
      (rights flat payload committed count j)+1 ≤ capacity payload committed count ∧
    2*(lefts flat payload committed count j).bits.length+1 ≤ capacity payload committed count ∧
    2*(rights flat payload committed count j).bits.length+1 ≤ capacity payload committed count := by
  obtain ⟨hl,hr⟩ := argument_widths flat payload committed count j
  have hb := RecoveryQueryCell.budget_quadratic (operations j) (lefts flat payload committed count j)
    (rights flat payload committed count j)
  have hs : (lefts flat payload committed count j).bits.length+
      (rights flat payload committed count j).bits.length+1 ≤ 191*(bytes payload committed count+1) := by omega
  have hsq := Nat.pow_le_pow_left hs 2
  have he : (191*(bytes payload committed count+1))^2=36481*(bytes payload committed count+1)^2 := by ring
  rw [he] at hsq
  have hbase : bytes payload committed count+1 ≤ (bytes payload committed count+1)^2 := by nlinarith
  have hpos : 1 ≤ (bytes payload committed count+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold capacity
  omega

end NearCubicWires.RepairSource.RecoveryQuery
