import Proof.Amplification.RecoveryUnpairCode

/-! One global binary field width suffices for recursive unpair. The low-width
copy preserves the whole value; padded arithmetic results do not enlarge the
width of later decoder fields. These are semantic premises for the paid copy. -/
namespace NearCubicWires.RepairOrdinary.RecoveryFixedWidth
open RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem take_value_and_high_zero (bits : List Bool) (width : Nat)
    (hw : width ≤ bits.length) (hv : value bits < 2 ^ width) :
    value (bits.take width) = value bits ∧ value (bits.drop width) = 0 := by
  have h := value_append (bits.take width) (bits.drop width)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hw] at h
  have hp : 0 < 2 ^ width := by positivity
  have hz : value (bits.drop width) = 0 := by
    by_contra hn
    have hpos : 1 ≤ value (bits.drop width) := by omega
    have hm := Nat.mul_le_mul_left (2 ^ width) hpos
    nlinarith
  exact ⟨by rw [hz] at h; simpa using h.symm, hz⟩

theorem take_binary (bits : List Bool) (width : Nat)
    (hw : width ≤ bits.length) (hv : value bits < 2 ^ width) :
    bits.take width = SignedSortKey.binary width (value bits) := by
  have h := BoundedCounter.binary_of_value (bits.take width)
  rw [List.length_take, Nat.min_eq_left hw, (take_value_and_high_zero bits width hw hv).1] at h
  exact h.symm

theorem unpair_low_words (bits : List Bool) :
    (RecoveryUnpair.leftWord bits).take bits.length =
      SignedSortKey.binary bits.length (Nat.unpair (value bits)).1 ∧
    (RecoveryUnpair.rightWord bits).take bits.length =
      SignedSortKey.binary bits.length (Nat.unpair (value bits)).2 := by
  obtain ⟨hl, hr⟩ := RecoveryUnpair.word_lengths bits
  obtain ⟨hvl, hvr⟩ := RecoveryUnpair.word_values bits
  have hn := value_lt bits
  have hlv : value (RecoveryUnpair.leftWord bits) < 2 ^ bits.length := by
    rw [hvl]
    exact (Nat.unpair_left_le _).trans_lt hn
  have hrv : value (RecoveryUnpair.rightWord bits) < 2 ^ bits.length := by
    rw [hvr]
    exact (Nat.unpair_right_le _).trans_lt hn
  constructor
  · simpa only [hvl] using take_binary (RecoveryUnpair.leftWord bits) bits.length (by omega) hlv
  · simpa only [hvr] using take_binary (RecoveryUnpair.rightWord bits) bits.length (by omega) hrv

end NearCubicWires.RepairOrdinary.RecoveryFixedWidth
