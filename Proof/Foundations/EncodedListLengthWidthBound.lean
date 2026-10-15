import Proof.Foundations.CanonicalEncodedListLengthProgram
import Proof.Foundations.TseitinCNF

/-!
# Canonical encoded-list length width bounds

The structural list-length fold is bounded directly by the binary width of
its canonical input code.  The executable width and fuel corollaries expose
the exact small linear charges used by downstream resource ledgers.
-/

namespace NearCubicWires.EncodedListLengthWidthBound

open NearCubicWires
open NearCubicWires.CanonicalEncodedListLengthProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.TseitinCNF

/-- The decoded list spine cannot contain more entries than the bit width of
its canonical natural-number code. -/
theorem encodedListLength_le_natBitLength (code : ℕ) :
    encodedListLength code ≤ natBitLength code := by
  rw [encodedListLength_eq_decode]
  let values := ((Encodable.decode code : Option (List ℕ)).getD [])
  have hcanonical : Encodable.encode values = code := by
    simp [values]
  rw [← hcanonical]
  simpa using list_length_le_encoded_bitLength values

/-- Exact linear fuel charge inherited from the structural list-length fold. -/
theorem encodedListLengthFuel_le_natBitLength (code : ℕ) :
    encodedListLengthFuel code ≤ 5 * natBitLength code + 4 := by
  unfold encodedListLengthFuel encodedListLengthLoopFuel
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 5 (encodedListLength_le_natBitLength code)) 4

/-- The program's register width is no larger than the input code's own
binary width. -/
theorem encodedListLengthBits_le_natBitLength (code : ℕ) :
    encodedListLengthBits code ≤ natBitLength code := by
  have hlengthCode : encodedListLength code ≤ code := by
    cases code with
    | zero => simp [encodedListLength]
    | succ code =>
        exact (encodedListLength_le_natBitLength (code + 1)).trans <| by
          unfold natBitLength
          have hlog : Nat.log 2 (code + 1) < code + 1 :=
            Nat.log_lt_self 2 (by omega)
          omega
  simp [encodedListLengthBits, max_eq_left hlengthCode]

end NearCubicWires.EncodedListLengthWidthBound
