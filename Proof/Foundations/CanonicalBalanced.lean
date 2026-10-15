import Mathlib
import Proof.Foundations.BitLength
import StatementSupport

/-!
# Width-safe canonical sequences

`Nat.pair` is quadratic in its larger input, so a linked list of `L` cells can
have exponentially many register bits.  Variable-length executable data uses
the deterministic balanced tree in this module instead.  Empty sequences are
zero, leaves have tag one, and internal nodes have tag two; midpoint splitting
fixes one tree shape for every ordered list.

The decoder re-encodes before accepting, so malformed tags, noncanonical tree
shapes, and alternate encodings are rejected.  `balancedListCodeBits_le`
charges the real binary width of the resulting natural and is the resource
bridge used by fixed interpreter programs.
-/

namespace NearCubicWires.CanonicalBinary

open NearCubicWires

/-- Structural height of the canonical midpoint tree.  This is also the
maximum number of pending right subtrees held by the fixed DFS controller. -/
def balancedListHeight : List ℕ → ℕ
  | [] => 0
  | [_] => 1
  | first :: second :: rest =>
      let values := first :: second :: rest
      let leftLength := (values.length + 1) / 2
      let left := values.take leftLength
      let right := values.drop leftLength
      1 + max (balancedListHeight left) (balancedListHeight right)
termination_by values => values.length
decreasing_by
  all_goals
    simp_wf
    have : ((rest.length + 2 + 1) / 2) ≤ rest.length + 1 := by omega
    simp
    omega

/-- Midpoint splitting makes continuation depth logarithmic, including the
singleton leaf level. -/
theorem balancedListHeight_le_clog (values : List ℕ) :
    balancedListHeight values ≤ Nat.clog 2 values.length + 1 := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h length ih =>
      cases values with
      | nil =>
          simp [balancedListHeight]
      | cons first rest =>
          cases rest with
          | nil =>
              simp [balancedListHeight]
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwo : 2 ≤ values.length := by simp [values]
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLeValues : leftLength ≤ values.length :=
                hleftLtValues.le
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLeValues]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hrightLeLeft : right.length ≤ left.length := by
                rw [hrightLengthEq, hleftLengthEq]
                dsimp [leftLength]
                omega
              have hleftLt : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length := by
                exact lt_of_le_of_lt hrightLeLeft hleftLt
              have ihLeft := ih left.length hleftLt left rfl
              have ihRight := ih right.length hrightLt right rfl
              have hclogMono :
                  Nat.clog 2 right.length ≤ Nat.clog 2 left.length :=
                Nat.clog_mono_right 2 hrightLeLeft
              rw [← hlengthValues]
              rw [Nat.clog_of_two_le (by omega) htwo]
              simp only [balancedListHeight]
              change
                1 + max (balancedListHeight left)
                    (balancedListHeight right) ≤
                  Nat.clog 2 leftLength + 1 + 1
              rw [← hleftLengthEq]
              omega

theorem decodeBalancedListAux_encode
    (values : List ℕ) (fuel : ℕ) (hfuel : values.length < fuel) :
    decodeBalancedListAux fuel (encodeBalancedList values) = some values := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values fuel with
  | h length ih =>
      cases values with
      | nil =>
          cases fuel <;> simp_all [encodeBalancedList,
            decodeBalancedListAux]
      | cons first rest =>
          cases rest with
          | nil =>
              cases fuel with
              | zero => simp at hfuel
              | succ fuel =>
                  have hnonzero : Nat.pair 1 first ≠ 0 := by
                    have := Nat.left_le_pair 1 first
                    omega
                  simp [encodeBalancedList, decodeBalancedListAux,
                    hnonzero]
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwo : 2 ≤ values.length := by
                simp [values]
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLeValues : leftLength ≤ values.length :=
                hleftLtValues.le
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLeValues]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hleftLength : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightPositive : 0 < right.length := by
                rw [hrightLengthEq]
                omega
              have hrightLength : right.length < length := by
                rw [hrightLengthEq, ← hlengthValues]
                omega
              cases fuel with
              | zero => simp at hfuel
              | succ fuel =>
                  have hvaluesFuel : values.length < fuel + 1 := by
                    simpa [values] using hfuel
                  have hleftFuel : left.length < fuel := by
                    omega
                  have hrightFuel : right.length < fuel := by
                    omega
                  have hleft :=
                    ih left.length hleftLength left fuel hleftFuel rfl
                  have hright :=
                    ih right.length hrightLength right fuel hrightFuel rfl
                  have hnonzero :
                      Nat.pair 2
                          (Nat.pair (encodeBalancedList left)
                            (encodeBalancedList right)) ≠ 0 := by
                    have := Nat.left_le_pair 2
                      (Nat.pair (encodeBalancedList left)
                        (encodeBalancedList right))
                    omega
                  have happend : left ++ right = values := by
                    simp [left, right]
                  simp only [encodeBalancedList, decodeBalancedListAux]
                  rw [if_neg hnonzero]
                  simp only [Nat.unpair_pair, OfNat.ofNat_ne_one,
                    ↓reduceIte]
                  change
                    (match decodeBalancedListAux fuel
                        (encodeBalancedList left),
                        decodeBalancedListAux fuel
                          (encodeBalancedList right) with
                      | some decodedLeft, some decodedRight =>
                          some (decodedLeft ++ decodedRight)
                      | _, _ => none) =
                      some values
                  rw [hleft, hright]
                  simpa only using congrArg some happend

theorem encodeBalancedList_length_le (values : List ℕ) :
    values.length ≤ encodeBalancedList values := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h length ih =>
      cases values with
      | nil =>
          have hzero : length = 0 := by
            simpa only [List.length_nil] using hlength.symm
          simpa only [encodeBalancedList] using hzero.le
      | cons first rest =>
          cases rest with
          | nil =>
              have hone : length = 1 := by simpa using hlength.symm
              rw [hone]
              simpa [encodeBalancedList] using Nat.left_le_pair 1 first
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwo : 2 ≤ values.length := by
                simp [values]
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLeValues : leftLength ≤ values.length :=
                hleftLtValues.le
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLeValues]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hleftLt : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length := by
                rw [hrightLengthEq, ← hlengthValues]
                omega
              have hleft := ih left.length hleftLt left rfl
              have hright := ih right.length hrightLt right rfl
              have happend : left ++ right = values := by
                simp [left, right]
              calc
                length = (first :: second :: rest).length :=
                  hlength.symm
                _ = left.length + right.length := by
                  rw [← List.length_append, happend]
                _ ≤ encodeBalancedList left +
                    encodeBalancedList right :=
                  Nat.add_le_add hleft hright
                _ ≤ Nat.pair (encodeBalancedList left)
                    (encodeBalancedList right) :=
                  Nat.add_le_pair _ _
                _ ≤ Nat.pair 2
                    (Nat.pair (encodeBalancedList left)
                      (encodeBalancedList right)) :=
                  Nat.right_le_pair _ _
                _ = encodeBalancedList (first :: second :: rest) := by
                  simp [encodeBalancedList, values, leftLength, left, right]

@[simp] theorem decodeBalancedList_encode (values : List ℕ) :
    decodeBalancedList (encodeBalancedList values) = some values := by
  have hcandidate :
      decodeBalancedListCandidate (encodeBalancedList values) =
        some values := by
    unfold decodeBalancedListCandidate
    exact decodeBalancedListAux_encode values
      (encodeBalancedList values + 1)
      (by
        have := encodeBalancedList_length_le values
        omega)
  unfold decodeBalancedList
  rw [hcandidate]
  simp

theorem encodeBalancedList_of_decode
    {code : ℕ} {values : List ℕ}
    (hdecode : decodeBalancedList code = some values) :
    encodeBalancedList values = code := by
  unfold decodeBalancedList at hdecode
  generalize hcandidate :
    decodeBalancedListCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      change
        (if encodeBalancedList decoded = code then some decoded else none) =
          some values at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

private theorem balancedListAtomBits_positive (values : List ℕ) :
    0 < balancedListAtomBits values := by
  simp [balancedListAtomBits]

/-- Shared false-first lexicographic order for canonical Boolean sequences. -/
def CanonicalBoolListLE (left right : List Bool) : Prop :=
  left ≤ right

end NearCubicWires.CanonicalBinary
