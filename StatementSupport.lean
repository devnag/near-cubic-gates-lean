import Statement

/-!
# Supporting declarations (not part of the statement)

Declarations of the machine model and the codecs that the proof uses but the statement does not reach.
Nothing here is trusted: the proof imports this file, and comparator checks the proof.
-/

/-! ## Balanced list codes (supporting declarations) -/

section

namespace NearCubicWires.CanonicalBinary

open NearCubicWires

private theorem natBitLength_lt_pow (value : ℕ) :
    value < 2 ^ natBitLength value := by
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self Nat.one_lt_two value

private theorem natBitLength_pair_le (left right : ℕ) :
    natBitLength (Nat.pair left right) ≤
      2 * max (natBitLength left) (natBitLength right) := by
  let width := max (natBitLength left) (natBitLength right)
  have hleft : left < 2 ^ width := by
    exact (natBitLength_lt_pow left).trans_le
      (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hright : right < 2 ^ width := by
    exact (natBitLength_lt_pow right).trans_le
      (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  have hmax : max left right + 1 ≤ 2 ^ width := by
    omega
  have hpair : Nat.pair left right < 2 ^ (2 * width) := by
    calc
      Nat.pair left right < (max left right + 1) ^ 2 :=
        Nat.pair_lt_max_add_one_sq left right
      _ ≤ (2 ^ width) ^ 2 :=
        Nat.pow_le_pow_left hmax 2
      _ = 2 ^ (2 * width) := by
        rw [← pow_mul]
        congr 1
        omega
  by_cases hzero : Nat.pair left right = 0
  · rw [hzero]
    change 1 ≤ 2 * width
    have hpositive : 1 ≤ natBitLength left := by
      unfold natBitLength
      omega
    have hwidth : natBitLength left ≤ width :=
      le_max_left _ _
    omega
  · change Nat.log 2 (Nat.pair left right) + 1 ≤ 2 * width
    have hlog :
        Nat.log 2 (Nat.pair left right) < 2 * width :=
      Nat.log_lt_of_lt_pow hzero hpair
    omega

/-- Public width rule used by fixed machine-control encodings.  Keeping the
pairing cost explicit prevents a constant-time `pair` instruction from hiding
an oversized register. -/
theorem pairCodeBits_le (left right : ℕ) :
    natBitLength (Nat.pair left right) ≤
      2 * max (natBitLength left) (natBitLength right) :=
  natBitLength_pair_le left right

/-- Sum of atom widths, with one unit retained for the empty sequence. -/
def balancedListAtomBits (values : List ℕ) : ℕ :=
  (values.map natBitLength).sum + 1

private theorem encodeBalancedList_bits_le_of_ne_nil
    (values : List ℕ) (hne : values ≠ []) :
    natBitLength (encodeBalancedList values) ≤
      2 * values.length ^ 4 * balancedListAtomBits values := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h length ih =>
      cases values with
      | nil => simp at hne
      | cons first rest =>
          cases rest with
          | nil =>
              have hone : length = 1 := by simpa using hlength.symm
              subst length
              have hpair := natBitLength_pair_le 1 first
              have hfirstPositive : 1 ≤ natBitLength first := by
                unfold natBitLength
                omega
              simpa [encodeBalancedList, balancedListAtomBits,
                natBitLength, max_eq_right hfirstPositive] using
                hpair.trans
                  (show 2 * natBitLength first ≤
                    2 * (natBitLength first + 1) by omega)
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
              have hrightPositive : 0 < right.length := by
                rw [hrightLengthEq]
                omega
              have hrightLt : right.length < length := by
                rw [hrightLengthEq, ← hlengthValues]
                omega
              have hleftNonempty : left ≠ [] :=
                List.ne_nil_of_length_pos
                  (hleftLengthEq.symm ▸ hleftPositive)
              have hrightNonempty : right ≠ [] :=
                List.ne_nil_of_length_pos hrightPositive
              have hleft :=
                ih left.length hleftLt left hleftNonempty rfl
              have hright :=
                ih right.length hrightLt right hrightNonempty rfl
              have happend : left ++ right = values := by
                simp [left, right]
              have hatom :
                  (left.map natBitLength).sum +
                      (right.map natBitLength).sum =
                    (values.map natBitLength).sum := by
                rw [← List.sum_append, ← List.map_append, happend]
              have hleftAtom :
                  balancedListAtomBits left ≤
                    balancedListAtomBits values := by
                unfold balancedListAtomBits
                omega
              have hrightAtom :
                  balancedListAtomBits right ≤
                    balancedListAtomBits values := by
                unfold balancedListAtomBits
                omega
              have hleftRatio :
                  3 * left.length ≤ 2 * values.length := by
                rw [hleftLengthEq]
                dsimp [leftLength]
                omega
              have hrightRatio :
                  3 * right.length ≤ 2 * values.length := by
                rw [hrightLengthEq]
                dsimp [leftLength]
                omega
              have hleftPower :
                  4 * left.length ^ 4 ≤ values.length ^ 4 := by
                have hp := Nat.pow_le_pow_left hleftRatio 4
                simp only [mul_pow] at hp
                norm_num at hp
                omega
              have hrightPower :
                  4 * right.length ^ 4 ≤ values.length ^ 4 := by
                have hp := Nat.pow_le_pow_left hrightRatio 4
                simp only [mul_pow] at hp
                norm_num at hp
                omega
              let leftCode := encodeBalancedList left
              let rightCode := encodeBalancedList right
              let inner := Nat.pair leftCode rightCode
              have hinner :
                  natBitLength inner ≤
                    2 * max (natBitLength leftCode)
                      (natBitLength rightCode) :=
                natBitLength_pair_le leftCode rightCode
              have hmaxPositive :
                  1 ≤ max (natBitLength leftCode)
                    (natBitLength rightCode) := by
                have hpositive : 1 ≤ natBitLength leftCode := by
                  unfold natBitLength
                  omega
                exact hpositive.trans (le_max_left _ _)
              have houter := natBitLength_pair_le 2 inner
              have hnode :
                  natBitLength (Nat.pair 2 inner) ≤
                    4 * max (natBitLength leftCode)
                      (natBitLength rightCode) := by
                apply houter.trans
                have hinnerMax :
                    max (natBitLength 2) (natBitLength inner) ≤
                      2 * max (natBitLength leftCode)
                        (natBitLength rightCode) := by
                  apply max_le
                  · norm_num [natBitLength]
                  · exact hinner
                omega
              have hleftScaled :
                  4 * natBitLength leftCode ≤
                    2 * values.length ^ 4 *
                      balancedListAtomBits values := by
                dsimp [leftCode]
                calc
                  4 * natBitLength (encodeBalancedList left) ≤
                      4 * (2 * left.length ^ 4 *
                        balancedListAtomBits left) :=
                    Nat.mul_le_mul_left 4 hleft
                  _ ≤ 2 * values.length ^ 4 *
                        balancedListAtomBits values := by
                    have hproduct :
                        4 * left.length ^ 4 *
                            balancedListAtomBits left ≤
                          values.length ^ 4 *
                            balancedListAtomBits values :=
                      Nat.mul_le_mul hleftPower hleftAtom
                    calc
                      4 * (2 * left.length ^ 4 *
                          balancedListAtomBits left) =
                          2 * (4 * left.length ^ 4 *
                            balancedListAtomBits left) := by ring
                      _ ≤ 2 * (values.length ^ 4 *
                            balancedListAtomBits values) :=
                        Nat.mul_le_mul_left 2 hproduct
                      _ = 2 * values.length ^ 4 *
                            balancedListAtomBits values := by ring
              have hrightScaled :
                  4 * natBitLength rightCode ≤
                    2 * values.length ^ 4 *
                      balancedListAtomBits values := by
                dsimp [rightCode]
                calc
                  4 * natBitLength (encodeBalancedList right) ≤
                      4 * (2 * right.length ^ 4 *
                        balancedListAtomBits right) :=
                    Nat.mul_le_mul_left 4 hright
                  _ ≤ 2 * values.length ^ 4 *
                        balancedListAtomBits values := by
                    have hproduct :
                        4 * right.length ^ 4 *
                            balancedListAtomBits right ≤
                          values.length ^ 4 *
                            balancedListAtomBits values :=
                      Nat.mul_le_mul hrightPower hrightAtom
                    calc
                      4 * (2 * right.length ^ 4 *
                          balancedListAtomBits right) =
                          2 * (4 * right.length ^ 4 *
                            balancedListAtomBits right) := by ring
                      _ ≤ 2 * (values.length ^ 4 *
                            balancedListAtomBits values) :=
                        Nat.mul_le_mul_left 2 hproduct
                      _ = 2 * values.length ^ 4 *
                            balancedListAtomBits values := by ring
              have hscaled :
                  4 * max (natBitLength leftCode)
                      (natBitLength rightCode) ≤
                    2 * values.length ^ 4 *
                      balancedListAtomBits values := by
                rcases le_total (natBitLength leftCode)
                    (natBitLength rightCode) with hle | hle
                · rw [max_eq_right hle]
                  exact hrightScaled
                · rw [max_eq_left hle]
                  exact hleftScaled
              simpa [encodeBalancedList, values, leftLength, left, right,
                leftCode, rightCode, inner, hlength] using
                hnode.trans hscaled

/-- The real register width is polynomial in sequence length and the sum of
atom widths; no depth-dependent side condition is hidden in the statement. -/
theorem balancedListCodeBits_le (values : List ℕ) :
    natBitLength (encodeBalancedList values) ≤
      1 + 2 * values.length ^ 4 * balancedListAtomBits values := by
  by_cases hnil : values = []
  · simp [hnil, encodeBalancedList, natBitLength]
  · exact (encodeBalancedList_bits_le_of_ne_nil values hnil).trans
      (Nat.le_add_left _ _)

end NearCubicWires.CanonicalBinary
end

/-! ## Balanced CNF codes (supporting declarations) -/

section

namespace NearCubicWires.BalancedCNFSATEncoding

open NearCubicWires
open NearCubicWires.CanonicalBinary

/-- One padded unit clause, definitionally matching the base
prefix-self-reduction clause. -/
def balancedPrefixUnitClause (value : Bool) (index : ℕ) :
    List (Bool × ℕ) :=
  [(value, index), (value, index), (value, index)]

/-- Committed prefix clauses in newest-first order, exactly the order produced
by repeated list cons in the base self-reducer. -/
def balancedPrefixClauses (count assignment : ℕ) :
    List (List (Bool × ℕ)) :=
  (List.range count).reverse.map fun index =>
    balancedPrefixUnitClause (assignment.testBit index) index

/-- Constant-size malformed marker carrying a base formula payload, a
binary assignment, and the number of committed prefix positions. -/
def balancedPrefixCNFMarkerOfPayload
    (payload assignment count : ℕ) : List (List (Bool × ℕ)) :=
  [[], [(true, payload)], [(false, assignment), (true, count)]]

def encodeBalancedPrefixCNFPayload
    (payload assignment count : ℕ) : ℕ :=
  Encodable.encode (balancedPrefixCNFMarkerOfPayload payload assignment count)

private def legacyDecodeCNF (code : ℕ) : List (List (Bool × ℕ)) :=
  match Encodable.decode (α := List (List (Bool × ℕ))) code with
  | some formula => formula
  | none => []

/-- Total decoder for the additive balanced-CNF query convention. -/
def decodeBalancedCNF (code : ℕ) : Option (List (List (Bool × ℕ))) :=
  match legacyDecodeCNF code with
  | [[], [(true, payload)]] =>
      match decodeBalancedList payload with
      | some clauses =>
          some (clauses.map fun clauseCode =>
            (Encodable.decode (α := List (Bool × ℕ)) clauseCode).getD [])
      | none => none
  | [[], [(true, payload)], [(false, assignment), (true, count)]] =>
      match decodeBalancedList payload with
      | some clauses =>
          some (balancedPrefixClauses count assignment ++
            clauses.map fun clauseCode =>
              (Encodable.decode (α := List (Bool × ℕ))
                clauseCode).getD [])
      | none => none
  | _ => none

/-- Validate and concatenate a list of balanced clause-code chunks. -/
def decodeBalancedClauseChunks : List ℕ → Option (List ℕ)
  | [] => some []
  | chunk :: rest => do
      let clauses ← decodeBalancedList chunk
      let suffix ← decodeBalancedClauseChunks rest
      some (clauses ++ suffix)

def decodeNestedBalancedCNFPayload (payload : ℕ) : Option (List ℕ) := do
  let chunks ← decodeBalancedList payload
  decodeBalancedClauseChunks chunks

private def decodeClauseCodes (clauses : List ℕ) :
    List (List (Bool × ℕ)) :=
  clauses.map fun clauseCode =>
    (Encodable.decode (α := List (Bool × ℕ)) clauseCode).getD []

/-- Standalone decoder for the two nested marker cases. -/
def decodeNestedBalancedCNF
    (code : ℕ) : Option (List (List (Bool × ℕ))) :=
  let legacy :=
    (Encodable.decode (α := List (List (Bool × ℕ))) code).getD []
  match legacy with
  | [[], [(false, payload)]] =>
      (decodeNestedBalancedCNFPayload payload).map decodeClauseCodes
  | [[], [(false, payload)], [(false, assignment), (true, count)]] =>
      (decodeNestedBalancedCNFPayload payload).map fun clauses =>
        balancedPrefixClauses count assignment ++ decodeClauseCodes clauses
  | _ => none

private theorem natBitLength_succ_le (value : ℕ) :
    natBitLength (value + 1) ≤ natBitLength value + 1 := by
  have hlt : value < 2 ^ natBitLength value := by
    simpa [natBitLength] using
      Nat.lt_pow_succ_log_self (b := 2) (by omega) value
  have hmono : Nat.log 2 (value + 1) ≤
      Nat.log 2 (2 ^ natBitLength value) := Nat.log_mono_right hlt
  unfold natBitLength at hmono ⊢
  rw [Nat.log_pow (by omega)] at hmono
  omega

private theorem pairSuccBits_le (left right : ℕ) :
    natBitLength (Nat.pair left right + 1) ≤
      2 * max (natBitLength left) (natBitLength right) + 1 := by
  exact (natBitLength_succ_le _).trans
    (Nat.add_le_add_right (pairCodeBits_le left right) 1)

/-- Constant-depth width bound for one prefix-constrained balanced query. -/
theorem encodeBalancedPrefixCNFPayload_bits_le
    (payload assignment count : ℕ) :
    natBitLength
        (encodeBalancedPrefixCNFPayload payload assignment count) ≤
      64 * max 1
        (max (natBitLength payload)
          (max (natBitLength assignment) (natBitLength count))) + 31 := by
  let width := max 1
    (max (natBitLength payload)
      (max (natBitLength assignment) (natBitLength count)))
  have hwidth : 1 ≤ width := Nat.le_max_left _ _
  have hpayload : natBitLength payload ≤ width :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hassignment : natBitLength assignment ≤ width :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hcount : natBitLength count ≤ width :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  let countLiteral := Nat.pair 1 count
  let countTail := Nat.pair countLiteral 0 + 1
  let assignmentLiteral := Nat.pair 0 assignment
  let fieldsClause := Nat.pair assignmentLiteral countTail + 1
  let fieldsTail := Nat.pair fieldsClause 0 + 1
  let payloadLiteral := Nat.pair 1 payload
  let payloadClause := Nat.pair payloadLiteral 0 + 1
  let payloadTail := Nat.pair payloadClause fieldsTail + 1
  have hcountLiteral : natBitLength countLiteral ≤ 2 * width := by
    have hpair := pairCodeBits_le 1 count
    have hmax : max (natBitLength 1) (natBitLength count) ≤ width :=
      max_le (by change 1 ≤ width; exact hwidth) hcount
    exact hpair.trans (Nat.mul_le_mul_left 2 hmax)
  have hcountTail : natBitLength countTail ≤ 4 * width + 1 := by
    change natBitLength (Nat.pair countLiteral 0 + 1) ≤ 4 * width + 1
    have hpair := pairSuccBits_le countLiteral 0
    have hmax : max (natBitLength countLiteral) (natBitLength 0) ≤
        2 * width :=
      max_le hcountLiteral (by change 1 ≤ 2 * width; omega)
    have hpair' := hpair.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 hmax) 1)
    omega
  have hassignmentLiteral :
      natBitLength assignmentLiteral ≤ 2 * width := by
    have hpair := pairCodeBits_le 0 assignment
    have hmax : max (natBitLength 0) (natBitLength assignment) ≤ width :=
      max_le (by change 1 ≤ width; exact hwidth) hassignment
    exact hpair.trans (Nat.mul_le_mul_left 2 hmax)
  have hfieldsClause :
      natBitLength fieldsClause ≤ 8 * width + 3 := by
    change natBitLength (Nat.pair assignmentLiteral countTail + 1) ≤
      8 * width + 3
    have hpair := pairSuccBits_le assignmentLiteral countTail
    have hmax : max (natBitLength assignmentLiteral)
        (natBitLength countTail) ≤ 4 * width + 1 :=
      max_le (by omega) hcountTail
    have hpair' := hpair.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 hmax) 1)
    omega
  have hfieldsTail : natBitLength fieldsTail ≤ 16 * width + 7 := by
    change natBitLength (Nat.pair fieldsClause 0 + 1) ≤ 16 * width + 7
    have hpair := pairSuccBits_le fieldsClause 0
    have hmax : max (natBitLength fieldsClause) (natBitLength 0) ≤
        8 * width + 3 :=
      max_le hfieldsClause (by change 1 ≤ 8 * width + 3; omega)
    have hpair' := hpair.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 hmax) 1)
    omega
  have hpayloadLiteral : natBitLength payloadLiteral ≤ 2 * width := by
    have hpair := pairCodeBits_le 1 payload
    have hmax : max (natBitLength 1) (natBitLength payload) ≤ width :=
      max_le (by change 1 ≤ width; exact hwidth) hpayload
    exact hpair.trans (Nat.mul_le_mul_left 2 hmax)
  have hpayloadClause : natBitLength payloadClause ≤ 4 * width + 1 := by
    change natBitLength (Nat.pair payloadLiteral 0 + 1) ≤ 4 * width + 1
    have hpair := pairSuccBits_le payloadLiteral 0
    have hmax : max (natBitLength payloadLiteral) (natBitLength 0) ≤
        2 * width :=
      max_le hpayloadLiteral (by change 1 ≤ 2 * width; omega)
    have hpair' := hpair.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 hmax) 1)
    omega
  have hpayloadTail : natBitLength payloadTail ≤ 32 * width + 15 := by
    change natBitLength (Nat.pair payloadClause fieldsTail + 1) ≤
      32 * width + 15
    have hpair := pairSuccBits_le payloadClause fieldsTail
    have hmax : max (natBitLength payloadClause)
        (natBitLength fieldsTail) ≤ 16 * width + 7 :=
      max_le (by omega) hfieldsTail
    have hpair' := hpair.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 hmax) 1)
    omega
  rw [show encodeBalancedPrefixCNFPayload payload assignment count =
      Nat.pair 0 payloadTail + 1 by
    simp [encodeBalancedPrefixCNFPayload,
      balancedPrefixCNFMarkerOfPayload, payloadTail, payloadClause,
      payloadLiteral, fieldsTail, fieldsClause, assignmentLiteral, countTail,
      countLiteral, Encodable.encode_list_cons,
      Encodable.encode_prod_val, Encodable.encode_true,
      Encodable.encode_false]]
  change natBitLength (Nat.pair 0 payloadTail + 1) ≤ 64 * width + 31
  have hpair := pairSuccBits_le 0 payloadTail
  have hmax : max (natBitLength 0) (natBitLength payloadTail) ≤
      32 * width + 15 :=
    max_le (by change 1 ≤ 32 * width + 15; omega) hpayloadTail
  omega

end NearCubicWires.BalancedCNFSATEncoding
end

/-! ## Boolean inputs and functions, real threshold gates, Boolean circuits (supporting declarations) -/

section

open Finset
open scoped BigOperators

namespace NearCubicWires

structure SymmetricThresholdCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  top : ℕ → Bool

noncomputable def SymmetricThresholdCircuit.eval {n : ℕ}
    (circuit : SymmetricThresholdCircuit n) (input : BitInput n) : Bool :=
  circuit.top ((Finset.univ.filter fun i => (circuit.bottom i).eval input).card)

structure ThresholdThresholdCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  topWeight : Fin bottomCount → ℝ
  topThreshold : ℝ

noncomputable def ThresholdThresholdCircuit.eval {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) (input : BitInput n) : Bool :=
  decide (circuit.topThreshold ≤
    ∑ i, circuit.topWeight i * bitAsReal ((circuit.bottom i).eval input))

def decodeCNF (code : ℕ) : EncodedCNF :=
  match Encodable.decode (α := EncodedCNF) code with
  | some formula => formula
  | none => []

def cnfVariableCount (formula : EncodedCNF) : ℕ :=
  formula.foldl
    (fun maximum clause =>
      clause.foldl (fun innerMaximum literal => max innerMaximum literal.2) maximum)
    0 + 1

def encodedLiteralEval {arity : ℕ} (harity : 0 < arity)
    (assignment : BitInput arity) (literal : Bool × ℕ) : Bool :=
  let value := assignment ⟨literal.2 % arity, Nat.mod_lt _ harity⟩
  if literal.1 then value else !value

def encodedCNFEval (formula : EncodedCNF)
    (assignment : BitInput (cnfVariableCount formula)) : Bool :=
  formula.all fun clause =>
    clause.any (encodedLiteralEval (by simp [cnfVariableCount]) assignment)

def wellSizedCNFEncoding (code : ℕ) (formula : EncodedCNF) : Bool :=
  formula.length ≤ natBitLength code &&
    formula.all fun clause =>
      clause.length = 3 &&
        clause.all fun literal => literal.2 < natBitLength code

/-- The base SAT-query semantics, unchanged for every ordinary
well-sized CNF code. -/
def legacyEncodedSat (code : ℕ) : Bool :=
  let formula := decodeCNF code
  if wellSizedCNFEncoding code formula then
    (List.range (2 ^ cnfVariableCount formula)).any fun assignmentCode =>
      encodedCNFEval formula fun index => assignmentCode.testBit index.val
  else false

/-- SAT on the unchanged canonical ABI, extended only on the two disjoint
malformed markers owned by `BalancedCNFSATEncoding`.  Each balanced branch
decodes the explicit clause list and then applies the exact base
well-sized semantics to that formula.

The first two branches are unchanged: every well-sized canonical code still gets
`legacyEncodedSat` verbatim, and every level-1 balanced marker still gets the
base answer on its decoded formula.  The third branch is reached only
when both earlier decoders reject, and it recognizes exactly the level-2
nested marker (payload literal `false` instead of `true`), which the
base well-sizedness gate rejects — see
`NestedBalancedCNFCodec.legacyEncodedSat_encodeNestedBalancedCNFPayloadMarker`
and its prefix companion.  The extension is therefore conservative: no query
that any earlier semantics answered changes its answer. -/
def encodedSat (code : ℕ) : Bool :=
  let formula := decodeCNF code
  if wellSizedCNFEncoding code formula then
    legacyEncodedSat code
  else
    match BalancedCNFSATEncoding.decodeBalancedCNF code with
    | some balancedFormula =>
        legacyEncodedSat (Encodable.encode balancedFormula)
    | none =>
        match BalancedCNFSATEncoding.decodeNestedBalancedCNF code with
        | some nestedFormula =>
            legacyEncodedSat (Encodable.encode nestedFormula)
        | none => false

inductive NPOracleInstruction where
  | halt (outputRegister : ℕ)
  | set (register value next : ℕ)
  | copy (source destination next : ℕ)
  | increment (register next : ℕ)
  /-- Total predecessor, saturating at zero. -/
  | decrement (register next : ℕ)
  /-- Binary addition; bounded writes charge the result's actual bit width. -/
  | add (left right destination next : ℕ)
  /-- Binary subtraction, saturating at zero as for `Nat.sub`. -/
  | subtract (left right destination next : ℕ)
  | pair (left right destination next : ℕ)
  | unpairLeft (source destination next : ℕ)
  | unpairRight (source destination next : ℕ)
  | branchZero (register zeroTarget nonzeroTarget : ℕ)
  /-- Total canonical binary encoding. `CanonicalBinary.encodeNat_bits_le`
  supplies its explicit polynomial bit-cost simulation charge. -/
  | encodeNat (source destination next : ℕ)
  /-- Total logical right shift by an immediate amount. -/
  | shiftRight (source amount destination next : ℕ)
  /-- Total logical left shift by an immediate amount.  Successful execution
  still requires the shifted result to fit the advertised register width. -/
  | shiftLeft (source amount destination next : ℕ)
  /-- Random-access binary digit extraction.  The index is a register because
  signed-plane controllers select a run-time bit while retaining logarithmic
  input width; the result is always one bit. -/
  | testBit (source index destination next : ℕ)
  | sat (queryRegister destination next : ℕ)
  deriving Repr

abbrev NPOracleProgram := List NPOracleInstruction

structure NPOracleState where
  pc : ℕ
  registers : ℕ → ℕ

def NPOracleState.write (state : NPOracleState) (register value : ℕ) :
    NPOracleState :=
  { state with registers := fun candidate =>
      if candidate = register then value else state.registers candidate }

def NPOracleState.jump (state : NPOracleState) (pc : ℕ) : NPOracleState :=
  { state with pc }

def NPOracleState.boundedWrite (state : NPOracleState) (maximumBits register value : ℕ) :
    Option NPOracleState :=
  if natBitLength value ≤ maximumBits then some (state.write register value) else none

/-- Fuel and register bit length are bounded independently.  Bounding both by
`2^(O(n))` keeps a standard bit-cost simulation within `2^(O(n))`. -/
def runNPOracleProgram (program : NPOracleProgram) (maximumBits : ℕ) :
    ℕ → NPOracleState → Option ℕ
  | 0, _ => none
  | fuel + 1, state =>
      match program[state.pc]? with
      | none => none
      | some (.halt outputRegister) =>
          if natBitLength (state.registers outputRegister) ≤ maximumBits then
            some (state.registers outputRegister)
          else none
      | some (.set register value next) =>
          match state.boundedWrite maximumBits register value with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel (nextState.jump next)
      | some (.copy source destination next) =>
          match state.boundedWrite maximumBits destination (state.registers source) with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel (nextState.jump next)
      | some (.increment register next) =>
          match state.boundedWrite maximumBits register (state.registers register + 1) with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel (nextState.jump next)
      | some (.decrement register next) =>
          match state.boundedWrite maximumBits register (Nat.pred (state.registers register)) with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel (nextState.jump next)
      | some (.add left right destination next) =>
          match state.boundedWrite maximumBits destination
              (state.registers left + state.registers right) with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel (nextState.jump next)
      | some (.subtract left right destination next) =>
          match state.boundedWrite maximumBits destination
              (state.registers left - state.registers right) with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel (nextState.jump next)
      | some (.pair left right destination next) =>
          match state.boundedWrite maximumBits destination
              (Nat.pair (state.registers left) (state.registers right)) with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel (nextState.jump next)
      | some (.unpairLeft source destination next) =>
          match state.boundedWrite maximumBits destination
              (Nat.unpair (state.registers source)).1 with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel (nextState.jump next)
      | some (.unpairRight source destination next) =>
          match state.boundedWrite maximumBits destination
              (Nat.unpair (state.registers source)).2 with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel (nextState.jump next)
      | some (.branchZero register zeroTarget nonzeroTarget) =>
          runNPOracleProgram program maximumBits fuel
            (state.jump (if state.registers register = 0 then
              zeroTarget else nonzeroTarget))
      | some (.encodeNat source destination next) =>
          match state.boundedWrite maximumBits destination
              (CanonicalBinary.encodeNat (state.registers source)) with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel
                (nextState.jump next)
      | some (.shiftRight source amount destination next) =>
          match state.boundedWrite maximumBits destination
              (Nat.shiftRight (state.registers source) amount) with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel
                (nextState.jump next)
      | some (.shiftLeft source amount destination next) =>
          match state.boundedWrite maximumBits destination
              (Nat.shiftLeft (state.registers source) amount) with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel
                (nextState.jump next)
      | some (.testBit source index destination next) =>
          match state.boundedWrite maximumBits destination
              (((state.registers source).testBit
                (state.registers index)).toNat) with
          | none => none
          | some nextState =>
              runNPOracleProgram program maximumBits fuel
                (nextState.jump next)
      | some (.sat queryRegister destination next) =>
          if natBitLength (state.registers queryRegister) ≤ maximumBits then
            match state.boundedWrite maximumBits destination
                (encodedSat (state.registers queryRegister)).toNat with
            | none => none
            | some nextState =>
                runNPOracleProgram program maximumBits fuel (nextState.jump next)
          else none

def initialNPOracleState (inputLength inputCode : ℕ) : NPOracleState where
  pc := 0
  registers := fun register =>
    if register = 0 then inputCode else if register = 1 then inputLength else 0

end NearCubicWires
end

/-! ## Matrices, literals, 3-CNF formulas, projected random bits and parity (supporting declarations) -/

section

open Finset
open scoped BigOperators

namespace NearCubicWires.SourceInterfaces

open NearCubicWires

structure ThreeCNF (arity : ℕ) where
  clauses : List (Fin 3 → Literal arity)

def ThreeCNF.eval {arity : ℕ} (formula : ThreeCNF arity)
    (assignment : BitInput arity) : Bool :=
  formula.clauses.all fun clause => ∃ i, (clause i).eval assignment

inductive ProjectedRandomBit (width : ℕ) where
  | bit (index : Fin width)
  | negatedBit (index : Fin width)
  | constant (value : Bool)

def ProjectedRandomBit.eval {width : ℕ} (projection : ProjectedRandomBit width)
    (randomness : BitInput width) : Bool :=
  match projection with
  | .bit index => randomness index
  | .negatedBit index => !(randomness index)
  | .constant value => value

structure TwoLiteralClause (arity : ℕ) where
  left : Literal arity
  right : Literal arity

def TwoLiteralClause.eval {arity : ℕ} (clause : TwoLiteralClause arity)
    (assignment : BitInput arity) : Bool :=
  clause.left.eval assignment || clause.right.eval assignment

structure TimeConstructible (bound : ℕ → ℕ) where
  program : NPOracleProgram
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  oracleFree : program.all (fun instruction => match instruction with
    | .halt _ => true
    | .set _ _ _ => true
    | .copy _ _ _ => true
    | .increment _ _ => true
    | .decrement _ _ => true
    | .add _ _ _ _ => true
    | .subtract _ _ _ _ => true
    | .pair _ _ _ _ => true
    | .unpairLeft _ _ _ => true
    | .unpairRight _ _ _ => true
    | .branchZero _ _ _ => true
    | .encodeNat _ _ _ => true
    | .shiftRight _ _ _ _ => true
    | .shiftLeft _ _ _ _ => true
    | .testBit _ _ _ _ => true
    | .sat _ _ _ => false
    ) = true
  computesBound : ∀ n,
    runNPOracleProgram program (coefficient * (bound n + 1))
      (coefficient * (bound n + 1))
      (initialNPOracleState n n) = some (bound n)

end NearCubicWires.SourceInterfaces
end

/-! ## Ordinary programs, word functions, verifiers, hierarchies and weak machines; projection and literal codes (supporting declarations) -/

section

namespace NearCubicWires.RepairSource

open SourceInterfaces LocalBitMultitape ExecutableInterfaces CanonicalBinary

set_option autoImplicit false

def projectionCode {r : ℕ} (p : ProjectedRandomBit r) : ℕ :=
  match p with
  | .bit i => Nat.pair 0 i.val
  | .negatedBit i => Nat.pair 1 i.val
  | .constant b => Nat.pair 2 b.toNat

end NearCubicWires.RepairSource
end

/-! ## Satisfiability of encoded CNF formulas (supporting declarations) -/

section

namespace NearCubicWires.RepairSource.RecoveryOracle

set_option autoImplicit false

open TseitinCNF BalancedCNFSATEncoding

/-- Mathematical specification; the efficient verifier is compactVerifier. -/
noncomputable def correctedSat (code : Nat) : Bool :=
  if wellSizedCNFEncoding code (decodeCNF code) then legacyEncodedSat code
  else
    match decodeBalancedCNF code with
    | some formula => formula.all (fun clause => clause.length = 3) && mathSat formula
    | none => match decodeNestedBalancedCNF code with
      | some formula => formula.all (fun clause => clause.length = 3) && mathSat formula
      | none => false

end NearCubicWires.RepairSource.RecoveryOracle
end

/-! ## The SAT oracle on encoded formulas (supporting declarations) -/

section

namespace NearCubicWires.RepairSource.RecoveryOracle

set_option autoImplicit false

open CanonicalBinary BalancedCNFSATEncoding

/-- Wrapping an arbitrary source query has constant pairing depth. -/
def liftSourceSAT (code : Nat) : Nat :=
  Encodable.encode ([[], [(true, code)]] : EncodedCNF)

theorem corrected_liftSourceSAT (code : Nat) :
    correctedSat (liftSourceSAT code) = sourceSAT code := by
  have hraw : wellSizedCNFEncoding (liftSourceSAT code)
      (decodeCNF (liftSourceSAT code)) = false := by
    simp [liftSourceSAT, decodeCNF, wellSizedCNFEncoding]
  have hflat : decodeBalancedCNF (liftSourceSAT code) = decodeSourceSAT code := by
    simp [decodeBalancedCNF, legacyDecodeCNF, liftSourceSAT,
      decodeSourceSAT]
    cases decodeBalancedList code <;> rfl
  have hnested : decodeNestedBalancedCNF (liftSourceSAT code) = none := by
    simp [decodeNestedBalancedCNF, liftSourceSAT]
  simp only [correctedSat, hraw, Bool.false_eq_true, if_false, hflat]
  cases hdecode : decodeSourceSAT code <;> simp [sourceSAT, hdecode, hnested]

theorem liftSourceSAT_bits (code : Nat) :
    natBitLength (liftSourceSAT code) ≤ 16 * max 1 (natBitLength code) + 7 := by
  let width := max 1 (natBitLength code)
  have hw : 1 ≤ width := Nat.le_max_left _ _
  have hc : natBitLength code ≤ width := Nat.le_max_right _ _
  have h0 : natBitLength 0 = 1 := rfl
  have h1 : natBitLength 1 = 1 := by decide
  have hl : natBitLength (Nat.pair 1 code) ≤ 2 * width := by
    apply (pairCodeBits_le _ _).trans
    exact Nat.mul_le_mul_left 2 (max_le (h1 ▸ hw) hc)
  have hcl : natBitLength (Nat.pair (Nat.pair 1 code) 0 + 1) ≤ 4 * width + 1 := by
    apply (pairSuccBits_le _ _).trans
    have hm := max_le hl (show natBitLength 0 ≤ 2 * width by rw [h0]; omega)
    omega
  have ht : natBitLength (Nat.pair (Nat.pair (Nat.pair 1 code) 0 + 1) 0 + 1) ≤
      8 * width + 3 := by
    apply (pairSuccBits_le _ _).trans
    have hm := max_le hcl
      (show natBitLength 0 ≤ 4 * width + 1 by rw [h0]; omega)
    omega
  change natBitLength (Nat.pair 0 (Nat.pair (Nat.pair (Nat.pair 1 code) 0 + 1) 0 + 1) + 1) ≤
    16 * width + 7
  apply (pairSuccBits_le _ _).trans
  have hm := max_le (show natBitLength 0 ≤ 8 * width + 3 by rw [h0]; omega) ht
  omega

end NearCubicWires.RepairSource.RecoveryOracle
end

/-! ## Number words (supporting declarations) -/

section

namespace NearCubicWires.RepairRepresentation

open SourceInterfaces ExecutableInterfaces RepairSource LocalBitMultitape CanonicalBinary
open WilliamsPublishedForm
open WilliamsProductCertificate
open scoped BigOperators

set_option autoImplicit false

def intWord (z : ℤ) : List Bool := decide (z < 0) :: natWord z.natAbs

def natListWord (xs : List ℕ) : List Bool :=
  natWord xs.length ++ xs.flatMap natWord

def literalIndex {n : ℕ} (l : Literal n) : ℕ :=
  match l with
  | .positive i => 2 * i.val
  | .negative i => 2 * i.val + 1

end NearCubicWires.RepairRepresentation
end

/-! ## Theorem 2.5 of the author's earlier near-cubic wire paper (shared code) (supporting declarations) -/

section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.defProp false

namespace NearCubicWires.Paper

open NearCubicWires RepairSource RepairRepresentation SourceInterfaces

set_option autoImplicit false

/-- Paper Theorem 2.5 written with every local definition expanded. -/
noncomputable def theorem_2_5 : Prop :=
  ∀ gamma : ℝ, 0 < gamma → gamma < 1 / 2 →
    ∃ language : (n : ℕ) → (Fin n → Bool) → Bool,
    ∃ bS bT : ℝ,
      (∃ oracle : ℕ → Bool, Nonempty (EncodedNPVerifier oracle) ∧
        Nonempty (OrdinaryENPCertificate oracle language)) ∧
      0 < bS ∧ 0 < bT ∧
      ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
        (∀ circuit : SymmetricThresholdCircuit n,
          1 / 2 + gamma ≤
            ((Finset.univ.filter fun x => circuit.eval x = language n x).card : ℝ) /
              (Fintype.card (Fin n → Bool) : ℝ) →
          bS * (n : ℝ) ^ 3 / (Nat.clog 2 (n + 2) : ℝ) ^ 5 <
            (∑ i : Fin circuit.bottomCount,
              ((circuit.bottom i).support.card + 1) : ℕ)) ∧
        (∀ circuit : ThresholdThresholdCircuit n,
          1 / 2 + gamma ≤
            ((Finset.univ.filter fun x => circuit.eval x = language n x).card : ℝ) /
              (Fintype.card (Fin n → Bool) : ℝ) →
          bT * (n : ℝ) ^ 3 / (Nat.clog 2 (n + 2) : ℝ) ^ 9 <
            (∑ i : Fin circuit.bottomCount,
              if circuit.topWeight i = 0 then 0
              else (circuit.bottom i).support.card + 1 : ℕ))

end NearCubicWires.Paper
end

/-! ## HLW06 Theorem 8.2, expander spectrum (shared code; not an input here) (supporting declarations) -/

section

namespace NearCubicWires.Bindings.HLW06

open NearCubicWires NearCubicWires.SourceInterfaces Matrix
open scoped BigOperators

set_option autoImplicit false

/-- HLW Construction 8.1: "the vertex set V = Zn × Zn". -/
abbrev V (n : ℕ) := ZMod n × ZMod n

/-- HLW Construction 8.1: "T1 = (1 2; 0 1)". -/
def T1 {n : ℕ} : Matrix (Fin 2) (Fin 2) (ZMod n) := !![1, 2; 0, 1]

/-- HLW Construction 8.1: "T2 = (1 0; 2 1)". -/
def T2 {n : ℕ} : Matrix (Fin 2) (Fin 2) (ZMod n) := !![1, 0; 2, 1]

/-- HLW Construction 8.1: "e1 = (1; 0)". -/
def e1 {n : ℕ} : V n := (1, 0)

/-- HLW Construction 8.1: "e2 = (0; 1)". -/
def e2 {n : ℕ} : V n := (0, 1)

/-- `T v` for the vertex `v = (x, y)` read as the column vector `(x; y)`, mod n. -/
def act {n : ℕ} (T : Matrix (Fin 2) (Fin 2) (ZMod n)) (v : V n) : V n :=
  ((T *ᵥ ![v.1, v.2]) 0, (T *ᵥ ![v.1, v.2]) 1)

/-- The four transformations of Construction 8.1, in HLW's order:
`v ↦ T1v, T2v, T1v + e1, T2v + e2`. -/
def forward {n : ℕ} (i : Fin 4) (v : V n) : V n :=
  ![act T1 v, act T2 v, act T1 v + e1, act T2 v + e2] i

/-- An explicit two-sided inverse, used ONLY to prove that `forward i` is a bijection. The
definition of the graph uses `Equiv.symm`, not this formula. -/
def backward {n : ℕ} (i : Fin 4) (v : V n) : V n :=
  ![(v.1 - 2 * v.2, v.2), (v.1, v.2 - 2 * v.1),
    (v.1 - 1 - 2 * v.2, v.2), (v.1, v.2 - 1 - 2 * v.1)] i

theorem act_T1 {n : ℕ} (v : V n) : act T1 v = (v.1 + 2 * v.2, v.2) := by
  simp [act, T1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem act_T2 {n : ℕ} (v : V n) : act T2 v = (v.1, 2 * v.1 + v.2) := by
  simp [act, T2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem forward_backward {n : ℕ} (i : Fin 4) (v : V n) : forward i (backward i v) = v := by
  fin_cases i <;> simp [forward, backward, act_T1, act_T2, e1, e2]

theorem backward_forward {n : ℕ} (i : Fin 4) (v : V n) : backward i (forward i v) = v := by
  fin_cases i <;> simp [forward, backward, act_T1, act_T2, e1, e2]

theorem forward_bijective {n : ℕ} (i : Fin 4) : Function.Bijective (forward (n := n) i) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨backward i, fun v => backward_forward i v, fun v => forward_backward i v⟩

/-- The four transformations as bijections of `V`. -/
noncomputable def transformation {n : ℕ} (i : Fin 4) : V n ≃ V n :=
  Equiv.ofBijective (forward i) (forward_bijective i)

/-- **HLW Construction 8.1, the neighbours of `v`:** "the four vertices T1v, T2v, T1v + e1,
T2v + e2, and the other four neighbors of v obtained by the four inverse transformations". -/
noncomputable def neighbor {n : ℕ} (k : Fin 8) (v : V n) : V n :=
  ![transformation 0 v, transformation 1 v, transformation 2 v, transformation 3 v,
    (transformation 0).symm v, (transformation 1).symm v, (transformation 2).symm v,
    (transformation 3).symm v] k

/-- The neighbour multiset of `v` (loops and multiple edges kept). -/
noncomputable def neighbors {n : ℕ} (v : V n) : Multiset (V n) :=
  Finset.univ.val.map fun k : Fin 8 => neighbor k v

/-- **HLW §2.3 adjacency matrix of `G_n`:** the `(u, w)` entry is "the number of edges in G
between vertex u and vertex w", the multiplicity of `w` among the neighbours of `u`. -/
noncomputable def adjacency (n : ℕ) : Matrix (V n) (V n) ℝ :=
  fun u w => ((neighbors u).count w : ℝ)

/-- HLW label `k` ↦ the label of its inverse transformation. -/
def inverseLabel : Fin 8 → Fin 8 := ![4, 5, 6, 7, 0, 1, 2, 3]

def inverseLabelEquiv : Fin 8 ≃ Fin 8 where
  toFun := inverseLabel
  invFun := inverseLabel
  left_inv := by intro k; fin_cases k <;> rfl
  right_inv := by intro k; fin_cases k <;> rfl

theorem neighbor_inverseLabel_iff {n : ℕ} (k : Fin 8) (u w : V n) :
    w = neighbor (inverseLabel k) u ↔ u = neighbor k w := by
  fin_cases k <;> simp only [neighbor, inverseLabel] <;>
    simp <;> constructor <;> rintro rfl <;> simp

theorem adjacency_apply {n : ℕ} (u w : V n) :
    adjacency n u w = ∑ k : Fin 8, if w = neighbor k u then (1 : ℝ) else 0 := by
  unfold adjacency neighbors
  rw [Multiset.count_map, ← Finset.filter_val, ← Finset.card_def, Finset.card_filter]
  push_cast
  rfl

theorem adjacency_symm {n : ℕ} (u w : V n) : adjacency n u w = adjacency n w u := by
  rw [adjacency_apply, adjacency_apply,
    ← Equiv.sum_comp inverseLabelEquiv (fun k => if w = neighbor k u then (1 : ℝ) else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact if_congr (neighbor_inverseLabel_iff k u w) rfl rfl

/-- HLW §2.3: "Being real and symmetric". -/
theorem adjacency_isHermitian (n : ℕ) : (adjacency n).IsHermitian :=
  Matrix.IsHermitian.ext fun i j => by rw [star_trivial]; exact adjacency_symm j i

/-- HLW §2.4, PDF p.16: "λ = λ(G) = max(|λ2|, |λn|)", where (§2.3) "λ1 ≥ λ2 ≥ · · · ≥ λn" are the
eigenvalues of the real symmetric adjacency matrix. HLW's `λi` is `eigenvalues₀ ⟨i - 1, _⟩`,
so `λ2 = eigenvalues₀ ⟨1, _⟩` and `λn = eigenvalues₀ ⟨|V| - 1, _⟩`. The hypothesis `2 ≤ |V|`
is what makes `λ2` exist. -/
noncomputable def hlwLambda {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (h2 : 2 ≤ Fintype.card W) : ℝ :=
  max |hA.eigenvalues₀ ⟨1, by omega⟩| |hA.eigenvalues₀ ⟨Fintype.card W - 1, by omega⟩|

/-- **HLW06 Theorem 8.2 (Gabber–Galil [GG81]), PDF p.65, verbatim:**
"The graph Gn satisfies λ(Gn) ≤ 5√2 < 8 for every positive integer n."

`[NeZero n]` says that `n` is a positive integer. `λ(G_n) = max(|λ2|, |λn|)` is asserted
whenever `λ2` exists (`2 ≤ |V| = n²`, i.e. `n ≥ 2`).

**The edge `n = 1`.** `G_1` has one vertex and eight
loops, so its adjacency matrix is `(8)`. Its only eigenvalue is `λ1 = λn = 8`
(`G1_eigenvalue`), and `λ2` does not exist. The printed formula `max(|λ2|, |λn|)` is therefore
undefined at `n = 1`. A transcription that reads `λ(G_1)` as `|λn|` would make the theorem
FALSE there (`G1_naive_lambda_false`: `¬ |λn(G_1)| ≤ 5√2`). HLW's own words, "λ is the largest
absolute value of an eigenvalue other than λ1 = d" (PDF p.16), give the empty maximum at a
single vertex. So this literal asserts the bound exactly when `λ2` exists, which is the weakest
faithful reading. The imported `ExpanderSpectrumContract` is vacuous at `m = 1`, because a
mean-zero vector on one vertex is zero, and `hlw06_to_import` handles that case directly. -/
def HLW06_Theorem8_2 : Prop :=
  ∀ (n : ℕ) [NeZero n] (h2 : 2 ≤ Fintype.card (V n)),
    hlwLambda (adjacency n) (adjacency_isHermitian n) h2 ≤ 5 * Real.sqrt 2 ∧
      5 * Real.sqrt 2 < 8

end NearCubicWires.Bindings.HLW06
end

/-! ## RS62 Theorem 4, the prime theta bound (shared code; not an input here) (supporting declarations) -/

section

namespace NearCubicWires.Bindings.RS62

open NearCubicWires NearCubicWires.SourceInterfaces
open scoped BigOperators

set_option autoImplicit false

/-- RS62 §2, PDF p.1 (printed p.64): `ϑ(x)` is "the logarithm of the product of all primes
≦ x" (natural logarithm, see the module docstring for (2.15)-(2.17)). -/
noncomputable def theta (x : ℝ) : ℝ :=
  Real.log (∏ᶠ p ∈ {p : ℕ | p.Prime ∧ (p : ℝ) ≤ x}, (p : ℝ))

/-- **RS62 Theorem 4, eq. (3.14), PDF page 7 (printed p.70), verbatim:**
"THEOREM 4. We have (3.14) x(1 − 1/(2 log x)) < ϑ(x) for 563 ≦ x," -/
def RS62_Theorem4_eq314 : Prop :=
  ∀ x : ℝ, 563 ≤ x → x * (1 - 1 / (2 * Real.log x)) < theta x

end NearCubicWires.Bindings.RS62
end

/-! ## Projection PCP circuits (used by input 6) (supporting declarations) -/

section

namespace NearCubicWires.Bindings.CLW20Lemma310

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape

set_option autoImplicit false

/-- Output bit `r·j + i` of `Q : {0,1}^r → {0,1}^{rt}` is bit `i` of `q_j`, where
"(q1, …, qt) = Q(z)". -/
def blockIndex {r t : ℕ} (j : Fin t) (i : Fin r) : Fin (r * t) :=
  ⟨r * j + i,
    calc r * (j : ℕ) + i < r * (j + 1) :=
          (Nat.add_lt_add_left i.isLt _).trans_eq (by rw [Nat.mul_add, Nat.mul_one])
      _ ≤ r * t := Nat.mul_le_mul_left _ j.isLt⟩

/-- "circuits Q: {0,1}^r → {0,1}^{rt} … and R: {0,1}^t → {0,1}", described as the Complexity
item says. "Q is a projection, i.e., each output bit of Q is a bit of input, the negation of a
bit, or a constant": `Q k` is that description of output bit `k`, over Q's input `z`.
"R is a 3CNF": `R` is the formula. -/
structure Circuits where
  r : ℕ
  t : ℕ
  Q : Fin (r * t) → ProjectedRandomBit r
  R : ThreeCNF t

/-- `Q(z) ∈ {0,1}^{rt}`. -/
def Circuits.evalQ (P : Circuits) (z : BitInput P.r) : BitInput (P.r * P.t) :=
  fun k => (P.Q k).eval z

/-- `q_j ∈ {0,1}^r`, where "(q1, …, qt) = Q(z)". -/
def Circuits.query (P : Circuits) (z : BitInput P.r) (j : Fin P.t) : BitInput P.r :=
  fun i => P.evalQ z (blockIndex j i)

/-- `R(π(q1), …, π(qt))`. -/
def Circuits.accepts (P : Circuits) (π : BitInput P.r → Bool) (z : BitInput P.r) : Bool :=
  P.R.eval fun j => π (P.query z j)

/-- Tier 1 output word: `r`, `t`, the projection code of each of the `r·t` output bits of Q in
order, then R's clauses (the explicit format of the import's `RawProjectionPCP.word`). -/
def Circuits.word (P : Circuits) : List Bool :=
  frame P.r.bits ++ frame P.t.bits ++
  (List.ofFn fun k : Fin (P.r * P.t) => frame (projectionCode (P.Q k)).bits).flatten ++
  frame P.R.clauses.length.bits ++
  (P.R.clauses.map fun clause =>
    (List.ofFn fun i : Fin 3 => frame (literalCode (clause i)).bits).flatten).flatten

/-- "M … running in time T = T(n) … on inputs of the form (x, y) where |x| = n": on EVERY
`(x, y)`, M halts within `T(n)` steps. -/
def RunsInTime (M : OrdinaryVerifier) (T : ℕ → ℕ) : Prop :=
  ∀ n (x : BitInput n) (y : List Bool), ∃ receipt,
    run M.machine (T n) (M.inputTapes (List.ofFn x) y) = some receipt

end NearCubicWires.Bindings.CLW20Lemma310
end

/-! ## Input 6: the short PCP (CLW20 Lemma 3.10) (supporting declarations) -/

section

namespace NearCubicWires.Bindings.CLW20Lemma310TM2

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
open NearCubicWires.Bindings.CLW20Lemma310

set_option autoImplicit false

/-- CLW20 Lemma 3.10 (PDF p.18) with its properties claimed for `n ≥ n₀` and time hypothesis
`runsInTime`, the constructor in Mathlib's TM2 model. The conjuncts follow the printed order, as
in the Tier 1 `lemma3_10Core`. -/
def lemma3_10CoreTM2 (n₀ : ℕ) (runsInTime : OrdinaryVerifier → (ℕ → ℕ) → Prop) : Prop :=
  ∀ (M : OrdinaryVerifier) (T : ℕ → ℕ), (∀ n, n ≤ T n) → runsInTime M T →
  ∃ out : InputRequest → Circuits,
    -- "Given x ∈ {0,1}^n, one can output in poly(n, log T) time circuits Q … and R" (Tier 2;
    -- the time bound T(n) is supplied in binary)
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun x : InputRequest => frame (List.ofFn x.2) ++ frame (T x.1).bits)
      (fun w : List Bool => w) (fun x => (out x).word)) ∧
    -- "for t = poly(r)"
    (∃ K e : ℕ, ∀ x : InputRequest, n₀ ≤ x.1 → (out x).t ≤ K * ((out x).r + 1) ^ e) ∧
    -- "Proof length. 2^r ≤ T · polylogT."
    (∃ K e : ℕ, ∀ x : InputRequest, n₀ ≤ x.1 →
      2 ^ (out x).r ≤ K * T x.1 * logScale (T x.1) ^ e) ∧
    -- "Completeness. If there is a y ∈ {0,1}^{T(n)} such that M(x, y) accepts then there is a
    -- map π: {0,1}^r → {0,1} such that for all z ∈ {0,1}^r, R(π(q1), …, π(qt)) = 1"
    (∀ x : InputRequest, n₀ ≤ x.1 →
      (∃ y : BitInput (T x.1), M.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∃ π : BitInput (out x).r → Bool, ∀ z, (out x).accepts π z = true) ∧
    -- "Soundness. If no y ∈ {0,1}^{T(n)} causes M(x, y) to accept, then for every map π, at most
    -- 2^r/n^10 distinct z ∈ {0,1}^r have R(π(q1), …, π(qt)) = 1"
    (∀ x : InputRequest, n₀ ≤ x.1 →
      (¬ ∃ y : BitInput (T x.1), M.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∀ π : BitInput (out x).r → Bool,
        ((Finset.univ.filter fun z => (out x).accepts π z = true).card : ℝ) ≤
          (2 : ℝ) ^ (out x).r / (x.1 : ℝ) ^ 10)

/-- **CLW20 Lemma 3.10, literal (Tier 2)**: time `T` on every input `(x, y)`, properties for
`n ≥ 1`, the constructor a Mathlib polynomial-time TM2 machine. -/
def CLW20_Lemma3_10_TM2 : Prop :=
  lemma3_10CoreTM2 1 RunsInTime

end NearCubicWires.Bindings.CLW20Lemma310TM2
end

/-! ## Circuits with a designated input (used by input 9) (supporting declarations) -/

section

namespace NearCubicWires.Bindings.CLW20Lemma311

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape
open scoped BigOperators

set_option autoImplicit false

/-- The circuits the lemma is read on: those with at least `n₀` inputs. -/
abbrev CircuitFrom (n₀ : ℕ) := {C : Circuit // n₀ ≤ C.n}

/-- "a 2-SAT instance F on the variable set Y ∪ Z", together with `Enc`.
`Ybits = |Y|` and `Zbits = |Z|`, and the Y variables are the indices below `|Y|`.
"the number of clauses in the 2-SAT instance F is a power of 2": there are `2 ^ clauseBits`
clauses, and each one is an OR of two literals.
"Enc_i(x) is a parity function": `Enc_i(x)` is the XOR of `x` over `encSupport i`. -/
structure Instance (n : ℕ) where
  Ybits : ℕ
  Zbits : ℕ
  clauseBits : ℕ
  clauses : Fin (2 ^ clauseBits) → TwoLiteralClause (Ybits + Zbits)
  encSupport : Fin Ybits → Finset (Fin n)

/-- `Enc(x) ∈ {0,1}^|Y|`, with `Enc_i(x) = ⊕_{j ∈ encSupport i} x_j`. -/
noncomputable def Instance.enc {n : ℕ} (F : Instance n) (x : BitInput n) : BitInput F.Ybits :=
  fun i => parityOn (F.encSupport i) x

/-- The assignment behind "F|Y=Enc(x)" with the Z variables set to `z`. -/
noncomputable def Instance.restrict {n : ℕ} (F : Instance n) (x : BitInput n)
    (z : BitInput F.Zbits) : BitInput (F.Ybits + F.Zbits) :=
  Fin.addCases (F.enc x) z

/-- The fraction of the clauses of `F|Y=Enc(x)` that the Z-assignment `z` satisfies. -/
noncomputable def Instance.fraction {n : ℕ} (F : Instance n) (x : BitInput n)
    (z : BitInput F.Zbits) : ℝ :=
  ((Finset.univ.filter fun i => (F.clauses i).eval (F.restrict x z)).card : ℝ) /
    (2 ^ F.clauseBits : ℝ)

/-- Tier 1 output word of the explicit-Enc reading: `F` with the support of every `Enc_i`
listed between the counts and the clauses (the import's `pcppOutput` layout). -/
def Instance.formulaEncWord {n : ℕ} (F : Instance n) : List Bool :=
  natListWord [F.Ybits, F.Zbits, F.clauseBits] ++
    (List.ofFn (fun i : Fin F.Ybits =>
      List.ofFn (fun j : Fin n => decide (j ∈ F.encSupport i)))).flatten ++
    natListWord ((List.ofFn fun i : Fin (2 ^ F.clauseBits) =>
      [literalIndex (F.clauses i).left, literalIndex (F.clauses i).right]).flatten)

end NearCubicWires.Bindings.CLW20Lemma311
end

/-! ## The amplifier of input 8 (CLW20 Lemma 3.9) (supporting declarations) -/

section

namespace NearCubicWires.Bindings.CLW20Lemma39TM2

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource
open NearCubicWires.Bindings.CLW20Lemma39

set_option autoImplicit false

/-- **CLW20 Lemma 3.9, literal (Tier 2).** "There is a constant c ≥ 1 such that, for any
time-constructible function S(n) and every f ..." -/
def CLW20_Lemma3_9_TM2 : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ S : ℕ → ℕ, TimeConstructible S → Nonempty (Lemma3_9AtTM2 c S)

end NearCubicWires.Bindings.CLW20Lemma39TM2
end

/-! ## CW19 Proposition 18(2) (shared code; not an input here) (supporting declarations) -/

section

namespace NearCubicWires.Bindings.CW19

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
open NearCubicWires.ExecutableInterfaces
open scoped BigOperators

set_option autoImplicit false

/-- CW19 p.13: "Let x ∈ {0, 1}^n." The 0-1 vectors in `ℤ^n`. -/
def IsBoolVec {n : ℕ} (x : Fin n → ℤ) : Prop := ∀ i, x i = 0 ∨ x i = 1

/-- CW19 Appendix B, Lemma 49, p.41: "Let G be a THR gate on n bits,
G(x) := [Σ_{i=1}^n w_i · x_i > T], such that all w_i's and T are integers". -/
structure THRGate (n : ℕ) where
  w : Fin n → ℤ
  T : ℤ

/-- `G(x) := [Σ_{i=1}^n w_i · x_i > T]` (Lemma 49, p.41). -/
def THRGate.eval {n : ℕ} (G : THRGate n) (x : Fin n → ℤ) : Bool :=
  decide (∑ i, G.w i * x i > G.T)

/-- CW19 p.13: "ETHR_{w,t}(x) (the exact threshold function) is the indicator function for the
condition w · x = t." Integral, as every ETHR gate built in Appendix B. -/
structure ETHRGate (n : ℕ) where
  w : Fin n → ℤ
  t : ℤ

/-- `ETHR_{w,t}(x) = [w · x = t]`. -/
def ETHRGate.eval {n : ℕ} (E : ETHRGate n) (x : Fin n → ℤ) : Bool :=
  decide (∑ i, E.w i * x i = E.t)

/-- A DOR ◦ ETHR circuit on `n` inputs: one top DOR gate whose inputs are the ETHR gates
`E_1, …, E_m` (in order, repetitions kept). -/
structure DORofETHR (n : ℕ) where
  gates : List (ETHRGate n)

/-- CW19 p.14: "DOR_n … an OR function with the promise that at most one input bit is true over
all inputs": at most one `E_j(x)` is true, on every `x ∈ {0,1}^n`. -/
def DORofETHR.Promise {n : ℕ} (C : DORofETHR n) : Prop :=
  ∀ x : Fin n → ℤ, IsBoolVec x → (C.gates.filter fun E => E.eval x).length ≤ 1

/-- The value of the circuit: the OR of `E_1(x), …, E_m(x)`. -/
def DORofETHR.eval {n : ℕ} (C : DORofETHR n) (x : Fin n → ℤ) : Bool :=
  C.gates.any fun E => E.eval x

/-- "THR ⊆ DOR ◦ ETHR", for one gate: `C` is a legal DOR ◦ ETHR circuit (the DOR promise holds)
and computes the same function as `G` on `{0,1}^n`. -/
def DORofETHR.Computes {n : ℕ} (C : DORofETHR n) (G : THRGate n) : Prop :=
  C.Promise ∧ ∀ x : Fin n → ℤ, IsBoolVec x → C.eval x = G.eval x

/-- Tier 1 description of a THR gate: `n`, then `w_1, …, w_n`, then `T` (self-delimiting binary
naturals `natWord`, signed integers `intWord` = sign bit then `natWord |z|`). -/
def gateWord {n : ℕ} (G : THRGate n) : List Bool :=
  natWord n ++ (List.ofFn G.w).flatMap intWord ++ intWord G.T

/-- Tier 1 description of one ETHR gate: its weights, then its threshold. -/
def ethrWord {n : ℕ} (E : ETHRGate n) : List Bool :=
  (List.ofFn E.w).flatMap intWord ++ intWord E.t

/-- Tier 1 description of a DOR ◦ ETHR circuit: `m`, then `E_1, …, E_m`. -/
def circuitWord {n : ℕ} (C : DORofETHR n) : List Bool :=
  natWord C.gates.length ++ C.gates.flatMap ethrWord

end NearCubicWires.Bindings.CW19
end

/-! ## CW19 Proposition 18(2) in Mathlib's machine model (shared code; not an input here) (supporting declarations) -/

section

namespace NearCubicWires.Bindings.CW19TM2

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairSource
open NearCubicWires.Bindings.CW19

set_option autoImplicit false

/-- TIER 2 ALGORITHMIC CLAUSE. "polynomial-time, deterministic constructions": a Mathlib
`TM2ComputableInPolyTime` machine from the description of every THR gate `G` to the description
of `dor G`. -/
def PolynomialTimeConstructionTM2 (dor : (n : ℕ) → THRGate n → DORofETHR n) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (fun G : (n : ℕ) × THRGate n => gateWord G.2)
    (fun w : List Bool => w) (fun G => circuitWord (dor G.1 G.2)))

/-- **CW19 Proposition 18(2), PDF page 14, verbatim:** "2. THR ⊆ DOR ◦ ETHR [24]. (also see
Appendix B)" … "Moreover, all the above have corresponding polynomial-time, deterministic
constructions." (Tier 2: the construction in Mathlib's TM2 model; everything else as Tier 1.) -/
def CW19_Proposition18_2_TM2 : Prop :=
  ∃ dor : (n : ℕ) → THRGate n → DORofETHR n,
    (∀ (n : ℕ) (G : THRGate n), (dor n G).Computes G) ∧ PolynomialTimeConstructionTM2 dor

end NearCubicWires.Bindings.CW19TM2
end

/-! ## CLW20 Lemma 3.11 in Mathlib's machine model (shared code; not an input here) (supporting declarations) -/

section

namespace NearCubicWires.Bindings.CLW20Lemma311TM2

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Lemma311

set_option autoImplicit false

/-- CLW20 Lemma 3.11 (PDF p.18) on circuits with at least `n₀` inputs, with the transformation's
output word `outputWord`, the two algorithms in Mathlib's TM2 model. The conjuncts follow the
printed order, as in the Tier 1 `lemma3_11Core`. -/
def lemma3_11CoreTM2 (n₀ : ℕ) (outputWord : (n : ℕ) → Instance n → List Bool) : Prop :=
  ∃ s c : ℝ, 0 < s ∧ s < c ∧ c < 1 ∧
  ∃ F : (C : CircuitFrom n₀) → Instance C.1.n,
    -- "a polynomial-time transformation that, given a circuit D …, outputs … F" (Tier 2)
    Nonempty (Turing.TM2ComputableInPolyTime (fun C : CircuitFrom n₀ => C.1.word)
      (fun w : List Bool => w) (fun C => outputWord C.1.n (F C))) ∧
    -- "|Y| ≤ poly(n)"
    (∃ K e : ℕ, ∀ C, (F C).Ybits ≤ K * (C.1.n + 1) ^ e) ∧
    -- "|Z| ≤ poly(m)"
    (∃ K e : ℕ, ∀ C, (F C).Zbits ≤ K * (C.1.m + 1) ^ e) ∧
    ∃ Zx : (C : CircuitFrom n₀) → BitInput C.1.n → BitInput (F C).Zbits,
      -- "If D(x) = 1, then F|Y=Enc(x) … has … Z_x such that at least c-fraction of the clauses
      -- are satisfied."
      (∀ C x, C.1.D.eval x = true → (F C).fraction x (Zx C x) ≥ c) ∧
      -- "there is a poly(m) time algorithm that given x outputs Z_x" (Tier 2)
      Nonempty (Turing.TM2ComputableInPolyTime
        (fun p : (Σ C : CircuitFrom n₀, BitInput C.1.n) => p.1.1.word ++ List.ofFn p.2)
        (fun w : List Bool => w) (fun p => List.ofFn (Zx p.1 p.2))) ∧
      -- "If D(x) = 0, then there is no assignment to the Z variables in F|Y=Enc(x) [that]
      -- satisfies more than s-fraction of the clauses."
      (∀ C x, C.1.D.eval x = false → ∀ z, (F C).fraction x z ≤ s) ∧
      -- "for each i ∈ [|Y|], Enc_i(x) is a parity function depending on at most n/2 bits of x"
      (∀ C i, ((F C).encSupport i).card ≤ C.1.n / 2)

/-- CLW20 Lemma 3.11 with `n ≥ 2` and the explicit-Enc output (Tier 2), the target form. -/
def CLW20_Lemma3_11_explicitEnc_TM2 : Prop := lemma3_11CoreTM2 2 (fun _ F => F.formulaEncWord)

end NearCubicWires.Bindings.CLW20Lemma311TM2
end
