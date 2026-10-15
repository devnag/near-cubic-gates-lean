import Proof.Foundations.CanonicalBinary
import StatementSupport

/-!
# Compact balanced CNF query codec

This low-level module sits below `Semantics`, so the fixed SAT opcode can
recognize the additive balanced query convention without changing the machine
instruction set.  The marker is an ordinary, constant-size CNF code whose
first clause is empty.  Hence the historical well-sized CNF convention rejects
it, while the singleton second clause carries a canonical balanced list of
ordinary clause codes.
-/

namespace NearCubicWires.BalancedCNFSATEncoding

open NearCubicWires
open NearCubicWires.CanonicalBinary

/-- Balanced payload containing the ordinary code of each clause. -/
def balancedCNFPayload (formula : List (List (Bool × ℕ))) : ℕ :=
  encodeBalancedList (formula.map Encodable.encode)

/-- The old-malformed marker formula. -/
def balancedCNFMarker (formula : List (List (Bool × ℕ))) :
    List (List (Bool × ℕ)) :=
  [[], [(true, balancedCNFPayload formula)]]

/-- Ordinary encoding of the constant-size marker around the balanced
payload. -/
def encodeBalancedCNF (formula : List (List (Bool × ℕ))) : ℕ :=
  Encodable.encode (balancedCNFMarker formula)

def encodeBalancedPrefixCNF
    (formula : List (List (Bool × ℕ)))
    (assignment count : ℕ) : ℕ :=
  encodeBalancedPrefixCNFPayload (balancedCNFPayload formula) assignment count

open private legacyDecodeCNF natBitLength_succ_le from StatementSupport
@[simp] theorem decodeBalancedCNF_encode
    (formula : List (List (Bool × ℕ))) :
    decodeBalancedCNF (encodeBalancedCNF formula) = some formula := by
  have hlegacy :
      legacyDecodeCNF (encodeBalancedCNF formula) =
        balancedCNFMarker formula := by
    simp [legacyDecodeCNF, encodeBalancedCNF, Encodable.encodek]
  rw [decodeBalancedCNF, hlegacy]
  simp [balancedCNFMarker, balancedCNFPayload, Encodable.encodek,
    Function.comp_def]

@[simp] theorem decodeBalancedCNF_encodePrefix
    (formula : List (List (Bool × ℕ))) (assignment count : ℕ) :
    decodeBalancedCNF (encodeBalancedPrefixCNF formula assignment count) =
      some (balancedPrefixClauses count assignment ++ formula) := by
  have hlegacy :
      legacyDecodeCNF
          (encodeBalancedPrefixCNF formula assignment count) =
        balancedPrefixCNFMarkerOfPayload (balancedCNFPayload formula)
          assignment count := by
    simp [legacyDecodeCNF, encodeBalancedPrefixCNF,
      encodeBalancedPrefixCNFPayload, Encodable.encodek]
  rw [decodeBalancedCNF, hlegacy]
  simp [balancedPrefixCNFMarkerOfPayload, balancedCNFPayload,
    Encodable.encodek, Function.comp_def]

/-! ## Level-2 (nested) balanced payload

The level-1 payload above is a single balanced list of clause codes.  A
scheduled producer cannot materialize that flat list without re-entering the
refuted geometric width cone of `OuterProofFormulaStreamGeometricDefect`, so
the additive convention below adds a second, disjointly tagged marker whose
payload is a balanced list of *chunk* codes, each chunk itself a balanced list
of canonical clause codes.  Decoding validates both levels and flattens only
afterwards, so no machine register ever holds the flat list.

The nested marker uses the `false` payload literal where the level-1 marker
uses `true`, so the two recognized regions are disjoint and both remain
old-malformed.  These definitions sit here, beside `decodeBalancedCNF`,
because `Proof.Foundations.Semantics` must see the nested decoder to dispatch `.sat`;
their theory is in `Proof.Foundations.NestedBalancedCNFCodec`. -/

/-- Two-level balanced payload of a chunked formula. -/
def encodeNestedBalancedCNFPayload (chunks : List (List ℕ)) : ℕ :=
  encodeBalancedList (chunks.map encodeBalancedList)

/-- Distinct base marker: the payload literal is false, whereas the flat
balanced marker uses true. -/
def nestedBalancedCNFMarkerOfPayload (payload : ℕ) :
    List (List (Bool × ℕ)) :=
  [[], [(false, payload)]]

/-- Prefix-constrained nested marker. -/
def nestedBalancedPrefixCNFMarkerOfPayload
    (payload assignment count : ℕ) : List (List (Bool × ℕ)) :=
  [[], [(false, payload)], [(false, assignment), (true, count)]]

def encodeNestedBalancedCNFPayloadMarker (payload : ℕ) : ℕ :=
  Encodable.encode (nestedBalancedCNFMarkerOfPayload payload)

def encodeNestedBalancedPrefixCNFPayloadMarker
    (payload assignment count : ℕ) : ℕ :=
  Encodable.encode
    (nestedBalancedPrefixCNFMarkerOfPayload payload assignment count)

/-- The marker has constant pairing depth around the balanced payload. -/
theorem encodeBalancedCNF_bits_le
    (formula : List (List (Bool × ℕ))) :
    natBitLength (encodeBalancedCNF formula) ≤
      16 * max 1 (natBitLength (balancedCNFPayload formula)) + 7 := by
  let payload := balancedCNFPayload formula
  let literalCode := Encodable.encode (true, payload)
  let clauseCode := Encodable.encode ([(true, payload)] : List (Bool × ℕ))
  let tailCode := Encodable.encode
    ([[(true, payload)]] : List (List (Bool × ℕ)))
  let width := max 1 (natBitLength payload)
  have hwidth : 1 ≤ width := Nat.le_max_left _ _
  have hpayload : natBitLength payload ≤ width := Nat.le_max_right _ _
  have hliteral : natBitLength literalCode ≤ 2 * width := by
    have hpair := pairCodeBits_le 1 payload
    have hbitsOne : natBitLength 1 = 1 := by decide
    have hmax : max (natBitLength 1) (natBitLength payload) ≤ width := by
      rw [hbitsOne]
    rw [show literalCode = Nat.pair 1 payload by
      simp [literalCode, Encodable.encode_prod_val, Encodable.encode_true]]
    exact hpair.trans (Nat.mul_le_mul_left 2 hmax)
  have hclause : natBitLength clauseCode ≤ 4 * width + 1 := by
    rw [show clauseCode = Nat.pair literalCode 0 + 1 by
      simp [clauseCode, literalCode, Encodable.encode_list_cons]]
    apply (natBitLength_succ_le _).trans
    have hpair := pairCodeBits_le literalCode 0
    have hone : natBitLength 0 = 1 := rfl
    have hmax : max (natBitLength literalCode) (natBitLength 0) ≤
        2 * width := by
      rw [hone]
      exact max_le hliteral (by omega)
    omega
  have htail : natBitLength tailCode ≤ 8 * width + 3 := by
    rw [show tailCode = Nat.pair clauseCode 0 + 1 by
      simp [tailCode, clauseCode, Encodable.encode_list_cons]]
    apply (natBitLength_succ_le _).trans
    have hpair := pairCodeBits_le clauseCode 0
    have hone : natBitLength 0 = 1 := rfl
    have hmax : max (natBitLength clauseCode) (natBitLength 0) ≤
        4 * width + 1 := by
      rw [hone]
      exact max_le hclause (by omega)
    omega
  rw [show encodeBalancedCNF formula = Nat.pair 0 tailCode + 1 by
    simp [encodeBalancedCNF, balancedCNFMarker, tailCode, payload,
      Encodable.encode_list_cons]]
  change natBitLength (Nat.pair 0 tailCode + 1) ≤ 16 * width + 7
  apply (natBitLength_succ_le _).trans
  have hpair := pairCodeBits_le 0 tailCode
  have hmax : max (natBitLength 0) (natBitLength tailCode) ≤
      8 * width + 3 := by
    exact max_le (by change 1 ≤ 8 * width + 3; omega) htail
  have hpair' := hpair.trans (Nat.mul_le_mul_left 2 hmax)
  omega

/-- Expanded polynomial upper bound in clause count and clause-code widths. -/
theorem encodeBalancedCNF_bits_le_clauseAtoms
    (formula : List (List (Bool × ℕ))) :
    natBitLength (encodeBalancedCNF formula) ≤
      16 * max 1
        (1 + 2 * formula.length ^ 4 *
          balancedListAtomBits (formula.map Encodable.encode)) + 7 := by
  apply (encodeBalancedCNF_bits_le formula).trans
  gcongr
  simpa only [balancedCNFPayload, List.length_map] using
    (balancedListCodeBits_le (formula.map Encodable.encode))

end NearCubicWires.BalancedCNFSATEncoding
