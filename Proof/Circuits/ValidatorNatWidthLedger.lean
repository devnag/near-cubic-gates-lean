import Proof.Circuits.ValidatorCircuitWidthLedger

/-!
# The canonical natural validator's register requirement

`ValidatorCircuitWidthLedger` §3 left two residual widths.  This module closes
the second of them down to the *traversal* layer: the canonical natural
validator's width is its candidate pass's width, plus a cone that is linear in
the raw code.

* §1 the candidate cone: the decoded candidate, its re-encoding and the
  equality request are all bounded by closed multiples of the raw code's
  width — the re-encoding by the published quadratic-free ledger.

* §2 the five-way maximum, reduced to the candidate pass.

* §3 the candidate pass, reduced to the two balanced-traversal widths.  What
  is left is exactly two charges of one shape — `balancedTraversalRequiredBits`
  over a decoded list — which is the shape `CanonicalBalancedCall` already
  closes by a fixed polynomial.
-/

namespace NearCubicWires.ValidatorNatWidthLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.ValidatorCircuitStageWidths
open NearCubicWires.ValidatorCircuitWidthLedger
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorWidthCombinatorLedger

open private duplicateRawBits candidateWithRawBits canonicalNatEqualityInput
  canonicalNatEqualityPrepareBits canonicalNatEqualityFlag
  canonicalNatEqualityBits canonicalNatValidationGateBits from
  Proof.MachineModel.CanonicalNatValidationProgram

/-! ## §1 The candidate cone -/

/-- The decoded candidate never exceeds twice the raw code's width: it is a
fold over the code's own atom list. -/
theorem natBitLength_canonicalNatCandidate_le_two_mul (raw : ℕ) :
    natBitLength (canonicalNatCandidate raw) ≤ 2 * natBitLength raw := by
  have hcandidate := natBitLength_canonicalNatCandidate_le raw
  have hatoms := rawBalancedTraversalTree_atoms_length_succ_le raw
  omega

/-- The equality flag is one bit wide. -/
theorem natBitLength_canonicalNatEqualityFlag_le (raw : ℕ) :
    natBitLength (canonicalNatEqualityFlag raw) ≤ 1 := by
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 = 1 := natBitLength_one
  simp only [canonicalNatEqualityFlag, nativeNatEqOutput]
  split <;> omega

/-! ## §2 The five-way maximum -/

/-- **The canonical natural validator's width, reduced to its candidate
pass.**  Four of the five entries are paid by the candidate cone; the fifth is
the candidate pass's own width. -/
theorem canonicalNatValidationBits_le
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    canonicalNatValidationBits inputLength raw ≤
      max (canonicalNatCandidateBits inputLength raw) (2048 * bound) := by
  have hcandidate :
      natBitLength (canonicalNatCandidate raw) ≤ 2 * bound := by
    have := natBitLength_canonicalNatCandidate_le_two_mul raw
    omega
  have hencoded :
      natBitLength (encodeNat (canonicalNatCandidate raw)) ≤ 512 * bound := by
    have := natBitLength_encodeNat_canonicalNatCandidate_le raw
    omega
  have hflag := natBitLength_canonicalNatEqualityFlag_le raw
  have hduplicate : duplicateRawBits raw ≤ 2 * bound := by
    have hpair := natBitLength_pair_le_two_mul hraw hraw
    simp only [duplicateRawBits]
    omega
  have hcandidateWith :
      candidateWithRawBits inputLength raw ≤
        max (canonicalNatCandidateBits inputLength raw) (2 * (2 * bound)) := by
    have hwrapper :=
      preserveRightBits_le
        (sourceBits := canonicalNatCandidateBits inputLength raw)
        (left := raw) (right := raw)
        (output := canonicalNatCandidate raw) (bound := 2 * bound)
        (by omega) (by omega) (by omega)
    simp only [candidateWithRawBits]
    omega
  have hrequest :
      natBitLength (nativeNatEqInput (encodeNat (canonicalNatCandidate raw)) raw) ≤
        2 * (512 * bound) := by
    simp only [nativeNatEqInput]
    exact natBitLength_pair_le_two_mul hencoded (by omega)
  have hequalityInput :
      natBitLength (canonicalNatEqualityInput raw) ≤ 2 * (2 * (512 * bound)) := by
    simp only [canonicalNatEqualityInput]
    exact natBitLength_pair_le_two_mul hrequest (by omega)
  have hcandidateRaw :
      natBitLength (Nat.pair (canonicalNatCandidate raw) raw) ≤
        2 * (2 * bound) :=
    natBitLength_pair_le_two_mul hcandidate (by omega)
  have hprepare :
      canonicalNatEqualityPrepareBits inputLength raw ≤ 2048 * bound := by
    simp only [canonicalNatEqualityPrepareBits]
    omega
  have hcallee :
      nativeNatEqBits inputLength (encodeNat (canonicalNatCandidate raw)) raw ≤
        4 * (512 * bound) :=
    nativeNatEqBits_le (by omega) (by omega) (by omega) (by omega)
  have hequality :
      canonicalNatEqualityBits inputLength raw ≤ 2048 * bound := by
    have hwrapper :=
      preserveRightBits_le
        (sourceBits :=
          nativeNatEqBits inputLength (encodeNat (canonicalNatCandidate raw))
            raw)
        (left := nativeNatEqInput (encodeNat (canonicalNatCandidate raw)) raw)
        (right := canonicalNatCandidate raw)
        (output := canonicalNatEqualityFlag raw) (bound := 2 * (512 * bound))
        (by omega) (by omega) (by omega)
    simp only [canonicalNatEqualityBits]
    omega
  have hgatePair :
      natBitLength
          (Nat.pair (canonicalNatEqualityFlag raw)
            (canonicalNatCandidate raw)) ≤ 2 * (2 * bound) :=
    natBitLength_pair_le_two_mul (by omega) hcandidate
  have hgateTag :
      natBitLength (Nat.pair 1 (canonicalNatCandidate raw)) ≤ 2 * (2 * bound) := by
    have hone : natBitLength 1 = 1 := natBitLength_one
    exact natBitLength_pair_le_two_mul (by omega) hcandidate
  have hgate :
      canonicalNatValidationGateBits (canonicalNatEqualityFlag raw)
          (canonicalNatCandidate raw) ≤ 2048 * bound := by
    simp only [canonicalNatValidationGateBits]
    omega
  simp only [canonicalNatValidationBits]
  omega

/-! ## §3 The candidate pass -/

theorem canonicalNatCandidateBits_le
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound) :
    canonicalNatCandidateBits inputLength raw ≤
      max
        (max
          (balancedRawCanonicalizeBits inputLength
            (rawBalancedTraversalTree raw))
          (canonicalNatDecodeListBits inputLength
            (rawBalancedTraversalTree raw).atoms))
        bound := by
  simp only [canonicalNatCandidateBits]
  omega

theorem canonicalNatValidationBits_le_traversalFrontier
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    canonicalNatValidationBits inputLength raw ≤
      max
        (max
          (balancedRawCanonicalizeBits inputLength
            (rawBalancedTraversalTree raw))
          (canonicalNatDecodeListBits inputLength
            (rawBalancedTraversalTree raw).atoms))
        (2048 * bound) := by
  have hstage := canonicalNatValidationBits_le hpositive hlength hraw
  have hcandidate := canonicalNatCandidateBits_le (raw := raw) hpositive hlength
  omega

theorem booleanCircuitValidationBits_le_traversalFrontier
    {inputLength raw bound : ℕ} (htwo : 2 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    booleanCircuitValidationBits inputLength raw ≤
      max
        (max
          (booleanNodeListValidationBits inputLength
            (booleanCircuitNodesCode raw))
          (max
            (balancedRawCanonicalizeBits inputLength
              (rawBalancedTraversalTree (booleanCircuitOutputCode raw)))
            (canonicalNatDecodeListBits inputLength
              (rawBalancedTraversalTree (booleanCircuitOutputCode raw)).atoms)))
        (16384 * bound) := by
  have hcircuit := booleanCircuitValidationBits_le htwo hlength hraw
  have houtput := natBitLength_booleanCircuitOutputCode_le raw
  have hnat :=
    canonicalNatValidationBits_le_traversalFrontier
      (inputLength := inputLength) (raw := booleanCircuitOutputCode raw)
      (bound := 8 * bound) (by omega) (by omega) (by omega)
  omega

end NearCubicWires.ValidatorNatWidthLedger
