import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorCircuitRebuildLedger

/-!
# The two rebuilt callee widths, walked down to their residuals

`ValidatorCircuitRebuildLedger` §6 states `hcall` at exactly two rebuilt
widths, `booleanNodeListValidationRebuildBits` and
`canonicalNatValidationRebuildBits`.  This module walks each of the two down to
what it still charges.

* §1 the rebuilt canonicality guard's width: one balanced measurement and a
  cone linear in the untrusted word.

* §2 the rebuilt normalization fork: the same measurement, both arms.

* §3 the rebuilt node-list validator's width, at its seven stages with the
  normalization entry replaced by that measurement.

* §4 the rebuilt natural validator's width, at its candidate pass —
  `ValidatorNatWidthLedger` §2 verbatim over the rebuilt candidate.

* §5 the seam: what each of the two still owes.
-/

namespace NearCubicWires.ValidatorRebuildWidthLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedMidpointRebuildProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanNodeListRebuildProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBalancedAtomIndexProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalGateAtomHeadListProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorCanonicalizerRebuildLedger
open NearCubicWires.ValidatorCircuitRebuildLedger
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorNatWidthLedger
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorWidthCombinatorLedger

open private duplicateNatBits from Proof.MachineModel.CanonicalBalancedValidationProgram

open private duplicateRawBits canonicalNatEqualityInput
  canonicalNatEqualityPrepareBits canonicalNatEqualityFlag
  canonicalNatEqualityBits canonicalNatValidationGateBits from
  Proof.MachineModel.CanonicalNatValidationProgram

/-! ## §1 The rebuilt canonicality guard's width -/

/-- The canonicality verdict is one bit wide. -/
theorem natBitLength_balancedCanonicalityOutput_le (raw : ℕ) :
    natBitLength (balancedCanonicalityOutput raw) ≤ 1 := by
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 = 1 := natBitLength_one
  simp only [balancedCanonicalityOutput]
  split <;> omega

/-- **The rebuilt guard's width.**  One balanced measurement, plus a cone that
is linear in the untrusted word and the code it rebuilds. -/
theorem balancedCanonicalityRebuildBits_le
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound)
    (hrebuilt : natBitLength (balancedCanonicalityRebuiltCode raw) ≤ bound) :
    balancedCanonicalityRebuildBits inputLength raw ≤
      max
        (balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw))
        (8 * bound) := by
  have hduplicate : duplicateNatBits raw ≤ 2 * bound := by
    have hpair := natBitLength_pair_le_two_mul hraw hraw
    simp only [duplicateNatBits]
    omega
  have hpreserve :=
    preserveRightBits_le
      (sourceBits :=
        balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw))
      (left := raw) (right := raw)
      (output := balancedCanonicalityRebuiltCode raw) (bound := bound)
      hraw hraw hrebuilt
  have hequality :
      nativeNatEqBits inputLength (balancedCanonicalityRebuiltCode raw) raw ≤
        4 * bound :=
    nativeNatEqBits_le hpositive hlength hrebuilt hraw
  simp only [balancedCanonicalityRebuildBits,
    balancedCanonicalityPrepareRebuildBits]
  omega

/-! ## §2 The rebuilt normalization fork -/

/-- **The rebuilt seam's width.**  Both arms of the fork are paid by the same
balanced measurement: the guard's own preparation stage runs the indexed
canonicalizer, and the seam's second arm *is* the indexed canonicalizer. -/
theorem booleanNodeListNormalizeRebuildBits_le
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound)
    (hnormalized :
      natBitLength (booleanNodeListNormalizedCode raw) ≤ bound) :
    booleanNodeListNormalizeRebuildBits inputLength raw ≤
      max
        (balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw))
        (8 * bound) := by
  have hrebuilt : natBitLength (balancedCanonicalityRebuiltCode raw) ≤ bound :=
    hnormalized
  have hflag : natBitLength (balancedCanonicalityOutput raw) ≤ bound := by
    have := natBitLength_balancedCanonicalityOutput_le raw
    omega
  have hguard :=
    balancedCanonicalityRebuildBits_le (inputLength := inputLength) (raw := raw)
      (bound := bound) hpositive hlength hraw hrebuilt
  have hfork :=
    forkCallBits_le
      (inputLength := inputLength) (raw := raw)
      (firstBits := balancedCanonicalityRebuildBits inputLength raw)
      (secondBits :=
        balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw))
      (firstOutput := balancedCanonicalityOutput raw)
      (secondOutput := booleanNodeListNormalizedCode raw)
      (bound := bound) hpositive hlength hraw hflag hnormalized
  simp only [booleanNodeListNormalizeRebuildBits]
  omega

/-! ## §3 The rebuilt node-list validator's width -/

set_option maxHeartbeats 1600000 in
-- One `omega` closes an eight-way maximum against the fork's own reduction.

theorem booleanNodeListValidationRebuildBits_le
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound)
    (hnormalized :
      natBitLength (booleanNodeListNormalizedCode raw) ≤ bound) :
    booleanNodeListValidationRebuildBits inputLength raw ≤
      max
        (balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw))
        (max (booleanNodeListPrepareBits inputLength raw)
          (max (booleanNodeListRangeLoweringBits inputLength raw)
            (max (booleanNodeListTopologyBits inputLength raw)
              (max
                (booleanNodeListTopologyEqualityLoweringBits inputLength raw)
                (max (booleanNodeListTopologyEqualityBits inputLength raw)
                  (max (booleanNodeListValidationGateBits inputLength raw)
                    (8 * bound))))))) := by
  have hnormalize :=
    booleanNodeListNormalizeRebuildBits_le (inputLength := inputLength)
      (raw := raw) (bound := bound) hpositive hlength hraw hnormalized
  simp only [booleanNodeListValidationRebuildBits]
  omega

/-- **The rebuilt node-list validator's width, at its one residual stage.**
Any bound on the preparation fork's charge and on the indexed canonicalizer's
lifts to the whole validator, provided the five scalar stages are paid.  This
is the socket the next repair plugs into. -/
theorem booleanNodeListValidationRebuildBits_le_of_stages_le
    {inputLength raw bound stageBound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound)
    (hnormalized : natBitLength (booleanNodeListNormalizedCode raw) ≤ bound)
    (hcanonicalize :
      balancedRawCanonicalizeFoldBits inputLength
        (rawBalancedTraversalTree raw) ≤ stageBound)
    (hprepare : booleanNodeListPrepareBits inputLength raw ≤ stageBound)
    (hrange : booleanNodeListRangeLoweringBits inputLength raw ≤ stageBound)
    (htopology : booleanNodeListTopologyBits inputLength raw ≤ stageBound)
    (hequalityLowering :
      booleanNodeListTopologyEqualityLoweringBits inputLength raw ≤ stageBound)
    (hequality :
      booleanNodeListTopologyEqualityBits inputLength raw ≤ stageBound)
    (hgate : booleanNodeListValidationGateBits inputLength raw ≤ stageBound) :
    booleanNodeListValidationRebuildBits inputLength raw ≤
      max stageBound (8 * bound) := by
  have hstage :=
    booleanNodeListValidationRebuildBits_le (inputLength := inputLength)
      (raw := raw) (bound := bound) hpositive hlength hraw hnormalized
  omega

/-! ## §4 The rebuilt natural validator's width -/

set_option maxHeartbeats 800000 in
-- One `omega` closes a five-way maximum over the whole candidate cone.
/-- **The rebuilt natural validator's width, reduced to its candidate pass.**
`ValidatorNatWidthLedger` §2 verbatim over the rebuilt candidate: the four
non-candidate entries are the frozen ones, and the candidate cone is unchanged
because the rebuilt pass returns exactly `canonicalNatCandidate raw`. -/
theorem canonicalNatValidationRebuildBits_le
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    canonicalNatValidationRebuildBits inputLength raw ≤
      max (canonicalNatCandidateRebuildBits inputLength raw) (2048 * bound) := by
  have hcandidate : natBitLength (canonicalNatCandidate raw) ≤ 2 * bound := by
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
  have hpreserve :=
    preserveRightBits_le
      (sourceBits := canonicalNatCandidateRebuildBits inputLength raw)
      (left := raw) (right := raw)
      (output := canonicalNatCandidate raw) (bound := 2 * bound)
      (by omega) (by omega) (by omega)
  have hrequest :
      natBitLength
          (nativeNatEqInput (encodeNat (canonicalNatCandidate raw)) raw) ≤
        2 * (512 * bound) := by
    simp only [nativeNatEqInput]
    exact natBitLength_pair_le_two_mul hencoded (by omega)
  have hequalityInput :
      natBitLength (canonicalNatEqualityInput raw) ≤
        2 * (2 * (512 * bound)) := by
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
      natBitLength (Nat.pair 1 (canonicalNatCandidate raw)) ≤
        2 * (2 * bound) := by
    have hone : natBitLength 1 = 1 := natBitLength_one
    exact natBitLength_pair_le_two_mul (by omega) hcandidate
  have hgate :
      canonicalNatValidationGateBits (canonicalNatEqualityFlag raw)
          (canonicalNatCandidate raw) ≤ 2048 * bound := by
    simp only [canonicalNatValidationGateBits]
    omega
  simp only [canonicalNatValidationRebuildBits, candidateWithRawRebuildBits]
  omega

/-- **The rebuilt natural validator's width, in balanced measurements only.**
Composing §4 with `ValidatorCanonicalizerRebuildLedger` §2: no summand is a
tagged list of the public atoms. -/
theorem canonicalNatValidationRebuildBits_le_measurements
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    canonicalNatValidationRebuildBits inputLength raw ≤
      max
        (max
          (balancedStructuralNormalizeBits inputLength
            (rawBalancedTraversalTree raw))
          (max
            (2 * balancedAtomCountBits inputLength
              (rawBalancedTraversalTree raw).normalized)
            (max
              (indexedAtomListBits inputLength
                (rawBalancedTraversalTree raw).atoms.length
                (rawBalancedTraversalTree raw).normalized.code
                (fun index =>
                  Nat.pair index
                    (rawBalancedTraversalTree raw).normalized.code))
              (max
                (balancedCallPolynomialBits
                  (atomIndexOutput (rawBalancedTraversalTree raw).normalized)
                  (atomIndexRequests
                    (rawBalancedTraversalTree raw).normalized))
                (atomIndexRequestBits
                  (rawBalancedTraversalTree raw).normalized)))))
        (max
          (max
            (balancedCallPolynomialBits (fun value => value)
              (rawBalancedTraversalTree raw).atoms)
            (2 * ((rawBalancedTraversalTree raw).atoms.length + 1)))
          (2048 * bound)) := by
  have hstage :=
    canonicalNatValidationRebuildBits_le (inputLength := inputLength)
      (raw := raw) (bound := bound) hpositive hlength hraw
  have hcandidate :=
    canonicalNatCandidateRebuildBits_le_measurements (inputLength := inputLength)
      (raw := raw) (bound := bound) hpositive hlength
  omega

/-! ## §5 The seam

`ValidatorCircuitRebuildLedger` §6 asks for two `PolyBounded` certificates.
§4 discharges the second down to `ValidatorCanonicalizerRebuildLedger`'s five
balanced measurements — every one of them a midpoint-balanced traversal charge,
the shape `CanonicalBalancedCall` closes by a fixed polynomial.

§3 discharges the first down to **one** residual stage.  Of the node-list
validator's seven stages,

* the normalization fork is repaired here, both arms at once;

* the range lowering, the topology stage, the topology-equality lowering, the
  topology equality and the validation gate are `foldr max` trace ledgers or
  wrappers over `nativeNatEqBits`, with no tagged public list anywhere in their
  cones;

* `booleanNodeListPrepareBits` is the residual.  It wraps
  `booleanCircuitPreparationBits`, which forks a balanced length count against
  `booleanNodeBatchBits` — a counted call that charges
  `booleanNodeValidationBits` once per descriptor, and each of those charges
  `taggedNatListValidationBits`, which runs
  `balancedClauseStreamFlattenProgram` over the descriptor's own tagged field
  list and calls the canonical natural validator underneath.

So the preparation fork is the single remaining geometric site on the node-list
route, and it needs the same two repairs already published: the indexed
canonicalizer for its tagged flattening, and the rebuilt natural validator for
its per-field callee. -/

/-- **The node-list residual, isolated.**  Everything the rebuilt node-list
validator charges beyond the balanced measurements and the five scalar stages
is the preparation fork's own width. -/
theorem booleanNodeListValidationRebuildBits_le_of_prepare_le
    {inputLength raw bound stageBound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound)
    (hnormalized : natBitLength (booleanNodeListNormalizedCode raw) ≤ bound)
    (hcanonicalize :
      balancedRawCanonicalizeFoldBits inputLength
        (rawBalancedTraversalTree raw) ≤ stageBound)
    (hscalars :
      max (booleanNodeListRangeLoweringBits inputLength raw)
          (max (booleanNodeListTopologyBits inputLength raw)
            (max
              (booleanNodeListTopologyEqualityLoweringBits inputLength raw)
              (max (booleanNodeListTopologyEqualityBits inputLength raw)
                (booleanNodeListValidationGateBits inputLength raw)))) ≤
        stageBound)
    (hprepare : booleanNodeListPrepareBits inputLength raw ≤ stageBound) :
    booleanNodeListValidationRebuildBits inputLength raw ≤
      max stageBound (8 * bound) :=
  booleanNodeListValidationRebuildBits_le_of_stages_le hpositive hlength hraw
    hnormalized hcanonicalize hprepare (by omega) (by omega) (by omega)
    (by omega) (by omega)

end NearCubicWires.ValidatorRebuildWidthLedger
