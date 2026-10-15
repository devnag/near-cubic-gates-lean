import Proof.MachineModel.ValidatorRebuiltMachineClosure

/-!
# The two rebuilt callee widths, as domination judgements

`ValidatorRebuiltMachineClosure` §3 asks the caller for `hnode` and `hnat` —
`PolyBounded` certificates for `booleanNodeListValidationRebuildBits` and
`canonicalNatValidationRebuildBits`.  `ValidatorRebuildWidthLedger` states both
of those as `≤` ledgers over named residuals.  This module converts each ledger
into the domination judgement the machine constructor consumes, so that the two
remaining width premises are exactly the residuals the ledgers name and nothing
else.

* §1 `hnat`, from the balanced measurements.

* §2 `hnode`, from the preparation fork and the six frozen stages.
-/

namespace NearCubicWires.ValidatorRebuiltWidthCertificates

open NearCubicWires
open NearCubicWires.CanonicalBalancedAtomIndexProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedMidpointRebuildProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanNodeListRebuildProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalGateAtomHeadListProgram
open NearCubicWires.ValidatorCanonicalizerRebuildLedger
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorRebuildWidthLedger

/-! ## §1 `hnat`, from the balanced measurements -/

/-- **The rebuilt natural validator's width, dominated.**  Seven residuals,
every one of them a midpoint-balanced traversal charge over the raw word's own
traversal tree, plus the public input's and the untrusted word's widths.  No
premise mentions `encodeTaggedList` of the public atom list. -/
theorem canonicalNatValidationRebuildBits_polyBounded
    {inputLength raw measure lengthCoefficient rawCoefficient
      normalizeCoefficient countCoefficient indexCoefficient
      indexCallCoefficient requestCoefficient decodeCallCoefficient
      atomsCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hraw : PolyBounded (natBitLength raw) measure rawCoefficient degree)
    (hnormalize :
      PolyBounded
        (balancedStructuralNormalizeBits inputLength
          (rawBalancedTraversalTree raw)) measure normalizeCoefficient degree)
    (hcount :
      PolyBounded
        (balancedAtomCountBits inputLength
          (rawBalancedTraversalTree raw).normalized) measure countCoefficient
        degree)
    (hindex :
      PolyBounded
        (indexedAtomListBits inputLength
          (rawBalancedTraversalTree raw).atoms.length
          (rawBalancedTraversalTree raw).normalized.code
          (fun index =>
            Nat.pair index (rawBalancedTraversalTree raw).normalized.code))
        measure indexCoefficient degree)
    (hindexCall :
      PolyBounded
        (balancedCallPolynomialBits
          (atomIndexOutput (rawBalancedTraversalTree raw).normalized)
          (atomIndexRequests (rawBalancedTraversalTree raw).normalized))
        measure indexCallCoefficient degree)
    (hrequest :
      PolyBounded
        (atomIndexRequestBits (rawBalancedTraversalTree raw).normalized)
        measure requestCoefficient degree)
    (hdecodeCall :
      PolyBounded
        (balancedCallPolynomialBits (fun value => value)
          (rawBalancedTraversalTree raw).atoms) measure decodeCallCoefficient
        degree)
    (hatoms :
      PolyBounded (rawBalancedTraversalTree raw).atoms.length measure
        atomsCoefficient degree) :
    PolyBounded (canonicalNatValidationRebuildBits inputLength raw) measure
      (max
        (max normalizeCoefficient
          (max (2 * countCoefficient)
            (max indexCoefficient
              (max indexCallCoefficient requestCoefficient))))
        (max (max decodeCallCoefficient (2 * atomsCoefficient + 2))
          (2048 * max lengthCoefficient (max rawCoefficient 2)))) degree := by
  have hcone :
      PolyBounded (max (natBitLength inputLength) (max (natBitLength raw) 2))
        measure (max lengthCoefficient (max rawCoefficient 2)) degree :=
    hlength.max (hraw.max (polyBounded_const 2 measure degree))
  have hatomsSucc :
      PolyBounded (2 * ((rawBalancedTraversalTree raw).atoms.length + 1))
        measure (2 * atomsCoefficient + 2) degree := by
    have hsum :
        PolyBounded ((rawBalancedTraversalTree raw).atoms.length + 1) measure
          (atomsCoefficient + 1) degree :=
      hatoms.add (polyBounded_const 1 measure degree)
    have hscaled := hsum.const_mul 2
    have hcoefficient : 2 * (atomsCoefficient + 1) = 2 * atomsCoefficient + 2 :=
      by ring
    rw [hcoefficient] at hscaled
    exact hscaled
  refine ((hnormalize.max ((hcount.const_mul 2).max
    (hindex.max (hindexCall.max hrequest)))).max
      ((hdecodeCall.max hatomsSucc).max (hcone.const_mul 2048))).mono ?_
  exact canonicalNatValidationRebuildBits_le_measurements
    (bound := max (natBitLength inputLength) (max (natBitLength raw) 2))
    (by omega) (by omega) (by omega)

/-! ## §2 `hnode`, from the preparation fork and the six frozen stages -/

/-- **The rebuilt node-list validator's width, dominated.**  The residuals are
the indexed canonicalizer's charge, the preparation fork's charge — the single
site `ValidatorRebuildWidthLedger` §5 isolates — and the five frozen scalar
stages. -/
theorem booleanNodeListValidationRebuildBits_polyBounded
    {inputLength raw measure lengthCoefficient rawCoefficient
      normalizedCoefficient canonicalizeCoefficient prepareCoefficient
      rangeCoefficient topologyCoefficient equalityLoweringCoefficient
      equalityCoefficient gateCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hraw : PolyBounded (natBitLength raw) measure rawCoefficient degree)
    (hnormalized :
      PolyBounded (natBitLength (booleanNodeListNormalizedCode raw)) measure
        normalizedCoefficient degree)
    (hcanonicalize :
      PolyBounded
        (balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw)) measure canonicalizeCoefficient
        degree)
    (hprepare :
      PolyBounded (booleanNodeListPrepareBits inputLength raw) measure
        prepareCoefficient degree)
    (hrange :
      PolyBounded (booleanNodeListRangeLoweringBits inputLength raw) measure
        rangeCoefficient degree)
    (htopology :
      PolyBounded (booleanNodeListTopologyBits inputLength raw) measure
        topologyCoefficient degree)
    (hequalityLowering :
      PolyBounded (booleanNodeListTopologyEqualityLoweringBits inputLength raw)
        measure equalityLoweringCoefficient degree)
    (hequality :
      PolyBounded (booleanNodeListTopologyEqualityBits inputLength raw) measure
        equalityCoefficient degree)
    (hgate :
      PolyBounded (booleanNodeListValidationGateBits inputLength raw) measure
        gateCoefficient degree) :
    PolyBounded (booleanNodeListValidationRebuildBits inputLength raw) measure
      (max canonicalizeCoefficient
        (max prepareCoefficient
          (max rangeCoefficient
            (max topologyCoefficient
              (max equalityLoweringCoefficient
                (max equalityCoefficient
                  (max gateCoefficient
                    (8 *
                      max lengthCoefficient
                        (max rawCoefficient
                          (max normalizedCoefficient 1)))))))))) degree := by
  have hcone :
      PolyBounded
        (max (natBitLength inputLength)
          (max (natBitLength raw)
            (max (natBitLength (booleanNodeListNormalizedCode raw)) 1)))
        measure
        (max lengthCoefficient
          (max rawCoefficient (max normalizedCoefficient 1))) degree :=
    hlength.max (hraw.max (hnormalized.max (polyBounded_const 1 measure degree)))
  refine (hcanonicalize.max (hprepare.max (hrange.max (htopology.max
    (hequalityLowering.max (hequality.max (hgate.max
      (hcone.const_mul 8)))))))).mono ?_
  exact booleanNodeListValidationRebuildBits_le
    (bound :=
      max (natBitLength inputLength)
        (max (natBitLength raw)
          (max (natBitLength (booleanNodeListNormalizedCode raw)) 1)))
    (by omega) (by omega) (by omega) (by omega)

end NearCubicWires.ValidatorRebuiltWidthCertificates
