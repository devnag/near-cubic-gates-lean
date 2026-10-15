import Proof.Circuits.ValidatorResidualLeafBudget

/-!
# The Boolean circuit validator's counting stages

`ValidatorResidualLeafBudget` §5 walked `booleanCircuitValidationFuel` down to
exactly two named fuel charges, one comparison stage and two width
certificates.  This module discharges the comparison stage and both width
certificates; the two remaining fuel charges are named precisely at the end,
together with the *one* missing counting ledger each of them needs.

Both width certificates are the same fact twice: the counts the circuit
validator compares are **decoded-list lengths**, and `ValidatorLeafWidthCore`
§2 caps a decoded list's length at twice the code's width.  Nothing here reads
a decoded magnitude.

* §1 identifies the node count as the structural parse's atom count, and the
  topology count as a nonzero count over a request list of that same length.
  Both are therefore capped by the code's width, which is the certificate
  `booleanNodeListTopologyEqualityFuel_polyBounded` consumes.

* §2 discharges the comparison stage `booleanCircuitLtStageFuel`.  It is one
  native call into the published width-linear comparator, so it costs a closed
  program-shape overhead plus a multiple of the compared operands' widths — and
  both operands are counts capped by §1 or by the canonical natural validator's
  own candidate bound.

* §3 records what is left of the Boolean circuit validator, with the single
  missing ledger named for each.
-/

namespace NearCubicWires.ValidatorCircuitStageWidths

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorResidualLeafBudget
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The two compared counts

The node-list validator compares two numbers: how many descriptors the
structural parse produced, and how many of them the topology pass accepted.
The first *is* the atom count; the second is a nonzero count over a request
list of exactly that length.  So one counting ledger pays for both. -/

/-- The machine-derived node count is the structural parse's atom count. -/
theorem booleanNodeListNodeCount_eq (raw : ℕ) :
    booleanNodeListNodeCount raw = (rawBalancedTraversalTree raw).atoms.length := by
  simp only [booleanNodeListNodeCount, booleanNodeListRangeContext,
    booleanNodeListPreparationOutput, booleanCircuitPreparationOutput,
    booleanNodeListAtoms, Nat.unpair_pair]

theorem booleanNodeListNodeCount_succ_le (raw : ℕ) :
    booleanNodeListNodeCount raw + 1 ≤ 2 * natBitLength raw := by
  rw [booleanNodeListNodeCount_eq]
  exact rawBalancedTraversalTree_atoms_length_succ_le raw

/-- The topology count is a nonzero count over one request per descriptor. -/
theorem booleanNodeListTopologyCount_le (inputLength raw : ℕ) :
    booleanNodeListTopologyCount inputLength raw ≤
      (rawBalancedTraversalTree raw).atoms.length := by
  have hdescriptors :
      (booleanNodeListDescriptors raw).length =
        (rawBalancedTraversalTree raw).atoms.length := by
    simp only [booleanNodeListDescriptors, booleanNodeOutputs, List.length_map,
      booleanNodeListAtoms]
  have hvalues :
      (fixedBooleanRangeValues inputLength (booleanNodeListDescriptors raw).length
          (booleanNodeTopologyRangeContext (booleanNodeListDescriptors raw))
          (booleanNodeTopologyRangeValue inputLength
            (booleanNodeListDescriptors raw))).length =
        (booleanNodeListDescriptors raw).length := by
    simp only [fixedBooleanRangeValues, fixedBooleanRangeRequests,
      List.length_map, balancedRangeRequestAtoms_length]
  have hcount :=
    nonzeroSupportCount_le_length
      (fixedBooleanRangeValues inputLength (booleanNodeListDescriptors raw).length
        (booleanNodeTopologyRangeContext (booleanNodeListDescriptors raw))
        (booleanNodeTopologyRangeValue inputLength
          (booleanNodeListDescriptors raw)))
  have hproject :
      booleanNodeListTopologyCount inputLength raw =
        nonzeroSupportCount
          (fixedBooleanRangeValues inputLength
            (booleanNodeListDescriptors raw).length
            (booleanNodeTopologyRangeContext (booleanNodeListDescriptors raw))
            (booleanNodeTopologyRangeValue inputLength
              (booleanNodeListDescriptors raw))) := by
    simp only [booleanNodeListTopologyCount, booleanNodeListTopologyOutput,
      booleanNodeTopologyRangeOutput, fixedBooleanRangeAggregationOutput,
      Nat.unpair_pair]
  omega

theorem booleanNodeListTopologyCount_succ_le (inputLength raw : ℕ) :
    booleanNodeListTopologyCount inputLength raw + 1 ≤ 2 * natBitLength raw := by
  have hcount := booleanNodeListTopologyCount_le inputLength raw
  have hatoms := rawBalancedTraversalTree_atoms_length_succ_le raw
  omega

/-- **The node-list validator's two width certificates, discharged.**  Both
counts are decoded-list lengths, so the raw code's width pays for both. -/
theorem polyBounded_booleanNodeListTopologyCount
    {inputLength raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (natBitLength (booleanNodeListTopologyCount inputLength raw))
      measure (2 * coefficient + 1) degree := by
  refine ((hraw.const_mul 2).add (polyBounded_const 1 measure degree)).mono ?_
  have hcount := booleanNodeListTopologyCount_succ_le inputLength raw
  have hwidth :=
    natBitLength_le_succ (booleanNodeListTopologyCount inputLength raw)
  omega

theorem polyBounded_booleanNodeListNodeCount
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (natBitLength (booleanNodeListNodeCount raw)) measure
      (2 * coefficient + 1) degree := by
  refine ((hraw.const_mul 2).add (polyBounded_const 1 measure degree)).mono ?_
  have hcount := booleanNodeListNodeCount_succ_le raw
  have hwidth := natBitLength_le_succ (booleanNodeListNodeCount raw)
  omega

/-- **The node-list validator's equality stage, closed unconditionally.**  This
removes the last two hypotheses of
`ValidatorResidualLeafBudget.booleanNodeListTopologyEqualityFuel_polyBounded`. -/
theorem booleanNodeListTopologyEqualityFuel_polyBounded_of_width
    {inputLength raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (booleanNodeListTopologyEqualityFuel inputLength raw) measure
      (nativeNatEqCoefficient (2 * coefficient + 1) (2 * coefficient + 1) + 4)
      degree :=
  booleanNodeListTopologyEqualityFuel_polyBounded
    (polyBounded_booleanNodeListTopologyCount hraw)
    (polyBounded_booleanNodeListNodeCount hraw)

/-! ## §2 The comparison stage

`booleanCircuitLtStageFuel` is one `nativeLtRequestFuel` under a
context-preserving wrapper, and `nativeLtRequestFuel` is a native call at a
singleton request list into the published width-linear comparator.  Both
compared operands are counts: the canonical natural validator's decoded value,
capped by its own candidate bound, and the node count of §1. -/

theorem booleanCircuitNatValue_le (raw : ℕ) :
    booleanCircuitNatValue raw ≤
      canonicalNatCandidate (booleanCircuitOutputCode raw) := by
  simp only [booleanCircuitNatValue, canonicalNatValidationOutput]
  split
  · simp
  · simp

theorem natBitLength_booleanCircuitOutputCode_le (raw : ℕ) :
    natBitLength (booleanCircuitOutputCode raw) ≤ 8 * natBitLength raw := by
  have hpow : (2 : ℕ) ^ 2 = 4 := by norm_num
  have htuple := natBitLength_taggedTupleOutput_le 2 raw
  rw [hpow] at htuple
  have hproject :
      natBitLength (booleanCircuitOutputCode raw) ≤
        natBitLength (taggedTupleOutput 2 raw) := by
    refine natBitLength_mono ?_
    simp only [booleanCircuitOutputCode, booleanCircuitTupleFields,
      booleanCircuitTupleOutput]
    exact (Nat.unpair_right_le _).trans (Nat.unpair_right_le _)
  omega

theorem natBitLength_booleanCircuitNatValue_le (raw : ℕ) :
    natBitLength (booleanCircuitNatValue raw) ≤ 16 * natBitLength raw + 1 := by
  have hvalue := natBitLength_mono (booleanCircuitNatValue_le raw)
  have hcandidate :=
    natBitLength_canonicalNatCandidate_le (booleanCircuitOutputCode raw)
  have hatoms :=
    rawBalancedTraversalTree_atoms_length_succ_le (booleanCircuitOutputCode raw)
  have hcode := natBitLength_booleanCircuitOutputCode_le raw
  omega

theorem booleanCircuitNodeCount_le (inputLength raw : ℕ) :
    booleanCircuitNodeCount inputLength raw ≤
      booleanNodeListNodeCount (booleanCircuitNodesCode raw) := by
  simp only [booleanCircuitNodeCount, booleanNodeListValidationOutput]
  split
  · simp
  · split
    · simp
    · simp

theorem natBitLength_booleanCircuitNodesCode_le (raw : ℕ) :
    natBitLength (booleanCircuitNodesCode raw) ≤ 8 * natBitLength raw := by
  have hpow : (2 : ℕ) ^ 2 = 4 := by norm_num
  have htuple := natBitLength_taggedTupleOutput_le 2 raw
  rw [hpow] at htuple
  have hproject :
      natBitLength (booleanCircuitNodesCode raw) ≤
        natBitLength (taggedTupleOutput 2 raw) := by
    refine natBitLength_mono ?_
    simp only [booleanCircuitNodesCode, booleanCircuitTupleFields,
      booleanCircuitTupleOutput]
    exact (Nat.unpair_right_le _).trans
      ((Nat.unpair_left_le _).trans (Nat.unpair_right_le _))
  omega

theorem natBitLength_booleanCircuitNodeCount_le (inputLength raw : ℕ) :
    natBitLength (booleanCircuitNodeCount inputLength raw) ≤
      16 * natBitLength raw + 1 := by
  have hvalue := natBitLength_mono (booleanCircuitNodeCount_le inputLength raw)
  have hwidth :=
    natBitLength_le_succ
      (booleanNodeListNodeCount (booleanCircuitNodesCode raw))
  have hcount :=
    booleanNodeListNodeCount_succ_le (booleanCircuitNodesCode raw)
  have hcode := natBitLength_booleanCircuitNodesCode_le raw
  omega

/-- One increment widens a code by at most one bit.  `ValidatorLeafWidthCore`
publishes the *pair* form of this; the comparator needs the successor form. -/
private theorem natBitLength_succ_le_succ (value : ℕ) :
    natBitLength (value + 1) ≤ natBitLength value + 1 := by
  rcases Nat.eq_zero_or_pos value with rfl | hpositive
  · have hzero : natBitLength 0 = 1 := natBitLength_zero
    have hone : natBitLength (0 + 1) = 1 := natBitLength_one
    omega
  · have hle : value + 1 ≤ value * 2 := by omega
    have hmono : Nat.log 2 (value + 1) ≤ Nat.log 2 (value * 2) :=
      Nat.log_mono_right hle
    have hmul : Nat.log 2 (value * 2) = Nat.log 2 value + 1 :=
      Nat.log_mul_base (by omega) (by omega)
    unfold natBitLength
    omega

/-- The closed program-shape overhead of the comparison stage. -/
def booleanCircuitLtStageOverhead : ℕ :=
  nativeCallOverhead binaryNatLtProgram + 2 +
    (programRegisterSpan nativeNatLeProgram + 14) + 4

/-- **The comparison stage's ledger.**  A closed overhead plus a multiple of
the compared counts' widths: no term grows with a decoded magnitude. -/
theorem booleanCircuitLtStageFuel_le (inputLength raw : ℕ) :
    booleanCircuitLtStageFuel inputLength raw ≤
      booleanCircuitLtStageOverhead +
        36 * (16 * natBitLength raw + 2) := by
  have hnative :=
    nativeCallFuel_le binaryNatLtProgram
      (2 + binaryNatLtLoopFuel (booleanCircuitNatValue raw)
        (booleanCircuitNodeCount inputLength raw))
      (booleanCircuitNodeCount inputLength raw) (booleanCircuitNatValue raw)
  have hloop :=
    binaryNatLtLoopFuel_le (booleanCircuitNatValue raw)
      (booleanCircuitNodeCount inputLength raw)
  have hleft :
      natBitLength (booleanCircuitNatValue raw + 1) ≤
        16 * natBitLength raw + 2 := by
    have hsucc := natBitLength_succ_le_succ (booleanCircuitNatValue raw)
    have hvalue := natBitLength_booleanCircuitNatValue_le raw
    omega
  have hright :
      natBitLength (booleanCircuitNodeCount inputLength raw) ≤
        16 * natBitLength raw + 2 := by
    have hcount := natBitLength_booleanCircuitNodeCount_le inputLength raw
    omega
  have hmax :
      max (natBitLength (booleanCircuitNatValue raw + 1))
          (natBitLength (booleanCircuitNodeCount inputLength raw)) ≤
        16 * natBitLength raw + 2 := Nat.max_le.2 ⟨hleft, hright⟩
  have hscale :
      36 * max (natBitLength (booleanCircuitNatValue raw + 1))
            (natBitLength (booleanCircuitNodeCount inputLength raw)) ≤
        36 * (16 * natBitLength raw + 2) :=
    Nat.mul_le_mul_left _ hmax
  simp only [booleanCircuitLtStageFuel, preserveRightFuel, nativeLtRequestFuel,
    booleanCircuitLtRequest, nativeLtRequest, nativeInputRequest,
    Nat.unpair_pair, booleanCircuitLtStageOverhead]
  omega

/-- **The comparison stage, dominated.**  Degree-preserving over the raw code's
width: this is the third of the four charges
`ValidatorResidualLeafBudget.booleanCircuitValidationFuel_polyBounded`
consumes. -/
theorem booleanCircuitLtStageFuel_polyBounded
    {inputLength raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (booleanCircuitLtStageFuel inputLength raw) measure
      (booleanCircuitLtStageOverhead + 36 * (16 * coefficient + 2)) degree := by
  refine ((polyBounded_const booleanCircuitLtStageOverhead measure degree).add
    (((hraw.const_mul 16).add
      (polyBounded_const 2 measure degree)).const_mul 36)).mono ?_
  exact booleanCircuitLtStageFuel_le inputLength raw

/-- The comparison stage and the equality stage, packaged in the shape
`booleanCircuitValidationFuel_polyBounded` consumes. -/
theorem booleanCircuitValidationFuel_polyBounded_of_two_charges
    {inputLength raw measure stage coefficient degree : ℕ}
    (hnumerals : max (taggedTupleFuel 2) 15 ≤ stage)
    (hnode :
      PolyBounded (booleanCircuitNodeStageFuel inputLength raw) measure stage
        degree)
    (hnat : PolyBounded (booleanCircuitNatStageFuel raw) measure stage degree)
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree)
    (hlt : booleanCircuitLtStageOverhead + 36 * (16 * coefficient + 2) ≤ stage) :
    ∃ circuitCoefficient : ℕ,
      PolyBounded (booleanCircuitValidationFuel inputLength raw) measure
        circuitCoefficient degree :=
  booleanCircuitValidationFuel_polyBounded hnumerals hnode hnat
    ((booleanCircuitLtStageFuel_polyBounded hraw).coefficient_mono hlt)

end NearCubicWires.ValidatorCircuitStageWidths
