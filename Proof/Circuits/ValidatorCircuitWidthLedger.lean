import Proof.Circuits.ValidatorWidthCombinatorLedger

namespace NearCubicWires.ValidatorCircuitWidthLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorCircuitLeafClosure
open NearCubicWires.ValidatorCircuitStageWidths
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorWidthCombinatorLedger

open private booleanCircuitFieldProjectionValues booleanCircuitNatLoweringValues
  booleanCircuitLtLoweringValues booleanCircuitValidationGateValues from
  Proof.MachineModel.CanonicalBooleanCircuitValidationProgram

/-! ## §1 The circuit's atom cone -/

/-- The node-list validator's answer is a tagged node count, so its width is
paid by the node-list code's own width. -/
theorem natBitLength_booleanNodeListValidationOutput_le
    (inputLength raw : ℕ) :
    natBitLength (booleanNodeListValidationOutput inputLength raw) ≤
      4 * natBitLength raw := by
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 = 1 := natBitLength_one
  have hpositive := one_le_natBitLength raw
  have hcount := booleanNodeListNodeCount_succ_le raw
  have hwidth := natBitLength_le_succ (booleanNodeListNodeCount raw)
  have hpair :
      natBitLength (Nat.pair 1 (booleanNodeListNodeCount raw)) ≤
        2 * (2 * natBitLength raw) :=
    natBitLength_pair_le_two_mul (by omega) (by omega)
  simp only [booleanNodeListValidationOutput]
  split
  · omega
  · split
    · omega
    · omega

/-- **The circuit's atom cone.**  Every value named by the four trace ledgers
and by the three wrapper stages is bounded by `256 * bound`, where `bound`
dominates both the public input length's width and the raw code's width.  The
constant is a closed numeral: the cone is four pairings deep over a projection
of the tagged tuple. -/
theorem booleanCircuitAtomCone
    {inputLength raw bound : ℕ} (_htwo : 2 ≤ bound)
    (_hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    natBitLength (booleanCircuitTupleOutput raw) ≤ 8 * bound ∧
      natBitLength (booleanCircuitTupleFlag raw) ≤ 8 * bound ∧
      natBitLength (booleanCircuitTupleFields raw) ≤ 8 * bound ∧
      natBitLength (booleanCircuitNodesCode raw) ≤ 8 * bound ∧
      natBitLength (booleanCircuitOutputCode raw) ≤ 8 * bound ∧
      natBitLength
          (booleanNodeListValidationOutput inputLength
            (booleanCircuitNodesCode raw)) ≤ 32 * bound ∧
      natBitLength
          (canonicalNatValidationOutput (booleanCircuitOutputCode raw)) ≤
        32 * bound := by
  have htuple := natBitLength_taggedTupleOutput_le 2 raw
  have hpow : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [hpow] at htuple
  have htupleOutput : natBitLength (booleanCircuitTupleOutput raw) ≤ 8 * bound := by
    simp only [booleanCircuitTupleOutput]
    omega
  have hflag : natBitLength (booleanCircuitTupleFlag raw) ≤ 8 * bound := by
    have :=
      natBitLength_mono
        (Nat.unpair_left_le (booleanCircuitTupleOutput raw))
    simp only [booleanCircuitTupleFlag]
    omega
  have hfields : natBitLength (booleanCircuitTupleFields raw) ≤ 8 * bound := by
    have :=
      natBitLength_mono
        (Nat.unpair_right_le (booleanCircuitTupleOutput raw))
    simp only [booleanCircuitTupleFields]
    omega
  have hnodes := natBitLength_booleanCircuitNodesCode_le raw
  have houtput := natBitLength_booleanCircuitOutputCode_le raw
  have hnodeList :=
    natBitLength_booleanNodeListValidationOutput_le inputLength
      (booleanCircuitNodesCode raw)
  have hnat :=
    natBitLength_canonicalNatValidationOutput_le (booleanCircuitOutputCode raw)
  exact ⟨htupleOutput, hflag, hfields, by omega, by omega, by omega, by omega⟩

/-- The strict-comparison request is one pairing over two decoded counts. -/
theorem natBitLength_booleanCircuitLtRequest_le
    {inputLength raw bound : ℕ} (htwo : 2 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    natBitLength (booleanCircuitLtRequest inputLength raw) ≤ 128 * bound := by
  obtain ⟨_, _, _, _, _, hnodeList, hnat⟩ :=
    booleanCircuitAtomCone htwo hlength hraw
  have hvalue :
      natBitLength (booleanCircuitNatValue raw) ≤ 32 * bound := by
    have :=
      natBitLength_mono
        (Nat.unpair_right_le
          (canonicalNatValidationOutput (booleanCircuitOutputCode raw)))
    simp only [booleanCircuitNatValue]
    omega
  have hcount :
      natBitLength (booleanCircuitNodeCount inputLength raw) ≤ 32 * bound := by
    have :=
      natBitLength_mono
        (Nat.unpair_right_le
          (booleanNodeListValidationOutput inputLength
            (booleanCircuitNodesCode raw)))
    simp only [booleanCircuitNodeCount]
    omega
  have hpair :
      natBitLength
          (Nat.pair (booleanCircuitNodeCount inputLength raw)
            (booleanCircuitNatValue raw)) ≤ 2 * (32 * bound) :=
    natBitLength_pair_le_two_mul hcount hvalue
  simp only [booleanCircuitLtRequest, nativeLtRequest, nativeInputRequest]
  omega

/-- The strict-comparison answer is one bit wide. -/
theorem natBitLength_booleanCircuitLtFlag_le (inputLength raw : ℕ) :
    natBitLength (booleanCircuitLtFlag inputLength raw) ≤ 1 := by
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 = 1 := natBitLength_one
  simp only [booleanCircuitLtFlag, nativeLtRequestOutput]
  rcases Nat.decLt
      (Nat.unpair (booleanCircuitLtRequest inputLength raw)).2
      (Nat.unpair (booleanCircuitLtRequest inputLength raw)).1 with hlt | hlt <;>
    simp_all

/-! ## §3 The ten-way maximum -/

set_option maxHeartbeats 1600000 in
-- One `omega` closes a twenty-way maximum over the whole circuit atom cone.
/-- **The Boolean circuit validator's width, reduced to two callee widths.**
Eight of the ten entries are paid by the atom cone; the two that survive are
the node-list validator's own width at the nodes code and the canonical
natural validator's own width at the output code.  The strict-comparison
stage is closed outright by `ValidatorWidthCombinatorLedger` §4. -/
theorem booleanCircuitValidationBits_le
    {inputLength raw bound : ℕ} (htwo : 2 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    booleanCircuitValidationBits inputLength raw ≤
      max
        (max
          (booleanNodeListValidationBits inputLength
            (booleanCircuitNodesCode raw))
          (canonicalNatValidationBits inputLength
            (booleanCircuitOutputCode raw)))
        (2048 * bound) := by
  obtain ⟨htuple, hflag, hfields, hnodes, houtput, hnodeList, hnat⟩ :=
    booleanCircuitAtomCone htwo hlength hraw
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 = 1 := natBitLength_one
  have hprefix : natBitLength (Nat.unpair (booleanCircuitTupleFields raw)).1 ≤
      8 * bound := by
    have :=
      natBitLength_mono
        (Nat.unpair_left_le (booleanCircuitTupleFields raw))
    omega
  have houtputFlag :
      natBitLength
          (Nat.pair (booleanCircuitOutputCode raw)
            (booleanCircuitTupleFlag raw)) ≤ 2 * (8 * bound) :=
    natBitLength_pair_le_two_mul houtput hflag
  have hprojectionOutput :
      natBitLength (booleanCircuitFieldProjectionOutput raw) ≤
        2 * (2 * (8 * bound)) := by
    simp only [booleanCircuitFieldProjectionOutput]
    exact natBitLength_pair_le_two_mul (by omega) houtputFlag
  have hnodeFlag :
      natBitLength
          (Nat.pair
            (booleanNodeListValidationOutput inputLength
              (booleanCircuitNodesCode raw))
            (booleanCircuitTupleFlag raw)) ≤ 2 * (32 * bound) :=
    natBitLength_pair_le_two_mul hnodeList (by omega)
  have hnodeContext :
      natBitLength
          (Nat.pair
            (booleanNodeListValidationOutput inputLength
              (booleanCircuitNodesCode raw))
            (Nat.pair (booleanCircuitOutputCode raw)
              (booleanCircuitTupleFlag raw))) ≤ 2 * (32 * bound) :=
    natBitLength_pair_le_two_mul hnodeList (by omega)
  have hnatLowering :
      natBitLength (booleanCircuitNatLoweringOutput inputLength raw) ≤
        2 * (2 * (32 * bound)) := by
    simp only [booleanCircuitNatLoweringOutput]
    exact natBitLength_pair_le_two_mul (by omega) hnodeFlag
  have hnatStage :
      natBitLength (booleanCircuitNatStageOutput inputLength raw) ≤
        2 * (2 * (32 * bound)) := by
    simp only [booleanCircuitNatStageOutput]
    exact natBitLength_pair_le_two_mul (by omega) hnodeFlag
  have hnodeStage :
      natBitLength (booleanCircuitNodeStageOutput inputLength raw) ≤
        2 * (2 * (32 * bound)) := by
    have houtputFlag' :
        natBitLength
            (Nat.pair (booleanCircuitOutputCode raw)
              (booleanCircuitTupleFlag raw)) ≤ 2 * (32 * bound) := by omega
    simp only [booleanCircuitNodeStageOutput]
    exact natBitLength_pair_le_two_mul (by omega) houtputFlag'
  have hvalue : natBitLength (booleanCircuitNatValue raw) ≤ 32 * bound := by
    have :=
      natBitLength_mono
        (Nat.unpair_right_le
          (canonicalNatValidationOutput (booleanCircuitOutputCode raw)))
    simp only [booleanCircuitNatValue]
    omega
  have hcount :
      natBitLength (booleanCircuitNodeCount inputLength raw) ≤ 32 * bound := by
    have :=
      natBitLength_mono
        (Nat.unpair_right_le
          (booleanNodeListValidationOutput inputLength
            (booleanCircuitNodesCode raw)))
    simp only [booleanCircuitNodeCount]
    omega
  have hrequest := natBitLength_booleanCircuitLtRequest_le htwo hlength hraw
  have hltFlag := natBitLength_booleanCircuitLtFlag_le inputLength raw
  have hnatContext :
      natBitLength
          (Nat.pair
            (canonicalNatValidationOutput (booleanCircuitOutputCode raw))
            (Nat.pair
              (booleanNodeListValidationOutput inputLength
                (booleanCircuitNodesCode raw))
              (booleanCircuitTupleFlag raw))) ≤ 2 * (2 * (32 * bound)) :=
    natBitLength_pair_le_two_mul (by omega) hnodeFlag
  have hltLowering :
      natBitLength (booleanCircuitLtLoweringOutput inputLength raw) ≤
        2 * (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitLtLoweringOutput]
    exact natBitLength_pair_le_two_mul (by omega) hnatStage
  have hltStage :
      natBitLength (booleanCircuitLtStageOutput inputLength raw) ≤
        2 * (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitLtStageOutput]
    exact natBitLength_pair_le_two_mul (by omega) hnatStage
  have hltGate :
      natBitLength
          (Nat.pair (booleanCircuitLtFlag inputLength raw)
            (Nat.pair
              (canonicalNatValidationOutput (booleanCircuitOutputCode raw))
              (Nat.pair
                (booleanNodeListValidationOutput inputLength
                  (booleanCircuitNodesCode raw))
                (booleanCircuitTupleFlag raw)))) ≤
        2 * (2 * (2 * (32 * bound))) :=
    natBitLength_pair_le_two_mul (by omega) hnatContext
  have hcountTag :
      natBitLength (Nat.pair 1 (booleanCircuitNodeCount inputLength raw)) ≤
        2 * (32 * bound) :=
    natBitLength_pair_le_two_mul (by omega) hcount
  -- the three wrapper stages
  have htupleBits : booleanCircuitTupleBits inputLength raw ≤ 8 * bound := by
    have htwoWidth : natBitLength 2 ≤ bound := by
      have hlog : Nat.log 2 2 = 1 := by norm_num
      simp only [natBitLength]
      omega
    have := taggedTupleBits_le (arity := 2) (by omega) hlength htwoWidth hraw
    have hpow : (2 : ℕ) ^ (2 + 1) = 8 := by norm_num
    rw [hpow] at this
    simpa only [booleanCircuitTupleBits] using this
  have hnodeStageBits :
      booleanCircuitNodeStageBits inputLength raw ≤
        max
          (booleanNodeListValidationBits inputLength
            (booleanCircuitNodesCode raw)) (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitNodeStageBits]
    exact preserveRightBits_le (by omega) (by omega) (by omega)
  have hnatStageBits :
      booleanCircuitNatStageBits inputLength raw ≤
        max
          (canonicalNatValidationBits inputLength
            (booleanCircuitOutputCode raw)) (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitNatStageBits]
    exact preserveRightBits_le (by omega) (by omega) (by omega)
  have hltCallee :
      nativeLtRequestBits inputLength (booleanCircuitLtRequest inputLength raw) ≤
        4 * (128 * bound) :=
    nativeLtRequestBits_le (by omega) (by omega) (by omega)
  have hltStageBits :
      booleanCircuitLtStageBits inputLength raw ≤
        max
          (nativeLtRequestBits inputLength
            (booleanCircuitLtRequest inputLength raw))
          (2 * (2 * (2 * (2 * (32 * bound))))) := by
    simp only [booleanCircuitLtStageBits]
    exact preserveRightBits_le (by omega) (by omega) (by omega)
  -- the four trace ledgers
  have hprojectionBits :
      booleanCircuitFieldProjectionBits inputLength raw ≤ 2 * (2 * (8 * bound)) := by
    simp only [booleanCircuitFieldProjectionBits,
      booleanCircuitFieldProjectionValues, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil]
    omega
  have hnatLoweringBits :
      booleanCircuitNatLoweringBits inputLength raw ≤ 2 * (2 * (32 * bound)) := by
    simp only [booleanCircuitNatLoweringBits, booleanCircuitNatLoweringValues,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    omega
  have hltLoweringBits :
      booleanCircuitLtLoweringBits inputLength raw ≤
        2 * (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitLtLoweringBits, booleanCircuitLtLoweringValues,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    omega
  have hgateBits :
      booleanCircuitValidationGateBits inputLength raw ≤
        2 * (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitValidationGateBits,
      booleanCircuitValidationGateValues, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil]
    omega
  simp only [booleanCircuitValidationBits]
  omega

/-! ## §4 The reduced charge, in the domination judgement

The cone is linear in the two width anchors, so the reduction is
degree-preserving: the Boolean circuit validator's width sits at exactly the
larger of its two callees' degrees. -/

/-- **The Boolean circuit validator's width, dominated.**  Two residuals. -/
theorem booleanCircuitValidationBits_polyBounded
    {inputLength raw measure lengthCoefficient rawCoefficient nodeCoefficient
      natCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hraw : PolyBounded (natBitLength raw) measure rawCoefficient degree)
    (hnode :
      PolyBounded
        (booleanNodeListValidationBits inputLength
          (booleanCircuitNodesCode raw)) measure nodeCoefficient degree)
    (hnat :
      PolyBounded
        (canonicalNatValidationBits inputLength
          (booleanCircuitOutputCode raw)) measure natCoefficient degree) :
    PolyBounded (booleanCircuitValidationBits inputLength raw) measure
      (max (max nodeCoefficient natCoefficient)
        (2048 * max lengthCoefficient (max rawCoefficient 2))) degree := by
  have hcone :
      PolyBounded (max (natBitLength inputLength) (max (natBitLength raw) 2))
        measure (max lengthCoefficient (max rawCoefficient 2)) degree :=
    hlength.max (hraw.max (polyBounded_const 2 measure degree))
  refine ((hnode.max hnat).max (hcone.const_mul 2048)).mono ?_
  exact booleanCircuitValidationBits_le
    (bound := max (natBitLength inputLength) (max (natBitLength raw) 2))
    (by omega) (by omega) (by omega)

/-! ## §5 `hcall`'s residual, at the machine's request family

`ValidatorOracleCallWidth` §3 consumes `hcircuitBits` — the Boolean circuit
validator's width at the oracle handoff's two projections.  §4 replaces it by
the two callee widths at the same projections, with no other premise: the two
width anchors are the published witness anchor and the published prefix
anchor. -/

/-- **`hcircuitBits`, from the node-list and canonical-natural widths.** -/
theorem hcircuitBits_at_computableLimits_of_two_widths
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier parameterCoefficient : ℕ)
    (hfrontier :
      2048 * max (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2))
          (max 4 2) ≤ frontier)
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient 1)
    (hnode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanNodeListValidationBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitNodesCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure frontier recoveryVerifierDegree)
    (hnat : ∀ request : WeakVerifierRequest,
      PolyBounded
        (canonicalNatValidationBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitOutputCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure frontier recoveryVerifierDegree)
    (request : WeakVerifierRequest) :
    PolyBounded
      (booleanCircuitValidationBits
        (handoffOracleArity
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        (handoffOracleCode
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness))))
      request.measure frontier recoveryVerifierDegree := by
  have hprefix :=
    polyBounded_computableLimits_prefixWidth_of_parameter profile copyBound
      oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      (by omega : (1 : ℕ) ≤ 2) (by omega : 2 * 1 ≤ 2) hparameter request
  have hcode :=
    (polyBounded_handoffOracleCode_structuralPrefixOutput
      (limits :=
        computableLimitsOf profile copyBound oracleArity oracleSizeCap sumArity
          symmetricWireCap thresholdWireCap request.inputArity)
      (polyBounded_witnessWidth request)).degree_mono
      (show 1 ≤ recoveryVerifierDegree by norm_num [recoveryVerifierDegree])
  have harity :=
    (polyBounded_natBitLength_of_le (polyBounded_structuralPrefixOutput hprefix)
      ((Nat.unpair_left_le _).trans
        ((Nat.unpair_right_le _).trans
          ((Nat.unpair_right_le _).trans
            ((Nat.unpair_right_le _).trans
              (Nat.unpair_right_le _)))))).degree_mono
      (show 2 ≤ recoveryVerifierDegree by norm_num [recoveryVerifierDegree])
  exact (booleanCircuitValidationBits_polyBounded harity hcode (hnode request)
    (hnat request)).coefficient_mono (by omega)

/-- **`hcall`, from the node-list and canonical-natural widths alone.** -/
theorem hcall_at_computableLimits_of_two_widths
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier parameterCoefficient : ℕ)
    (hfour : 4 ≤ frontier)
    (hhandoffFrontier :
      16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) ≤ frontier)
    (hcircuitFrontier :
      2048 * max (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2))
          (max 4 2) ≤ frontier)
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient 1)
    (hnode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanNodeListValidationBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitNodesCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure frontier recoveryVerifierDegree)
    (hnat : ∀ request : WeakVerifierRequest,
      PolyBounded
        (canonicalNatValidationBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitOutputCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure frontier recoveryVerifierDegree)
    (request : WeakVerifierRequest) :
    PolyBounded
      (recoveryOracleCallBits (WeakVerifierRequest.length request)
        (recoveryValidatorStructuralPrefixOutput
          (computableLimitsOf profile copyBound oracleArity oracleSizeCap
            sumArity symmetricWireCap thresholdWireCap request.inputArity)
          (encodeBitInput request.witness)))
      request.measure (128 * frontier + 8) recoveryVerifierDegree :=
  ValidatorOracleCallWidth.hcall_at_computableLimits_of_circuitBits profile
    copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
    thresholdWireCap frontier parameterCoefficient hfour hhandoffFrontier
    hparameter
    (fun request =>
      hcircuitBits_at_computableLimits_of_two_widths profile copyBound
        oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        frontier parameterCoefficient hcircuitFrontier hparameter hnode hnat
        request)
    request

end NearCubicWires.ValidatorCircuitWidthLedger
