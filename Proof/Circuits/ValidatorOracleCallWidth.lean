import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorThreeLeafClosure

namespace NearCubicWires.ValidatorOracleCallWidth

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorOracleResultWidth
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes

open private nativeContextCallAdapterBits nativeCallWrapBits
  nativeCallUnwrapBits from Proof.MachineModel.CanonicalNativeCallProgram

/-! ## §1 The native contextual call's width ledger -/

private theorem pair_width {left right bound : ℕ}
    (hleft : natBitLength left ≤ bound) (hright : natBitLength right ≤ bound) :
    natBitLength (Nat.pair left right) ≤ 2 * bound := by
  have hbound := pairCodeBits_le left right
  omega

private theorem balancedTraversalTree_singleton (atom : ℕ) :
    balancedTraversalTree [atom] = .leaf atom := by
  simp only [balancedTraversalTree]

/-- The empty traversal stack's code is the empty tagged list. -/
private theorem encodeBalancedTraversalStack_nil :
    encodeBalancedTraversalStack [] = 0 := by
  simp only [encodeBalancedTraversalStack, List.map_nil, encodeTaggedList]

/-- **One native call's register requirement at a singleton request.** -/
private theorem nativeCallBits_le
    (outerInputLength calleeInputLength requestCode output calleeBits
      width : ℕ)
    (hpositive : 1 ≤ width)
    (houter : natBitLength outerInputLength ≤ width)
    (hcallee : natBitLength calleeInputLength ≤ width)
    (hrequest : natBitLength requestCode ≤ width)
    (houtput : natBitLength output ≤ width) :
    nativeCallBits outerInputLength calleeInputLength requestCode output
        calleeBits ≤ max calleeBits (2 * (2 * width)) := by
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 ≤ width := by
    rw [natBitLength_one]; omega
  have hrequestPair :
      natBitLength (Nat.pair calleeInputLength requestCode) ≤ 2 * width :=
    pair_width hcallee hrequest
  have hwrap :
      natBitLength (Nat.pair 1 (Nat.pair calleeInputLength requestCode)) ≤
        2 * (2 * width) :=
    pair_width (le_trans hone (by omega)) hrequestPair
  have hunwrap : natBitLength (Nat.pair 1 output) ≤ 2 * width :=
    pair_width hone houtput
  have hcallPair :
      natBitLength (Nat.pair (Nat.pair calleeInputLength requestCode) output) ≤
        2 * (2 * width) :=
    pair_width hrequestPair (le_trans houtput (by omega))
  simp only [nativeCallBits, nativeCallWrapBits, nativeCallUnwrapBits,
    nativeInputRequest, balancedCallRequiredBits,
    balancedTraversalTree_singleton, balancedTraversalRequiredBits,
    encodeBalancedTraversalStack_nil, BalancedTraversalTree.code,
    BalancedTraversalTree.map, encodeBalancedList, List.map_cons,
    List.map_nil, List.foldr_cons, List.foldr_nil]
  omega

/-- **One native contextual call's register requirement.**  A closed multiple of
the widest scalar argument, or the callee's own width.  Stated over variables:
nothing here is a program span, so nothing is evaluated. -/
theorem nativeContextCallBits_le
    (outerInputLength calleeInputLength requestCode context output calleeBits
      width : ℕ)
    (hpositive : 1 ≤ width)
    (houter : natBitLength outerInputLength ≤ width)
    (hcallee : natBitLength calleeInputLength ≤ width)
    (hrequest : natBitLength requestCode ≤ width)
    (hcontext : natBitLength context ≤ width)
    (houtput : natBitLength output ≤ width) :
    nativeContextCallBits outerInputLength calleeInputLength requestCode context
        output calleeBits ≤ max calleeBits (4 * width) := by
  have hinner :=
    nativeCallBits_le outerInputLength calleeInputLength requestCode output
      calleeBits width hpositive houter hcallee hrequest houtput
  have hrequestPair :
      natBitLength (Nat.pair calleeInputLength requestCode) ≤ 2 * width :=
    pair_width hcallee hrequest
  have hretained :
      natBitLength (Nat.pair calleeInputLength context) ≤ 2 * width :=
    pair_width hcallee hcontext
  have hadapterLeft :
      natBitLength
          (Nat.pair requestCode (Nat.pair calleeInputLength context)) ≤
        2 * (2 * width) :=
    pair_width (le_trans hrequest (by omega)) hretained
  have hadapterRight :
      natBitLength
          (Nat.pair (Nat.pair calleeInputLength requestCode)
            (Nat.pair calleeInputLength context)) ≤ 2 * (2 * width) :=
    pair_width hrequestPair hretained
  have hexit :
      natBitLength (Nat.pair output (Nat.pair calleeInputLength context)) ≤
        2 * (2 * width) :=
    pair_width (le_trans houtput (by omega)) hretained
  simp only [nativeContextCallBits, nativeContextCallAdapterBits,
    preserveRightBits, nativeInputRequest]
  omega

/-! ## §2 The validator's oracle call

At the validator's own call the five arguments are the public input length, the
handoff's two projections, the handoff itself and the oracle validation result
— and every one of those is bounded by the oracle stage's published width. -/

/-- **`hcall`, reduced to the Boolean circuit validator's register
requirement.**  No part of the native call's plumbing survives: what is left is
the callee's own width and the oracle stage's published width parameter. -/
theorem recoveryOracleCallBits_le (inputLength handoff : ℕ) :
    recoveryOracleCallBits inputLength handoff ≤
      max
        (booleanCircuitValidationBits (handoffOracleArity handoff)
          (handoffOracleCode handoff))
        (4 * max (natBitLength inputLength)
          (recoveryOracleStageWidth handoff)) := by
  have hstage := one_le_recoveryOracleStageWidth handoff
  have hhandoff : natBitLength handoff ≤ recoveryOracleStageWidth handoff :=
    le_max_right _ _
  have hresult :
      natBitLength (recoveryOracleValidationResult handoff) ≤
        recoveryOracleStageWidth handoff := le_max_left _ _
  have hcode : natBitLength (handoffOracleCode handoff) ≤ natBitLength handoff :=
    natBitLength_mono (handoffOracleCode_le handoff)
  have harity :
      natBitLength (handoffOracleArity handoff) ≤ natBitLength handoff :=
    natBitLength_mono
      ((Nat.unpair_left_le _).trans
        ((Nat.unpair_right_le _).trans
          ((Nat.unpair_right_le _).trans
            ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _)))))
  exact nativeContextCallBits_le inputLength (handoffOracleArity handoff)
    (handoffOracleCode handoff) handoff
    (recoveryOracleValidationResult handoff)
    (booleanCircuitValidationBits (handoffOracleArity handoff)
      (handoffOracleCode handoff))
    (max (natBitLength inputLength) (recoveryOracleStageWidth handoff))
    (by omega) (le_max_left _ _) (by omega) (by omega) (by omega) (by omega)

/-- **`hcall`, dominated.**  One residual: the Boolean circuit validator's own
register requirement. -/
theorem recoveryOracleCallBits_polyBounded
    {inputLength handoff measure lengthCoefficient widthCoefficient
      calleeCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hwidth :
      PolyBounded (recoveryOracleStageWidth handoff) measure widthCoefficient
        degree)
    (hcallee :
      PolyBounded
        (booleanCircuitValidationBits (handoffOracleArity handoff)
          (handoffOracleCode handoff)) measure calleeCoefficient degree) :
    PolyBounded (recoveryOracleCallBits inputLength handoff) measure
      (max calleeCoefficient (4 * max lengthCoefficient widthCoefficient))
      degree :=
  (hcallee.max ((hlength.max hwidth).const_mul 4)).mono
    (recoveryOracleCallBits_le inputLength handoff)

/-! ## §3 `hcall` at the machine's request family

The three width certificates the reduced ledger consumes are all published: the
request length's own width anchor, the structural prefix's output width, and the
oracle validation result.  So `hcall` costs exactly one new premise — the
Boolean circuit validator's register requirement. -/

/-- **`hcall`, discharged from the Boolean circuit validator's width alone.** -/
theorem hcall_at_computableLimits_of_circuitBits
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier parameterCoefficient : ℕ)
    (hfour : 4 ≤ frontier)
    (hhandoffFrontier :
      16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) ≤ frontier)
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient 1)
    (hcircuitBits : ∀ request : WeakVerifierRequest,
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
        request.measure frontier recoveryVerifierDegree)
    (request : WeakVerifierRequest) :
    PolyBounded
      (recoveryOracleCallBits (WeakVerifierRequest.length request)
        (recoveryValidatorStructuralPrefixOutput
          (computableLimitsOf profile copyBound oracleArity oracleSizeCap
            sumArity symmetricWireCap thresholdWireCap request.inputArity)
          (encodeBitInput request.witness)))
      request.measure (128 * frontier + 8) recoveryVerifierDegree := by
  have hprefix :=
    polyBounded_computableLimits_prefixWidth_of_parameter profile copyBound
      oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      (degree := recoveryVerifierDegree)
      (by norm_num [recoveryVerifierDegree])
      (by norm_num [recoveryVerifierDegree]) hparameter request
  have hhandoff :=
    (polyBounded_structuralPrefixOutput hprefix).coefficient_mono
      (show 16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) ≤ frontier by
        omega)
  have hresult := polyBounded_recoveryOracleValidationResult hhandoff
  have hstage :=
    polyBounded_recoveryOracleStageWidth hresult
      (hhandoff.coefficient_mono (show frontier ≤ 32 * frontier + 2 by omega))
  have hlength :=
    (polyBounded_requestLengthWidth request).degree_mono
      (show 1 ≤ recoveryVerifierDegree by norm_num [recoveryVerifierDegree])
  exact (recoveryOracleCallBits_polyBounded hlength hstage
    (hcircuitBits request)).coefficient_mono (by omega)

end NearCubicWires.ValidatorOracleCallWidth
