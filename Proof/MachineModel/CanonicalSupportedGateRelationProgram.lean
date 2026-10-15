import Proof.MachineModel.CanonicalBalancedLengthProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.MachineModel.CanonicalNativeEqualityProgram
import Proof.MachineModel.CanonicalSupplierSupportCompressionProgram
import Proof.MachineModel.CanonicalSupportedGateValidationProgram
import Proof.Circuits.CanonicalWitnessCodec
import Proof.MachineModel.TaggedProgramChoice

/-!
# Canonical supported-gate relations

The field validator establishes canonical syntax.  This module checks the
dependent gate relations: both vectors have the public arity, and every weight
outside the declared support is zero.  Support checking reuses the production
support compressor and the shared nonzero counter; it does not introduce a
second list traversal or decoder.
-/

namespace NearCubicWires.CanonicalSupportedGateRelationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalSupportedGateValidationProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## Semantic support invariant -/

def supportedGateZeroOutsideCodes
    (weights : List ℕ) (membership : List Bool) : Prop :=
  List.Forall₂
    (fun weight bit => bit = false → weight = 0)
    weights membership

private theorem supportedWeights_nonzeroCount_le :
    ∀ weights membership,
      nonzeroAtomCount (supportedWeights weights membership) ≤
        nonzeroAtomCount weights
  | [], _ => by simp [supportedWeights, nonzeroAtomCount]
  | _ :: _, [] => by simp [supportedWeights, nonzeroAtomCount]
  | weight :: weights, bit :: membership => by
      have htail :=
        supportedWeights_nonzeroCount_le weights membership
      cases bit with
      | false =>
          simp only [supportedWeights, nonzeroAtomCount]
          by_cases hweight : weight = 0
          · simp [hweight, htail]
          · simp [hweight]
            omega
      | true =>
          simp [supportedWeights, nonzeroAtomCount, htail]

theorem nonzeroAtomCount_supportedWeights_eq_iff_zeroOutside
    (weights : List ℕ) (membership : List Bool)
    (hlength : weights.length = membership.length) :
    nonzeroAtomCount (supportedWeights weights membership) =
        nonzeroAtomCount weights ↔
      supportedGateZeroOutsideCodes weights membership := by
  induction weights generalizing membership with
  | nil =>
      have hmembership : membership = [] := by
        simpa using hlength.symm
      subst membership
      simp [supportedWeights, nonzeroAtomCount,
        supportedGateZeroOutsideCodes]
  | cons weight weights inductionHypothesis =>
      cases membership with
      | nil => simp at hlength
      | cons bit membership =>
          have htailLength : weights.length = membership.length := by
            simpa using hlength
          cases bit with
          | false =>
              have htailLe :
                  nonzeroAtomCount (supportedWeights weights membership) ≤
                    nonzeroAtomCount weights :=
                supportedWeights_nonzeroCount_le weights membership
              constructor
              · intro hequal
                have hweight : weight = 0 := by
                  simp [supportedWeights, nonzeroAtomCount] at hequal
                  by_contra hnonzero
                  simp [hnonzero] at hequal
                  omega
                have htail :
                    nonzeroAtomCount
                        (supportedWeights weights membership) =
                      nonzeroAtomCount weights := by
                  simpa [supportedWeights, nonzeroAtomCount, hweight] using
                    hequal
                apply List.Forall₂.cons
                · intro _
                  exact hweight
                · exact
                    (inductionHypothesis membership htailLength).1 htail
              · intro hzeroOutside
                cases hzeroOutside with
                | cons hweight htail =>
                  have hzero : weight = 0 := hweight rfl
                  have hequal :=
                    (inductionHypothesis membership htailLength).2 htail
                  simpa [supportedWeights, nonzeroAtomCount, hzero] using
                    hequal
          | true =>
              constructor
              · intro hequal
                have htail :
                    nonzeroAtomCount
                        (supportedWeights weights membership) =
                      nonzeroAtomCount weights := by
                  simpa [supportedWeights, nonzeroAtomCount] using hequal
                exact
                  .cons (by simp)
                    ((inductionHypothesis membership htailLength).1 htail)
              · intro hzeroOutside
                cases hzeroOutside with
                | cons _ htail =>
                  have hequal :=
                    (inductionHypothesis membership htailLength).2 htail
                  simpa [supportedWeights, nonzeroAtomCount] using hequal

theorem supportedGateZeroOutsideCodes_map_encodeInt_iff
    (weights : List ℤ) (membership : List Bool)
    (hlength : weights.length = membership.length) :
    supportedGateZeroOutsideCodes (weights.map encodeInt) membership ↔
      List.Forall₂
        (fun weight bit => bit = false → weight = 0)
        weights membership := by
  induction weights generalizing membership with
  | nil =>
      have hmembership : membership = [] := by
        simpa using hlength.symm
      subst membership
      simp [supportedGateZeroOutsideCodes]
  | cons weight weights inductionHypothesis =>
      cases membership with
      | nil => simp at hlength
      | cons bit membership =>
          have htailLength : weights.length = membership.length := by
            simpa using hlength
          simp only [List.map_cons, supportedGateZeroOutsideCodes,
            List.forall₂_cons]
          constructor
          · rintro ⟨hhead, htail⟩
            exact
              ⟨fun hfalse =>
                (encodeInt_eq_zero_iff weight).1 (hhead hfalse),
                (inductionHypothesis membership htailLength).1 htail⟩
          · rintro ⟨hhead, htail⟩
            exact
              ⟨fun hfalse =>
                (encodeInt_eq_zero_iff weight).2 (hhead hfalse),
                (inductionHypothesis membership htailLength).2 htail⟩

def rejectProgram : NPOracleProgram :=
  [ .set 0 0 1
  , .halt 0
  ]

def acceptTaggedPayloadProgram : NPOracleProgram :=
  [ .set 2 1 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] theorem rejectProgram_oracleFree : OracleFree rejectProgram := by
  rfl

@[simp] theorem acceptTaggedPayloadProgram_oracleFree :
    OracleFree acceptTaggedPayloadProgram := by
  rfl

theorem run_rejectProgram
    (inputLength payload maximumBits extraFuel : ℕ)
    (hzero : natBitLength 0 ≤ maximumBits) :
    runNPOracleProgram rejectProgram maximumBits (extraFuel + 2)
        (initialNPOracleState inputLength payload) =
      some 0 := by
  rw [show extraFuel + 2 = (extraFuel + 1) + 1 by omega]
  rw [run_set_instruction (by rfl) rfl hzero]
  exact run_halt_instruction (fuel := extraFuel) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]) hzero

def acceptTaggedPayloadBits (payload : ℕ) : ℕ :=
  max (natBitLength payload) (natBitLength (Nat.pair 1 payload))

theorem run_acceptTaggedPayloadProgram
    (inputLength payload : ℕ) :
    runNPOracleProgram acceptTaggedPayloadProgram
        (acceptTaggedPayloadBits payload) 3
        (initialNPOracleState inputLength payload) =
      some (Nat.pair 1 payload) := by
  let maximumBits := acceptTaggedPayloadBits payload
  have hone : natBitLength 1 ≤ maximumBits := by
    exact (show natBitLength 1 ≤ natBitLength payload by
      simp [natBitLength]).trans (Nat.le_max_left _ _)
  have houtput :
      natBitLength (Nat.pair 1 payload) ≤ maximumBits :=
    Nat.le_max_right _ _
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_set_instruction (by rfl) rfl hone]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## Canonical field payload adapters -/

def supportedGateFieldPayload
    (thresholdCode weightsCode membershipCode : ℕ) : ℕ :=
  Nat.pair thresholdCode (Nat.pair weightsCode membershipCode)

def supportedGateFieldPairOutput
    (thresholdCode weightsCode membershipCode : ℕ) : ℕ :=
  let payload :=
    supportedGateFieldPayload thresholdCode weightsCode membershipCode
  Nat.pair (Nat.pair weightsCode membershipCode) payload

def supportedGateFieldPairProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] theorem supportedGateFieldPairProgram_oracleFree :
    OracleFree supportedGateFieldPairProgram := by
  rfl

def supportedGateFieldPairBits
    (thresholdCode weightsCode membershipCode : ℕ) : ℕ :=
  max
    (natBitLength
      (supportedGateFieldPayload thresholdCode weightsCode membershipCode))
    (natBitLength
      (supportedGateFieldPairOutput thresholdCode weightsCode membershipCode))

theorem run_supportedGateFieldPairProgram
    (inputLength thresholdCode weightsCode membershipCode : ℕ) :
    runNPOracleProgram supportedGateFieldPairProgram
        (supportedGateFieldPairBits thresholdCode weightsCode membershipCode) 3
        (initialNPOracleState inputLength
          (supportedGateFieldPayload thresholdCode weightsCode
            membershipCode)) =
      some
        (supportedGateFieldPairOutput thresholdCode weightsCode
          membershipCode) := by
  let payload :=
    supportedGateFieldPayload thresholdCode weightsCode membershipCode
  let request := Nat.pair weightsCode membershipCode
  let output :=
    supportedGateFieldPairOutput thresholdCode weightsCode membershipCode
  let maximumBits :=
    supportedGateFieldPairBits thresholdCode weightsCode membershipCode
  have hinput : natBitLength payload ≤ maximumBits :=
    Nat.le_max_left _ _
  have hrequest : natBitLength request ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair thresholdCode request)).trans hinput
  have houtput : natBitLength output ≤ maximumBits :=
    Nat.le_max_right _ _
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [supportedGateFieldPayload, initialNPOracleState, request])
    hrequest]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, output, supportedGateFieldPairOutput,
      request]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput

def supportedGateLengthEqualityInput
    (thresholdCode weightsCode membershipCode weightsLength
      membershipLength : ℕ) : ℕ :=
  Nat.pair (Nat.pair weightsLength membershipLength)
    (supportedGateFieldPayload thresholdCode weightsCode membershipCode)

def supportedGateLengthEqualityOutput
    (inputLength thresholdCode weightsCode membershipCode weightsLength
      membershipLength : ℕ) : ℕ :=
  Nat.pair
    (nativeNatEqInput
      (Nat.pair weightsLength membershipLength)
      (Nat.pair inputLength inputLength))
    (supportedGateFieldPayload thresholdCode weightsCode membershipCode)

def supportedGateLengthEqualityProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 1 1 4 3
  , .pair 2 4 5 4
  , .pair 5 3 0 5
  , .halt 0
  ]

@[simp] theorem supportedGateLengthEqualityProgram_oracleFree :
    OracleFree supportedGateLengthEqualityProgram := by
  rfl

def supportedGateLengthEqualityBits
    (inputLength thresholdCode weightsCode membershipCode weightsLength
      membershipLength : ℕ) : ℕ :=
  max
    (natBitLength
      (supportedGateLengthEqualityInput thresholdCode weightsCode
        membershipCode weightsLength membershipLength))
    (natBitLength
      (supportedGateLengthEqualityOutput inputLength thresholdCode
        weightsCode membershipCode weightsLength membershipLength))

theorem run_supportedGateLengthEqualityProgram
    (inputLength thresholdCode weightsCode membershipCode weightsLength
      membershipLength : ℕ) :
    runNPOracleProgram supportedGateLengthEqualityProgram
        (supportedGateLengthEqualityBits inputLength thresholdCode weightsCode
          membershipCode weightsLength membershipLength)
        6
        (initialNPOracleState inputLength
          (supportedGateLengthEqualityInput thresholdCode weightsCode
            membershipCode weightsLength membershipLength)) =
      some
        (supportedGateLengthEqualityOutput inputLength thresholdCode weightsCode
          membershipCode weightsLength membershipLength) := by
  let lengths := Nat.pair weightsLength membershipLength
  let arities := Nat.pair inputLength inputLength
  let payload :=
    supportedGateFieldPayload thresholdCode weightsCode membershipCode
  let request := nativeNatEqInput lengths arities
  let input :=
    supportedGateLengthEqualityInput thresholdCode weightsCode membershipCode
      weightsLength membershipLength
  let output :=
    supportedGateLengthEqualityOutput inputLength thresholdCode weightsCode
      membershipCode weightsLength membershipLength
  let maximumBits :=
    supportedGateLengthEqualityBits inputLength thresholdCode weightsCode
      membershipCode weightsLength membershipLength
  have hinput : natBitLength input ≤ maximumBits :=
    Nat.le_max_left _ _
  have houtput : natBitLength output ≤ maximumBits :=
    Nat.le_max_right _ _
  have hlengths : natBitLength lengths ≤ maximumBits := by
    exact
      (natBitLength_mono (Nat.left_le_pair lengths payload)).trans hinput
  have hpayload : natBitLength payload ≤ maximumBits := by
    exact
      (natBitLength_mono (Nat.right_le_pair lengths payload)).trans hinput
  have hrequest : natBitLength request ≤ maximumBits := by
    exact
      (natBitLength_mono (Nat.left_le_pair request payload)).trans houtput
  have harities : natBitLength arities ≤ maximumBits := by
    exact
      (natBitLength_mono
        ((Nat.right_le_pair lengths arities).trans
          (Nat.left_le_pair request payload))).trans houtput
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [supportedGateLengthEqualityInput, lengths,
      initialNPOracleState]) hlengths]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [supportedGateLengthEqualityInput, payload,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpayload]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, arities]) harities]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, request, nativeNatEqInput]) hrequest]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, output, supportedGateLengthEqualityOutput,
      request, lengths, arities, payload, nativeNatEqInput]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput

/-! ## Exact public-arity validation -/

def supportedGateLengthValidationProgram : NPOracleProgram :=
  linkPrograms supportedGateFieldPairProgram <|
    linkPrograms
      (preserveRightProgram (pairedCallProgram balancedLengthProgram)) <|
      linkPrograms supportedGateLengthEqualityProgram
        (preserveRightProgram nativeNatEqProgram)

@[simp] theorem supportedGateLengthValidationProgram_oracleFree :
    OracleFree supportedGateLengthValidationProgram := by
  exact
    oracleFree_linkPrograms supportedGateFieldPairProgram_oracleFree <|
      oracleFree_linkPrograms
        (preserveRightProgram_oracleFree _
          (pairedCallProgram_oracleFree _ balancedLengthProgram_oracleFree)) <|
        oracleFree_linkPrograms
          supportedGateLengthEqualityProgram_oracleFree
          (preserveRightProgram_oracleFree _
            nativeNatEqProgram_oracleFree)

def supportedGateLengthValidationOutput
    (inputLength thresholdCode : ℕ)
    (weightAtoms membershipAtoms : List ℕ) : ℕ :=
  Nat.pair
    (nativeNatEqOutput
      (Nat.pair weightAtoms.length membershipAtoms.length)
      (Nat.pair inputLength inputLength))
    (supportedGateFieldPayload thresholdCode
      (encodeBalancedList weightAtoms)
      (encodeBalancedList membershipAtoms))

private def supportedGatePairedLengthBits
    (inputLength : ℕ) (weightAtoms membershipAtoms : List ℕ) : ℕ :=
  pairedCallBits inputLength
    (balancedLengthBits inputLength weightAtoms)
    (balancedLengthBits inputLength membershipAtoms)
    (encodeBalancedList weightAtoms)
    (encodeBalancedList membershipAtoms)
    weightAtoms.length membershipAtoms.length

def supportedGateLengthValidationBits
    (inputLength thresholdCode : ℕ)
    (weightAtoms membershipAtoms : List ℕ) : ℕ :=
  let weightsCode := encodeBalancedList weightAtoms
  let membershipCode := encodeBalancedList membershipAtoms
  let payload :=
    supportedGateFieldPayload thresholdCode weightsCode membershipCode
  let lengths := Nat.pair weightAtoms.length membershipAtoms.length
  let arities := Nat.pair inputLength inputLength
  let flag := nativeNatEqOutput lengths arities
  max 1 <|
    max (supportedGateFieldPairBits thresholdCode weightsCode membershipCode) <|
      max
        (preserveRightBits
          (supportedGatePairedLengthBits inputLength weightAtoms membershipAtoms)
          (Nat.pair weightsCode membershipCode) payload lengths) <|
        max
          (supportedGateLengthEqualityBits inputLength thresholdCode weightsCode
            membershipCode weightAtoms.length membershipAtoms.length)
          (preserveRightBits
            (nativeNatEqBits inputLength lengths arities)
            (nativeNatEqInput lengths arities) payload flag)

def supportedGateLengthValidationFuel
    (inputLength : ℕ) (weightAtoms membershipAtoms : List ℕ) : ℕ :=
  let pairedFuel :=
    pairedCallFuel balancedLengthProgram
      (balancedLengthFuel weightAtoms)
      (balancedLengthFuel membershipAtoms)
  linkFuel
    (linkPrograms
      (preserveRightProgram (pairedCallProgram balancedLengthProgram)) <|
      linkPrograms supportedGateLengthEqualityProgram
        (preserveRightProgram nativeNatEqProgram))
    3 <|
    linkFuel
      (linkPrograms supportedGateLengthEqualityProgram
        (preserveRightProgram nativeNatEqProgram))
      (preserveRightFuel pairedFuel) <|
      linkFuel (preserveRightProgram nativeNatEqProgram) 6 <|
        preserveRightFuel
          (nativeNatEqFuel
            (Nat.pair weightAtoms.length membershipAtoms.length)
            (Nat.pair inputLength inputLength))

theorem run_supportedGateLengthValidationProgram
    (inputLength thresholdCode : ℕ)
    (weightAtoms membershipAtoms : List ℕ) :
    runNPOracleProgram supportedGateLengthValidationProgram
        (supportedGateLengthValidationBits inputLength thresholdCode
          weightAtoms membershipAtoms)
        (supportedGateLengthValidationFuel inputLength weightAtoms
          membershipAtoms)
        (initialNPOracleState inputLength
          (supportedGateFieldPayload thresholdCode
            (encodeBalancedList weightAtoms)
            (encodeBalancedList membershipAtoms))) =
      some
        (supportedGateLengthValidationOutput inputLength thresholdCode
          weightAtoms membershipAtoms) := by
  let weightsCode := encodeBalancedList weightAtoms
  let membershipCode := encodeBalancedList membershipAtoms
  let payload :=
    supportedGateFieldPayload thresholdCode weightsCode membershipCode
  let lengths := Nat.pair weightAtoms.length membershipAtoms.length
  let arities := Nat.pair inputLength inputLength
  let flag := nativeNatEqOutput lengths arities
  let pairedBits :=
    supportedGatePairedLengthBits inputLength weightAtoms membershipAtoms
  let pairedFuel :=
    pairedCallFuel balancedLengthProgram
      (balancedLengthFuel weightAtoms)
      (balancedLengthFuel membershipAtoms)
  let maximumBits :=
    supportedGateLengthValidationBits inputLength thresholdCode
      weightAtoms membershipAtoms
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, supportedGateLengthValidationBits]
  have hfieldBits :
      supportedGateFieldPairBits thresholdCode weightsCode membershipCode ≤
        maximumBits := by
    simp [maximumBits, supportedGateLengthValidationBits, weightsCode,
      membershipCode]
  have hpairedBits :
      preserveRightBits pairedBits (Nat.pair weightsCode membershipCode)
          payload lengths ≤ maximumBits := by
    simp [maximumBits, supportedGateLengthValidationBits, weightsCode,
      membershipCode, payload, lengths, pairedBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    have hsource : natBitLength inputLength ≤ pairedBits := by
      dsimp only [pairedBits, supportedGatePairedLengthBits,
        pairedCallBits]
      exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    exact hsource.trans <|
      (Nat.le_max_left _ _).trans hpairedBits
  have hprojectionBits :
      supportedGateLengthEqualityBits inputLength thresholdCode weightsCode
          membershipCode weightAtoms.length membershipAtoms.length ≤
        maximumBits := by
    simp [maximumBits, supportedGateLengthValidationBits, weightsCode,
      membershipCode]
  have hequalityBits :
      preserveRightBits
          (nativeNatEqBits inputLength lengths arities)
          (nativeNatEqInput lengths arities) payload flag ≤ maximumBits := by
    simp [maximumBits, supportedGateLengthValidationBits, weightsCode,
      membershipCode, payload, lengths, arities, flag]
  have hfield :
      runNPOracleProgram supportedGateFieldPairProgram maximumBits 3
          (initialNPOracleState inputLength payload) =
        some (Nat.pair (Nat.pair weightsCode membershipCode) payload) := by
    have hrun :=
      run_bits_mono
        (run_supportedGateFieldPairProgram inputLength thresholdCode
          weightsCode membershipCode)
        hfieldBits
    simpa [supportedGateFieldPairOutput, payload] using hrun
  have hpaired :
      runNPOracleProgram (pairedCallProgram balancedLengthProgram)
          pairedBits pairedFuel
          (initialNPOracleState inputLength
            (Nat.pair weightsCode membershipCode)) =
        some lengths := by
    have hrun :=
      run_pairedCallProgram balancedLengthProgram inputLength
        (balancedLengthBits inputLength weightAtoms)
        (balancedLengthBits inputLength membershipAtoms)
        (balancedLengthFuel weightAtoms)
        (balancedLengthFuel membershipAtoms)
        weightsCode membershipCode weightAtoms.length membershipAtoms.length
        (by simpa [weightsCode] using
          run_balancedLengthProgram inputLength weightAtoms)
        (by simpa [membershipCode] using
          run_balancedLengthProgram inputLength membershipAtoms)
    simpa [pairedBits, pairedFuel,
      supportedGatePairedLengthBits, lengths] using hrun
  have hpairedPreserved :
      runNPOracleProgram
          (preserveRightProgram (pairedCallProgram balancedLengthProgram))
          maximumBits (preserveRightFuel pairedFuel)
          (initialNPOracleState inputLength
            (Nat.pair (Nat.pair weightsCode membershipCode) payload)) =
        some (Nat.pair lengths payload) := by
    exact run_bits_mono
      (run_preserveRightProgram (pairedCallProgram balancedLengthProgram)
        inputLength pairedBits pairedFuel
        (Nat.pair weightsCode membershipCode) payload lengths hpaired)
      hpairedBits
  have hprojection :
      runNPOracleProgram supportedGateLengthEqualityProgram maximumBits 6
          (initialNPOracleState inputLength (Nat.pair lengths payload)) =
        some (Nat.pair (nativeNatEqInput lengths arities) payload) := by
    have hrun :=
      run_bits_mono
        (run_supportedGateLengthEqualityProgram inputLength thresholdCode
          weightsCode membershipCode weightAtoms.length
          membershipAtoms.length)
        hprojectionBits
    simpa [supportedGateLengthEqualityInput,
      supportedGateLengthEqualityOutput, lengths, arities, payload,
      nativeNatEqInput] using hrun
  have hequality :
      runNPOracleProgram nativeNatEqProgram
          (nativeNatEqBits inputLength lengths arities)
          (nativeNatEqFuel lengths arities)
          (initialNPOracleState inputLength
            (nativeNatEqInput lengths arities)) =
        some flag := by
    simpa [flag] using run_nativeNatEqProgram inputLength lengths arities
  have hequalityPreserved :
      runNPOracleProgram (preserveRightProgram nativeNatEqProgram)
          maximumBits (preserveRightFuel (nativeNatEqFuel lengths arities))
          (initialNPOracleState inputLength
            (Nat.pair (nativeNatEqInput lengths arities) payload)) =
        some (Nat.pair flag payload) := by
    exact run_bits_mono
      (run_preserveRightProgram nativeNatEqProgram inputLength
        (nativeNatEqBits inputLength lengths arities)
        (nativeNatEqFuel lengths arities)
        (nativeNatEqInput lengths arities) payload flag hequality)
      hequalityBits
  have hprojectionTail :=
    run_linkPrograms hpositive hlength hprojection hequalityPreserved
  have hlengthTail :=
    run_linkPrograms hpositive hlength hpairedPreserved hprojectionTail
  have hrun :=
    run_linkPrograms hpositive hlength hfield hlengthTail
  simpa [supportedGateLengthValidationProgram,
    supportedGateLengthValidationFuel,
    supportedGateLengthValidationOutput, weightsCode, membershipCode,
    payload, lengths, arities, flag, pairedFuel] using hrun

/-! ## Compression and zero-outside count framing -/

private def supportedGateCompressionResult
    (selectedWeightsCode supportCount membershipCode : ℕ) : ℕ :=
  Nat.pair selectedWeightsCode (Nat.pair supportCount membershipCode)

def supportedGateCompressionCountFrameInput
    (thresholdCode weightsCode membershipCode selectedWeightsCode
      supportCount : ℕ) : ℕ :=
  Nat.pair
    (supportedGateCompressionResult selectedWeightsCode supportCount
      membershipCode)
    (supportedGateFieldPayload thresholdCode weightsCode membershipCode)

def supportedGateCompressedPayload
    (thresholdCode selectedWeightsCode supportCount membershipCode : ℕ) : ℕ :=
  Nat.pair thresholdCode <|
    Nat.pair selectedWeightsCode (Nat.pair supportCount membershipCode)

def supportedGateCompressionCountFrameOutput
    (thresholdCode weightsCode membershipCode selectedWeightsCode
      supportCount : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair (Nat.pair 0 weightsCode)
      (Nat.pair 0 selectedWeightsCode))
    (supportedGateCompressedPayload thresholdCode selectedWeightsCode
      supportCount membershipCode)

def supportedGateCompressionCountFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairLeft 3 5 4
  , .unpairRight 3 6 5
  , .unpairLeft 6 7 6
  , .set 8 0 7
  , .pair 8 7 9 8
  , .pair 8 4 10 9
  , .pair 9 10 11 10
  , .pair 5 2 12 11
  , .pair 11 12 0 12
  , .halt 0
  ]

@[simp] theorem supportedGateCompressionCountFrameProgram_oracleFree :
    OracleFree supportedGateCompressionCountFrameProgram := by
  rfl

def supportedGateCompressionCountFrameBits
    (thresholdCode weightsCode membershipCode selectedWeightsCode
      supportCount : ℕ) : ℕ :=
  max
    (natBitLength
      (supportedGateCompressionCountFrameInput thresholdCode weightsCode
        membershipCode selectedWeightsCode supportCount))
    (natBitLength
      (supportedGateCompressionCountFrameOutput thresholdCode weightsCode
        membershipCode selectedWeightsCode supportCount))

theorem run_supportedGateCompressionCountFrameProgram
    (inputLength thresholdCode weightsCode membershipCode selectedWeightsCode
      supportCount : ℕ) :
    runNPOracleProgram supportedGateCompressionCountFrameProgram
        (supportedGateCompressionCountFrameBits thresholdCode weightsCode
          membershipCode selectedWeightsCode supportCount)
        13
        (initialNPOracleState inputLength
          (supportedGateCompressionCountFrameInput thresholdCode weightsCode
            membershipCode selectedWeightsCode supportCount)) =
      some
        (supportedGateCompressionCountFrameOutput thresholdCode weightsCode
          membershipCode selectedWeightsCode supportCount) := by
  let compression :=
    supportedGateCompressionResult selectedWeightsCode supportCount
      membershipCode
  let fieldContext := Nat.pair weightsCode membershipCode
  let payload := Nat.pair thresholdCode fieldContext
  let originalRequest := Nat.pair 0 weightsCode
  let selectedRequest := Nat.pair 0 selectedWeightsCode
  let requests := Nat.pair originalRequest selectedRequest
  let compressedPayload := Nat.pair thresholdCode compression
  let input := Nat.pair compression payload
  let output := Nat.pair requests compressedPayload
  let maximumBits :=
    supportedGateCompressionCountFrameBits thresholdCode weightsCode
      membershipCode selectedWeightsCode supportCount
  have hinput : natBitLength input ≤ maximumBits :=
    Nat.le_max_left _ _
  have houtput : natBitLength output ≤ maximumBits :=
    Nat.le_max_right _ _
  have hcompression : natBitLength compression ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair compression payload)).trans hinput
  have hpayload : natBitLength payload ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair compression payload)).trans hinput
  have hselected : natBitLength selectedWeightsCode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair selectedWeightsCode
          (Nat.pair supportCount membershipCode))).trans hcompression
  have hthreshold : natBitLength thresholdCode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair thresholdCode fieldContext)).trans hpayload
  have hfieldContext : natBitLength fieldContext ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair thresholdCode fieldContext)).trans hpayload
  have hweights : natBitLength weightsCode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair weightsCode membershipCode)).trans hfieldContext
  have hzero : natBitLength 0 ≤ maximumBits := by
    exact (natBitLength_mono (Nat.zero_le input)).trans hinput
  have horiginal : natBitLength originalRequest ≤ maximumBits := by
    exact
      (natBitLength_mono
        ((Nat.left_le_pair originalRequest selectedRequest).trans
          (Nat.left_le_pair requests compressedPayload))).trans houtput
  have hselectedRequest :
      natBitLength selectedRequest ≤ maximumBits := by
    exact
      (natBitLength_mono
        ((Nat.right_le_pair originalRequest selectedRequest).trans
          (Nat.left_le_pair requests compressedPayload))).trans houtput
  have hrequests : natBitLength requests ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair requests compressedPayload)).trans houtput
  have hcompressedPayload :
      natBitLength compressedPayload ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair requests compressedPayload)).trans houtput
  rw [show (13 : ℕ) = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [supportedGateCompressionCountFrameInput, compression,
      supportedGateCompressionResult, supportedGateFieldPayload,
      initialNPOracleState]) hcompression]
  rw [show (12 : ℕ) = 11 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [supportedGateCompressionCountFrameInput, compression,
      payload, fieldContext, supportedGateCompressionResult,
      supportedGateFieldPayload,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpayload]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [compression, supportedGateCompressionResult,
      NPOracleState.write, NPOracleState.jump]) hselected]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [payload, NPOracleState.write, NPOracleState.jump]) hthreshold]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [payload, fieldContext, NPOracleState.write,
      NPOracleState.jump]) hfieldContext]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [fieldContext, NPOracleState.write, NPOracleState.jump])
    hweights]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_set_instruction (by rfl) rfl hzero]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [originalRequest, NPOracleState.write, NPOracleState.jump])
    horiginal]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [selectedRequest, NPOracleState.write, NPOracleState.jump])
    hselectedRequest]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [requests, NPOracleState.write, NPOracleState.jump]) hrequests]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [compressedPayload, compression, NPOracleState.write,
      NPOracleState.jump]) hcompressedPayload]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [output, NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      supportedGateCompressionCountFrameOutput, requests, originalRequest,
      selectedRequest, compressedPayload, compression,
      supportedGateCompressedPayload, supportedGateCompressionResult])
    houtput

def supportedGateCountEqualityInput
    (originalCount selectedCount compressedPayload : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair (Nat.pair originalCount 0) (Nat.pair selectedCount 0))
    compressedPayload

def supportedGateCountEqualityOutput
    (originalCount selectedCount compressedPayload : ℕ) : ℕ :=
  Nat.pair (nativeNatEqInput selectedCount originalCount) compressedPayload

def supportedGateCountEqualityProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairLeft 4 6 5
  , .unpairLeft 5 7 6
  , .pair 7 6 8 7
  , .pair 8 3 0 8
  , .halt 0
  ]

@[simp] theorem supportedGateCountEqualityProgram_oracleFree :
    OracleFree supportedGateCountEqualityProgram := by
  rfl

def supportedGateCountEqualityBits
    (originalCount selectedCount compressedPayload : ℕ) : ℕ :=
  max
    (natBitLength
      (supportedGateCountEqualityInput originalCount selectedCount
        compressedPayload))
    (natBitLength
      (supportedGateCountEqualityOutput originalCount selectedCount
        compressedPayload))

theorem run_supportedGateCountEqualityProgram
    (inputLength originalCount selectedCount compressedPayload : ℕ) :
    runNPOracleProgram supportedGateCountEqualityProgram
        (supportedGateCountEqualityBits originalCount selectedCount
          compressedPayload)
        9
        (initialNPOracleState inputLength
          (supportedGateCountEqualityInput originalCount selectedCount
            compressedPayload)) =
      some
        (supportedGateCountEqualityOutput originalCount selectedCount
          compressedPayload) := by
  let originalOutput := Nat.pair originalCount 0
  let selectedOutput := Nat.pair selectedCount 0
  let counts := Nat.pair originalOutput selectedOutput
  let request := nativeNatEqInput selectedCount originalCount
  let input := Nat.pair counts compressedPayload
  let output := Nat.pair request compressedPayload
  let maximumBits :=
    supportedGateCountEqualityBits originalCount selectedCount
      compressedPayload
  have hinput : natBitLength input ≤ maximumBits :=
    Nat.le_max_left _ _
  have houtput : natBitLength output ≤ maximumBits :=
    Nat.le_max_right _ _
  have hcounts : natBitLength counts ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair counts compressedPayload)).trans hinput
  have hpayload : natBitLength compressedPayload ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair counts compressedPayload)).trans hinput
  have horiginalOutput :
      natBitLength originalOutput ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair originalOutput selectedOutput)).trans hcounts
  have hselectedOutput :
      natBitLength selectedOutput ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair originalOutput selectedOutput)).trans hcounts
  have horiginal : natBitLength originalCount ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair originalCount 0)).trans horiginalOutput
  have hselected : natBitLength selectedCount ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair selectedCount 0)).trans hselectedOutput
  have hrequest : natBitLength request ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair request compressedPayload)).trans houtput
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [supportedGateCountEqualityInput, counts, originalOutput,
      selectedOutput, initialNPOracleState]) hcounts]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [supportedGateCountEqualityInput, counts, originalOutput,
      selectedOutput, initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]) hpayload]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [counts, NPOracleState.write, NPOracleState.jump])
    horiginalOutput]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [counts, NPOracleState.write, NPOracleState.jump])
    hselectedOutput]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [originalOutput, NPOracleState.write, NPOracleState.jump])
    horiginal]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [selectedOutput, NPOracleState.write, NPOracleState.jump])
    hselected]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [request, nativeNatEqInput, NPOracleState.write,
      NPOracleState.jump]) hrequest]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [output, NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      supportedGateCountEqualityOutput, request]) houtput

/-! ## Guarded zero-outside executable -/

def supportedGateZeroOutsideProgram : NPOracleProgram :=
  linkPrograms supportedGateFieldPairProgram <|
    linkPrograms
      (preserveRightProgram supplierSupportCompressionProgram) <|
      linkPrograms supportedGateCompressionCountFrameProgram <|
        linkPrograms
          (preserveRightProgram
            (pairedCallProgram balancedBoolCountProgram)) <|
          linkPrograms supportedGateCountEqualityProgram <|
            linkPrograms (preserveRightProgram nativeNatEqProgram) <|
              taggedProgramChoice rejectProgram acceptTaggedPayloadProgram

@[simp] theorem supportedGateZeroOutsideProgram_oracleFree :
    OracleFree supportedGateZeroOutsideProgram := by
  exact
    oracleFree_linkPrograms supportedGateFieldPairProgram_oracleFree <|
      oracleFree_linkPrograms
        (preserveRightProgram_oracleFree _
          supplierSupportCompressionProgram_oracleFree) <|
        oracleFree_linkPrograms
          supportedGateCompressionCountFrameProgram_oracleFree <|
          oracleFree_linkPrograms
            (preserveRightProgram_oracleFree _
              (pairedCallProgram_oracleFree _
                balancedBoolCountProgram_oracleFree)) <|
            oracleFree_linkPrograms
              supportedGateCountEqualityProgram_oracleFree <|
              oracleFree_linkPrograms
                (preserveRightProgram_oracleFree _
                  nativeNatEqProgram_oracleFree)
                (taggedProgramChoice_oracleFree _ _
                  rejectProgram_oracleFree
                  acceptTaggedPayloadProgram_oracleFree)

def supportedGateZeroOutsideOutput
    (thresholdCode : ℕ) (weightAtoms : List ℕ)
    (membership : List Bool) : ℕ :=
  let selected := supportedWeights weightAtoms membership
  let compressedPayload :=
    supportedGateCompressedPayload thresholdCode
      (encodeBalancedList selected)
      (nonzeroSupportCount membership)
      (encodeBoolList membership)
  if nonzeroAtomCount selected = nonzeroAtomCount weightAtoms then
    Nat.pair 1 compressedPayload
  else
    0

private def supportedGatePairedCountBits
    (inputLength : ℕ) (weightAtoms : List ℕ)
    (membership : List Bool) : ℕ :=
  let selected := supportedWeights weightAtoms membership
  pairedCallBits inputLength
    (balancedNonzeroCountBits inputLength 0 weightAtoms)
    (balancedNonzeroCountBits inputLength 0 selected)
    (Nat.pair 0 (encodeBalancedList weightAtoms))
    (Nat.pair 0 (encodeBalancedList selected))
    (Nat.pair (nonzeroAtomCount weightAtoms) 0)
    (Nat.pair (nonzeroAtomCount selected) 0)

private def supportedGateZeroOutsideStageBits
    (inputLength thresholdCode : ℕ) (weightAtoms : List ℕ)
    (membership : List Bool) : List ℕ :=
  let weightsCode := encodeBalancedList weightAtoms
  let membershipCode := encodeBoolList membership
  let payload :=
    supportedGateFieldPayload thresholdCode weightsCode membershipCode
  let compression :=
    supplierSupportCompressionOutput weightAtoms membership
  let selected := supportedWeights weightAtoms membership
  let selectedCode := encodeBalancedList selected
  let supportCount := nonzeroSupportCount membership
  let compressedPayload :=
    supportedGateCompressedPayload thresholdCode selectedCode supportCount
      membershipCode
  let originalCount := nonzeroAtomCount weightAtoms
  let selectedCount := nonzeroAtomCount selected
  let countsOutput :=
    Nat.pair (Nat.pair originalCount 0) (Nat.pair selectedCount 0)
  let equalityFlag := nativeNatEqOutput selectedCount originalCount
  let pairedCountBits :=
    supportedGatePairedCountBits inputLength weightAtoms membership
  [ natBitLength inputLength
  , supportedGateFieldPairBits thresholdCode weightsCode membershipCode
  , preserveRightBits
      (supplierSupportCompressionBits inputLength weightAtoms membership)
      (Nat.pair weightsCode membershipCode) payload compression
  , supportedGateCompressionCountFrameBits thresholdCode weightsCode
      membershipCode selectedCode supportCount
  , preserveRightBits pairedCountBits
      (Nat.pair (Nat.pair 0 weightsCode) (Nat.pair 0 selectedCode))
      compressedPayload countsOutput
  , supportedGateCountEqualityBits originalCount selectedCount
      compressedPayload
  , preserveRightBits
      (nativeNatEqBits inputLength selectedCount originalCount)
      (nativeNatEqInput selectedCount originalCount)
      compressedPayload equalityFlag
  , natBitLength
      (Nat.pair inputLength (Nat.pair equalityFlag compressedPayload))
  , natBitLength 0
  , acceptTaggedPayloadBits compressedPayload
  ]

def supportedGateZeroOutsideBits
    (inputLength thresholdCode : ℕ) (weightAtoms : List ℕ)
    (membership : List Bool) : ℕ :=
  max 1 <|
    (supportedGateZeroOutsideStageBits inputLength thresholdCode weightAtoms
      membership).foldr max 0

private theorem relation_le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hvalue
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at hvalue
      simp only [List.foldr]
      rcases hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact
          (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

private theorem supportedGateZeroOutsideBits_of_mem
    {inputLength thresholdCode value : ℕ}
    {weightAtoms : List ℕ} {membership : List Bool}
    (hvalue :
      value ∈
        supportedGateZeroOutsideStageBits inputLength thresholdCode weightAtoms
          membership) :
    value ≤
      supportedGateZeroOutsideBits inputLength thresholdCode weightAtoms
        membership := by
  exact
    (relation_le_foldr_max_of_mem hvalue).trans
      (Nat.le_max_right _ _)

def supportedGateZeroOutsideFuel
    (weightAtoms : List ℕ) (membership : List Bool) : ℕ :=
  let selected := supportedWeights weightAtoms membership
  let compressionFuel :=
    preserveRightFuel
      (supplierSupportCompressionFuel weightAtoms membership)
  let countFuel :=
    preserveRightFuel <|
      pairedCallFuel balancedBoolCountProgram
        (balancedNonzeroCountFuel weightAtoms)
        (balancedNonzeroCountFuel selected)
  let equalityFuel :=
    preserveRightFuel
      (nativeNatEqFuel
        (nonzeroAtomCount selected)
        (nonzeroAtomCount weightAtoms))
  let choiceFuel := taggedProgramChoiceFuel 3
  linkFuel
    (linkPrograms
      (preserveRightProgram supplierSupportCompressionProgram) <|
      linkPrograms supportedGateCompressionCountFrameProgram <|
        linkPrograms
          (preserveRightProgram
            (pairedCallProgram balancedBoolCountProgram)) <|
          linkPrograms supportedGateCountEqualityProgram <|
            linkPrograms (preserveRightProgram nativeNatEqProgram) <|
              taggedProgramChoice rejectProgram
                acceptTaggedPayloadProgram)
    3 <|
    linkFuel
      (linkPrograms supportedGateCompressionCountFrameProgram <|
        linkPrograms
          (preserveRightProgram
            (pairedCallProgram balancedBoolCountProgram)) <|
          linkPrograms supportedGateCountEqualityProgram <|
            linkPrograms (preserveRightProgram nativeNatEqProgram) <|
              taggedProgramChoice rejectProgram
                acceptTaggedPayloadProgram)
      compressionFuel <|
      linkFuel
        (linkPrograms
          (preserveRightProgram
            (pairedCallProgram balancedBoolCountProgram)) <|
          linkPrograms supportedGateCountEqualityProgram <|
            linkPrograms (preserveRightProgram nativeNatEqProgram) <|
              taggedProgramChoice rejectProgram
                acceptTaggedPayloadProgram)
        13 <|
        linkFuel
          (linkPrograms supportedGateCountEqualityProgram <|
            linkPrograms (preserveRightProgram nativeNatEqProgram) <|
              taggedProgramChoice rejectProgram
                acceptTaggedPayloadProgram)
          countFuel <|
          linkFuel
            (linkPrograms (preserveRightProgram nativeNatEqProgram) <|
              taggedProgramChoice rejectProgram
                acceptTaggedPayloadProgram)
            9 <|
            linkFuel
              (taggedProgramChoice rejectProgram
                acceptTaggedPayloadProgram)
              equalityFuel choiceFuel

theorem run_supportedGateZeroOutsideProgram
    (inputLength thresholdCode : ℕ) (weightAtoms : List ℕ)
    (membership : List Bool)
    (hinputLength : inputLength = weightAtoms.length)
    (hlength : weightAtoms.length = membership.length) :
    runNPOracleProgram supportedGateZeroOutsideProgram
        (supportedGateZeroOutsideBits inputLength thresholdCode weightAtoms
          membership)
        (supportedGateZeroOutsideFuel weightAtoms membership)
        (initialNPOracleState inputLength
          (supportedGateFieldPayload thresholdCode
            (encodeBalancedList weightAtoms)
            (encodeBoolList membership))) =
      some
        (supportedGateZeroOutsideOutput thresholdCode weightAtoms
          membership) := by
  let weightsCode := encodeBalancedList weightAtoms
  let membershipCode := encodeBoolList membership
  let payload :=
    supportedGateFieldPayload thresholdCode weightsCode membershipCode
  let compression :=
    supplierSupportCompressionOutput weightAtoms membership
  let selected := supportedWeights weightAtoms membership
  let selectedCode := encodeBalancedList selected
  let supportCount := nonzeroSupportCount membership
  let compressedPayload :=
    supportedGateCompressedPayload thresholdCode selectedCode supportCount
      membershipCode
  let originalCount := nonzeroAtomCount weightAtoms
  let selectedCount := nonzeroAtomCount selected
  let originalOutput := Nat.pair originalCount 0
  let selectedOutput := Nat.pair selectedCount 0
  let countsOutput := Nat.pair originalOutput selectedOutput
  let equalityFlag := nativeNatEqOutput selectedCount originalCount
  let pairedCountBits :=
    supportedGatePairedCountBits inputLength weightAtoms membership
  let pairedCountFuel :=
    pairedCallFuel balancedBoolCountProgram
      (balancedNonzeroCountFuel weightAtoms)
      (balancedNonzeroCountFuel selected)
  let maximumBits :=
    supportedGateZeroOutsideBits inputLength thresholdCode weightAtoms
      membership
  have hpositive : 1 ≤ maximumBits := by
    dsimp only [maximumBits, supportedGateZeroOutsideBits]
    exact Nat.le_max_left _ _
  have hfieldBits :
      supportedGateFieldPairBits thresholdCode weightsCode membershipCode ≤
        maximumBits := by
    apply supportedGateZeroOutsideBits_of_mem
    simp [supportedGateZeroOutsideStageBits, weightsCode, membershipCode]
  have hcompressionBits :
      preserveRightBits
          (supplierSupportCompressionBits inputLength weightAtoms membership)
          (Nat.pair weightsCode membershipCode) payload compression ≤
        maximumBits := by
    apply supportedGateZeroOutsideBits_of_mem
    simp [supportedGateZeroOutsideStageBits, weightsCode, membershipCode,
      payload, compression]
  have hlengthBits : natBitLength inputLength ≤ maximumBits := by
    apply supportedGateZeroOutsideBits_of_mem
    simp [supportedGateZeroOutsideStageBits]
  have hframeBits :
      supportedGateCompressionCountFrameBits thresholdCode weightsCode
          membershipCode selectedCode supportCount ≤ maximumBits := by
    apply supportedGateZeroOutsideBits_of_mem
    simp [supportedGateZeroOutsideStageBits, weightsCode, membershipCode,
      selected, selectedCode, supportCount]
  have hcountBits :
      preserveRightBits pairedCountBits
          (Nat.pair (Nat.pair 0 weightsCode) (Nat.pair 0 selectedCode))
          compressedPayload countsOutput ≤ maximumBits := by
    apply supportedGateZeroOutsideBits_of_mem
    simp [supportedGateZeroOutsideStageBits, weightsCode, membershipCode,
      selected, selectedCode, supportCount, compressedPayload,
      originalCount, selectedCount, originalOutput, selectedOutput,
      countsOutput, pairedCountBits]
  have hcountFrameBits :
      supportedGateCountEqualityBits originalCount selectedCount
          compressedPayload ≤ maximumBits := by
    apply supportedGateZeroOutsideBits_of_mem
    simp [supportedGateZeroOutsideStageBits, membershipCode, selected,
      selectedCode, supportCount, compressedPayload, originalCount,
      selectedCount]
  have hequalityBits :
      preserveRightBits
          (nativeNatEqBits inputLength selectedCount originalCount)
          (nativeNatEqInput selectedCount originalCount)
          compressedPayload equalityFlag ≤ maximumBits := by
    apply supportedGateZeroOutsideBits_of_mem
    simp [supportedGateZeroOutsideStageBits, membershipCode, selected,
      selectedCode, supportCount, compressedPayload, originalCount,
      selectedCount, equalityFlag]
  have hchoiceInput :
      natBitLength
          (Nat.pair inputLength
            (Nat.pair equalityFlag compressedPayload)) ≤ maximumBits := by
    apply supportedGateZeroOutsideBits_of_mem
    simp [supportedGateZeroOutsideStageBits, membershipCode, selected,
      selectedCode, supportCount, compressedPayload, originalCount,
      selectedCount, equalityFlag]
  have hrejectOutput : natBitLength 0 ≤ maximumBits := by
    apply supportedGateZeroOutsideBits_of_mem
    simp [supportedGateZeroOutsideStageBits]
  have hacceptBits :
      acceptTaggedPayloadBits compressedPayload ≤ maximumBits := by
    apply supportedGateZeroOutsideBits_of_mem
    simp [supportedGateZeroOutsideStageBits, membershipCode, selected,
      selectedCode, supportCount, compressedPayload]
  have hacceptOutput :
      natBitLength (Nat.pair 1 compressedPayload) ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans hacceptBits
  have hfield :
      runNPOracleProgram supportedGateFieldPairProgram maximumBits 3
          (initialNPOracleState inputLength payload) =
        some (Nat.pair (Nat.pair weightsCode membershipCode) payload) := by
    have hrun :=
      run_bits_mono
        (run_supportedGateFieldPairProgram inputLength thresholdCode
          weightsCode membershipCode)
        hfieldBits
    simpa [supportedGateFieldPairOutput, payload] using hrun
  have hcompressionSource :
      runNPOracleProgram supplierSupportCompressionProgram
          (supplierSupportCompressionBits inputLength weightAtoms membership)
          (supplierSupportCompressionFuel weightAtoms membership)
          (initialNPOracleState inputLength
            (Nat.pair weightsCode membershipCode)) =
        some compression := by
    simpa [weightsCode, membershipCode, compression] using
      run_supplierSupportCompressionProgram inputLength weightAtoms
        membership hinputLength hlength
  have hcompressionPreserved :
      runNPOracleProgram
          (preserveRightProgram supplierSupportCompressionProgram)
          maximumBits
          (preserveRightFuel
            (supplierSupportCompressionFuel weightAtoms membership))
          (initialNPOracleState inputLength
            (Nat.pair (Nat.pair weightsCode membershipCode) payload)) =
        some (Nat.pair compression payload) := by
    exact run_bits_mono
      (run_preserveRightProgram supplierSupportCompressionProgram
        inputLength
        (supplierSupportCompressionBits inputLength weightAtoms membership)
        (supplierSupportCompressionFuel weightAtoms membership)
        (Nat.pair weightsCode membershipCode) payload compression
        hcompressionSource)
      hcompressionBits
  have hframe :
      runNPOracleProgram supportedGateCompressionCountFrameProgram
          maximumBits 13
          (initialNPOracleState inputLength (Nat.pair compression payload)) =
        some
          (Nat.pair
            (Nat.pair (Nat.pair 0 weightsCode)
              (Nat.pair 0 selectedCode))
            compressedPayload) := by
    have hrun :=
      run_bits_mono
        (run_supportedGateCompressionCountFrameProgram inputLength
          thresholdCode weightsCode membershipCode selectedCode supportCount)
        hframeBits
    simpa [compression, supplierSupportCompressionOutput, selectedCode,
      supportCount, payload, supportedGateCompressionCountFrameInput,
      supportedGateCompressionResult,
      supportedGateCompressionCountFrameOutput, compressedPayload] using hrun
  have hpairedCounts :
      runNPOracleProgram (pairedCallProgram balancedBoolCountProgram)
          pairedCountBits pairedCountFuel
          (initialNPOracleState inputLength
            (Nat.pair (Nat.pair 0 weightsCode)
              (Nat.pair 0 selectedCode))) =
        some countsOutput := by
    have hrun :=
      run_pairedCallProgram balancedBoolCountProgram inputLength
        (balancedNonzeroCountBits inputLength 0 weightAtoms)
        (balancedNonzeroCountBits inputLength 0 selected)
        (balancedNonzeroCountFuel weightAtoms)
        (balancedNonzeroCountFuel selected)
        (Nat.pair 0 weightsCode) (Nat.pair 0 selectedCode)
        originalOutput selectedOutput
        (by simpa [weightsCode, originalOutput, originalCount,
            balancedNonzeroCountOutput] using
          run_balancedNonzeroCountProgram inputLength 0 weightAtoms)
        (by simpa [selectedCode, selectedOutput, selectedCount,
            balancedNonzeroCountOutput] using
          run_balancedNonzeroCountProgram inputLength 0 selected)
    simpa [pairedCountBits, supportedGatePairedCountBits,
      pairedCountFuel, countsOutput] using hrun
  have hcountsPreserved :
      runNPOracleProgram
          (preserveRightProgram
            (pairedCallProgram balancedBoolCountProgram))
          maximumBits (preserveRightFuel pairedCountFuel)
          (initialNPOracleState inputLength
            (Nat.pair
              (Nat.pair (Nat.pair 0 weightsCode)
                (Nat.pair 0 selectedCode))
              compressedPayload)) =
        some (Nat.pair countsOutput compressedPayload) := by
    exact run_bits_mono
      (run_preserveRightProgram
        (pairedCallProgram balancedBoolCountProgram)
        inputLength pairedCountBits pairedCountFuel
        (Nat.pair (Nat.pair 0 weightsCode) (Nat.pair 0 selectedCode))
        compressedPayload countsOutput hpairedCounts)
      hcountBits
  have hcountFrame :
      runNPOracleProgram supportedGateCountEqualityProgram maximumBits 9
          (initialNPOracleState inputLength
            (Nat.pair countsOutput compressedPayload)) =
        some
          (Nat.pair (nativeNatEqInput selectedCount originalCount)
            compressedPayload) := by
    have hrun :=
      run_bits_mono
        (run_supportedGateCountEqualityProgram inputLength originalCount
          selectedCount compressedPayload)
        hcountFrameBits
    simpa [supportedGateCountEqualityInput, countsOutput, originalOutput,
      selectedOutput, supportedGateCountEqualityOutput] using hrun
  have hequalitySource :
      runNPOracleProgram nativeNatEqProgram
          (nativeNatEqBits inputLength selectedCount originalCount)
          (nativeNatEqFuel selectedCount originalCount)
          (initialNPOracleState inputLength
            (nativeNatEqInput selectedCount originalCount)) =
        some equalityFlag := by
    simpa [equalityFlag] using
      run_nativeNatEqProgram inputLength selectedCount originalCount
  have hequalityPreserved :
      runNPOracleProgram (preserveRightProgram nativeNatEqProgram)
          maximumBits
          (preserveRightFuel
            (nativeNatEqFuel selectedCount originalCount))
          (initialNPOracleState inputLength
            (Nat.pair (nativeNatEqInput selectedCount originalCount)
              compressedPayload)) =
        some (Nat.pair equalityFlag compressedPayload) := by
    exact run_bits_mono
      (run_preserveRightProgram nativeNatEqProgram inputLength
        (nativeNatEqBits inputLength selectedCount originalCount)
        (nativeNatEqFuel selectedCount originalCount)
        (nativeNatEqInput selectedCount originalCount)
        compressedPayload equalityFlag hequalitySource)
      hequalityBits
  have hchoice :
      runNPOracleProgram
          (taggedProgramChoice rejectProgram acceptTaggedPayloadProgram)
          maximumBits (taggedProgramChoiceFuel 3)
          (initialNPOracleState inputLength
            (Nat.pair equalityFlag compressedPayload)) =
        some
          (if selectedCount = originalCount then
            Nat.pair 1 compressedPayload
          else
            0) := by
    by_cases hequal : selectedCount = originalCount
    · have hflag : equalityFlag = 1 := by
        simp [equalityFlag, nativeNatEqOutput, hequal]
      have hsource :
          runNPOracleProgram acceptTaggedPayloadProgram maximumBits 3
              (initialNPOracleState inputLength compressedPayload) =
            some (Nat.pair 1 compressedPayload) :=
        run_bits_mono
          (run_acceptTaggedPayloadProgram inputLength compressedPayload)
          hacceptBits
      simpa [hequal, hflag] using
        run_taggedProgramChoice_nonzero rejectProgram
          acceptTaggedPayloadProgram inputLength 1 compressedPayload
          maximumBits 3 (Nat.pair 1 compressedPayload)
          (by omega) (by simpa [hflag] using hchoiceInput)
          hsource hacceptOutput
    · have hflag : equalityFlag = 0 := by
        simp [equalityFlag, nativeNatEqOutput, hequal]
      have hsource :
          runNPOracleProgram rejectProgram maximumBits 3
              (initialNPOracleState inputLength compressedPayload) =
            some 0 := by
        simpa using
          run_rejectProgram inputLength compressedPayload maximumBits 1
            hrejectOutput
      simpa [hequal, hflag] using
        run_taggedProgramChoice_zero rejectProgram
          acceptTaggedPayloadProgram inputLength compressedPayload
          maximumBits 3 0
          (by simpa [hflag] using hchoiceInput)
          hsource hrejectOutput
  have hequalityTail :=
    run_linkPrograms hpositive hlengthBits hequalityPreserved hchoice
  have hcountFrameTail :=
    run_linkPrograms hpositive hlengthBits hcountFrame hequalityTail
  have hcountsTail :=
    run_linkPrograms hpositive hlengthBits hcountsPreserved hcountFrameTail
  have hframeTail :=
    run_linkPrograms hpositive hlengthBits hframe hcountsTail
  have hcompressionTail :=
    run_linkPrograms hpositive hlengthBits hcompressionPreserved hframeTail
  have hrun :=
    run_linkPrograms hpositive hlengthBits hfield hcompressionTail
  simpa [supportedGateZeroOutsideProgram, supportedGateZeroOutsideFuel,
    supportedGateZeroOutsideOutput, weightsCode, membershipCode, payload,
    compression, selected, selectedCode, supportCount, compressedPayload,
    originalCount, selectedCount, equalityFlag, pairedCountFuel] using hrun

/-! ## Length-guarded relation -/

def supportedGateValidFieldProgram : NPOracleProgram :=
  linkPrograms supportedGateLengthValidationProgram <|
    taggedProgramChoice rejectProgram supportedGateZeroOutsideProgram

@[simp] theorem supportedGateValidFieldProgram_oracleFree :
    OracleFree supportedGateValidFieldProgram := by
  exact
    oracleFree_linkPrograms supportedGateLengthValidationProgram_oracleFree <|
      taggedProgramChoice_oracleFree _ _
        rejectProgram_oracleFree
        supportedGateZeroOutsideProgram_oracleFree

def supportedGateValidFieldOutput
    (inputLength thresholdCode : ℕ) (weightAtoms : List ℕ)
    (membership : List Bool) : ℕ :=
  if weightAtoms.length = inputLength ∧ membership.length = inputLength then
    supportedGateZeroOutsideOutput thresholdCode weightAtoms membership
  else
    0

private def supportedGateValidFieldStageBits
    (inputLength thresholdCode : ℕ) (weightAtoms : List ℕ)
    (membership : List Bool) : List ℕ :=
  let membershipAtoms := membership.map boolCode
  let payload :=
    supportedGateFieldPayload thresholdCode
      (encodeBalancedList weightAtoms) (encodeBoolList membership)
  let flag :=
    nativeNatEqOutput
      (Nat.pair weightAtoms.length membershipAtoms.length)
      (Nat.pair inputLength inputLength)
  [ natBitLength inputLength
  , supportedGateLengthValidationBits inputLength thresholdCode
      weightAtoms membershipAtoms
  , supportedGateZeroOutsideBits inputLength thresholdCode weightAtoms
      membership
  , natBitLength (Nat.pair inputLength (Nat.pair flag payload))
  , natBitLength 0
  , natBitLength
      (supportedGateZeroOutsideOutput thresholdCode weightAtoms membership)
  ]

def supportedGateValidFieldBits
    (inputLength thresholdCode : ℕ) (weightAtoms : List ℕ)
    (membership : List Bool) : ℕ :=
  max 1 <|
    (supportedGateValidFieldStageBits inputLength thresholdCode weightAtoms
      membership).foldr max 0

private theorem supportedGateValidFieldBits_of_mem
    {inputLength thresholdCode value : ℕ}
    {weightAtoms : List ℕ} {membership : List Bool}
    (hvalue :
      value ∈
        supportedGateValidFieldStageBits inputLength thresholdCode weightAtoms
          membership) :
    value ≤
      supportedGateValidFieldBits inputLength thresholdCode weightAtoms
        membership := by
  exact
    (relation_le_foldr_max_of_mem hvalue).trans
      (Nat.le_max_right _ _)

def supportedGateValidFieldFuel
    (inputLength : ℕ) (weightAtoms : List ℕ)
    (membership : List Bool) : ℕ :=
  let relationFuel :=
    if weightAtoms.length = inputLength ∧ membership.length = inputLength then
      supportedGateZeroOutsideFuel weightAtoms membership
    else
      2
  linkFuel
    (taggedProgramChoice rejectProgram supportedGateZeroOutsideProgram)
    (supportedGateLengthValidationFuel inputLength weightAtoms
      (membership.map boolCode))
    (taggedProgramChoiceFuel relationFuel)

theorem run_supportedGateValidFieldProgram
    (inputLength thresholdCode : ℕ) (weightAtoms : List ℕ)
    (membership : List Bool) :
    runNPOracleProgram supportedGateValidFieldProgram
        (supportedGateValidFieldBits inputLength thresholdCode weightAtoms
          membership)
        (supportedGateValidFieldFuel inputLength weightAtoms membership)
        (initialNPOracleState inputLength
          (supportedGateFieldPayload thresholdCode
            (encodeBalancedList weightAtoms)
            (encodeBoolList membership))) =
      some
        (supportedGateValidFieldOutput inputLength thresholdCode weightAtoms
          membership) := by
  let membershipAtoms := membership.map boolCode
  let payload :=
    supportedGateFieldPayload thresholdCode
      (encodeBalancedList weightAtoms) (encodeBoolList membership)
  let lengths := Nat.pair weightAtoms.length membershipAtoms.length
  let arities := Nat.pair inputLength inputLength
  let flag := nativeNatEqOutput lengths arities
  let maximumBits :=
    supportedGateValidFieldBits inputLength thresholdCode weightAtoms
      membership
  have hpositive : 1 ≤ maximumBits := by
    dsimp only [maximumBits, supportedGateValidFieldBits]
    exact Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits := by
    apply supportedGateValidFieldBits_of_mem
    simp [supportedGateValidFieldStageBits]
  have hvalidationBits :
      supportedGateLengthValidationBits inputLength thresholdCode
          weightAtoms membershipAtoms ≤ maximumBits := by
    apply supportedGateValidFieldBits_of_mem
    simp [supportedGateValidFieldStageBits, membershipAtoms]
  have hrelationBits :
      supportedGateZeroOutsideBits inputLength thresholdCode weightAtoms
          membership ≤ maximumBits := by
    apply supportedGateValidFieldBits_of_mem
    simp [supportedGateValidFieldStageBits]
  have hchoiceInput :
      natBitLength (Nat.pair inputLength (Nat.pair flag payload)) ≤
        maximumBits := by
    apply supportedGateValidFieldBits_of_mem
    simp [supportedGateValidFieldStageBits, membershipAtoms, payload,
      lengths, arities, flag]
  have hzero : natBitLength 0 ≤ maximumBits := by
    apply supportedGateValidFieldBits_of_mem
    simp [supportedGateValidFieldStageBits]
  have hrelationOutput :
      natBitLength
          (supportedGateZeroOutsideOutput thresholdCode weightAtoms
            membership) ≤ maximumBits := by
    apply supportedGateValidFieldBits_of_mem
    simp [supportedGateValidFieldStageBits]
  have hvalidation :
      runNPOracleProgram supportedGateLengthValidationProgram maximumBits
          (supportedGateLengthValidationFuel inputLength weightAtoms
            membershipAtoms)
          (initialNPOracleState inputLength payload) =
        some (Nat.pair flag payload) := by
    have hrun :=
      run_bits_mono
        (run_supportedGateLengthValidationProgram inputLength thresholdCode
          weightAtoms membershipAtoms)
        hvalidationBits
    simpa [membershipAtoms, payload, lengths, arities, flag,
      supportedGateLengthValidationOutput, encodeBoolList] using hrun
  have hchoice :
      runNPOracleProgram
          (taggedProgramChoice rejectProgram
            supportedGateZeroOutsideProgram)
          maximumBits
          (taggedProgramChoiceFuel <|
            if weightAtoms.length = inputLength ∧
                membership.length = inputLength then
              supportedGateZeroOutsideFuel weightAtoms membership
            else
              2)
          (initialNPOracleState inputLength (Nat.pair flag payload)) =
        some
          (supportedGateValidFieldOutput inputLength thresholdCode
            weightAtoms membership) := by
    by_cases hdimensions :
        weightAtoms.length = inputLength ∧
          membership.length = inputLength
    · have hlengths : lengths = arities := by
        simp [lengths, arities, membershipAtoms, hdimensions]
      have hflag : flag = 1 := by
        simp [flag, nativeNatEqOutput, hlengths]
      have hsource :
          runNPOracleProgram supportedGateZeroOutsideProgram maximumBits
              (supportedGateZeroOutsideFuel weightAtoms membership)
              (initialNPOracleState inputLength payload) =
            some
              (supportedGateZeroOutsideOutput thresholdCode weightAtoms
                membership) := by
        have hrun :=
          run_bits_mono
            (run_supportedGateZeroOutsideProgram inputLength thresholdCode
              weightAtoms membership hdimensions.1.symm
              (hdimensions.1.trans hdimensions.2.symm))
            hrelationBits
        simpa [payload] using hrun
      simpa [supportedGateValidFieldOutput, hdimensions, hflag] using
        run_taggedProgramChoice_nonzero rejectProgram
          supportedGateZeroOutsideProgram inputLength 1 payload maximumBits
          (supportedGateZeroOutsideFuel weightAtoms membership)
          (supportedGateZeroOutsideOutput thresholdCode weightAtoms membership)
          (by omega) (by simpa [hflag] using hchoiceInput)
          hsource hrelationOutput
    · have hlengths : lengths ≠ arities := by
        intro hequal
        have hpairs := Nat.pair_eq_pair.mp hequal
        apply hdimensions
        simpa [lengths, arities, membershipAtoms] using hpairs
      have hflag : flag = 0 := by
        simp [flag, nativeNatEqOutput, hlengths]
      have hsource :
          runNPOracleProgram rejectProgram maximumBits 2
              (initialNPOracleState inputLength payload) =
            some 0 := by
        simpa using
          run_rejectProgram inputLength payload maximumBits 0 hzero
      simpa [supportedGateValidFieldOutput, hdimensions, hflag] using
        run_taggedProgramChoice_zero rejectProgram
          supportedGateZeroOutsideProgram inputLength payload maximumBits
          2 0 (by simpa [hflag] using hchoiceInput) hsource hzero
  have hrun :=
    run_linkPrograms hpositive hlengthBits hvalidation hchoice
  simpa [supportedGateValidFieldProgram, supportedGateValidFieldFuel,
    membershipAtoms, payload] using hrun

/-! ## Total raw-code relation validator -/

def decodeSupportedGateRelationLists
    (raw : ℕ) : Option (List ℤ × List Bool) := do
  let weights ← decodeIntList (supportedGateWeightsCode raw)
  let membership ← decodeBoolList (supportedGateMembershipCode raw)
  pure (weights, membership)

theorem supportedGateFieldValidationOutput_eq_payload_of_ne_zero
    (inputLength raw : ℕ)
    (hnonzero : supportedGateFieldValidationOutput inputLength raw ≠ 0) :
    supportedGateFieldValidationOutput inputLength raw =
      Nat.pair 1
        (supportedGateFieldPayload
          (supportedGateThresholdCode raw)
          (supportedGateWeightsCode raw)
          (supportedGateMembershipCode raw)) := by
  unfold supportedGateFieldValidationOutput at hnonzero ⊢
  split
  · simp_all
  · split
    · simp_all
    · split
      · simp_all
      · split
        · simp_all
        · rfl

def supportedGateRelationProgram : NPOracleProgram :=
  linkPrograms supportedGateFieldValidationProgram <|
    taggedProgramChoice rejectProgram supportedGateValidFieldProgram

@[simp] theorem supportedGateRelationProgram_oracleFree :
    OracleFree supportedGateRelationProgram := by
  exact
    oracleFree_linkPrograms supportedGateFieldValidationProgram_oracleFree <|
      taggedProgramChoice_oracleFree _ _
        rejectProgram_oracleFree
        supportedGateValidFieldProgram_oracleFree

def supportedGateRelationOutput (inputLength raw : ℕ) : ℕ :=
  if supportedGateFieldValidationOutput inputLength raw = 0 then
    0
  else
    match decodeSupportedGateRelationLists raw with
    | some (weights, membership) =>
        supportedGateValidFieldOutput inputLength
          (supportedGateThresholdCode raw)
          (weights.map encodeInt) membership
    | none => 0

private def supportedGateRelationStageBits
    (inputLength raw : ℕ) : List ℕ :=
  let fieldOutput := supportedGateFieldValidationOutput inputLength raw
  let decoded := decodeSupportedGateRelationLists raw
  let validBits :=
    match decoded with
    | some (weights, membership) =>
        supportedGateValidFieldBits inputLength
          (supportedGateThresholdCode raw)
          (weights.map encodeInt) membership
    | none => 1
  [ natBitLength inputLength
  , supportedGateFieldValidationBits inputLength raw
  , natBitLength (Nat.pair inputLength fieldOutput)
  , validBits
  , natBitLength 0
  , natBitLength (supportedGateRelationOutput inputLength raw)
  ]

def supportedGateRelationBits (inputLength raw : ℕ) : ℕ :=
  max 1 <|
    (supportedGateRelationStageBits inputLength raw).foldr max 0

private theorem supportedGateRelationBits_of_mem
    {inputLength raw value : ℕ}
    (hvalue :
      value ∈ supportedGateRelationStageBits inputLength raw) :
    value ≤ supportedGateRelationBits inputLength raw := by
  exact
    (relation_le_foldr_max_of_mem hvalue).trans
      (Nat.le_max_right _ _)

private def supportedGateRelationSourceFuel
    (inputLength raw : ℕ) : ℕ :=
  if supportedGateFieldValidationOutput inputLength raw = 0 then
    2
  else
    match decodeSupportedGateRelationLists raw with
    | some (weights, membership) =>
        supportedGateValidFieldFuel inputLength
          (weights.map encodeInt) membership
    | none => 2

def supportedGateRelationFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel
    (taggedProgramChoice rejectProgram supportedGateValidFieldProgram)
    (supportedGateFieldValidationFuel inputLength raw)
    (taggedProgramChoiceFuel <|
      supportedGateRelationSourceFuel inputLength raw)

theorem run_supportedGateRelationProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram supportedGateRelationProgram
        (supportedGateRelationBits inputLength raw)
        (supportedGateRelationFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (supportedGateRelationOutput inputLength raw) := by
  let fieldOutput := supportedGateFieldValidationOutput inputLength raw
  let maximumBits := supportedGateRelationBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    dsimp only [maximumBits, supportedGateRelationBits]
    exact Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits := by
    apply supportedGateRelationBits_of_mem
    simp [supportedGateRelationStageBits]
  have hfieldBits :
      supportedGateFieldValidationBits inputLength raw ≤ maximumBits := by
    apply supportedGateRelationBits_of_mem
    simp [supportedGateRelationStageBits]
  have hchoiceInput :
      natBitLength (Nat.pair inputLength fieldOutput) ≤ maximumBits := by
    apply supportedGateRelationBits_of_mem
    simp [supportedGateRelationStageBits, fieldOutput]
  have hzero : natBitLength 0 ≤ maximumBits := by
    apply supportedGateRelationBits_of_mem
    simp [supportedGateRelationStageBits]
  have houtput :
      natBitLength (supportedGateRelationOutput inputLength raw) ≤
        maximumBits := by
    apply supportedGateRelationBits_of_mem
    simp [supportedGateRelationStageBits]
  have hfield :
      runNPOracleProgram supportedGateFieldValidationProgram maximumBits
          (supportedGateFieldValidationFuel inputLength raw)
          (initialNPOracleState inputLength raw) =
        some fieldOutput := by
    exact run_bits_mono
      (run_supportedGateFieldValidationProgram inputLength raw)
      hfieldBits
  have hchoice :
      runNPOracleProgram
          (taggedProgramChoice rejectProgram supportedGateValidFieldProgram)
          maximumBits
          (taggedProgramChoiceFuel <|
            supportedGateRelationSourceFuel inputLength raw)
          (initialNPOracleState inputLength fieldOutput) =
        some (supportedGateRelationOutput inputLength raw) := by
    by_cases hfieldZero : fieldOutput = 0
    · have hfieldActual :
          supportedGateFieldValidationOutput inputLength raw = 0 := by
        simpa [fieldOutput] using hfieldZero
      have hpairZero : Nat.pair 0 0 = 0 := by
        rfl
      have hsource :
          runNPOracleProgram rejectProgram maximumBits 2
              (initialNPOracleState inputLength 0) =
            some 0 := by
        simpa using run_rejectProgram inputLength 0 maximumBits 0 hzero
      have hinput :
          natBitLength (Nat.pair inputLength (Nat.pair 0 0)) ≤
            maximumBits := by
        simpa only [hpairZero, hfieldZero] using hchoiceInput
      have hchoiceZero :=
        run_taggedProgramChoice_zero rejectProgram
          supportedGateValidFieldProgram inputLength 0 maximumBits 2 0
          hinput hsource hzero
      have hchoiceAtZero :
          runNPOracleProgram
              (taggedProgramChoice rejectProgram
                supportedGateValidFieldProgram)
              maximumBits (taggedProgramChoiceFuel 2)
              (initialNPOracleState inputLength 0) =
            some 0 := by
        simpa only [hpairZero] using hchoiceZero
      unfold supportedGateRelationSourceFuel supportedGateRelationOutput
      rw [if_pos hfieldActual, if_pos hfieldActual, hfieldZero]
      exact hchoiceAtZero
    · obtain ⟨weightsCode, thresholdCode, membershipCode, htuple,
        hweightsSome, _hthresholdSome, hmembershipSome⟩ :=
        (supportedGateFieldValidationOutput_ne_zero_iff
          inputLength raw).1 hfieldZero
      have hcodes := supportedGateCodes_of_decode htuple
      have hweightsAccessor :
          (decodeIntList (supportedGateWeightsCode raw)).isSome := by
        exact hcodes.1.symm ▸ hweightsSome
      have hmembershipAccessor :
          (decodeBoolList (supportedGateMembershipCode raw)).isSome := by
        exact hcodes.2.2.symm ▸ hmembershipSome
      cases hweights :
          decodeIntList (supportedGateWeightsCode raw) with
      | none => simp [hweights] at hweightsAccessor
      | some weights =>
          cases hmembership :
              decodeBoolList (supportedGateMembershipCode raw) with
          | none => simp [hmembership] at hmembershipAccessor
          | some membership =>
              have hdecoded :
                  decodeSupportedGateRelationLists raw =
                    some (weights, membership) := by
                simp [decodeSupportedGateRelationLists, hweights, hmembership]
              have hfieldPayload :
                  fieldOutput =
                    Nat.pair 1
                      (supportedGateFieldPayload
                        (supportedGateThresholdCode raw)
                        (supportedGateWeightsCode raw)
                        (supportedGateMembershipCode raw)) := by
                exact
                  supportedGateFieldValidationOutput_eq_payload_of_ne_zero
                    inputLength raw hfieldZero
              have hfieldActual :
                  supportedGateFieldValidationOutput inputLength raw ≠ 0 := by
                simpa [fieldOutput] using hfieldZero
              have hweightsCode :
                  encodeBalancedList (weights.map encodeInt) =
                    supportedGateWeightsCode raw := by
                change encodeIntList weights =
                  supportedGateWeightsCode raw
                exact encodeIntList_of_decode hweights
              have hmembershipCode :
                  encodeBoolList membership =
                    supportedGateMembershipCode raw :=
                encodeBoolList_of_decode hmembership
              have hvalidBits :
                  supportedGateValidFieldBits inputLength
                      (supportedGateThresholdCode raw)
                      (weights.map encodeInt) membership ≤ maximumBits := by
                apply supportedGateRelationBits_of_mem
                simp [supportedGateRelationStageBits, hdecoded]
              have hsource :
                  runNPOracleProgram supportedGateValidFieldProgram
                      maximumBits
                      (supportedGateValidFieldFuel inputLength
                        (weights.map encodeInt) membership)
                      (initialNPOracleState inputLength
                        (supportedGateFieldPayload
                          (supportedGateThresholdCode raw)
                          (supportedGateWeightsCode raw)
                          (supportedGateMembershipCode raw))) =
                    some
                      (supportedGateValidFieldOutput inputLength
                        (supportedGateThresholdCode raw)
                        (weights.map encodeInt) membership) := by
                have hrun :=
                  run_bits_mono
                    (run_supportedGateValidFieldProgram inputLength
                      (supportedGateThresholdCode raw)
                      (weights.map encodeInt) membership)
                    hvalidBits
                simpa [hweightsCode, hmembershipCode] using hrun
              have hinput :
                  natBitLength
                      (Nat.pair inputLength
                        (Nat.pair 1
                          (supportedGateFieldPayload
                            (supportedGateThresholdCode raw)
                            (supportedGateWeightsCode raw)
                            (supportedGateMembershipCode raw)))) ≤
                    maximumBits := by
                simpa [hfieldPayload] using hchoiceInput
              have hvalidOutput :
                  natBitLength
                      (supportedGateValidFieldOutput inputLength
                        (supportedGateThresholdCode raw)
                        (weights.map encodeInt) membership) ≤ maximumBits := by
                simpa [supportedGateRelationOutput, fieldOutput,
                  hfieldZero, hdecoded] using houtput
              have hchoiceValid :=
                run_taggedProgramChoice_nonzero rejectProgram
                  supportedGateValidFieldProgram inputLength 1
                  (supportedGateFieldPayload
                    (supportedGateThresholdCode raw)
                    (supportedGateWeightsCode raw)
                    (supportedGateMembershipCode raw))
                  maximumBits
                  (supportedGateValidFieldFuel inputLength
                    (weights.map encodeInt) membership)
                  (supportedGateValidFieldOutput inputLength
                    (supportedGateThresholdCode raw)
                    (weights.map encodeInt) membership)
                  (by omega) hinput hsource hvalidOutput
              unfold supportedGateRelationSourceFuel
                supportedGateRelationOutput
              rw [if_neg hfieldActual, if_neg hfieldActual, hdecoded,
                hfieldPayload]
              exact hchoiceValid
  have hrun :=
    run_linkPrograms hpositive hlengthBits hfield hchoice
  simpa [supportedGateRelationProgram, supportedGateRelationFuel,
    fieldOutput] using hrun

/-! ## Exact relation semantics -/

theorem supportedGateValidFieldOutput_ne_zero_iff
    (inputLength thresholdCode : ℕ) (weights : List ℤ)
    (membership : List Bool) :
    supportedGateValidFieldOutput inputLength thresholdCode
          (weights.map encodeInt) membership ≠ 0 ↔
      weights.length = inputLength ∧
        membership.length = inputLength ∧
        List.Forall₂
          (fun weight bit => bit = false → weight = 0)
          weights membership := by
  constructor
  · intro houtput
    have hdimensions :
        (weights.map encodeInt).length = inputLength ∧
          membership.length = inputLength := by
      unfold supportedGateValidFieldOutput at houtput
      split at houtput
      · assumption
      · simp at houtput
    have hlength :
        (weights.map encodeInt).length = membership.length :=
      hdimensions.1.trans hdimensions.2.symm
    have hcount :
        nonzeroAtomCount
            (supportedWeights (weights.map encodeInt) membership) =
          nonzeroAtomCount (weights.map encodeInt) := by
      unfold supportedGateValidFieldOutput at houtput
      rw [if_pos hdimensions] at houtput
      change
        (if nonzeroAtomCount
              (supportedWeights (weights.map encodeInt) membership) =
                nonzeroAtomCount (weights.map encodeInt) then
            Nat.pair 1 _
          else
            0) ≠ 0 at houtput
      by_contra hnot
      simp [hnot] at houtput
    have hcodes :=
      (nonzeroAtomCount_supportedWeights_eq_iff_zeroOutside
        (weights.map encodeInt) membership hlength).1 hcount
    exact
      ⟨by simpa using hdimensions.1, hdimensions.2,
        (supportedGateZeroOutsideCodes_map_encodeInt_iff
          weights membership (by simpa using hlength)).1 hcodes⟩
  · rintro ⟨hweightsLength, hmembershipLength, hzeroOutside⟩
    have hlength :
        (weights.map encodeInt).length = membership.length := by
      simpa using hweightsLength.trans hmembershipLength.symm
    have hcodes :
        supportedGateZeroOutsideCodes (weights.map encodeInt) membership :=
      (supportedGateZeroOutsideCodes_map_encodeInt_iff
        weights membership (by simpa using hlength)).2 hzeroOutside
    have hcount :
        nonzeroAtomCount
            (supportedWeights (weights.map encodeInt) membership) =
          nonzeroAtomCount (weights.map encodeInt) :=
      (nonzeroAtomCount_supportedWeights_eq_iff_zeroOutside
        (weights.map encodeInt) membership hlength).2 hcodes
    have hdimensions :
        (weights.map encodeInt).length = inputLength ∧
          membership.length = inputLength := by
      exact ⟨by simpa using hweightsLength, hmembershipLength⟩
    unfold supportedGateValidFieldOutput
    rw [if_pos hdimensions]
    change
      (if nonzeroAtomCount
            (supportedWeights (weights.map encodeInt) membership) =
              nonzeroAtomCount (weights.map encodeInt) then
          Nat.pair 1 _
        else
          0) ≠ 0
    rw [if_pos hcount]
    exact (Nat.zero_lt_one.trans_le (Nat.left_le_pair 1 _)).ne'

theorem supportedGateRelationOutput_ne_zero_iff
    (inputLength raw : ℕ) :
    supportedGateRelationOutput inputLength raw ≠ 0 ↔
      ∃ weightsCode thresholdCode membershipCode weights threshold membership,
        decodeTaggedList raw =
            some [weightsCode, thresholdCode, membershipCode] ∧
          decodeIntList weightsCode = some weights ∧
          decodeInt thresholdCode = some threshold ∧
          decodeBoolList membershipCode = some membership ∧
          weights.length = inputLength ∧
          membership.length = inputLength ∧
          List.Forall₂
            (fun weight bit => bit = false → weight = 0)
            weights membership := by
  constructor
  · intro houtput
    have hfield :
        supportedGateFieldValidationOutput inputLength raw ≠ 0 := by
      intro hzero
      apply houtput
      simp [supportedGateRelationOutput, hzero]
    obtain ⟨weightsCode, thresholdCode, membershipCode, htuple,
        hweightsSome, hthresholdSome, hmembershipSome⟩ :=
      (supportedGateFieldValidationOutput_ne_zero_iff
        inputLength raw).1 hfield
    have hcodes := supportedGateCodes_of_decode htuple
    cases hweights :
        decodeIntList (supportedGateWeightsCode raw) with
    | none =>
        have : (decodeIntList weightsCode).isSome = false := by
          simpa [hcodes.1] using congrArg Option.isSome hweights
        simp [this] at hweightsSome
    | some weights =>
        cases hmembership :
            decodeBoolList (supportedGateMembershipCode raw) with
        | none =>
            have : (decodeBoolList membershipCode).isSome = false := by
              simpa [hcodes.2.2] using congrArg Option.isSome hmembership
            simp [this] at hmembershipSome
        | some membership =>
            have hdecoded :
                decodeSupportedGateRelationLists raw =
                  some (weights, membership) := by
              simp [decodeSupportedGateRelationLists, hweights, hmembership]
            have hvalid :
                supportedGateValidFieldOutput inputLength
                    (supportedGateThresholdCode raw)
                    (weights.map encodeInt) membership ≠ 0 := by
              unfold supportedGateRelationOutput at houtput
              rw [if_neg hfield, hdecoded] at houtput
              exact houtput
            have hrelations :=
              (supportedGateValidFieldOutput_ne_zero_iff inputLength
                (supportedGateThresholdCode raw) weights membership).1 hvalid
            cases hthreshold : decodeInt thresholdCode with
            | none => simp [hthreshold] at hthresholdSome
            | some threshold =>
                exact
                  ⟨weightsCode, thresholdCode, membershipCode, weights,
                    threshold, membership, htuple,
                    by simpa [hcodes.1] using hweights,
                    hthreshold,
                    by simpa [hcodes.2.2] using hmembership,
                    hrelations.1, hrelations.2.1, hrelations.2.2⟩
  · rintro ⟨weightsCode, thresholdCode, membershipCode, weights, threshold,
      membership, htuple, hweights, hthreshold, hmembership,
      hweightsLength, hmembershipLength, hzeroOutside⟩
    have hcodes := supportedGateCodes_of_decode htuple
    have hfield :
        supportedGateFieldValidationOutput inputLength raw ≠ 0 := by
      apply
        (supportedGateFieldValidationOutput_ne_zero_iff
          inputLength raw).2
      exact
        ⟨weightsCode, thresholdCode, membershipCode, htuple,
          by simp [hweights], by simp [hthreshold], by simp [hmembership]⟩
    have hdecoded :
        decodeSupportedGateRelationLists raw =
          some (weights, membership) := by
      simp [decodeSupportedGateRelationLists, hcodes.1, hcodes.2.2,
        hweights, hmembership]
    have hvalid :
        supportedGateValidFieldOutput inputLength
            (supportedGateThresholdCode raw)
            (weights.map encodeInt) membership ≠ 0 :=
      (supportedGateValidFieldOutput_ne_zero_iff inputLength
        (supportedGateThresholdCode raw) weights membership).2
        ⟨hweightsLength, hmembershipLength, hzeroOutside⟩
    unfold supportedGateRelationOutput
    rw [if_neg hfield, hdecoded]
    exact hvalid

theorem supportedGateRelationOutput_ne_zero_iff_decode
    (inputLength raw : ℕ) :
    supportedGateRelationOutput inputLength raw ≠ 0 ↔
      (decodeSupportedNormalizedGate inputLength raw).isSome := by
  exact
    (supportedGateRelationOutput_ne_zero_iff inputLength raw).trans
      (decodeSupportedNormalizedGate_isSome_iff_fields
        inputLength raw).symm

theorem supportedGateRelationOutput_eq_of_fields
    (inputLength raw weightsCode thresholdCode membershipCode : ℕ)
    (weights : List ℤ) (threshold : ℤ) (membership : List Bool)
    (htuple :
      decodeTaggedList raw =
        some [weightsCode, thresholdCode, membershipCode])
    (hweights : decodeIntList weightsCode = some weights)
    (hthreshold : decodeInt thresholdCode = some threshold)
    (hmembership : decodeBoolList membershipCode = some membership)
    (hweightsLength : weights.length = inputLength)
    (hmembershipLength : membership.length = inputLength)
    (hzeroOutside :
      List.Forall₂
        (fun weight bit => bit = false → weight = 0)
        weights membership) :
    supportedGateRelationOutput inputLength raw =
      Nat.pair 1
        (supportedGateCompressedPayload thresholdCode
          (encodeBalancedList (supportedWeights (weights.map encodeInt)
            membership))
          (nonzeroSupportCount membership)
          membershipCode) := by
  have hcodes := supportedGateCodes_of_decode htuple
  have hfield :
      supportedGateFieldValidationOutput inputLength raw ≠ 0 := by
    apply
      (supportedGateFieldValidationOutput_ne_zero_iff
        inputLength raw).2
    exact
      ⟨weightsCode, thresholdCode, membershipCode, htuple,
        by simp [hweights], by simp [hthreshold], by simp [hmembership]⟩
  have hdecoded :
      decodeSupportedGateRelationLists raw = some (weights, membership) := by
    simp [decodeSupportedGateRelationLists, hcodes.1, hcodes.2.2,
      hweights, hmembership]
  have hlength :
      (weights.map encodeInt).length = membership.length := by
    simpa using hweightsLength.trans hmembershipLength.symm
  have hzeroCodes :
      supportedGateZeroOutsideCodes (weights.map encodeInt) membership :=
    (supportedGateZeroOutsideCodes_map_encodeInt_iff weights membership
      (by simpa using hlength)).2 hzeroOutside
  have hcount :
      nonzeroAtomCount
          (supportedWeights (weights.map encodeInt) membership) =
        nonzeroAtomCount (weights.map encodeInt) :=
    (nonzeroAtomCount_supportedWeights_eq_iff_zeroOutside
      (weights.map encodeInt) membership hlength).2 hzeroCodes
  unfold supportedGateRelationOutput
  rw [if_neg hfield, hdecoded]
  change
    supportedGateValidFieldOutput inputLength
        (supportedGateThresholdCode raw)
        (weights.map encodeInt) membership =
      _
  unfold supportedGateValidFieldOutput
  rw [if_pos (by
    exact ⟨by simpa using hweightsLength, hmembershipLength⟩)]
  unfold supportedGateZeroOutsideOutput
  rw [if_pos hcount]
  rw [hcodes.2.1]
  rw [encodeBoolList_of_decode hmembership]

end NearCubicWires.CanonicalSupportedGateRelationProgram
