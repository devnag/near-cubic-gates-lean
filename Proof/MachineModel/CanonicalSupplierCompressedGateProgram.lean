import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.MachineModel.CanonicalSupplierGateProgram
import Proof.MachineModel.CanonicalSupplierSupportCompressionProgram
import Proof.MachineModel.CanonicalSupportedGateRelationProgram
import Proof.MachineModel.TaggedProgramChoice

/-!
# Canonical support-compressed supplier gate decomposition

Top threshold gates must be decomposed over their physically retained bottom
coordinates.  This module first identifies the unique semantic compressed
gate.  Its executable path is built below from the existing field parser,
support compressor, threshold predecessor, request packer, and native caller;
none of those wire formats is decoded into a host-side gate.
-/

namespace NearCubicWires.CanonicalSupplierCompressedGateProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalIntPredecessorProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalSupplierGateProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalSupportedGateRelationProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CompilerSemantics
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## Semantic support compression -/

/-- The unique support-ordered gate seen by the imported exact decomposer.
Its coordinates use the same increasing `Finset` order as `retainedTopGate`. -/
def supportCompressedGate {n : ℕ}
    (gate : SupportedNormalizedGate n) :
    NormalizedThresholdGate gate.support.card where
  weight index :=
    gate.gate.weight (gate.support.orderEmbOfFin rfl index)
  threshold := gate.gate.threshold

private theorem supportedWeights_map_filter
    {ι : Type} (indices : List ι) (value : ι → ℕ)
    (selected : ι → Bool) :
    supportedWeights (indices.map value) (indices.map selected) =
      (indices.filter selected).map value := by
  induction indices with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      cases hselected : selected index <;>
        simp [supportedWeights, hselected, inductionHypothesis]

private theorem filter_finRange_membership_eq_sort
    {n : ℕ} (support : Finset (Fin n)) :
    (List.finRange n).filter
        (fun index => decide (index ∈ support)) =
      support.sort (· ≤ ·) := by
  apply List.Subset.antisymm_of_sortedLT
  · intro index hindex
    simpa using hindex
  · intro index hindex
    simpa using hindex
  · exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT
  · exact Finset.sortedLT_sort support

/-- Machine-selected integer atoms are exactly the increasing support-ordered
weights of the semantic compressed gate. -/
theorem supportedWeights_eq_supportCompressedGate
    {n : ℕ} (gate : SupportedNormalizedGate n) :
    supportedWeights
        ((List.ofFn gate.gate.weight).map encodeInt)
        (List.ofFn fun index =>
          decide (index ∈ gate.support)) =
      (List.ofFn (supportCompressedGate gate).weight).map encodeInt := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, List.map_map]
  rw [supportedWeights_map_filter]
  rw [filter_finRange_membership_eq_sort]
  have hindices :
      (List.finRange gate.support.card).map
          (gate.support.orderEmbOfFin rfl) =
        gate.support.sort (· ≤ ·) := by
    exact Finset.listMap_orderEmbOfFin_finRange gate.support rfl
  rw [List.ofFn_eq_map]
  simp only [List.map_map, supportCompressedGate]
  rw [← hindices]
  simp only [List.map_map]
  rfl

private theorem nonzeroSupportCount_eq_filter_length
    (support : List Bool) :
    nonzeroSupportCount support = (support.filter id).length := by
  induction support with
  | nil => rfl
  | cons bit support inductionHypothesis =>
      cases bit <;>
        simp [nonzeroSupportCount, inductionHypothesis, Nat.add_comm]

/-- The native count produced by support compression is the type-level arity
of `supportCompressedGate`. -/
theorem nonzeroSupportCount_eq_supportCard
    {n : ℕ} (gate : SupportedNormalizedGate n) :
    nonzeroSupportCount
        (List.ofFn fun index =>
          decide (index ∈ gate.support)) =
      gate.support.card := by
  rw [nonzeroSupportCount_eq_filter_length]
  rw [List.ofFn_eq_map]
  rw [List.filter_map]
  simp only [List.length_map, Function.id_comp]
  rw [filter_finRange_membership_eq_sort]
  simp

def supportCompressedGateExactRequest {n : ℕ}
    (gate : SupportedNormalizedGate n) : ExactDecompositionRequest :=
  ⟨gate.support.card,
    nonStrictAsStrict (supportCompressedGate gate)⟩

@[simp] theorem supportCompressedGateExactRequest_code
    {n : ℕ} (gate : SupportedNormalizedGate n) :
    (supportCompressedGateExactRequest gate).code =
      supplierGateExactRequestCode
        (encodeBalancedList <|
          supportedWeights
            ((List.ofFn gate.gate.weight).map encodeInt)
            (List.ofFn fun index =>
              decide (index ∈ gate.support)))
        (supplierGateStrictThresholdCode gate) := by
  rw [supportedWeights_eq_supportCompressedGate]
  rfl

@[simp] theorem supportCompressedGate_top
    {n : ℕ} (circuit : NormalizedThresholdThresholdCircuit n) :
    supportCompressedGate circuit.top = retainedTopGate circuit := by
  rfl

@[simp] theorem supportCompressedGateExactRequest_top
    {n : ℕ} (circuit : NormalizedThresholdThresholdCircuit n) :
    supportCompressedGateExactRequest circuit.top =
      (⟨circuit.top.support.card,
        nonStrictAsStrict (retainedTopGate circuit)⟩ :
          ExactDecompositionRequest) := by
  rfl

/-! ## Sole executable compressed-gate path -/

private def supplierCompressedGateTailProgram
    (algorithm : ExecutableExactDecompositionAlgorithm) : NPOracleProgram :=
  linkPrograms supplierGateThresholdPredecessorProgram <|
    linkPrograms supplierGateRequestPackerProgram
      (nativeContextCallProgram algorithm.runner.program)

/-- The relation validator is the only raw supported-gate prefix.  Invalid
syntax, wrong arity, or a nonzero weight outside support reaches `rejectProgram`;
the exact decomposer is callable only from the validated nonzero branch. -/
def supplierCompressedGateProgram
    (algorithm : ExecutableExactDecompositionAlgorithm) : NPOracleProgram :=
  linkPrograms supportedGateRelationProgram <|
    taggedProgramChoice rejectProgram
      (supplierCompressedGateTailProgram algorithm)

private def supplierCompressedGateTailFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {n : ℕ} (gate : SupportedNormalizedGate n) : ℕ :=
  let request := supportCompressedGateExactRequest gate
  linkFuel
    (linkPrograms supplierGateRequestPackerProgram
      (nativeContextCallProgram algorithm.runner.program))
    (supplierGateThresholdPredecessorFuel gate) <|
    linkFuel (nativeContextCallProgram algorithm.runner.program)
      supplierGateRequestPackerFuel <|
      nativeContextCallFuel algorithm.runner.program
        (algorithm.runner.budget request) gate.support.card request.code

def supplierCompressedGateFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {n : ℕ} (gate : SupportedNormalizedGate n) : ℕ :=
  linkFuel
    (taggedProgramChoice rejectProgram
      (supplierCompressedGateTailProgram algorithm))
    (supportedGateRelationFuel n (encodeSupportedNormalizedGate gate))
    (taggedProgramChoiceFuel <|
      supplierCompressedGateTailFuel algorithm gate)

def supplierCompressedGateBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {n : ℕ} (gate : SupportedNormalizedGate n) : ℕ :=
  let weightAtoms := (List.ofFn gate.gate.weight).map encodeInt
  let supportBits :=
    List.ofFn fun index => decide (index ∈ gate.support)
  let thresholdCode := supplierGateThresholdCode gate
  let supportCode := encodeBoolList supportBits
  let compressedWeightsCode :=
    encodeBalancedList (supportedWeights weightAtoms supportBits)
  let countSupport := Nat.pair gate.support.card supportCode
  let compressedContext := Nat.pair compressedWeightsCode countSupport
  let compressedPayload := Nat.pair thresholdCode compressedContext
  let strictThresholdCode := supplierGateStrictThresholdCode gate
  let request := supportCompressedGateExactRequest gate
  max (natBitLength n) <|
    max
      (supportedGateRelationBits n (encodeSupportedNormalizedGate gate)) <|
      max
        (natBitLength
          (Nat.pair n (Nat.pair 1 compressedPayload))) <|
        max
          (preserveRightBits
            (canonicalIntPredecessorBits n gate.gate.threshold)
            thresholdCode compressedContext strictThresholdCode) <|
          max
            (supplierGateRequestPackerBits compressedWeightsCode
              strictThresholdCode countSupport)
            (nativeContextCallBits n gate.support.card request.code
              supportCode (algorithm.runner.execute request)
              (algorithm.runner.budget request))

def supplierCompressedGateOutput
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {n : ℕ} (gate : SupportedNormalizedGate n) : ℕ :=
  Nat.pair
    (algorithm.runner.execute (supportCompressedGateExactRequest gate))
    (Nat.pair gate.support.card (supplierGateSupportCode gate))

/-- A malformed raw gate reaches the constant reject branch, so its resource
envelope is independent of every execution property of the exact decomposer. -/
def supplierCompressedGateRejectBits (inputLength raw : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max (supportedGateRelationBits inputLength raw) <|
        max
          (natBitLength (Nat.pair inputLength (Nat.pair 0 0)))
          (natBitLength 0)

def supplierCompressedGateRejectFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (inputLength raw : ℕ) : ℕ :=
  linkFuel
    (taggedProgramChoice rejectProgram
      (supplierCompressedGateTailProgram algorithm))
    (supportedGateRelationFuel inputLength raw)
    (taggedProgramChoiceFuel 2)

@[simp] theorem supplierCompressedGateProgram_oracleFree
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    OracleFree (supplierCompressedGateProgram algorithm) := by
  have htail :
      OracleFree (supplierCompressedGateTailProgram algorithm) := by
    exact
      oracleFree_linkPrograms
        (preserveRightProgram_oracleFree _
          canonicalIntPredecessorProgram_oracleFree) <|
        oracleFree_linkPrograms
          supplierGateRequestPackerProgram_oracleFree
          (nativeContextCallProgram_oracleFree algorithm.oracleFree)
  exact
    oracleFree_linkPrograms supportedGateRelationProgram_oracleFree <|
      taggedProgramChoice_oracleFree _ _
        rejectProgram_oracleFree htail

theorem run_supplierCompressedGateProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {n : ℕ} (gate : SupportedNormalizedGate n) :
    runNPOracleProgram (supplierCompressedGateProgram algorithm)
        (supplierCompressedGateBits algorithm gate)
        (supplierCompressedGateFuel algorithm gate)
        (initialNPOracleState n
          (encodeSupportedNormalizedGate gate)) =
      some (supplierCompressedGateOutput algorithm gate) := by
  let weights := List.ofFn gate.gate.weight
  let weightAtoms := weights.map encodeInt
  let supportBits :=
    List.ofFn fun index => decide (index ∈ gate.support)
  let weightsCode := encodeIntList weights
  let thresholdCode := supplierGateThresholdCode gate
  let supportCode := encodeBoolList supportBits
  let compressedWeightsCode :=
    encodeBalancedList (supportedWeights weightAtoms supportBits)
  let countSupport := Nat.pair gate.support.card supportCode
  let compressedContext := Nat.pair compressedWeightsCode countSupport
  let compressedPayload := Nat.pair thresholdCode compressedContext
  let strictThresholdCode := supplierGateStrictThresholdCode gate
  let predecessorOutput := Nat.pair strictThresholdCode compressedContext
  let request := supportCompressedGateExactRequest gate
  let packerOutput := Nat.pair request.code countSupport
  let finalOutput := supplierCompressedGateOutput algorithm gate
  let tailFuel := supplierCompressedGateTailFuel algorithm gate
  let maximumBits := supplierCompressedGateBits algorithm gate
  have hcount :
      nonzeroSupportCount supportBits = gate.support.card := by
    simpa only [supportBits] using
      nonzeroSupportCount_eq_supportCard gate
  have hzeroOutside :
      List.Forall₂
        (fun weight bit => bit = false → weight = 0)
        weights supportBits := by
    apply List.forall₂_of_length_eq_of_get
    · simp [weights, supportBits]
    · intro index hweights hsupport
      simp only [weights, supportBits, List.get_ofFn]
      intro hfalse
      apply gate.zeroOutside
      simpa using hfalse
  have hrelationOutput :
      supportedGateRelationOutput n (encodeSupportedNormalizedGate gate) =
        Nat.pair 1 compressedPayload := by
    have hrun :=
      supportedGateRelationOutput_eq_of_fields n
        (encodeSupportedNormalizedGate gate) weightsCode thresholdCode
        supportCode weights gate.gate.threshold supportBits
        (by
          simp [encodeSupportedNormalizedGate, weightsCode, thresholdCode,
            supportCode, weights, supportBits, supplierGateThresholdCode])
        (by simp [weightsCode])
        (by simp [thresholdCode, supplierGateThresholdCode])
        (by simp [supportCode])
        (by simp [weights])
        (by simp [supportBits])
        hzeroOutside
    simpa [compressedPayload, compressedContext, countSupport,
      compressedWeightsCode, weightAtoms, weightsCode, thresholdCode,
      supportCode, hcount, supportedGateCompressedPayload] using hrun
  have hpublicLength : natBitLength n ≤ maximumBits := by
    simp [maximumBits, supplierCompressedGateBits]
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength n by
      unfold natBitLength
      omega).trans hpublicLength
  have hrelationBits :
      supportedGateRelationBits n (encodeSupportedNormalizedGate gate) ≤
        maximumBits := by
    simp [maximumBits, supplierCompressedGateBits]
  have hchoiceInput :
      natBitLength (Nat.pair n (Nat.pair 1 compressedPayload)) ≤
        maximumBits := by
    simp [maximumBits, supplierCompressedGateBits, compressedPayload,
      compressedContext, compressedWeightsCode, countSupport, thresholdCode,
      supportCode, weightAtoms, weights, supportBits]
  have hpredecessorBits :
      preserveRightBits
          (canonicalIntPredecessorBits n gate.gate.threshold)
          thresholdCode compressedContext strictThresholdCode ≤
        maximumBits := by
    simp [maximumBits, supplierCompressedGateBits, thresholdCode,
      compressedContext, compressedWeightsCode, countSupport,
      strictThresholdCode, supportCode, weightAtoms, weights, supportBits]
  have hpackerBits :
      supplierGateRequestPackerBits compressedWeightsCode
          strictThresholdCode countSupport ≤ maximumBits := by
    simp [maximumBits, supplierCompressedGateBits,
      compressedWeightsCode, strictThresholdCode, countSupport,
      supportCode, weightAtoms, weights, supportBits]
  have hcallBits :
      nativeContextCallBits n gate.support.card request.code supportCode
          (algorithm.runner.execute request)
          (algorithm.runner.budget request) ≤ maximumBits := by
    simp [maximumBits, supplierCompressedGateBits, request,
      supportCode, supportBits]
  have hrelation :
      runNPOracleProgram supportedGateRelationProgram maximumBits
          (supportedGateRelationFuel n (encodeSupportedNormalizedGate gate))
          (initialNPOracleState n (encodeSupportedNormalizedGate gate)) =
        some (Nat.pair 1 compressedPayload) := by
    have hrun :=
      run_bits_mono
        (run_supportedGateRelationProgram n
          (encodeSupportedNormalizedGate gate))
        hrelationBits
    simpa [hrelationOutput] using hrun
  have hpredecessor :
      runNPOracleProgram supplierGateThresholdPredecessorProgram
          maximumBits (supplierGateThresholdPredecessorFuel gate)
          (initialNPOracleState n compressedPayload) =
        some predecessorOutput := by
    have hrun :=
      run_preserveRightProgram canonicalIntPredecessorProgram n
        (canonicalIntPredecessorBits n gate.gate.threshold)
        (canonicalIntPredecessorFuel gate.gate.threshold)
        thresholdCode compressedContext strictThresholdCode
        (run_canonicalIntPredecessorProgram n gate.gate.threshold)
    have hlarger := run_bits_mono hrun hpredecessorBits
    simpa only [supplierGateThresholdPredecessorProgram,
      supplierGateThresholdPredecessorFuel, compressedPayload,
      predecessorOutput] using hlarger
  have hpacker :
      runNPOracleProgram supplierGateRequestPackerProgram maximumBits
          supplierGateRequestPackerFuel
          (initialNPOracleState n predecessorOutput) =
        some packerOutput := by
    have hrun :=
      run_bits_mono
        (run_supplierGateRequestPackerProgram n compressedWeightsCode
          strictThresholdCode countSupport)
        hpackerBits
    simpa only [predecessorOutput, compressedContext,
      supplierGateRequestPackerInput, supplierGateFieldContext,
      packerOutput, supplierGateRequestPackerOutput,
      supportCompressedGateExactRequest_code, request] using hrun
  have hcall :
      runNPOracleProgram
          (nativeContextCallProgram algorithm.runner.program)
          maximumBits
          (nativeContextCallFuel algorithm.runner.program
            (algorithm.runner.budget request) gate.support.card request.code)
          (initialNPOracleState n packerOutput) =
        some finalOutput := by
    have hrun :=
      run_nativeContextCallProgram algorithm.runner.program n
        gate.support.card request.code supportCode
        (algorithm.runner.execute request)
        (algorithm.runner.budget request)
        (algorithm.runner.budget request)
        (algorithm.runner.run_eq_execute request)
    have hlarger := run_bits_mono hrun hcallBits
    simpa only [packerOutput, countSupport, finalOutput,
      supplierCompressedGateOutput, request, supportCode, supportBits,
      supplierGateSupportCode] using hlarger
  have hpackerCall :=
    run_linkPrograms hpositive hpublicLength hpacker hcall
  have htail :
      runNPOracleProgram (supplierCompressedGateTailProgram algorithm)
          maximumBits tailFuel
          (initialNPOracleState n compressedPayload) =
        some finalOutput := by
    have hrun :=
      run_linkPrograms hpositive hpublicLength hpredecessor hpackerCall
    dsimp only [supplierCompressedGateTailProgram, tailFuel,
      supplierCompressedGateTailFuel]
    exact hrun
  have hchoice :
      runNPOracleProgram
          (taggedProgramChoice rejectProgram
            (supplierCompressedGateTailProgram algorithm))
          maximumBits (taggedProgramChoiceFuel tailFuel)
          (initialNPOracleState n (Nat.pair 1 compressedPayload)) =
        some finalOutput := by
    exact
      run_taggedProgramChoice_nonzero rejectProgram
        (supplierCompressedGateTailProgram algorithm) n 1 compressedPayload
        maximumBits tailFuel finalOutput (by omega) hchoiceInput
        htail
        (run_output_bounded hcall)
  have hrun :=
    run_linkPrograms hpositive hpublicLength hrelation hchoice
  dsimp only [supplierCompressedGateProgram, supplierCompressedGateFuel,
    tailFuel]
  exact hrun

/-- Canonically decoded raw inputs use the same unique executable path as the
typed theorem; no separately assembled or trusted gate is accepted. -/
theorem run_supplierCompressedGateProgram_of_decode
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {inputLength raw : ℕ} {gate : SupportedNormalizedGate inputLength}
    (hdecode :
      decodeSupportedNormalizedGate inputLength raw = some gate) :
    runNPOracleProgram (supplierCompressedGateProgram algorithm)
        (supplierCompressedGateBits algorithm gate)
        (supplierCompressedGateFuel algorithm gate)
        (initialNPOracleState inputLength raw) =
      some (supplierCompressedGateOutput algorithm gate) := by
  have hcanonical := encodeSupportedNormalizedGate_of_decode hdecode
  subst raw
  exact run_supplierCompressedGateProgram algorithm gate

/-- Invalid syntax, wrong arity, and nonzero weights outside the declared
support all reject before the imported decomposer is reachable. -/
theorem run_supplierCompressedGateProgram_rejects_invalid
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (inputLength raw : ℕ)
    (hdecode :
      decodeSupportedNormalizedGate inputLength raw = none) :
    runNPOracleProgram (supplierCompressedGateProgram algorithm)
        (supplierCompressedGateRejectBits inputLength raw)
        (supplierCompressedGateRejectFuel algorithm inputLength raw)
        (initialNPOracleState inputLength raw) =
      some 0 := by
  let maximumBits := supplierCompressedGateRejectBits inputLength raw
  have hrelationOutput :
      supportedGateRelationOutput inputLength raw = 0 := by
    by_contra hnonzero
    have hsome :=
      (supportedGateRelationOutput_ne_zero_iff_decode
        inputLength raw).1 hnonzero
    simp [hdecode] at hsome
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, supplierCompressedGateRejectBits]
  have hinputLength :
      natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, supplierCompressedGateRejectBits]
  have hrelationBits :
      supportedGateRelationBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, supplierCompressedGateRejectBits]
  have hchoiceInput :
      natBitLength (Nat.pair inputLength (Nat.pair 0 0)) ≤
        maximumBits := by
    simp [maximumBits, supplierCompressedGateRejectBits]
  have hzero : natBitLength 0 ≤ maximumBits := by
    simp [maximumBits, supplierCompressedGateRejectBits]
  have hrelation :
      runNPOracleProgram supportedGateRelationProgram maximumBits
          (supportedGateRelationFuel inputLength raw)
          (initialNPOracleState inputLength raw) =
        some 0 := by
    have hrun :=
      run_bits_mono
        (run_supportedGateRelationProgram inputLength raw)
        hrelationBits
    simpa only [hrelationOutput] using hrun
  have hrejection :
      runNPOracleProgram rejectProgram maximumBits 2
          (initialNPOracleState inputLength 0) =
        some 0 := by
    simpa using
      run_rejectProgram inputLength 0 maximumBits 0 hzero
  have hchoice :
      runNPOracleProgram
          (taggedProgramChoice rejectProgram
            (supplierCompressedGateTailProgram algorithm))
          maximumBits (taggedProgramChoiceFuel 2)
          (initialNPOracleState inputLength 0) =
        some 0 := by
    simpa only [show Nat.pair 0 0 = 0 by rfl] using
      run_taggedProgramChoice_zero rejectProgram
        (supplierCompressedGateTailProgram algorithm)
        inputLength 0 maximumBits 2 0 hchoiceInput hrejection hzero
  have hrun :=
    run_linkPrograms hpositive hinputLength hrelation hchoice
  dsimp only [supplierCompressedGateProgram,
    supplierCompressedGateRejectFuel]
  exact hrun

end NearCubicWires.CanonicalSupplierCompressedGateProgram
