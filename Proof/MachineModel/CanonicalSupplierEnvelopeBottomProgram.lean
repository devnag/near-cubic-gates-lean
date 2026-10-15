import Proof.MachineModel.CanonicalSupplierCircuitBatchProgram
import Proof.MachineModel.CanonicalSupplierCircuitBottomBatchProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Canonical supplier envelope-to-bottom decomposition

The canonical envelope batch already returns one balanced forest of native
circuit headers beside the single outer `(mode, q)` context.  This module
links that output directly to the sole circuit-bottom batch program through
`preserveRightProgram`; no request framing or decoder is duplicated here.
-/

namespace NearCubicWires.CanonicalSupplierEnvelopeBottomProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalSupplierCircuitBatchProgram
open NearCubicWires.CanonicalSupplierCircuitBottomBatchProgram
open NearCubicWires.CanonicalSupplierCircuitHeaderProgram
open NearCubicWires.CanonicalSupplierGateBatchProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Published-family bottom views -/

def symmetricCircuitBottomView {q : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit q) :
    SupplierCircuitBottomView q where
  thresholdFamily := false
  bottomCount := circuit.bottomCount
  gates := List.ofFn circuit.bottom
  topCode := encodeBoolList (List.ofFn circuit.top)

def thresholdCircuitBottomView {q : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit q) :
    SupplierCircuitBottomView q where
  thresholdFamily := true
  bottomCount := circuit.bottomCount
  gates := List.ofFn circuit.bottom
  topCode := encodeSupportedNormalizedGate circuit.top

@[simp] theorem symmetricCircuitBottomView_header
    {q : ℕ} (circuit : NormalizedSymmetricThresholdCircuit q) :
    (symmetricCircuitBottomView circuit).header =
      (symmetricCircuitHeaderView circuit).output := by
  simp [symmetricCircuitBottomView, symmetricCircuitHeaderView,
    SupplierCircuitBottomView.header,
    SupplierCircuitBottomView.familyCode,
    SupplierCircuitHeaderView.output, supplierGateCodes,
    symmetricCircuitFamilyTag, encodeNat, encodeBits,
    encodeBoolList, encodeBalancedList, Function.comp_def]

@[simp] theorem thresholdCircuitBottomView_header
    {q : ℕ} (circuit : NormalizedThresholdThresholdCircuit q) :
    (thresholdCircuitBottomView circuit).header =
      (thresholdCircuitHeaderView circuit).output := by
  have hpair : Nat.pair 1 1 ≠ 0 := by
    have hleft := Nat.left_le_pair 1 1
    omega
  simp [thresholdCircuitBottomView, thresholdCircuitHeaderView,
    SupplierCircuitBottomView.header,
    SupplierCircuitBottomView.familyCode,
    SupplierCircuitHeaderView.output, supplierGateCodes,
    thresholdCircuitFamilyTag, supplierCircuitHeaderOutput,
    supplierCircuitHeaderContext, supplierCircuitMode,
    encodeNat, encodeBits, encodeBoolList, encodeBalancedList,
    boolCode, Function.comp_def, hpair]

def symmetricCircuitBottomViews
    (request :
      FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List (SupplierCircuitBottomView request.q) :=
  request.circuits.map symmetricCircuitBottomView

def thresholdCircuitBottomViews
    (request :
      FourfoldRequest NormalizedThresholdThresholdCircuit) :
    List (SupplierCircuitBottomView request.q) :=
  request.circuits.map thresholdCircuitBottomView

@[simp] theorem symmetricCircuitBottomHeaders
    (request :
      FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    supplierCircuitHeaderOutputs
        (symmetricCircuitHeaderViews request) =
      supplierCircuitBottomHeaders
        (symmetricCircuitBottomViews request) := by
  simp [supplierCircuitHeaderOutputs, symmetricCircuitHeaderViews,
    supplierCircuitBottomHeaders, symmetricCircuitBottomViews]

@[simp] theorem thresholdCircuitBottomHeaders
    (request :
      FourfoldRequest NormalizedThresholdThresholdCircuit) :
    supplierCircuitHeaderOutputs
        (thresholdCircuitHeaderViews request) =
      supplierCircuitBottomHeaders
        (thresholdCircuitBottomViews request) := by
  simp [supplierCircuitHeaderOutputs, thresholdCircuitHeaderViews,
    supplierCircuitBottomHeaders, thresholdCircuitBottomViews]

/-! ## Unique envelope-to-bottom composition -/

def supplierCircuitEnvelopeBottomProgram
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    NPOracleProgram :=
  linkPrograms supplierCircuitEnvelopeBatchProgram <|
    preserveRightProgram
      (supplierCircuitBottomBatchProgram algorithm)

def supplierCircuitEnvelopeBottomOutput
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (mode q : ℕ)
    (views : List (SupplierCircuitBottomView q)) : ℕ :=
  Nat.pair
    (encodeBalancedList
      (supplierCircuitBottomOutputs algorithm views))
    (supplierCircuitBatchContext mode q)

def supplierCircuitEnvelopeBottomPreservingBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (mode q : ℕ)
    (views : List (SupplierCircuitBottomView q)) : ℕ :=
  preserveRightBits
    (supplierCircuitBottomBatchBits algorithm views)
    (encodeBalancedList (supplierCircuitBottomHeaders views))
    (supplierCircuitBatchContext mode q)
    (encodeBalancedList
      (supplierCircuitBottomOutputs algorithm views))

def supplierCircuitEnvelopeBottomBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (mode q : ℕ)
    (headerViews : List SupplierCircuitHeaderView)
    (bottomViews : List (SupplierCircuitBottomView q)) : ℕ :=
  max (natBitLength q) <|
    max
      (supplierCircuitEnvelopeBatchBits mode q headerViews)
      (supplierCircuitEnvelopeBottomPreservingBits algorithm
        mode q bottomViews)

def supplierCircuitEnvelopeBottomFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {q : ℕ}
    (headerViews : List SupplierCircuitHeaderView)
    (bottomViews : List (SupplierCircuitBottomView q)) : ℕ :=
  linkFuel
    (preserveRightProgram
      (supplierCircuitBottomBatchProgram algorithm))
    (supplierCircuitEnvelopeBatchFuel headerViews)
    (preserveRightFuel
      (supplierCircuitBottomBatchFuel algorithm bottomViews))

@[simp] theorem supplierCircuitEnvelopeBottomProgram_oracleFree
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    OracleFree (supplierCircuitEnvelopeBottomProgram algorithm) := by
  apply oracleFree_linkPrograms
  · exact supplierCircuitEnvelopeBatchProgram_oracleFree
  · exact preserveRightProgram_oracleFree _
      (supplierCircuitBottomBatchProgram_oracleFree algorithm)

private theorem run_supplierCircuitEnvelopeBottomProgram_of_run
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (mode q inputCode : ℕ)
    (headerViews : List SupplierCircuitHeaderView)
    (bottomViews : List (SupplierCircuitBottomView q))
    (hheaders :
      supplierCircuitHeaderOutputs headerViews =
        supplierCircuitBottomHeaders bottomViews)
    (henvelope :
      runNPOracleProgram supplierCircuitEnvelopeBatchProgram
          (supplierCircuitEnvelopeBatchBits mode q headerViews)
          (supplierCircuitEnvelopeBatchFuel headerViews)
          (initialNPOracleState q inputCode) =
        some (supplierCircuitBatchOutput mode q headerViews)) :
    runNPOracleProgram
        (supplierCircuitEnvelopeBottomProgram algorithm)
        (supplierCircuitEnvelopeBottomBits algorithm mode q
          headerViews bottomViews)
        (supplierCircuitEnvelopeBottomFuel algorithm
          headerViews bottomViews)
        (initialNPOracleState q inputCode) =
      some
        (supplierCircuitEnvelopeBottomOutput algorithm
          mode q bottomViews) := by
  let headerTree :=
    encodeBalancedList (supplierCircuitBottomHeaders bottomViews)
  let outputTree :=
    encodeBalancedList
      (supplierCircuitBottomOutputs algorithm bottomViews)
  let context := supplierCircuitBatchContext mode q
  let maximumBits :=
    supplierCircuitEnvelopeBottomBits algorithm mode q
      headerViews bottomViews
  have hqBits : natBitLength q ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength q by
      unfold natBitLength
      omega).trans hqBits
  have henvelopeBits :
      supplierCircuitEnvelopeBatchBits mode q headerViews ≤
        maximumBits := by
    exact
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hbottomBits :
      supplierCircuitEnvelopeBottomPreservingBits algorithm
          mode q bottomViews ≤
        maximumBits := by
    exact
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have henvelopeAtMaximum :
      runNPOracleProgram supplierCircuitEnvelopeBatchProgram
          maximumBits
          (supplierCircuitEnvelopeBatchFuel headerViews)
          (initialNPOracleState q inputCode) =
        some (Nat.pair headerTree context) := by
    have hrun := run_bits_mono henvelope henvelopeBits
    rw [supplierCircuitBatchOutput, hheaders] at hrun
    simpa only [headerTree, context] using hrun
  have hbottomSource :
      runNPOracleProgram
          (supplierCircuitBottomBatchProgram algorithm)
          (supplierCircuitBottomBatchBits algorithm bottomViews)
          (supplierCircuitBottomBatchFuel algorithm bottomViews)
          (initialNPOracleState q headerTree) =
        some outputTree := by
    simpa only [headerTree, outputTree] using
      run_supplierCircuitBottomBatchProgram algorithm bottomViews
  have hbottom :
      runNPOracleProgram
          (preserveRightProgram
            (supplierCircuitBottomBatchProgram algorithm))
          maximumBits
          (preserveRightFuel
            (supplierCircuitBottomBatchFuel algorithm bottomViews))
          (initialNPOracleState q (Nat.pair headerTree context)) =
        some (Nat.pair outputTree context) := by
    have hrun :=
      run_preserveRightProgram
        (supplierCircuitBottomBatchProgram algorithm) q
        (supplierCircuitBottomBatchBits algorithm bottomViews)
        (supplierCircuitBottomBatchFuel algorithm bottomViews)
        headerTree context outputTree hbottomSource
    exact run_bits_mono hrun <| by
      simpa only [supplierCircuitEnvelopeBottomPreservingBits,
        headerTree, outputTree, context] using hbottomBits
  have hrun :=
    run_linkPrograms hpositive hqBits henvelopeAtMaximum hbottom
  simpa only [supplierCircuitEnvelopeBottomProgram,
    supplierCircuitEnvelopeBottomFuel,
    supplierCircuitEnvelopeBottomOutput, outputTree, context] using hrun

/-! ## Published canonical Fourfold envelopes -/

theorem run_supplierCircuitEnvelopeBottomProgram_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request :
      FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    let headerViews := symmetricCircuitHeaderViews request
    let bottomViews := symmetricCircuitBottomViews request
    runNPOracleProgram
        (supplierCircuitEnvelopeBottomProgram algorithm)
        (supplierCircuitEnvelopeBottomBits algorithm
          symmetricCircuitFamilyTag request.q headerViews bottomViews)
        (supplierCircuitEnvelopeBottomFuel algorithm
          headerViews bottomViews)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) =
      some
        (supplierCircuitEnvelopeBottomOutput algorithm
          symmetricCircuitFamilyTag request.q bottomViews) := by
  dsimp only
  exact
    run_supplierCircuitEnvelopeBottomProgram_of_run
      algorithm symmetricCircuitFamilyTag request.q
      (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
        encodeNormalizedSymmetricThresholdCircuit request)
      (symmetricCircuitHeaderViews request)
      (symmetricCircuitBottomViews request)
      (symmetricCircuitBottomHeaders request)
      (run_supplierCircuitEnvelopeBatchProgram_symmetric request)

theorem run_supplierCircuitEnvelopeBottomProgram_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request :
      FourfoldRequest NormalizedThresholdThresholdCircuit) :
    let headerViews := thresholdCircuitHeaderViews request
    let bottomViews := thresholdCircuitBottomViews request
    runNPOracleProgram
        (supplierCircuitEnvelopeBottomProgram algorithm)
        (supplierCircuitEnvelopeBottomBits algorithm
          thresholdCircuitFamilyTag request.q headerViews bottomViews)
        (supplierCircuitEnvelopeBottomFuel algorithm
          headerViews bottomViews)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
            encodeNormalizedThresholdThresholdCircuit request)) =
      some
        (supplierCircuitEnvelopeBottomOutput algorithm
          thresholdCircuitFamilyTag request.q bottomViews) := by
  dsimp only
  exact
    run_supplierCircuitEnvelopeBottomProgram_of_run
      algorithm thresholdCircuitFamilyTag request.q
      (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
        encodeNormalizedThresholdThresholdCircuit request)
      (thresholdCircuitHeaderViews request)
      (thresholdCircuitBottomViews request)
      (thresholdCircuitBottomHeaders request)
      (run_supplierCircuitEnvelopeBatchProgram_threshold request)

end NearCubicWires.CanonicalSupplierEnvelopeBottomProgram
