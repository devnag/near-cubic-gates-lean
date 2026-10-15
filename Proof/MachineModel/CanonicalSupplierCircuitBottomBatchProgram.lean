import Proof.MachineModel.CanonicalSupplierCircuitBottomProgram
import Proof.MachineModel.CanonicalSupplierGateBatchProgram
import Proof.Circuits.CanonicalWitnessCodec

namespace NearCubicWires.CanonicalSupplierCircuitBottomBatchProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalSupplierCircuitBottomProgram
open NearCubicWires.CanonicalSupplierCircuitHeaderProgram
open NearCubicWires.CanonicalSupplierGateBatchProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Proof-only typed native-header view -/

private def fallbackSupportedNormalizedGate
    (arity : ℕ) : SupportedNormalizedGate arity where
  gate :=
    { weight := fun _ => 0
      threshold := 0 }
  support := ∅
  zeroOutside := by simp

private def decodeSupportedNormalizedGateTotal
    (arity gateCode : ℕ) : SupportedNormalizedGate arity :=
  (decodeSupportedNormalizedGate arity gateCode).getD <|
    fallbackSupportedNormalizedGate arity

@[simp] private theorem decodeSupportedNormalizedGateTotal_encode
    {arity : ℕ} (gate : SupportedNormalizedGate arity) :
    decodeSupportedNormalizedGateTotal arity
        (encodeSupportedNormalizedGate gate) =
      gate := by
  simp [decodeSupportedNormalizedGateTotal,
    decodeSupportedNormalizedGate_encode]

/-- A Boolean family selector makes the proof view canonical: `false` is mode
zero and `true` is mode one.  The VM receives only `header`. -/
structure SupplierCircuitBottomView (arity : ℕ) where
  thresholdFamily : Bool
  bottomCount : ℕ
  gates : List (SupportedNormalizedGate arity)
  topCode : ℕ

def SupplierCircuitBottomView.familyCode
    {arity : ℕ} (view : SupplierCircuitBottomView arity) : ℕ :=
  if view.thresholdFamily then 1 else 0

def SupplierCircuitBottomView.header
    {arity : ℕ} (view : SupplierCircuitBottomView arity) : ℕ :=
  supplierCircuitHeaderOutput view.familyCode view.bottomCount
    (encodeBalancedList (supplierGateCodes view.gates)) view.topCode

private def SupplierCircuitBottomView.request
    {arity : ℕ} (view : SupplierCircuitBottomView arity) : ℕ :=
  nativeInputRequest arity view.header

def SupplierCircuitBottomView.output
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ} (view : SupplierCircuitBottomView arity) : ℕ :=
  supplierCircuitBottomOutput algorithm view.familyCode
    view.bottomCount view.gates view.topCode

/-- Total projection for proof-level resource certificates.  Malformed
balanced trees or gates map to deterministic defaults; executable state is
always produced by the arity-framing traversal, never by this function. -/
private def decodeSupplierCircuitBottomView
    (arity headerCode : ℕ) : SupplierCircuitBottomView arity :=
  let bottomCount := (Nat.unpair headerCode).1
  let headerContext := (Nat.unpair headerCode).2
  let modeCode := (Nat.unpair headerContext).1
  let bottomTop := (Nat.unpair headerContext).2
  let bottomTree := (Nat.unpair bottomTop).1
  let topCode := (Nat.unpair bottomTop).2
  let gateCodes := (decodeBalancedList bottomTree).getD []
  { thresholdFamily := modeCode != 0
    bottomCount
    gates :=
      gateCodes.map (decodeSupportedNormalizedGateTotal arity)
    topCode }

@[simp] private theorem decodeSupplierCircuitBottomView_header
    {arity : ℕ} (view : SupplierCircuitBottomView arity) :
    decodeSupplierCircuitBottomView arity view.header = view := by
  cases view with
  | mk thresholdFamily bottomCount gates topCode =>
      cases thresholdFamily <;>
        simp [decodeSupplierCircuitBottomView,
          SupplierCircuitBottomView.header,
          SupplierCircuitBottomView.familyCode,
          supplierCircuitHeaderOutput,
          supplierCircuitHeaderContext,
          supplierCircuitMode, supplierGateCodes]
        <;> simp [Function.comp_def]

private def supplierCircuitBottomRequestView
    (arity request : ℕ) : SupplierCircuitBottomView arity :=
  decodeSupplierCircuitBottomView arity (Nat.unpair request).2

private def supplierCircuitBottomCallOutput
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (arity request : ℕ) : ℕ :=
  (supplierCircuitBottomRequestView arity request).output algorithm

private def supplierCircuitBottomCallFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (arity request : ℕ) : ℕ :=
  supplierCircuitBottomFuel algorithm
    (supplierCircuitBottomRequestView arity request).gates

private def supplierCircuitBottomCallBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (arity request : ℕ) : ℕ :=
  let view := supplierCircuitBottomRequestView arity request
  supplierCircuitBottomBits algorithm view.familyCode
    view.bottomCount view.gates view.topCode

@[simp] private theorem supplierCircuitBottomRequestView_request
    {arity : ℕ} (view : SupplierCircuitBottomView arity) :
    supplierCircuitBottomRequestView arity view.request = view := by
  simp [supplierCircuitBottomRequestView,
    SupplierCircuitBottomView.request, nativeInputRequest]

@[simp] private theorem supplierCircuitBottomCallOutput_request
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ} (view : SupplierCircuitBottomView arity) :
    supplierCircuitBottomCallOutput algorithm arity view.request =
      view.output algorithm := by
  simp [supplierCircuitBottomCallOutput]

@[simp] private theorem supplierCircuitBottomCallFuel_request
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ} (view : SupplierCircuitBottomView arity) :
    supplierCircuitBottomCallFuel algorithm arity view.request =
      supplierCircuitBottomFuel algorithm view.gates := by
  simp [supplierCircuitBottomCallFuel]

@[simp] private theorem supplierCircuitBottomCallBits_request
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ} (view : SupplierCircuitBottomView arity) :
    supplierCircuitBottomCallBits algorithm arity view.request =
      supplierCircuitBottomBits algorithm view.familyCode
        view.bottomCount view.gates view.topCode := by
  simp [supplierCircuitBottomCallBits]

def supplierCircuitBottomHeaders
    {arity : ℕ}
    (views : List (SupplierCircuitBottomView arity)) : List ℕ :=
  views.map SupplierCircuitBottomView.header

private def supplierCircuitBottomRequests
    {arity : ℕ}
    (views : List (SupplierCircuitBottomView arity)) : List ℕ :=
  (supplierCircuitBottomHeaders views).map
    (nativeInputRequest arity)

def supplierCircuitBottomOutputs
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (views : List (SupplierCircuitBottomView arity)) : List ℕ :=
  views.map (SupplierCircuitBottomView.output algorithm)

/-! ## Exact balanced call over the native-header forest -/

private def supplierCircuitBottomCallBitsBound
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (views : List (SupplierCircuitBottomView arity)) : ℕ :=
  max (natBitLength arity) <|
    max
      (balancedCallRequiredBits
        (supplierCircuitBottomCallOutput algorithm arity)
        (supplierCircuitBottomRequests views))
      (((supplierCircuitBottomRequests views).map
        (supplierCircuitBottomCallBits algorithm arity)).foldr max 1)

private def supplierCircuitBottomCallFuelBound
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (views : List (SupplierCircuitBottomView arity)) : ℕ :=
  balancedCallFuel (supplierCircuitBottomProgram algorithm)
    (supplierCircuitBottomCallFuel algorithm arity)
    (supplierCircuitBottomRequests views)

private theorem bottomBatch_le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 1 := by
  induction values with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

private theorem supplierCircuitBottomOutputs_eq_map
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (views : List (SupplierCircuitBottomView arity)) :
    (supplierCircuitBottomRequests views).map
        (supplierCircuitBottomCallOutput algorithm arity) =
      supplierCircuitBottomOutputs algorithm views := by
  induction views with
  | nil => rfl
  | cons view views ih =>
      change
        supplierCircuitBottomCallOutput algorithm arity
              (nativeInputRequest arity view.header) ::
            (supplierCircuitBottomRequests views).map
              (supplierCircuitBottomCallOutput algorithm arity) =
          view.output algorithm ::
            supplierCircuitBottomOutputs algorithm views
      rw [show nativeInputRequest arity view.header =
          view.request by rfl]
      rw [supplierCircuitBottomCallOutput_request, ih]

private theorem run_supplierCircuitBottomCallProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (views : List (SupplierCircuitBottomView arity)) :
    runNPOracleProgram
        (balancedCallProgram
          (supplierCircuitBottomProgram algorithm))
        (supplierCircuitBottomCallBitsBound algorithm views)
        (supplierCircuitBottomCallFuelBound algorithm views)
        (initialNPOracleState arity
          (encodeBalancedList
            (supplierCircuitBottomRequests views))) =
      some
        (encodeBalancedList
          (supplierCircuitBottomOutputs algorithm views)) := by
  rw [← supplierCircuitBottomOutputs_eq_map algorithm views]
  apply run_balancedCallProgram_from arity
    (supplierCircuitBottomRequests views)
    (supplierCircuitBottomCallFuel algorithm arity)
    (supplierCircuitBottomCallOutput algorithm arity)
  · exact
      (Nat.le_max_left _ _).trans
        (Nat.le_max_right _ _)
  · intro request hrequest
    have hrequestBits :
        supplierCircuitBottomCallBits algorithm arity request ≤
          supplierCircuitBottomCallBitsBound algorithm views := by
      apply
        (bottomBatch_le_foldr_max_of_mem
          (values :=
            (supplierCircuitBottomRequests views).map
              (supplierCircuitBottomCallBits algorithm arity)) ?_).trans
      · exact
          (Nat.le_max_right _ _).trans
            (Nat.le_max_right _ _)
      · exact List.mem_map.mpr ⟨request, hrequest, rfl⟩
    rcases List.mem_map.mp hrequest with
      ⟨headerCode, hheaderCode, rfl⟩
    rcases List.mem_map.mp hheaderCode with
      ⟨view, _hview, rfl⟩
    change
      runNPOracleProgram (supplierCircuitBottomProgram algorithm)
          (supplierCircuitBottomCallBitsBound algorithm views)
          (supplierCircuitBottomCallFuel algorithm arity view.request)
          (initialNPOracleState (Nat.unpair view.request).1
            (Nat.unpair view.request).2) =
        some
          (supplierCircuitBottomCallOutput algorithm arity
            view.request)
    change
      supplierCircuitBottomCallBits algorithm arity view.request ≤
        supplierCircuitBottomCallBitsBound algorithm views at hrequestBits
    rw [supplierCircuitBottomCallFuel_request,
      supplierCircuitBottomCallOutput_request]
    rw [supplierCircuitBottomCallBits_request] at hrequestBits
    simp only [SupplierCircuitBottomView.request,
      nativeInputRequest, Nat.unpair_pair]
    exact
      run_bits_mono
        (run_supplierCircuitBottomProgram algorithm
          view.familyCode view.bottomCount view.gates view.topCode)
        hrequestBits

/-! ## Native-header forest to exact bottom-decomposition forest -/

def supplierCircuitBottomBatchProgram
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    NPOracleProgram :=
  linkPrograms nativeInputRequestTreeProgram <|
    balancedCallProgram (supplierCircuitBottomProgram algorithm)

def supplierCircuitBottomBatchBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (views : List (SupplierCircuitBottomView arity)) : ℕ :=
  max
    (nativeInputRequestTreeBits arity
      (supplierCircuitBottomHeaders views))
    (supplierCircuitBottomCallBitsBound algorithm views)

def supplierCircuitBottomBatchFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (views : List (SupplierCircuitBottomView arity)) : ℕ :=
  linkFuel
    (balancedCallProgram (supplierCircuitBottomProgram algorithm))
    (nativeInputRequestTreeFuel
      (supplierCircuitBottomHeaders views))
    (supplierCircuitBottomCallFuelBound algorithm views)

@[simp] theorem supplierCircuitBottomBatchProgram_oracleFree
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    OracleFree (supplierCircuitBottomBatchProgram algorithm) := by
  apply oracleFree_linkPrograms
  · exact nativeInputRequestTreeProgram_oracleFree
  · exact balancedCallProgram_oracleFree
      (supplierCircuitBottomProgram_oracleFree algorithm)

theorem run_supplierCircuitBottomBatchProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (views : List (SupplierCircuitBottomView arity)) :
    runNPOracleProgram (supplierCircuitBottomBatchProgram algorithm)
        (supplierCircuitBottomBatchBits algorithm views)
        (supplierCircuitBottomBatchFuel algorithm views)
        (initialNPOracleState arity
          (encodeBalancedList
            (supplierCircuitBottomHeaders views))) =
      some
        (encodeBalancedList
          (supplierCircuitBottomOutputs algorithm views)) := by
  let headerTree :=
    encodeBalancedList (supplierCircuitBottomHeaders views)
  let requestTree :=
    encodeBalancedList (supplierCircuitBottomRequests views)
  let outputTree :=
    encodeBalancedList (supplierCircuitBottomOutputs algorithm views)
  let maximumBits :=
    supplierCircuitBottomBatchBits algorithm views
  have hframingBits :
      nativeInputRequestTreeBits arity
          (supplierCircuitBottomHeaders views) ≤
        maximumBits :=
    Nat.le_max_left _ _
  have hcallBits :
      supplierCircuitBottomCallBitsBound algorithm views ≤
        maximumBits :=
    Nat.le_max_right _ _
  have harityBits : natBitLength arity ≤ maximumBits := by
    exact
      (Nat.le_max_left _ _).trans hframingBits
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength arity by
      unfold natBitLength
      omega).trans harityBits
  have hframing :
      runNPOracleProgram nativeInputRequestTreeProgram maximumBits
          (nativeInputRequestTreeFuel
            (supplierCircuitBottomHeaders views))
          (initialNPOracleState arity headerTree) =
        some requestTree := by
    have hrun :=
      run_bits_mono
        (run_nativeInputRequestTreeProgram arity
          (supplierCircuitBottomHeaders views))
        hframingBits
    simpa only [headerTree, requestTree,
      supplierCircuitBottomRequests] using hrun
  have hcalls :
      runNPOracleProgram
          (balancedCallProgram
            (supplierCircuitBottomProgram algorithm))
          maximumBits
          (supplierCircuitBottomCallFuelBound algorithm views)
          (initialNPOracleState arity requestTree) =
        some outputTree := by
    have hrun :=
      run_bits_mono
        (run_supplierCircuitBottomCallProgram algorithm views)
        hcallBits
    simpa only [requestTree, outputTree] using hrun
  have hrun :=
    run_linkPrograms hpositive harityBits hframing hcalls
  simpa only [supplierCircuitBottomBatchProgram,
    supplierCircuitBottomBatchFuel, headerTree, outputTree] using hrun

end NearCubicWires.CanonicalSupplierCircuitBottomBatchProgram
