import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalSupplierCompressedGateProgram
import Proof.Circuits.CanonicalWitnessCodec

namespace NearCubicWires.CanonicalSupplierGateBatchProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalSupplierCompressedGateProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Exact decomposition call over the framed tree -/

def decodeNativeArityGateRequest
    (arity request : ℕ) : Option (SupportedNormalizedGate arity) :=
  decodeSupportedNormalizedGate arity (Nat.unpair request).2

@[simp] theorem decodeNativeArityGateRequest_request
    {arity : ℕ} (gate : SupportedNormalizedGate arity) :
    decodeNativeArityGateRequest arity
        (nativeInputRequest arity
          (encodeSupportedNormalizedGate gate)) =
      some gate := by
  simpa [decodeNativeArityGateRequest, nativeInputRequest] using
    decodeSupportedNormalizedGate_encode gate

def supplierGateDecompositionOutput
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ} (gate : SupportedNormalizedGate arity) : ℕ :=
  supplierCompressedGateOutput algorithm gate

def supplierGateCallOutput
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (arity request : ℕ) : ℕ :=
  match decodeNativeArityGateRequest arity request with
  | some gate => supplierGateDecompositionOutput algorithm gate
  | none => 0

def supplierGateCallFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (arity request : ℕ) : ℕ :=
  match decodeNativeArityGateRequest arity request with
  | some gate => supplierCompressedGateFuel algorithm gate
  | none =>
      supplierCompressedGateRejectFuel algorithm arity
        (Nat.unpair request).2

def supplierGateCallBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (arity request : ℕ) : ℕ :=
  match decodeNativeArityGateRequest arity request with
  | some gate => supplierCompressedGateBits algorithm gate
  | none =>
      supplierCompressedGateRejectBits arity (Nat.unpair request).2

@[simp] theorem supplierGateCallOutput_request
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ} (gate : SupportedNormalizedGate arity) :
    supplierGateCallOutput algorithm arity
        (nativeInputRequest arity
          (encodeSupportedNormalizedGate gate)) =
      supplierGateDecompositionOutput algorithm gate := by
  simp [supplierGateCallOutput]

@[simp] theorem supplierGateCallFuel_request
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ} (gate : SupportedNormalizedGate arity) :
    supplierGateCallFuel algorithm arity
        (nativeInputRequest arity
          (encodeSupportedNormalizedGate gate)) =
      supplierCompressedGateFuel algorithm gate := by
  simp [supplierGateCallFuel]

@[simp] theorem supplierGateCallBits_request
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ} (gate : SupportedNormalizedGate arity) :
    supplierGateCallBits algorithm arity
        (nativeInputRequest arity
          (encodeSupportedNormalizedGate gate)) =
      supplierCompressedGateBits algorithm gate := by
  simp [supplierGateCallBits]

def supplierGateCodes {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) : List ℕ :=
  gates.map encodeSupportedNormalizedGate

def supplierGateRequests {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) : List ℕ :=
  gates.map fun gate =>
    nativeInputRequest arity (encodeSupportedNormalizedGate gate)

def supplierGateOutputs
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) : List ℕ :=
  gates.map (supplierGateDecompositionOutput algorithm)

def supplierGateDecompositionCallBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) : ℕ :=
  max (natBitLength arity) <|
    max
      (balancedCallRequiredBits
        (supplierGateCallOutput algorithm arity)
        (supplierGateRequests gates))
      (((supplierGateRequests gates).map
        (supplierGateCallBits algorithm arity)).foldr max 1)

def supplierGateDecompositionCallFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) : ℕ :=
  balancedCallFuel (supplierCompressedGateProgram algorithm)
    (supplierGateCallFuel algorithm arity)
    (supplierGateRequests gates)

private theorem gateBatch_le_foldr_max_of_mem
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

private theorem supplierGateOutputs_eq_map
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) :
    (supplierGateRequests gates).map
        (supplierGateCallOutput algorithm arity) =
      supplierGateOutputs algorithm gates := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      change
        supplierGateCallOutput algorithm arity
              (nativeInputRequest arity
                (encodeSupportedNormalizedGate gate)) ::
            (supplierGateRequests gates).map
              (supplierGateCallOutput algorithm arity) =
          supplierGateDecompositionOutput algorithm gate ::
            supplierGateOutputs algorithm gates
      rw [supplierGateCallOutput_request, ih]

theorem run_supplierGateDecompositionCallProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) :
    runNPOracleProgram
        (balancedCallProgram
          (supplierCompressedGateProgram algorithm))
        (supplierGateDecompositionCallBits algorithm gates)
        (supplierGateDecompositionCallFuel algorithm gates)
        (initialNPOracleState arity
          (encodeBalancedList (supplierGateRequests gates))) =
      some (encodeBalancedList (supplierGateOutputs algorithm gates)) := by
  rw [← supplierGateOutputs_eq_map algorithm gates]
  apply run_balancedCallProgram_from arity
    (supplierGateRequests gates)
    (supplierGateCallFuel algorithm arity)
    (supplierGateCallOutput algorithm arity)
  · exact
      (Nat.le_max_left _ _).trans
        (Nat.le_max_right _ _)
  · intro request hrequest
    have hrequestBits :
        supplierGateCallBits algorithm arity request ≤
          supplierGateDecompositionCallBits algorithm gates := by
      apply
        (gateBatch_le_foldr_max_of_mem
          (values :=
            (supplierGateRequests gates).map
              (supplierGateCallBits algorithm arity)) ?_).trans
      · exact
          (Nat.le_max_right _ _).trans
            (Nat.le_max_right _ _)
      · exact List.mem_map.mpr ⟨request, hrequest, rfl⟩
    rcases List.mem_map.mp hrequest with
      ⟨gate, _hgate, rfl⟩
    rw [supplierGateCallBits_request] at hrequestBits
    have hrun :=
      run_bits_mono
        (run_supplierCompressedGateProgram algorithm gate)
        hrequestBits
    rw [supplierGateCallFuel_request, supplierGateCallOutput_request]
    simp only [nativeInputRequest, Nat.unpair_pair]
    exact hrun

/-! ## Raw balanced gate tree to decomposed balanced gate tree -/

def supplierGateBatchProgram
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    NPOracleProgram :=
  linkPrograms nativeInputRequestTreeProgram <|
    balancedCallProgram (supplierCompressedGateProgram algorithm)

def supplierGateBatchBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) : ℕ :=
  max
    (nativeInputRequestTreeBits arity (supplierGateCodes gates))
    (supplierGateDecompositionCallBits algorithm gates)

def supplierGateBatchFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) : ℕ :=
  linkFuel
    (balancedCallProgram (supplierCompressedGateProgram algorithm))
    (nativeInputRequestTreeFuel (supplierGateCodes gates))
    (supplierGateDecompositionCallFuel algorithm gates)

private theorem supplierGateCodes_map_request
    {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) :
    (supplierGateCodes gates).map (nativeInputRequest arity) =
      supplierGateRequests gates := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      change
        nativeInputRequest arity
              (encodeSupportedNormalizedGate gate) ::
            (supplierGateCodes gates).map
              (nativeInputRequest arity) =
          nativeInputRequest arity
              (encodeSupportedNormalizedGate gate) ::
            supplierGateRequests gates
      rw [ih]

@[simp] theorem supplierGateBatchProgram_oracleFree
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    OracleFree (supplierGateBatchProgram algorithm) := by
  apply oracleFree_linkPrograms
  · exact nativeInputRequestTreeProgram_oracleFree
  · exact balancedCallProgram_oracleFree
      (supplierCompressedGateProgram_oracleFree algorithm)

theorem run_supplierGateBatchProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) :
    runNPOracleProgram (supplierGateBatchProgram algorithm)
        (supplierGateBatchBits algorithm gates)
        (supplierGateBatchFuel algorithm gates)
        (initialNPOracleState arity
          (encodeBalancedList (supplierGateCodes gates))) =
      some
        (encodeBalancedList
          (supplierGateOutputs algorithm gates)) := by
  let rawTree := encodeBalancedList (supplierGateCodes gates)
  let requestTree := encodeBalancedList (supplierGateRequests gates)
  let outputTree :=
    encodeBalancedList (supplierGateOutputs algorithm gates)
  let maximumBits := supplierGateBatchBits algorithm gates
  have hframingBits :
      nativeInputRequestTreeBits arity (supplierGateCodes gates) ≤
        maximumBits :=
    Nat.le_max_left _ _
  have hcallBits :
      supplierGateDecompositionCallBits algorithm gates ≤
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
          (nativeInputRequestTreeFuel (supplierGateCodes gates))
          (initialNPOracleState arity rawTree) =
        some requestTree := by
    have hrun :=
      run_bits_mono
        (run_nativeInputRequestTreeProgram arity
          (supplierGateCodes gates))
        hframingBits
    dsimp only [rawTree, requestTree]
    rw [← supplierGateCodes_map_request]
    exact hrun
  have hcalls :
      runNPOracleProgram
          (balancedCallProgram
            (supplierCompressedGateProgram algorithm))
          maximumBits
          (supplierGateDecompositionCallFuel algorithm gates)
          (initialNPOracleState arity requestTree) =
        some outputTree := by
    have hrun :=
      run_bits_mono
        (run_supplierGateDecompositionCallProgram algorithm gates)
        hcallBits
    simpa only [requestTree, outputTree] using hrun
  have hrun :=
    run_linkPrograms hpositive harityBits hframing hcalls
  simpa only [supplierGateBatchProgram, supplierGateBatchFuel,
    rawTree, outputTree] using hrun

end NearCubicWires.CanonicalSupplierGateBatchProgram
