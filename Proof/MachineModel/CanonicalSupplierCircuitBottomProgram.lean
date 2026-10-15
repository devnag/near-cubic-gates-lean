import Proof.MachineModel.CanonicalSupplierCircuitHeaderProgram
import Proof.MachineModel.CanonicalSupplierGateBatchProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Canonical supplier single-circuit bottom decomposition

The native circuit header already contains the decoded bottom count, mode,
balanced bottom-gate tree, and top code.  A fixed adapter moves only the bottom
tree to the left of the pair.  The sole gate-batch program then decomposes that
tree while `preserveRightProgram` retains the remaining circuit context.
-/

namespace NearCubicWires.CanonicalSupplierCircuitBottomProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalSupplierCircuitHeaderProgram
open NearCubicWires.CanonicalSupplierGateBatchProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Fixed native-header adapter -/

def supplierCircuitBottomContext
    (bottomCount mode topCode : ℕ) : ℕ :=
  Nat.pair bottomCount (Nat.pair mode topCode)

def supplierCircuitBottomAdapterOutput
    (familyCode bottomCount bottomTree topCode : ℕ) : ℕ :=
  Nat.pair bottomTree <|
    supplierCircuitBottomContext bottomCount
      (supplierCircuitMode familyCode) topCode

/-- Reframe the native header as `pair(bottomTree, retainedContext)`. -/
def supplierCircuitBottomAdapterProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 4 7 8 7
  , .pair 2 8 9 8
  , .pair 6 9 0 9
  , .halt 0
  ]

@[simp] theorem supplierCircuitBottomAdapterProgram_oracleFree :
    OracleFree supplierCircuitBottomAdapterProgram := by
  rfl

def supplierCircuitBottomAdapterFuel : ℕ := 10

def supplierCircuitBottomAdapterBits
    (familyCode bottomCount bottomTree topCode : ℕ) : ℕ :=
  max
    (natBitLength
      (supplierCircuitHeaderOutput familyCode bottomCount
        bottomTree topCode))
    (natBitLength
      (supplierCircuitBottomAdapterOutput familyCode bottomCount
        bottomTree topCode))

theorem run_supplierCircuitBottomAdapterProgram
    (inputLength familyCode bottomCount bottomTree topCode : ℕ) :
    runNPOracleProgram supplierCircuitBottomAdapterProgram
        (supplierCircuitBottomAdapterBits familyCode bottomCount
          bottomTree topCode)
        supplierCircuitBottomAdapterFuel
        (initialNPOracleState inputLength
          (supplierCircuitHeaderOutput familyCode bottomCount
            bottomTree topCode)) =
      some
        (supplierCircuitBottomAdapterOutput familyCode bottomCount
          bottomTree topCode) := by
  let mode := supplierCircuitMode familyCode
  let bottomTop := Nat.pair bottomTree topCode
  let headerContext := Nat.pair mode bottomTop
  let modeTop := Nat.pair mode topCode
  let context := supplierCircuitBottomContext bottomCount mode topCode
  let input :=
    supplierCircuitHeaderOutput familyCode bottomCount bottomTree topCode
  let output :=
    supplierCircuitBottomAdapterOutput familyCode bottomCount
      bottomTree topCode
  let maximumBits :=
    supplierCircuitBottomAdapterBits familyCode bottomCount
      bottomTree topCode
  have hinput : natBitLength input ≤ maximumBits :=
    Nat.le_max_left _ _
  have houtput : natBitLength output ≤ maximumBits :=
    Nat.le_max_right _ _
  have hcount : natBitLength bottomCount ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair bottomCount headerContext)).trans hinput
  have hheader : natBitLength headerContext ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair bottomCount headerContext)).trans hinput
  have hmode : natBitLength mode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair mode bottomTop)).trans hheader
  have hbottomTop : natBitLength bottomTop ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair mode bottomTop)).trans hheader
  have hbottom : natBitLength bottomTree ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair bottomTree topCode)).trans hbottomTop
  have htop : natBitLength topCode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair bottomTree topCode)).trans hbottomTop
  have hcontext : natBitLength context ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans houtput
    exact Nat.right_le_pair bottomTree context
  have hmodeTop : natBitLength modeTop ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hcontext
    exact Nat.right_le_pair bottomCount modeTop
  rw [show supplierCircuitBottomAdapterFuel = 9 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := bottomCount)
    (by rfl) rfl
    (by
      simp [initialNPOracleState,
        supplierCircuitHeaderOutput,
        supplierCircuitHeaderContext])
    hcount]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := headerContext)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, supplierCircuitHeaderOutput,
        supplierCircuitHeaderContext, headerContext, mode,
        bottomTop])
    hheader]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := mode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        headerContext])
    hmode]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := bottomTop)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        headerContext])
    hbottomTop]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := bottomTree)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, bottomTop])
    hbottom]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := topCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, bottomTop])
    htop]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := modeTop)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, modeTop])
    hmodeTop]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := context)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, context,
        supplierCircuitBottomContext, modeTop])
    hcontext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        supplierCircuitBottomAdapterOutput, context, mode])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

/-! ## Header to exact bottom decompositions -/

def supplierCircuitBottomProgram
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    NPOracleProgram :=
  linkPrograms supplierCircuitBottomAdapterProgram <|
    preserveRightProgram (supplierGateBatchProgram algorithm)

def supplierCircuitBottomOutput
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (familyCode bottomCount : ℕ)
    (gates : List (SupportedNormalizedGate arity))
    (topCode : ℕ) : ℕ :=
  Nat.pair
    (encodeBalancedList (supplierGateOutputs algorithm gates))
    (supplierCircuitBottomContext bottomCount
      (supplierCircuitMode familyCode) topCode)

def supplierCircuitBottomPreservingBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (familyCode bottomCount : ℕ)
    (gates : List (SupportedNormalizedGate arity))
    (topCode : ℕ) : ℕ :=
  preserveRightBits
    (supplierGateBatchBits algorithm gates)
    (encodeBalancedList (supplierGateCodes gates))
    (supplierCircuitBottomContext bottomCount
      (supplierCircuitMode familyCode) topCode)
    (encodeBalancedList (supplierGateOutputs algorithm gates))

def supplierCircuitBottomBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (familyCode bottomCount : ℕ)
    (gates : List (SupportedNormalizedGate arity))
    (topCode : ℕ) : ℕ :=
  max (natBitLength arity) <|
    max
      (supplierCircuitBottomAdapterBits familyCode bottomCount
        (encodeBalancedList (supplierGateCodes gates)) topCode)
      (supplierCircuitBottomPreservingBits algorithm familyCode
        bottomCount gates topCode)

def supplierCircuitBottomFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (gates : List (SupportedNormalizedGate arity)) : ℕ :=
  linkFuel
    (preserveRightProgram (supplierGateBatchProgram algorithm))
    supplierCircuitBottomAdapterFuel
    (preserveRightFuel (supplierGateBatchFuel algorithm gates))

@[simp] theorem supplierCircuitBottomProgram_oracleFree
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    OracleFree (supplierCircuitBottomProgram algorithm) := by
  apply oracleFree_linkPrograms
  · exact supplierCircuitBottomAdapterProgram_oracleFree
  · exact preserveRightProgram_oracleFree _
      (supplierGateBatchProgram_oracleFree algorithm)

theorem run_supplierCircuitBottomProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ}
    (familyCode bottomCount : ℕ)
    (gates : List (SupportedNormalizedGate arity))
    (topCode : ℕ) :
    runNPOracleProgram (supplierCircuitBottomProgram algorithm)
        (supplierCircuitBottomBits algorithm familyCode bottomCount
          gates topCode)
        (supplierCircuitBottomFuel algorithm gates)
        (initialNPOracleState arity
          (supplierCircuitHeaderOutput familyCode bottomCount
            (encodeBalancedList (supplierGateCodes gates)) topCode)) =
      some
        (supplierCircuitBottomOutput algorithm familyCode bottomCount
          gates topCode) := by
  let bottomTree :=
    encodeBalancedList (supplierGateCodes gates)
  let decompositionTree :=
    encodeBalancedList (supplierGateOutputs algorithm gates)
  let mode := supplierCircuitMode familyCode
  let context :=
    supplierCircuitBottomContext bottomCount mode topCode
  let adapterOutput := Nat.pair bottomTree context
  let output := Nat.pair decompositionTree context
  let maximumBits :=
    supplierCircuitBottomBits algorithm familyCode bottomCount
      gates topCode
  have harityBits : natBitLength arity ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength arity by
      unfold natBitLength
      omega).trans harityBits
  have hadapterBits :
      supplierCircuitBottomAdapterBits familyCode bottomCount
          bottomTree topCode ≤
        maximumBits := by
    exact
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreservingBits :
      supplierCircuitBottomPreservingBits algorithm familyCode
          bottomCount gates topCode ≤
        maximumBits := by
    exact
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hadapter :
      runNPOracleProgram supplierCircuitBottomAdapterProgram
          maximumBits supplierCircuitBottomAdapterFuel
          (initialNPOracleState arity
            (supplierCircuitHeaderOutput familyCode bottomCount
              bottomTree topCode)) =
        some adapterOutput := by
    have hrun :=
      run_bits_mono
        (run_supplierCircuitBottomAdapterProgram arity familyCode
          bottomCount bottomTree topCode)
        hadapterBits
    simpa only [supplierCircuitBottomAdapterOutput, adapterOutput,
      context, mode] using hrun
  have hbottom :
      runNPOracleProgram
          (preserveRightProgram
            (supplierGateBatchProgram algorithm))
          maximumBits
          (preserveRightFuel
            (supplierGateBatchFuel algorithm gates))
          (initialNPOracleState arity adapterOutput) =
        some output := by
    have hsource :=
      run_supplierGateBatchProgram algorithm gates
    have hrun :=
      run_preserveRightProgram
        (supplierGateBatchProgram algorithm) arity
        (supplierGateBatchBits algorithm gates)
        (supplierGateBatchFuel algorithm gates)
        bottomTree context decompositionTree hsource
    exact run_bits_mono hrun <| by
      simpa only [supplierCircuitBottomPreservingBits,
        bottomTree, decompositionTree, context, mode] using
        hpreservingBits
  have hrun :=
    run_linkPrograms hpositive harityBits hadapter hbottom
  simpa only [supplierCircuitBottomProgram,
    supplierCircuitBottomFuel, supplierCircuitBottomOutput,
    bottomTree, decompositionTree, output, context, mode] using hrun

end NearCubicWires.CanonicalSupplierCircuitBottomProgram
