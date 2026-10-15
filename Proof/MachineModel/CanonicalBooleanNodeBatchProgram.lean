import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalBooleanNodeValidationProgram

namespace NearCubicWires.CanonicalBooleanNodeBatchProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

def booleanNodeCallFuel (request : ℕ) : ℕ :=
  booleanNodeValidationFuel (Nat.unpair request).1 (Nat.unpair request).2

def booleanNodeCallOutput (request : ℕ) : ℕ :=
  booleanNodeStructuralOutput (Nat.unpair request).2

def booleanNodeCallBits (request : ℕ) : ℕ :=
  booleanNodeValidationBits (Nat.unpair request).1 (Nat.unpair request).2

def booleanNodeRequests (inputLength : ℕ) (rawNodes : List ℕ) : List ℕ :=
  rawNodes.map (nativeInputRequest inputLength)

def booleanNodeOutputs (rawNodes : List ℕ) : List ℕ :=
  rawNodes.map booleanNodeStructuralOutput

def booleanNodeCallMaximumBits
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max
      (balancedCallRequiredBits booleanNodeCallOutput
        (booleanNodeRequests inputLength rawNodes))
      (((booleanNodeRequests inputLength rawNodes).map
        booleanNodeCallBits).foldr max 1)

def booleanNodeCallFuelFor
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  balancedCallFuel booleanNodeValidationProgram booleanNodeCallFuel
    (booleanNodeRequests inputLength rawNodes)

private theorem value_le_foldr_max_of_mem
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

private theorem booleanNodeRequests_map_output
    (inputLength : ℕ) (rawNodes : List ℕ) :
    (booleanNodeRequests inputLength rawNodes).map booleanNodeCallOutput =
      booleanNodeOutputs rawNodes := by
  induction rawNodes with
  | nil => rfl
  | cons raw rest ih =>
      simp [booleanNodeRequests, booleanNodeOutputs, booleanNodeCallOutput,
        nativeInputRequest]

theorem run_booleanNodeCallProgram
    (inputLength : ℕ) (rawNodes : List ℕ) :
    runNPOracleProgram (balancedCallProgram booleanNodeValidationProgram)
        (booleanNodeCallMaximumBits inputLength rawNodes)
        (booleanNodeCallFuelFor inputLength rawNodes)
        (initialNPOracleState inputLength
          (encodeBalancedList (booleanNodeRequests inputLength rawNodes))) =
      some (encodeBalancedList (booleanNodeOutputs rawNodes)) := by
  rw [← booleanNodeRequests_map_output inputLength rawNodes]
  apply run_balancedCallProgram_from inputLength
    (booleanNodeRequests inputLength rawNodes)
    booleanNodeCallFuel booleanNodeCallOutput
  · exact
      (Nat.le_max_left _ _).trans
        (Nat.le_max_right _ _)
  · intro request hrequest
    have hrequestBits :
        booleanNodeCallBits request ≤
          booleanNodeCallMaximumBits inputLength rawNodes := by
      apply
        (value_le_foldr_max_of_mem
          (values :=
            (booleanNodeRequests inputLength rawNodes).map
              booleanNodeCallBits) ?_).trans
      · exact
          (Nat.le_max_right _ _).trans
            (Nat.le_max_right _ _)
      · exact List.mem_map.mpr ⟨request, hrequest, rfl⟩
    exact run_bits_mono
      (run_booleanNodeValidationProgram
        (Nat.unpair request).1 (Nat.unpair request).2)
      hrequestBits

def booleanNodeBatchProgram : NPOracleProgram :=
  linkPrograms nativeInputRequestTreeProgram <|
    balancedCallProgram booleanNodeValidationProgram

@[simp] theorem booleanNodeBatchProgram_oracleFree :
    OracleFree booleanNodeBatchProgram := by
  exact oracleFree_linkPrograms
    nativeInputRequestTreeProgram_oracleFree
    (balancedCallProgram_oracleFree booleanNodeValidationProgram_oracleFree)

def booleanNodeBatchBits
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  max
    (nativeInputRequestTreeBits inputLength rawNodes)
    (booleanNodeCallMaximumBits inputLength rawNodes)

def booleanNodeBatchFuel
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  linkFuel (balancedCallProgram booleanNodeValidationProgram)
    (nativeInputRequestTreeFuel rawNodes)
    (booleanNodeCallFuelFor inputLength rawNodes)

theorem run_booleanNodeBatchProgram
    (inputLength : ℕ) (rawNodes : List ℕ) :
    runNPOracleProgram booleanNodeBatchProgram
        (booleanNodeBatchBits inputLength rawNodes)
        (booleanNodeBatchFuel inputLength rawNodes)
        (initialNPOracleState inputLength
          (encodeBalancedList rawNodes)) =
      some (encodeBalancedList (booleanNodeOutputs rawNodes)) := by
  let requestTree :=
    encodeBalancedList (booleanNodeRequests inputLength rawNodes)
  let maximumBits := booleanNodeBatchBits inputLength rawNodes
  have hframingBits :
      nativeInputRequestTreeBits inputLength rawNodes ≤ maximumBits :=
    Nat.le_max_left _ _
  have hcallBits :
      booleanNodeCallMaximumBits inputLength rawNodes ≤ maximumBits :=
    Nat.le_max_right _ _
  have hlength : natBitLength inputLength ≤ maximumBits := by
    exact
      (Nat.le_max_left _ _).trans hframingBits
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hframing :
      runNPOracleProgram nativeInputRequestTreeProgram maximumBits
          (nativeInputRequestTreeFuel rawNodes)
          (initialNPOracleState inputLength (encodeBalancedList rawNodes)) =
        some requestTree := by
    have hrun :=
      run_bits_mono
        (run_nativeInputRequestTreeProgram inputLength rawNodes)
        hframingBits
    simpa [requestTree, booleanNodeRequests] using hrun
  have hcalls :
      runNPOracleProgram
          (balancedCallProgram booleanNodeValidationProgram)
          maximumBits
          (booleanNodeCallFuelFor inputLength rawNodes)
          (initialNPOracleState inputLength requestTree) =
        some (encodeBalancedList (booleanNodeOutputs rawNodes)) := by
    exact run_bits_mono
      (run_booleanNodeCallProgram inputLength rawNodes)
      hcallBits
  have hrun :=
    run_linkPrograms hpositive hlength hframing hcalls
  simpa [booleanNodeBatchProgram, booleanNodeBatchFuel] using hrun

end NearCubicWires.CanonicalBooleanNodeBatchProgram
