import Batteries.Tactic.OpenPrivate
import Proof.MachineModel.CanonicalBooleanNodeListRebuildProgram
import Proof.MachineModel.CanonicalTaggedNatListRebuildProgram

/-!
# The preparation fork, rebuilt on the indexed tagged spine

`ValidatorRebuildWidthLedger` §5 isolates `booleanNodeListPrepareBits` as the
single residual stage of the rebuilt node-list validator, and walks it down to

> `booleanCircuitPreparationBits`, which forks a balanced length count against
> `booleanNodeBatchBits` — a counted call that charges
> `booleanNodeValidationBits` once per descriptor, and each of those charges
> `taggedNatListValidationBits`.

`CanonicalTaggedNatListRebuildProgram` replaces the bottom of that chain at an
unchanged output contract.  This module is the frozen linking with the callee
swapped, one stage at a time, exactly as
`CanonicalBooleanNodeListRebuildProgram` did for the normalization fork: every
stage above the swap is stated at the *value* the swapped callee returns, so
each linking proof replays verbatim.

* §1 the node validator, rebuilt.

* §2 the node batch, rebuilt.

* §3 the preparation fork, rebuilt.

* §4 the node-list preparation stage, rebuilt.

* §5 the node-list validator over **both** repairs — the normalization fork of
  `CanonicalBooleanNodeListRebuildProgram` and the preparation fork of §4.
-/

namespace NearCubicWires.CanonicalBooleanNodePrepareRebuildProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeListRebuildProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalTaggedNatListRebuildProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

open private booleanNodeStructuralDescriptorProgram
  booleanNodeStructuralDescriptorProgram_oracleFree
  booleanNodeStructuralDescriptorFuel booleanNodeStructuralDescriptorBits
  run_booleanNodeStructuralDescriptorProgram from
  Proof.MachineModel.CanonicalBooleanNodeValidationProgram

open private booleanNodeRequests_map_output from
  Proof.MachineModel.CanonicalBooleanNodeBatchProgram

private theorem le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 1 := by
  induction values with
  | nil => simp at hmem
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmem).trans (Nat.le_max_right _ _)

/-! ## §1 The node validator, rebuilt -/

/-- **The raw-node validator, over the indexed tagged spine.**  The structural
postprocessor is stated at the tagged-nat validator's *value*, so it reuses
verbatim. -/
def booleanNodeValidationRebuildProgram : NPOracleProgram :=
  linkPrograms taggedNatListValidationRebuildProgram
    booleanNodeStructuralDescriptorProgram

@[simp] theorem booleanNodeValidationRebuildProgram_oracleFree :
    OracleFree booleanNodeValidationRebuildProgram :=
  oracleFree_linkPrograms taggedNatListValidationRebuildProgram_oracleFree
    booleanNodeStructuralDescriptorProgram_oracleFree

def booleanNodeValidationRebuildFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel booleanNodeStructuralDescriptorProgram
    (taggedNatListValidationRebuildFuel inputLength raw)
    booleanNodeStructuralDescriptorFuel

def booleanNodeValidationRebuildBits (inputLength raw : ℕ) : ℕ :=
  max (taggedNatListValidationRebuildBits inputLength raw)
    (booleanNodeStructuralDescriptorBits inputLength
      (taggedNatListValidationOutput raw))

/-- **The rebuilt node validator returns the published descriptor.**  Output
contract unchanged from `run_booleanNodeValidationProgram`. -/
theorem run_booleanNodeValidationRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeValidationRebuildProgram
        (booleanNodeValidationRebuildBits inputLength raw)
        (booleanNodeValidationRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (booleanNodeStructuralOutput raw) := by
  let maximumBits := booleanNodeValidationRebuildBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    refine (?_ : 1 ≤ taggedNatListValidationRebuildBits inputLength raw).trans
      (Nat.le_max_left _ _)
    exact taggedNatListValidationRebuildBits_of_mem
      (by simp [taggedNatListValidationRebuildStageBits])
  have hlength : natBitLength inputLength ≤ maximumBits := by
    refine (?_ : natBitLength inputLength ≤
      taggedNatListValidationRebuildBits inputLength raw).trans
        (Nat.le_max_left _ _)
    exact taggedNatListValidationRebuildBits_of_mem
      (by simp [taggedNatListValidationRebuildStageBits])
  have hmapper :
      runNPOracleProgram taggedNatListValidationRebuildProgram maximumBits
          (taggedNatListValidationRebuildFuel inputLength raw)
          (initialNPOracleState inputLength raw) =
        some (taggedNatListValidationOutput raw) :=
    run_bits_mono (run_taggedNatListValidationRebuildProgram inputLength raw)
      (Nat.le_max_left _ _)
  have hdescriptor :
      runNPOracleProgram booleanNodeStructuralDescriptorProgram maximumBits
          booleanNodeStructuralDescriptorFuel
          (initialNPOracleState inputLength
            (taggedNatListValidationOutput raw)) =
        some (booleanNodeStructuralOutput raw) :=
    run_bits_mono
      (run_booleanNodeStructuralDescriptorProgram inputLength
        (taggedNatFieldOutputs raw))
      (Nat.le_max_right _ _)
  exact run_linkPrograms hpositive hlength hmapper hdescriptor

/-! ## §2 The node batch, rebuilt -/

def booleanNodeCallRebuildFuel (request : ℕ) : ℕ :=
  booleanNodeValidationRebuildFuel (Nat.unpair request).1
    (Nat.unpair request).2

def booleanNodeCallRebuildBits (request : ℕ) : ℕ :=
  booleanNodeValidationRebuildBits (Nat.unpair request).1
    (Nat.unpair request).2

def booleanNodeCallRebuildMaximumBits
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max
      (balancedCallRequiredBits booleanNodeCallOutput
        (booleanNodeRequests inputLength rawNodes))
      (((booleanNodeRequests inputLength rawNodes).map
        booleanNodeCallRebuildBits).foldr max 1)

def booleanNodeCallRebuildFuelFor
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  balancedCallFuel booleanNodeValidationRebuildProgram booleanNodeCallRebuildFuel
    (booleanNodeRequests inputLength rawNodes)

theorem run_booleanNodeCallRebuildProgram
    (inputLength : ℕ) (rawNodes : List ℕ) :
    runNPOracleProgram (balancedCallProgram booleanNodeValidationRebuildProgram)
        (booleanNodeCallRebuildMaximumBits inputLength rawNodes)
        (booleanNodeCallRebuildFuelFor inputLength rawNodes)
        (initialNPOracleState inputLength
          (encodeBalancedList (booleanNodeRequests inputLength rawNodes))) =
      some (encodeBalancedList (booleanNodeOutputs rawNodes)) := by
  rw [← booleanNodeRequests_map_output inputLength rawNodes]
  apply run_balancedCallProgram_from inputLength
    (booleanNodeRequests inputLength rawNodes)
    booleanNodeCallRebuildFuel booleanNodeCallOutput
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  · intro request hrequest
    have hrequestBits :
        booleanNodeCallRebuildBits request ≤
          booleanNodeCallRebuildMaximumBits inputLength rawNodes := by
      apply
        (le_foldr_max_of_mem
          (values :=
            (booleanNodeRequests inputLength rawNodes).map
              booleanNodeCallRebuildBits) ?_).trans
      · exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
      · exact List.mem_map.mpr ⟨request, hrequest, rfl⟩
    exact run_bits_mono
      (run_booleanNodeValidationRebuildProgram (Nat.unpair request).1
        (Nat.unpair request).2)
      hrequestBits

/-- **The node batch, over the rebuilt node validator.** -/
def booleanNodeBatchRebuildProgram : NPOracleProgram :=
  linkPrograms nativeInputRequestTreeProgram <|
    balancedCallProgram booleanNodeValidationRebuildProgram

@[simp] theorem booleanNodeBatchRebuildProgram_oracleFree :
    OracleFree booleanNodeBatchRebuildProgram :=
  oracleFree_linkPrograms nativeInputRequestTreeProgram_oracleFree
    (balancedCallProgram_oracleFree booleanNodeValidationRebuildProgram_oracleFree)

def booleanNodeBatchRebuildBits
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  max (nativeInputRequestTreeBits inputLength rawNodes)
    (booleanNodeCallRebuildMaximumBits inputLength rawNodes)

def booleanNodeBatchRebuildFuel
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  linkFuel (balancedCallProgram booleanNodeValidationRebuildProgram)
    (nativeInputRequestTreeFuel rawNodes)
    (booleanNodeCallRebuildFuelFor inputLength rawNodes)

/-- **The rebuilt batch returns the published descriptor list.** -/
theorem run_booleanNodeBatchRebuildProgram
    (inputLength : ℕ) (rawNodes : List ℕ) :
    runNPOracleProgram booleanNodeBatchRebuildProgram
        (booleanNodeBatchRebuildBits inputLength rawNodes)
        (booleanNodeBatchRebuildFuel inputLength rawNodes)
        (initialNPOracleState inputLength (encodeBalancedList rawNodes)) =
      some (encodeBalancedList (booleanNodeOutputs rawNodes)) := by
  let requestTree :=
    encodeBalancedList (booleanNodeRequests inputLength rawNodes)
  let maximumBits := booleanNodeBatchRebuildBits inputLength rawNodes
  have hframingBits :
      nativeInputRequestTreeBits inputLength rawNodes ≤ maximumBits :=
    Nat.le_max_left _ _
  have hcallBits :
      booleanNodeCallRebuildMaximumBits inputLength rawNodes ≤ maximumBits :=
    Nat.le_max_right _ _
  have hlength : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hframingBits
  have hpositive : 1 ≤ maximumBits := by
    refine (?_ : 1 ≤ natBitLength inputLength).trans hlength
    unfold natBitLength
    omega
  have hframing :
      runNPOracleProgram nativeInputRequestTreeProgram maximumBits
          (nativeInputRequestTreeFuel rawNodes)
          (initialNPOracleState inputLength (encodeBalancedList rawNodes)) =
        some requestTree := by
    have hrun :=
      run_bits_mono (run_nativeInputRequestTreeProgram inputLength rawNodes)
        hframingBits
    simpa [requestTree, booleanNodeRequests] using hrun
  have hcalls :
      runNPOracleProgram
          (balancedCallProgram booleanNodeValidationRebuildProgram) maximumBits
          (booleanNodeCallRebuildFuelFor inputLength rawNodes)
          (initialNPOracleState inputLength requestTree) =
        some (encodeBalancedList (booleanNodeOutputs rawNodes)) :=
    run_bits_mono (run_booleanNodeCallRebuildProgram inputLength rawNodes)
      hcallBits
  have hrun := run_linkPrograms hpositive hlength hframing hcalls
  simpa [booleanNodeBatchRebuildProgram, booleanNodeBatchRebuildFuel] using hrun

/-! ## §3 The preparation fork, rebuilt -/

/-- **The circuit preparation fork, over the rebuilt batch.**  The balanced
length count is untouched. -/
def booleanCircuitPreparationRebuildProgram : NPOracleProgram :=
  forkCallProgram balancedLengthProgram booleanNodeBatchRebuildProgram

@[simp] theorem booleanCircuitPreparationRebuildProgram_oracleFree :
    OracleFree booleanCircuitPreparationRebuildProgram :=
  forkCallProgram_oracleFree balancedLengthProgram booleanNodeBatchRebuildProgram
    balancedLengthProgram_oracleFree booleanNodeBatchRebuildProgram_oracleFree

def booleanCircuitPreparationRebuildBits
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  forkCallBits inputLength (encodeBalancedList rawNodes)
    (balancedLengthBits inputLength rawNodes)
    (booleanNodeBatchRebuildBits inputLength rawNodes)
    rawNodes.length
    (encodeBalancedList (booleanNodeOutputs rawNodes))

def booleanCircuitPreparationRebuildFuel
    (inputLength : ℕ) (rawNodes : List ℕ) : ℕ :=
  forkCallFuel balancedLengthProgram booleanNodeBatchRebuildProgram
    (balancedLengthFuel rawNodes)
    (booleanNodeBatchRebuildFuel inputLength rawNodes)

/-- **The rebuilt preparation fork returns the published pair.** -/
theorem run_booleanCircuitPreparationRebuildProgram
    (inputLength : ℕ) (rawNodes : List ℕ) :
    runNPOracleProgram booleanCircuitPreparationRebuildProgram
        (booleanCircuitPreparationRebuildBits inputLength rawNodes)
        (booleanCircuitPreparationRebuildFuel inputLength rawNodes)
        (initialNPOracleState inputLength (encodeBalancedList rawNodes)) =
      some (booleanCircuitPreparationOutput rawNodes) :=
  run_forkCallProgram balancedLengthProgram booleanNodeBatchRebuildProgram
    inputLength (encodeBalancedList rawNodes)
    (balancedLengthBits inputLength rawNodes)
    (booleanNodeBatchRebuildBits inputLength rawNodes)
    (balancedLengthFuel rawNodes)
    (booleanNodeBatchRebuildFuel inputLength rawNodes)
    rawNodes.length
    (encodeBalancedList (booleanNodeOutputs rawNodes))
    (run_balancedLengthProgram inputLength rawNodes)
    (run_booleanNodeBatchRebuildProgram inputLength rawNodes)

/-! ## §4 The node-list preparation stage, rebuilt -/

/-- **The node-list preparation stage, over the rebuilt fork.** -/
def booleanNodeListPrepareRebuildProgram : NPOracleProgram :=
  linkPrograms swapPairProgram <|
    preserveRightProgram booleanCircuitPreparationRebuildProgram

@[simp] theorem booleanNodeListPrepareRebuildProgram_oracleFree :
    OracleFree booleanNodeListPrepareRebuildProgram :=
  oracleFree_linkPrograms swapPairProgram_oracleFree <|
    preserveRightProgram_oracleFree booleanCircuitPreparationRebuildProgram
      booleanCircuitPreparationRebuildProgram_oracleFree

def booleanNodeListPrepareRebuildFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel (preserveRightProgram booleanCircuitPreparationRebuildProgram) 4 <|
    preserveRightFuel
      (booleanCircuitPreparationRebuildFuel inputLength
        (booleanNodeListAtoms raw))

/-- **The rebuilt preparation charge.**  Exactly `booleanNodeListPrepareBits`
with the fork's entry replaced. -/
def booleanNodeListPrepareRebuildBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max
      (swapPairBits (balancedCanonicalityOutput raw)
        (booleanNodeListNormalizedCode raw)) <|
      preserveRightBits
        (booleanCircuitPreparationRebuildBits inputLength
          (booleanNodeListAtoms raw))
        (booleanNodeListNormalizedCode raw) (balancedCanonicalityOutput raw)
        (booleanNodeListPreparationOutput raw)

/-- **The rebuilt preparation stage returns the published pair.**  Output
contract unchanged from `run_booleanNodeListPrepareProgram`. -/
theorem run_booleanNodeListPrepareRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListPrepareRebuildProgram
        (booleanNodeListPrepareRebuildBits inputLength raw)
        (booleanNodeListPrepareRebuildFuel inputLength raw)
        (initialNPOracleState inputLength
          (Nat.pair (balancedCanonicalityOutput raw)
            (booleanNodeListNormalizedCode raw))) =
      some
        (Nat.pair (booleanNodeListPreparationOutput raw)
          (balancedCanonicalityOutput raw)) := by
  let flag := balancedCanonicalityOutput raw
  let normalized := booleanNodeListNormalizedCode raw
  let prepared := booleanNodeListPreparationOutput raw
  let maximumBits := booleanNodeListPrepareRebuildBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, booleanNodeListPrepareRebuildBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, booleanNodeListPrepareRebuildBits]
  have hswap : swapPairBits flag normalized ≤ maximumBits := by
    simp [maximumBits, booleanNodeListPrepareRebuildBits, flag, normalized]
  have hprepare :
      preserveRightBits
          (booleanCircuitPreparationRebuildBits inputLength
            (booleanNodeListAtoms raw))
          normalized flag prepared ≤ maximumBits := by
    simp [maximumBits, booleanNodeListPrepareRebuildBits, flag, normalized,
      prepared]
  have hfirst :
      runNPOracleProgram swapPairProgram maximumBits 4
          (initialNPOracleState inputLength (Nat.pair flag normalized)) =
        some (Nat.pair normalized flag) :=
    run_bits_mono (run_swapPairProgram inputLength flag normalized) hswap
  have hsecond :
      runNPOracleProgram
          (preserveRightProgram booleanCircuitPreparationRebuildProgram)
          maximumBits
          (preserveRightFuel
            (booleanCircuitPreparationRebuildFuel inputLength
              (booleanNodeListAtoms raw)))
          (initialNPOracleState inputLength (Nat.pair normalized flag)) =
        some (Nat.pair prepared flag) := by
    have hrun :=
      run_preserveRightProgram booleanCircuitPreparationRebuildProgram
        inputLength
        (booleanCircuitPreparationRebuildBits inputLength
          (booleanNodeListAtoms raw))
        (booleanCircuitPreparationRebuildFuel inputLength
          (booleanNodeListAtoms raw))
        normalized flag prepared
        (by
          simpa [normalized, prepared, booleanNodeListNormalizedCode,
            booleanNodeListPreparationOutput] using
            run_booleanCircuitPreparationRebuildProgram inputLength
              (booleanNodeListAtoms raw))
    exact run_bits_mono hrun hprepare
  simpa [booleanNodeListPrepareRebuildProgram,
    booleanNodeListPrepareRebuildFuel, flag, normalized, prepared] using
    run_linkPrograms hpositive hlength hfirst hsecond

/-! ## §5 The node-list validator over both repairs -/

/-- **The public node-list validator, over the rebuilt seam and the rebuilt
preparation fork.**  Two of the seven stages change; the other five are stated
at the same values, so they reuse verbatim. -/
def booleanNodeListValidationPrepareRebuildProgram : NPOracleProgram :=
  linkPrograms booleanNodeListNormalizeRebuildProgram <|
    linkPrograms booleanNodeListPrepareRebuildProgram <|
      linkPrograms booleanNodeListRangeLoweringProgram <|
        linkPrograms booleanNodeListTopologyProgram <|
          linkPrograms booleanNodeListTopologyEqualityLoweringProgram <|
            linkPrograms booleanNodeListTopologyEqualityProgram
              booleanNodeListValidationGateProgram

@[simp] theorem booleanNodeListValidationPrepareRebuildProgram_oracleFree :
    OracleFree booleanNodeListValidationPrepareRebuildProgram :=
  oracleFree_linkPrograms booleanNodeListNormalizeRebuildProgram_oracleFree <|
    oracleFree_linkPrograms booleanNodeListPrepareRebuildProgram_oracleFree <|
      oracleFree_linkPrograms
        booleanNodeListRangeLoweringProgram_oracleFree <|
        oracleFree_linkPrograms booleanNodeListTopologyProgram_oracleFree <|
          oracleFree_linkPrograms
            booleanNodeListTopologyEqualityLoweringProgram_oracleFree <|
            oracleFree_linkPrograms
              booleanNodeListTopologyEqualityProgram_oracleFree
              booleanNodeListValidationGateProgram_oracleFree

def booleanNodeListValidationPrepareRebuildFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel
      (linkPrograms booleanNodeListPrepareRebuildProgram <|
        linkPrograms booleanNodeListRangeLoweringProgram <|
          linkPrograms booleanNodeListTopologyProgram <|
            linkPrograms
              booleanNodeListTopologyEqualityLoweringProgram <|
              linkPrograms booleanNodeListTopologyEqualityProgram
                booleanNodeListValidationGateProgram)
      (booleanNodeListNormalizeRebuildFuel inputLength raw) <|
    linkFuel
        (linkPrograms booleanNodeListRangeLoweringProgram <|
          linkPrograms booleanNodeListTopologyProgram <|
            linkPrograms
              booleanNodeListTopologyEqualityLoweringProgram <|
              linkPrograms booleanNodeListTopologyEqualityProgram
                booleanNodeListValidationGateProgram)
        (booleanNodeListPrepareRebuildFuel inputLength raw) <|
      linkFuel
          (linkPrograms booleanNodeListTopologyProgram <|
            linkPrograms
              booleanNodeListTopologyEqualityLoweringProgram <|
              linkPrograms booleanNodeListTopologyEqualityProgram
                booleanNodeListValidationGateProgram)
          booleanNodeListRangeLoweringFuel <|
        linkFuel
            (linkPrograms
              booleanNodeListTopologyEqualityLoweringProgram <|
              linkPrograms booleanNodeListTopologyEqualityProgram
                booleanNodeListValidationGateProgram)
            (booleanNodeListTopologyFuel inputLength raw) <|
          linkFuel
              (linkPrograms booleanNodeListTopologyEqualityProgram
                booleanNodeListValidationGateProgram)
              booleanNodeListTopologyEqualityLoweringFuel <|
            linkFuel booleanNodeListValidationGateProgram
              (booleanNodeListTopologyEqualityFuel inputLength raw)
              booleanNodeListValidationGateFuel

/-- **The doubly rebuilt node-list charge.**  Exactly
`booleanNodeListValidationRebuildBits` with its *preparation* entry replaced as
well; the five remaining entries are the frozen ones. -/
def booleanNodeListValidationPrepareRebuildBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (booleanNodeListNormalizeRebuildBits inputLength raw) <|
      max (booleanNodeListPrepareRebuildBits inputLength raw) <|
        max (booleanNodeListRangeLoweringBits inputLength raw) <|
          max (booleanNodeListTopologyBits inputLength raw) <|
            max
              (booleanNodeListTopologyEqualityLoweringBits
                inputLength raw) <|
              max (booleanNodeListTopologyEqualityBits inputLength raw)
                (booleanNodeListValidationGateBits inputLength raw)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
-- The proof links two rebuilt stages to five frozen runners at the same values.
/-- **The doubly rebuilt node-list validator returns the published verdict.**
Output contract unchanged from `run_booleanNodeListValidationProgram`. -/
theorem run_booleanNodeListValidationPrepareRebuildProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListValidationPrepareRebuildProgram
        (booleanNodeListValidationPrepareRebuildBits inputLength raw)
        (booleanNodeListValidationPrepareRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (booleanNodeListValidationOutput inputLength raw) := by
  let maximumBits := booleanNodeListValidationPrepareRebuildBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationPrepareRebuildBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationPrepareRebuildBits]
  have hnormalizeBits :
      booleanNodeListNormalizeRebuildBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationPrepareRebuildBits]
  have hprepareBits :
      booleanNodeListPrepareRebuildBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationPrepareRebuildBits]
  have hloweringBits :
      booleanNodeListRangeLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationPrepareRebuildBits]
  have htopologyBits :
      booleanNodeListTopologyBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationPrepareRebuildBits]
  have hequalityLoweringBits :
      booleanNodeListTopologyEqualityLoweringBits inputLength raw ≤
        maximumBits := by
    simp [maximumBits, booleanNodeListValidationPrepareRebuildBits]
  have hequalityBits :
      booleanNodeListTopologyEqualityBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationPrepareRebuildBits]
  have hgateBits :
      booleanNodeListValidationGateBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationPrepareRebuildBits]
  have hnormalize :=
    run_bits_mono
      (run_booleanNodeListNormalizeRebuildProgram inputLength raw)
      hnormalizeBits
  have hprepare :=
    run_bits_mono
      (run_booleanNodeListPrepareRebuildProgram inputLength raw) hprepareBits
  have hlowering :=
    run_bits_mono
      (run_booleanNodeListRangeLoweringProgram inputLength raw) hloweringBits
  have htopology :=
    run_bits_mono
      (run_booleanNodeListTopologyProgram inputLength raw) htopologyBits
  have hequalityLowering :=
    run_bits_mono
      (run_booleanNodeListTopologyEqualityLoweringProgram inputLength raw)
      hequalityLoweringBits
  have hequality :=
    run_bits_mono
      (run_booleanNodeListTopologyEqualityProgram inputLength raw)
      hequalityBits
  have hgate :=
    run_bits_mono
      (run_booleanNodeListValidationGateProgram inputLength raw) hgateBits
  have hequalityTail :=
    run_linkPrograms hpositive hlength hequality hgate
  have hequalityLoweringTail :=
    run_linkPrograms hpositive hlength hequalityLowering hequalityTail
  have htopologyTail :=
    run_linkPrograms hpositive hlength htopology hequalityLoweringTail
  have hloweringTail :=
    run_linkPrograms hpositive hlength hlowering htopologyTail
  have hprepareTail :=
    run_linkPrograms hpositive hlength hprepare hloweringTail
  have hrun :=
    run_linkPrograms hpositive hlength hnormalize hprepareTail
  simpa [booleanNodeListValidationPrepareRebuildProgram,
    booleanNodeListValidationPrepareRebuildFuel] using hrun

end NearCubicWires.CanonicalBooleanNodePrepareRebuildProgram
