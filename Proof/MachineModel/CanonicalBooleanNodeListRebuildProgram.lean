import Batteries.Tactic.OpenPrivate
import Proof.MachineModel.CanonicalBalancedMidpointRebuildProgram
import Proof.MachineModel.CanonicalBooleanNodeListValidationProgram

/-!
# The node-list validator, rebuilt on the indexed canonicalizer

`CanonicalBooleanNodeListValidationProgram.booleanNodeListValidationProgram`
links seven stages, and the **first** one carries the same geometric charge
`ValidatorCanonicalizerRebuildLedger` repaired for the canonical natural
validator — twice over, once through each arm of a fork:

* the fork's second arm is `balancedRawCanonicalizeProgram` itself, so its
  charge is `balancedRawCanonicalizeBits`, which
  `ValidatorTaggedIntermediateVerdict.two_pow_atoms_le_balancedRawCanonicalizeBits`
  floors at `2 ^ atoms.length`;

* the fork's **first** arm is `balancedCanonicalityProgram`, whose preparation
  stage runs `balancedRawCanonicalizeProgram` under `preserveRightProgram`.  So
  the canonicality guard carries the *same* floor.

`CanonicalBalancedMidpointRebuildProgram.balancedRawCanonicalizeFoldProgram`
replaces that program at an unchanged output contract, so both arms swap at
once.  This module performs the swap and re-assembles the public node-list
validator at its published output.

* §1 the canonicality guard, rebuilt.

* §2 the normalization fork, rebuilt.

* §3 the node-list validator, rebuilt.
-/

namespace NearCubicWires.CanonicalBooleanNodeListRebuildProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedMidpointRebuildProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

open private duplicateNatBits duplicateNatProgram_oracleFree
  run_duplicateNatProgram from Proof.MachineModel.CanonicalBalancedValidationProgram

/-! ## §1 The canonicality guard, rebuilt -/

/-- The code the guard compares the untrusted word against.  Definitionally
`booleanNodeListNormalizedCode`. -/
def balancedCanonicalityRebuiltCode (raw : ℕ) : ℕ :=
  encodeBalancedList (rawBalancedTraversalTree raw).atoms

theorem balancedCanonicalityRebuiltCode_eq (raw : ℕ) :
    balancedCanonicalityRebuiltCode raw = booleanNodeListNormalizedCode raw :=
  rfl

/-- The guard's preparation stage, over the indexed canonicalizer. -/
def balancedCanonicalityPrepareRebuildProgram : NPOracleProgram :=
  linkPrograms duplicateNatProgram <|
    preserveRightProgram balancedRawCanonicalizeFoldProgram

@[simp] theorem balancedCanonicalityPrepareRebuildProgram_oracleFree :
    OracleFree balancedCanonicalityPrepareRebuildProgram :=
  oracleFree_linkPrograms duplicateNatProgram_oracleFree <|
    preserveRightProgram_oracleFree balancedRawCanonicalizeFoldProgram
      balancedRawCanonicalizeFoldProgram_oracleFree

def balancedCanonicalityPrepareRebuildFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel (preserveRightProgram balancedRawCanonicalizeFoldProgram) 2 <|
    preserveRightFuel
      (balancedRawCanonicalizeFoldFuel inputLength
        (rawBalancedTraversalTree raw))

def balancedCanonicalityPrepareRebuildBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (duplicateNatBits raw) <|
      preserveRightBits
        (balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw))
        raw raw (balancedCanonicalityRebuiltCode raw)

theorem run_balancedCanonicalityPrepareRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram balancedCanonicalityPrepareRebuildProgram
        (balancedCanonicalityPrepareRebuildBits inputLength raw)
        (balancedCanonicalityPrepareRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (nativeNatEqInput (balancedCanonicalityRebuiltCode raw) raw) := by
  let rebuilt := balancedCanonicalityRebuiltCode raw
  let maximumBits := balancedCanonicalityPrepareRebuildBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityPrepareRebuildBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityPrepareRebuildBits]
  have hduplicate : duplicateNatBits raw ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityPrepareRebuildBits]
  have hpreserve :
      preserveRightBits
          (balancedRawCanonicalizeFoldBits inputLength
            (rawBalancedTraversalTree raw))
          raw raw rebuilt ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityPrepareRebuildBits, rebuilt]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono (run_duplicateNatProgram inputLength raw) hduplicate
  · have hrun :=
      run_preserveRightProgram balancedRawCanonicalizeFoldProgram inputLength
        (balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw))
        (balancedRawCanonicalizeFoldFuel inputLength
          (rawBalancedTraversalTree raw))
        raw raw rebuilt
        (run_balancedRawCanonicalizeFoldProgram_total inputLength raw)
    simpa [nativeNatEqInput, rebuilt] using run_bits_mono hrun hpreserve

/-- **The canonicality guard, over the indexed canonicalizer.** -/
def balancedCanonicalityRebuildProgram : NPOracleProgram :=
  linkPrograms balancedCanonicalityPrepareRebuildProgram nativeNatEqProgram

@[simp] theorem balancedCanonicalityRebuildProgram_oracleFree :
    OracleFree balancedCanonicalityRebuildProgram :=
  oracleFree_linkPrograms balancedCanonicalityPrepareRebuildProgram_oracleFree
    nativeNatEqProgram_oracleFree

def balancedCanonicalityRebuildFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel nativeNatEqProgram
    (balancedCanonicalityPrepareRebuildFuel inputLength raw)
    (nativeNatEqFuel (balancedCanonicalityRebuiltCode raw) raw)

def balancedCanonicalityRebuildBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedCanonicalityPrepareRebuildBits inputLength raw)
      (nativeNatEqBits inputLength (balancedCanonicalityRebuiltCode raw) raw)

/-- The comparison the guard performs is the published canonicality verdict. -/
theorem nativeNatEqOutput_rebuiltCode (raw : ℕ) :
    nativeNatEqOutput (balancedCanonicalityRebuiltCode raw) raw =
      balancedCanonicalityOutput raw :=
  rfl

/-- **The rebuilt guard returns the published canonicality flag.** -/
theorem run_balancedCanonicalityRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram balancedCanonicalityRebuildProgram
        (balancedCanonicalityRebuildBits inputLength raw)
        (balancedCanonicalityRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (balancedCanonicalityOutput raw) := by
  let maximumBits := balancedCanonicalityRebuildBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityRebuildBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityRebuildBits]
  have hprepare :
      balancedCanonicalityPrepareRebuildBits inputLength raw ≤
        maximumBits := by
    simp [maximumBits, balancedCanonicalityRebuildBits]
  have hequality :
      nativeNatEqBits inputLength (balancedCanonicalityRebuiltCode raw) raw ≤
        maximumBits := by
    simp [maximumBits, balancedCanonicalityRebuildBits]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_balancedCanonicalityPrepareRebuildProgram inputLength raw) hprepare
  · rw [← nativeNatEqOutput_rebuiltCode raw]
    exact run_bits_mono
      (run_nativeNatEqProgram inputLength (balancedCanonicalityRebuiltCode raw)
        raw)
      hequality

/-! ## §2 The normalization fork, rebuilt -/

/-- **The node-list normalization seam, over the indexed canonicalizer.**
Both arms of the fork swap at once. -/
def booleanNodeListNormalizeRebuildProgram : NPOracleProgram :=
  forkCallProgram balancedCanonicalityRebuildProgram
    balancedRawCanonicalizeFoldProgram

@[simp] theorem booleanNodeListNormalizeRebuildProgram_oracleFree :
    OracleFree booleanNodeListNormalizeRebuildProgram :=
  forkCallProgram_oracleFree balancedCanonicalityRebuildProgram
    balancedRawCanonicalizeFoldProgram
    balancedCanonicalityRebuildProgram_oracleFree
    balancedRawCanonicalizeFoldProgram_oracleFree

def booleanNodeListNormalizeRebuildFuel (inputLength raw : ℕ) : ℕ :=
  forkCallFuel balancedCanonicalityRebuildProgram
    balancedRawCanonicalizeFoldProgram
    (balancedCanonicalityRebuildFuel inputLength raw)
    (balancedRawCanonicalizeFoldFuel inputLength
      (rawBalancedTraversalTree raw))

def booleanNodeListNormalizeRebuildBits (inputLength raw : ℕ) : ℕ :=
  forkCallBits inputLength raw
    (balancedCanonicalityRebuildBits inputLength raw)
    (balancedRawCanonicalizeFoldBits inputLength
      (rawBalancedTraversalTree raw))
    (balancedCanonicalityOutput raw)
    (booleanNodeListNormalizedCode raw)

/-- **The rebuilt seam returns the published pair.**  Output contract
unchanged from `run_booleanNodeListNormalizeProgram`. -/
theorem run_booleanNodeListNormalizeRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListNormalizeRebuildProgram
        (booleanNodeListNormalizeRebuildBits inputLength raw)
        (booleanNodeListNormalizeRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some
        (Nat.pair (balancedCanonicalityOutput raw)
          (booleanNodeListNormalizedCode raw)) :=
  run_forkCallProgram balancedCanonicalityRebuildProgram
    balancedRawCanonicalizeFoldProgram inputLength raw
    (balancedCanonicalityRebuildBits inputLength raw)
    (balancedRawCanonicalizeFoldBits inputLength
      (rawBalancedTraversalTree raw))
    (balancedCanonicalityRebuildFuel inputLength raw)
    (balancedRawCanonicalizeFoldFuel inputLength
      (rawBalancedTraversalTree raw))
    (balancedCanonicalityOutput raw)
    (booleanNodeListNormalizedCode raw)
    (run_balancedCanonicalityRebuildProgram inputLength raw)
    (by
      simpa [booleanNodeListNormalizedCode, booleanNodeListAtoms] using
        run_balancedRawCanonicalizeFoldProgram_total inputLength raw)

/-! ## §3 The node-list validator, rebuilt -/

/-- **The public node-list validator, over the rebuilt seam.**  Only the first
of the seven stages changes; the other six are stated at the seam's *value*, so
they reuse verbatim. -/
def booleanNodeListValidationRebuildProgram : NPOracleProgram :=
  linkPrograms booleanNodeListNormalizeRebuildProgram <|
    linkPrograms booleanNodeListPrepareProgram <|
      linkPrograms booleanNodeListRangeLoweringProgram <|
        linkPrograms booleanNodeListTopologyProgram <|
          linkPrograms booleanNodeListTopologyEqualityLoweringProgram <|
            linkPrograms booleanNodeListTopologyEqualityProgram
              booleanNodeListValidationGateProgram

@[simp] theorem booleanNodeListValidationRebuildProgram_oracleFree :
    OracleFree booleanNodeListValidationRebuildProgram :=
  oracleFree_linkPrograms booleanNodeListNormalizeRebuildProgram_oracleFree <|
    oracleFree_linkPrograms booleanNodeListPrepareProgram_oracleFree <|
      oracleFree_linkPrograms
        booleanNodeListRangeLoweringProgram_oracleFree <|
        oracleFree_linkPrograms booleanNodeListTopologyProgram_oracleFree <|
          oracleFree_linkPrograms
            booleanNodeListTopologyEqualityLoweringProgram_oracleFree <|
            oracleFree_linkPrograms
              booleanNodeListTopologyEqualityProgram_oracleFree
              booleanNodeListValidationGateProgram_oracleFree

def booleanNodeListValidationRebuildFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel
      (linkPrograms booleanNodeListPrepareProgram <|
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
        (booleanNodeListPrepareFuel inputLength raw) <|
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

/-- **The rebuilt node-list charge.**  Exactly `booleanNodeListValidationBits`
with its first entry replaced; the other six entries are the frozen ones. -/
def booleanNodeListValidationRebuildBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (booleanNodeListNormalizeRebuildBits inputLength raw) <|
      max (booleanNodeListPrepareBits inputLength raw) <|
        max (booleanNodeListRangeLoweringBits inputLength raw) <|
          max (booleanNodeListTopologyBits inputLength raw) <|
            max
              (booleanNodeListTopologyEqualityLoweringBits
                inputLength raw) <|
              max (booleanNodeListTopologyEqualityBits inputLength raw)
                (booleanNodeListValidationGateBits inputLength raw)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The proof links the rebuilt seam to six frozen runners at the same values.
/-- **The rebuilt node-list validator returns the published verdict.**  Output
contract unchanged from `run_booleanNodeListValidationProgram`. -/
theorem run_booleanNodeListValidationRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListValidationRebuildProgram
        (booleanNodeListValidationRebuildBits inputLength raw)
        (booleanNodeListValidationRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (booleanNodeListValidationOutput inputLength raw) := by
  let maximumBits := booleanNodeListValidationRebuildBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationRebuildBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationRebuildBits]
  have hnormalizeBits :
      booleanNodeListNormalizeRebuildBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationRebuildBits]
  have hprepareBits :
      booleanNodeListPrepareBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationRebuildBits]
  have hloweringBits :
      booleanNodeListRangeLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationRebuildBits]
  have htopologyBits :
      booleanNodeListTopologyBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationRebuildBits]
  have hequalityLoweringBits :
      booleanNodeListTopologyEqualityLoweringBits inputLength raw ≤
        maximumBits := by
    simp [maximumBits, booleanNodeListValidationRebuildBits]
  have hequalityBits :
      booleanNodeListTopologyEqualityBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationRebuildBits]
  have hgateBits :
      booleanNodeListValidationGateBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationRebuildBits]
  have hnormalize :=
    run_bits_mono
      (run_booleanNodeListNormalizeRebuildProgram inputLength raw)
      hnormalizeBits
  have hprepare :=
    run_bits_mono
      (run_booleanNodeListPrepareProgram inputLength raw) hprepareBits
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
  simpa [booleanNodeListValidationRebuildProgram,
    booleanNodeListValidationRebuildFuel] using hrun

end NearCubicWires.CanonicalBooleanNodeListRebuildProgram
