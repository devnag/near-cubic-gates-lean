import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorCircuitRebuildLedger
import Proof.Circuits.ValidatorPrepareRebuildWidthLedger

/-!
# The Boolean circuit validator, rebuilt a second time — and `hcall` re-landed

`ValidatorCircuitRebuildLedger` links the Boolean circuit validator's node-list
stage on `CanonicalBooleanNodeListRebuildProgram`'s first-generation repair, and
lands `hcall` on the two widths

* `booleanNodeListValidationRebuildBits`, and
* `canonicalNatValidationRebuildBits`.

`ValidatorPrepareRebuildWidthLedger` §7 **refutes** the first of those: its
preparation entry is the frozen `booleanNodeListPrepareBits`, which carries
`canonicalNatValidationBits` at every field of every structural descriptor, and
`ValidatorTaggedIntermediateVerdict` floors that charge at `2 ^ n` on the
canonical atom family.  So `hnode` is not open at the first-generation name; it
is false there.

`CanonicalBooleanNodePrepareRebuildProgram.booleanNodeListValidationPrepare-
RebuildProgram` replaces that program at an unchanged output contract —
`booleanNodeListValidationOutput inputLength raw`, the value the frozen and the
first-generation validators both return.  This module spends it: the circuit
validator's node-list stage is relinked on the second-generation validator, and
`ValidatorCircuitRebuildLedger` §1–§6 replays verbatim at the new callee, because
every stage above the swap is stated at the value the swapped callee returns.

The *natural* callee does not change: `canonicalNatValidationRebuildBits` is
already a rebuilt name and `ValidatorRebuiltWidthCertificates` isolates it as
`hnat`.

* §1 the second-generation node-list stage.

* §2 the second-generation Boolean circuit validator, executed.

* §3 the second-generation circuit width, reduced to two callee widths.

* §4 the reduced charge, in the domination judgement.

* §5 the second-generation oracle call.

* §6 `hcall`, at the second-generation node width and the rebuilt natural width.
-/

namespace NearCubicWires.ValidatorCircuitPrepareRebuildLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodePrepareRebuildProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.ValidatorCanonicalizerRebuildLedger
open NearCubicWires.ValidatorCircuitLeafClosure
open NearCubicWires.ValidatorCircuitRebuildLedger
open NearCubicWires.ValidatorCircuitStageWidths
open NearCubicWires.ValidatorCircuitWidthLedger
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorOracleCallWidth
open NearCubicWires.ValidatorOracleResultWidth
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorWidthCombinatorLedger
open NearCubicWires.VerifiedLinker

open private booleanCircuitFieldProjectionValues booleanCircuitNatLoweringValues
  booleanCircuitLtLoweringValues booleanCircuitValidationGateValues from
  Proof.MachineModel.CanonicalBooleanCircuitValidationProgram

/-! ## §1 The second-generation node-list stage -/

/-- The node-list stage, over the doubly rebuilt node-list validator. -/
def booleanCircuitNodeStagePrepareRebuildProgram : NPOracleProgram :=
  preserveRightProgram booleanNodeListValidationPrepareRebuildProgram

@[simp] theorem booleanCircuitNodeStagePrepareRebuildProgram_oracleFree :
    OracleFree booleanCircuitNodeStagePrepareRebuildProgram :=
  preserveRightProgram_oracleFree booleanNodeListValidationPrepareRebuildProgram
    booleanNodeListValidationPrepareRebuildProgram_oracleFree

def booleanCircuitNodeStagePrepareRebuildFuel (inputLength raw : ℕ) : ℕ :=
  preserveRightFuel <|
    booleanNodeListValidationPrepareRebuildFuel inputLength
      (booleanCircuitNodesCode raw)

def booleanCircuitNodeStagePrepareRebuildBits (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (booleanNodeListValidationPrepareRebuildBits inputLength
      (booleanCircuitNodesCode raw))
    (booleanCircuitNodesCode raw)
    (Nat.pair (booleanCircuitOutputCode raw) (booleanCircuitTupleFlag raw))
    (booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw))

theorem run_booleanCircuitNodeStagePrepareRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitNodeStagePrepareRebuildProgram
        (booleanCircuitNodeStagePrepareRebuildBits inputLength raw)
        (booleanCircuitNodeStagePrepareRebuildFuel inputLength raw)
        (initialNPOracleState inputLength
          (booleanCircuitFieldProjectionOutput raw)) =
      some (booleanCircuitNodeStageOutput inputLength raw) :=
  run_preserveRightProgram booleanNodeListValidationPrepareRebuildProgram
    inputLength
    (booleanNodeListValidationPrepareRebuildBits inputLength
      (booleanCircuitNodesCode raw))
    (booleanNodeListValidationPrepareRebuildFuel inputLength
      (booleanCircuitNodesCode raw))
    (booleanCircuitNodesCode raw)
    (Nat.pair (booleanCircuitOutputCode raw) (booleanCircuitTupleFlag raw))
    (booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw))
    (run_booleanNodeListValidationPrepareRebuildProgram inputLength
      (booleanCircuitNodesCode raw))

/-! ## §2 The second-generation Boolean circuit validator -/

/-- **The public Boolean circuit validator, over the doubly rebuilt node-list
callee.**  Seven of the eight stages are exactly the ones
`ValidatorCircuitRebuildLedger` §2 links; only the node-list stage changes. -/
def booleanCircuitValidationPrepareRebuildProgram : NPOracleProgram :=
  linkPrograms booleanCircuitTupleProgram <|
    linkPrograms booleanCircuitFieldProjectionProgram <|
      linkPrograms booleanCircuitNodeStagePrepareRebuildProgram <|
        linkPrograms booleanCircuitNatLoweringProgram <|
          linkPrograms booleanCircuitNatStageRebuildProgram <|
            linkPrograms booleanCircuitLtLoweringProgram <|
              linkPrograms booleanCircuitLtStageProgram
                booleanCircuitValidationGateProgram

@[simp] theorem booleanCircuitValidationPrepareRebuildProgram_oracleFree :
    OracleFree booleanCircuitValidationPrepareRebuildProgram :=
  oracleFree_linkPrograms booleanCircuitTupleProgram_oracleFree <|
    oracleFree_linkPrograms booleanCircuitFieldProjectionProgram_oracleFree <|
      oracleFree_linkPrograms
        booleanCircuitNodeStagePrepareRebuildProgram_oracleFree <|
        oracleFree_linkPrograms booleanCircuitNatLoweringProgram_oracleFree <|
          oracleFree_linkPrograms
            booleanCircuitNatStageRebuildProgram_oracleFree <|
            oracleFree_linkPrograms
              booleanCircuitLtLoweringProgram_oracleFree <|
              oracleFree_linkPrograms booleanCircuitLtStageProgram_oracleFree
                booleanCircuitValidationGateProgram_oracleFree

def booleanCircuitValidationPrepareRebuildFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel
      (linkPrograms booleanCircuitFieldProjectionProgram <|
        linkPrograms booleanCircuitNodeStagePrepareRebuildProgram <|
          linkPrograms booleanCircuitNatLoweringProgram <|
            linkPrograms booleanCircuitNatStageRebuildProgram <|
              linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
      booleanCircuitTupleFuel <|
    linkFuel
        (linkPrograms booleanCircuitNodeStagePrepareRebuildProgram <|
          linkPrograms booleanCircuitNatLoweringProgram <|
            linkPrograms booleanCircuitNatStageRebuildProgram <|
              linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
        booleanCircuitFieldProjectionFuel <|
      linkFuel
          (linkPrograms booleanCircuitNatLoweringProgram <|
            linkPrograms booleanCircuitNatStageRebuildProgram <|
              linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
          (booleanCircuitNodeStagePrepareRebuildFuel inputLength raw) <|
        linkFuel
            (linkPrograms booleanCircuitNatStageRebuildProgram <|
              linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
            booleanCircuitNatLoweringFuel <|
          linkFuel
              (linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
              (booleanCircuitNatStageRebuildFuel inputLength raw) <|
            linkFuel
                (linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
                booleanCircuitLtLoweringFuel <|
              linkFuel booleanCircuitValidationGateProgram
                (booleanCircuitLtStageFuel inputLength raw)
                booleanCircuitValidationGateFuel

/-- **The second-generation circuit charge.**  Exactly
`booleanCircuitValidationRebuildBits` with its node-list entry replaced. -/
def booleanCircuitValidationPrepareRebuildBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (booleanCircuitTupleBits inputLength raw) <|
      max (booleanCircuitFieldProjectionBits inputLength raw) <|
        max (booleanCircuitNodeStagePrepareRebuildBits inputLength raw) <|
          max (booleanCircuitNatLoweringBits inputLength raw) <|
            max (booleanCircuitNatStageRebuildBits inputLength raw) <|
              max (booleanCircuitLtLoweringBits inputLength raw) <|
                max (booleanCircuitLtStageBits inputLength raw)
                  (booleanCircuitValidationGateBits inputLength raw)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
-- The exact runner links eight independently bounded validation stages.
/-- **The second-generation circuit validator returns the published verdict.**
Output contract unchanged from `run_booleanCircuitValidationProgram`. -/
theorem run_booleanCircuitValidationPrepareRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitValidationPrepareRebuildProgram
        (booleanCircuitValidationPrepareRebuildBits inputLength raw)
        (booleanCircuitValidationPrepareRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (booleanCircuitValidationOutput inputLength raw) := by
  let maximumBits := booleanCircuitValidationPrepareRebuildBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationPrepareRebuildBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationPrepareRebuildBits]
  have htupleBits : booleanCircuitTupleBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationPrepareRebuildBits]
  have hprojectionBits :
      booleanCircuitFieldProjectionBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationPrepareRebuildBits]
  have hnodeBits :
      booleanCircuitNodeStagePrepareRebuildBits inputLength raw ≤
        maximumBits := by
    simp [maximumBits, booleanCircuitValidationPrepareRebuildBits]
  have hnatLoweringBits :
      booleanCircuitNatLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationPrepareRebuildBits]
  have hnatBits :
      booleanCircuitNatStageRebuildBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationPrepareRebuildBits]
  have hltLoweringBits :
      booleanCircuitLtLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationPrepareRebuildBits]
  have hltBits : booleanCircuitLtStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationPrepareRebuildBits]
  have hgateBits :
      booleanCircuitValidationGateBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationPrepareRebuildBits]
  have htuple :=
    run_bits_mono (run_booleanCircuitTupleProgram inputLength raw) htupleBits
  have hprojection :=
    run_bits_mono (run_booleanCircuitFieldProjectionProgram inputLength raw)
      hprojectionBits
  have hnode :=
    run_bits_mono
      (run_booleanCircuitNodeStagePrepareRebuildProgram inputLength raw)
      hnodeBits
  have hnatLowering :=
    run_bits_mono (run_booleanCircuitNatLoweringProgram inputLength raw)
      hnatLoweringBits
  have hnat :=
    run_bits_mono (run_booleanCircuitNatStageRebuildProgram inputLength raw)
      hnatBits
  have hltLowering :=
    run_bits_mono (run_booleanCircuitLtLoweringProgram inputLength raw)
      hltLoweringBits
  have hlt :=
    run_bits_mono (run_booleanCircuitLtStageProgram inputLength raw) hltBits
  have hgate :=
    run_bits_mono (run_booleanCircuitValidationGateProgram inputLength raw)
      hgateBits
  have hltTail := run_linkPrograms hpositive hlength hlt hgate
  have hltLoweringTail := run_linkPrograms hpositive hlength hltLowering hltTail
  have hnatTail := run_linkPrograms hpositive hlength hnat hltLoweringTail
  have hnatLoweringTail :=
    run_linkPrograms hpositive hlength hnatLowering hnatTail
  have hnodeTail := run_linkPrograms hpositive hlength hnode hnatLoweringTail
  have hprojectionTail :=
    run_linkPrograms hpositive hlength hprojection hnodeTail
  have hrun := run_linkPrograms hpositive hlength htuple hprojectionTail
  simpa [booleanCircuitValidationPrepareRebuildProgram,
    booleanCircuitValidationPrepareRebuildFuel] using hrun

/-! ## §3 The second-generation circuit width, reduced to two callee widths -/

set_option maxHeartbeats 1600000 in
-- One `omega` closes a twenty-way maximum over the whole circuit atom cone.
/-- **The second-generation circuit validator's width, reduced to two callee
widths.**  `ValidatorCircuitRebuildLedger` §3 verbatim, at the second-generation
node-list callee: the atom cone is untouched, because the swapped validator
returns exactly the value the first-generation one returned. -/
theorem booleanCircuitValidationPrepareRebuildBits_le
    {inputLength raw bound : ℕ} (htwo : 2 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    booleanCircuitValidationPrepareRebuildBits inputLength raw ≤
      max
        (max
          (booleanNodeListValidationPrepareRebuildBits inputLength
            (booleanCircuitNodesCode raw))
          (canonicalNatValidationRebuildBits inputLength
            (booleanCircuitOutputCode raw)))
        (2048 * bound) := by
  obtain ⟨htuple, hflag, hfields, hnodes, houtput, hnodeList, hnat⟩ :=
    booleanCircuitAtomCone htwo hlength hraw
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 = 1 := natBitLength_one
  have hprefix : natBitLength (Nat.unpair (booleanCircuitTupleFields raw)).1 ≤
      8 * bound := by
    have :=
      natBitLength_mono (Nat.unpair_left_le (booleanCircuitTupleFields raw))
    omega
  have houtputFlag :
      natBitLength
          (Nat.pair (booleanCircuitOutputCode raw)
            (booleanCircuitTupleFlag raw)) ≤ 2 * (8 * bound) :=
    natBitLength_pair_le_two_mul houtput hflag
  have hprojectionOutput :
      natBitLength (booleanCircuitFieldProjectionOutput raw) ≤
        2 * (2 * (8 * bound)) := by
    simp only [booleanCircuitFieldProjectionOutput]
    exact natBitLength_pair_le_two_mul (by omega) houtputFlag
  have hnodeFlag :
      natBitLength
          (Nat.pair
            (booleanNodeListValidationOutput inputLength
              (booleanCircuitNodesCode raw))
            (booleanCircuitTupleFlag raw)) ≤ 2 * (32 * bound) :=
    natBitLength_pair_le_two_mul hnodeList (by omega)
  have hnodeContext :
      natBitLength
          (Nat.pair
            (booleanNodeListValidationOutput inputLength
              (booleanCircuitNodesCode raw))
            (Nat.pair (booleanCircuitOutputCode raw)
              (booleanCircuitTupleFlag raw))) ≤ 2 * (32 * bound) :=
    natBitLength_pair_le_two_mul hnodeList (by omega)
  have hnatLowering :
      natBitLength (booleanCircuitNatLoweringOutput inputLength raw) ≤
        2 * (2 * (32 * bound)) := by
    simp only [booleanCircuitNatLoweringOutput]
    exact natBitLength_pair_le_two_mul (by omega) hnodeFlag
  have hnatStage :
      natBitLength (booleanCircuitNatStageOutput inputLength raw) ≤
        2 * (2 * (32 * bound)) := by
    simp only [booleanCircuitNatStageOutput]
    exact natBitLength_pair_le_two_mul (by omega) hnodeFlag
  have hnodeStage :
      natBitLength (booleanCircuitNodeStageOutput inputLength raw) ≤
        2 * (2 * (32 * bound)) := by
    have houtputFlag' :
        natBitLength
            (Nat.pair (booleanCircuitOutputCode raw)
              (booleanCircuitTupleFlag raw)) ≤ 2 * (32 * bound) := by omega
    simp only [booleanCircuitNodeStageOutput]
    exact natBitLength_pair_le_two_mul (by omega) houtputFlag'
  have hvalue : natBitLength (booleanCircuitNatValue raw) ≤ 32 * bound := by
    have :=
      natBitLength_mono
        (Nat.unpair_right_le
          (canonicalNatValidationOutput (booleanCircuitOutputCode raw)))
    simp only [booleanCircuitNatValue]
    omega
  have hcount :
      natBitLength (booleanCircuitNodeCount inputLength raw) ≤ 32 * bound := by
    have :=
      natBitLength_mono
        (Nat.unpair_right_le
          (booleanNodeListValidationOutput inputLength
            (booleanCircuitNodesCode raw)))
    simp only [booleanCircuitNodeCount]
    omega
  have hrequest := natBitLength_booleanCircuitLtRequest_le htwo hlength hraw
  have hltFlag := natBitLength_booleanCircuitLtFlag_le inputLength raw
  have hnatContext :
      natBitLength
          (Nat.pair
            (canonicalNatValidationOutput (booleanCircuitOutputCode raw))
            (Nat.pair
              (booleanNodeListValidationOutput inputLength
                (booleanCircuitNodesCode raw))
              (booleanCircuitTupleFlag raw))) ≤ 2 * (2 * (32 * bound)) :=
    natBitLength_pair_le_two_mul (by omega) hnodeFlag
  have hltLowering :
      natBitLength (booleanCircuitLtLoweringOutput inputLength raw) ≤
        2 * (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitLtLoweringOutput]
    exact natBitLength_pair_le_two_mul (by omega) hnatStage
  have hltStage :
      natBitLength (booleanCircuitLtStageOutput inputLength raw) ≤
        2 * (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitLtStageOutput]
    exact natBitLength_pair_le_two_mul (by omega) hnatStage
  have hltGate :
      natBitLength
          (Nat.pair (booleanCircuitLtFlag inputLength raw)
            (Nat.pair
              (canonicalNatValidationOutput (booleanCircuitOutputCode raw))
              (Nat.pair
                (booleanNodeListValidationOutput inputLength
                  (booleanCircuitNodesCode raw))
                (booleanCircuitTupleFlag raw)))) ≤
        2 * (2 * (2 * (32 * bound))) :=
    natBitLength_pair_le_two_mul (by omega) hnatContext
  have hcountTag :
      natBitLength (Nat.pair 1 (booleanCircuitNodeCount inputLength raw)) ≤
        2 * (32 * bound) :=
    natBitLength_pair_le_two_mul (by omega) hcount
  -- the three wrapper stages
  have htupleBits : booleanCircuitTupleBits inputLength raw ≤ 8 * bound := by
    have htwoWidth : natBitLength 2 ≤ bound := by
      have hlog : Nat.log 2 2 = 1 := by norm_num
      simp only [natBitLength]
      omega
    have := taggedTupleBits_le (arity := 2) (by omega) hlength htwoWidth hraw
    have hpow : (2 : ℕ) ^ (2 + 1) = 8 := by norm_num
    rw [hpow] at this
    simpa only [booleanCircuitTupleBits] using this
  have hnodeStageBits :
      booleanCircuitNodeStagePrepareRebuildBits inputLength raw ≤
        max
          (booleanNodeListValidationPrepareRebuildBits inputLength
            (booleanCircuitNodesCode raw)) (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitNodeStagePrepareRebuildBits]
    exact preserveRightBits_le (by omega) (by omega) (by omega)
  have hnatStageBits :
      booleanCircuitNatStageRebuildBits inputLength raw ≤
        max
          (canonicalNatValidationRebuildBits inputLength
            (booleanCircuitOutputCode raw)) (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitNatStageRebuildBits]
    exact preserveRightBits_le (by omega) (by omega) (by omega)
  have hltCallee :
      nativeLtRequestBits inputLength (booleanCircuitLtRequest inputLength raw) ≤
        4 * (128 * bound) :=
    nativeLtRequestBits_le (by omega) (by omega) (by omega)
  have hltStageBits :
      booleanCircuitLtStageBits inputLength raw ≤
        max
          (nativeLtRequestBits inputLength
            (booleanCircuitLtRequest inputLength raw))
          (2 * (2 * (2 * (2 * (32 * bound))))) := by
    simp only [booleanCircuitLtStageBits]
    exact preserveRightBits_le (by omega) (by omega) (by omega)
  -- the four trace ledgers
  have hprojectionBits :
      booleanCircuitFieldProjectionBits inputLength raw ≤
        2 * (2 * (8 * bound)) := by
    simp only [booleanCircuitFieldProjectionBits,
      booleanCircuitFieldProjectionValues, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil]
    omega
  have hnatLoweringBits :
      booleanCircuitNatLoweringBits inputLength raw ≤
        2 * (2 * (32 * bound)) := by
    simp only [booleanCircuitNatLoweringBits, booleanCircuitNatLoweringValues,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    omega
  have hltLoweringBits :
      booleanCircuitLtLoweringBits inputLength raw ≤
        2 * (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitLtLoweringBits, booleanCircuitLtLoweringValues,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    omega
  have hgateBits :
      booleanCircuitValidationGateBits inputLength raw ≤
        2 * (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitValidationGateBits,
      booleanCircuitValidationGateValues, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil]
    omega
  simp only [booleanCircuitValidationPrepareRebuildBits]
  omega

/-! ## §4 The reduced charge, in the domination judgement -/

/-- **The second-generation circuit validator's width, dominated.**  Two
residuals: the doubly rebuilt node-list width and the rebuilt natural width. -/
theorem booleanCircuitValidationPrepareRebuildBits_polyBounded
    {inputLength raw measure lengthCoefficient rawCoefficient nodeCoefficient
      natCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hraw : PolyBounded (natBitLength raw) measure rawCoefficient degree)
    (hnode :
      PolyBounded
        (booleanNodeListValidationPrepareRebuildBits inputLength
          (booleanCircuitNodesCode raw)) measure nodeCoefficient degree)
    (hnat :
      PolyBounded
        (canonicalNatValidationRebuildBits inputLength
          (booleanCircuitOutputCode raw)) measure natCoefficient degree) :
    PolyBounded (booleanCircuitValidationPrepareRebuildBits inputLength raw)
      measure
      (max (max nodeCoefficient natCoefficient)
        (2048 * max lengthCoefficient (max rawCoefficient 2))) degree := by
  have hcone :
      PolyBounded (max (natBitLength inputLength) (max (natBitLength raw) 2))
        measure (max lengthCoefficient (max rawCoefficient 2)) degree :=
    hlength.max (hraw.max (polyBounded_const 2 measure degree))
  refine ((hnode.max hnat).max (hcone.const_mul 2048)).mono ?_
  exact booleanCircuitValidationPrepareRebuildBits_le
    (bound := max (natBitLength inputLength) (max (natBitLength raw) 2))
    (by omega) (by omega) (by omega)

/-! ## §5 The second-generation oracle call -/

/-- **The validator's native contextual call, over the second-generation
callee.** -/
def recoveryOracleCallPrepareRebuildProgram : NPOracleProgram :=
  nativeContextCallProgram booleanCircuitValidationPrepareRebuildProgram

@[simp] theorem recoveryOracleCallPrepareRebuildProgram_oracleFree :
    OracleFree recoveryOracleCallPrepareRebuildProgram :=
  nativeContextCallProgram_oracleFree
    booleanCircuitValidationPrepareRebuildProgram_oracleFree

def recoveryOracleCallPrepareRebuildFuel (handoff : ℕ) : ℕ :=
  nativeContextCallFuel booleanCircuitValidationPrepareRebuildProgram
    (booleanCircuitValidationPrepareRebuildFuel (handoffOracleArity handoff)
      (handoffOracleCode handoff))
    (handoffOracleArity handoff) (handoffOracleCode handoff)

/-- **The second-generation oracle call's charge.**  Exactly
`recoveryOracleCallRebuildBits` with the callee width replaced. -/
def recoveryOracleCallPrepareRebuildBits (inputLength handoff : ℕ) : ℕ :=
  nativeContextCallBits inputLength (handoffOracleArity handoff)
    (handoffOracleCode handoff) handoff (recoveryOracleValidationResult handoff)
    (booleanCircuitValidationPrepareRebuildBits (handoffOracleArity handoff)
      (handoffOracleCode handoff))

/-- **The second-generation oracle call returns the published value.** -/
theorem run_recoveryOracleCallPrepareRebuildProgram (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryOracleCallPrepareRebuildProgram
        (recoveryOracleCallPrepareRebuildBits inputLength handoff)
        (recoveryOracleCallPrepareRebuildFuel handoff)
        (initialNPOracleState inputLength (recoveryOracleCallInput handoff)) =
      some (recoveryOracleCallOutput handoff) :=
  run_nativeContextCallProgram booleanCircuitValidationPrepareRebuildProgram
    inputLength (handoffOracleArity handoff) (handoffOracleCode handoff) handoff
    (recoveryOracleValidationResult handoff)
    (booleanCircuitValidationPrepareRebuildBits (handoffOracleArity handoff)
      (handoffOracleCode handoff))
    (booleanCircuitValidationPrepareRebuildFuel (handoffOracleArity handoff)
      (handoffOracleCode handoff))
    (run_booleanCircuitValidationPrepareRebuildProgram
      (handoffOracleArity handoff) (handoffOracleCode handoff))

/-- **`hcall`'s second-generation charge, reduced to the callee's width.**
`ValidatorOracleCallWidth` §2 verbatim, at the second-generation callee. -/
theorem recoveryOracleCallPrepareRebuildBits_le (inputLength handoff : ℕ) :
    recoveryOracleCallPrepareRebuildBits inputLength handoff ≤
      max
        (booleanCircuitValidationPrepareRebuildBits (handoffOracleArity handoff)
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
    (booleanCircuitValidationPrepareRebuildBits (handoffOracleArity handoff)
      (handoffOracleCode handoff))
    (max (natBitLength inputLength) (recoveryOracleStageWidth handoff))
    (by omega) (le_max_left _ _) (by omega) (by omega) (by omega) (by omega)

/-- **`hcall`'s second-generation charge, dominated.**  One residual: the
second-generation circuit validator's own register requirement. -/
theorem recoveryOracleCallPrepareRebuildBits_polyBounded
    {inputLength handoff measure lengthCoefficient widthCoefficient
      calleeCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hwidth :
      PolyBounded (recoveryOracleStageWidth handoff) measure widthCoefficient
        degree)
    (hcallee :
      PolyBounded
        (booleanCircuitValidationPrepareRebuildBits (handoffOracleArity handoff)
          (handoffOracleCode handoff)) measure calleeCoefficient degree) :
    PolyBounded (recoveryOracleCallPrepareRebuildBits inputLength handoff)
      measure (max calleeCoefficient (4 * max lengthCoefficient widthCoefficient))
      degree :=
  (hcallee.max ((hlength.max hwidth).const_mul 4)).mono
    (recoveryOracleCallPrepareRebuildBits_le inputLength handoff)

/-! ## §6 `hcall`, at the second-generation node width -/

/-- **`hcircuitBits`, from the second-generation node width and the rebuilt
natural width.** -/
theorem hcircuitBits_prepareRebuild_at_computableLimits
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier parameterCoefficient : ℕ)
    (hfrontier :
      2048 * max (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2))
          (max 4 2) ≤ frontier)
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient 1)
    (hnode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanNodeListValidationPrepareRebuildBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitNodesCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure frontier recoveryVerifierDegree)
    (hnat : ∀ request : WeakVerifierRequest,
      PolyBounded
        (canonicalNatValidationRebuildBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitOutputCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure frontier recoveryVerifierDegree)
    (request : WeakVerifierRequest) :
    PolyBounded
      (booleanCircuitValidationPrepareRebuildBits
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
      request.measure frontier recoveryVerifierDegree := by
  have hprefix :=
    polyBounded_computableLimits_prefixWidth_of_parameter profile copyBound
      oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      (by omega : (1 : ℕ) ≤ 2) (by omega : 2 * 1 ≤ 2) hparameter request
  have hcode :=
    (polyBounded_handoffOracleCode_structuralPrefixOutput
      (limits :=
        computableLimitsOf profile copyBound oracleArity oracleSizeCap sumArity
          symmetricWireCap thresholdWireCap request.inputArity)
      (polyBounded_witnessWidth request)).degree_mono
      (show 1 ≤ recoveryVerifierDegree by norm_num [recoveryVerifierDegree])
  have harity :=
    (polyBounded_natBitLength_of_le (polyBounded_structuralPrefixOutput hprefix)
      ((Nat.unpair_left_le _).trans
        ((Nat.unpair_right_le _).trans
          ((Nat.unpair_right_le _).trans
            ((Nat.unpair_right_le _).trans
              (Nat.unpair_right_le _)))))).degree_mono
      (show 2 ≤ recoveryVerifierDegree by norm_num [recoveryVerifierDegree])
  exact (booleanCircuitValidationPrepareRebuildBits_polyBounded harity hcode
    (hnode request) (hnat request)).coefficient_mono (by omega)

/-- **`hcall`, from the second-generation node width and the rebuilt natural
width alone.**  This is `ValidatorCircuitRebuildLedger`'s
`hcall_rebuild_at_computableLimits` with the node-list callee name replaced by
the doubly rebuilt program's name.  Nothing else survives, and the surviving
node premise no longer carries the frozen preparation fork's geometric floor. -/
theorem hcall_prepareRebuild_at_computableLimits
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier parameterCoefficient : ℕ)
    (hfour : 4 ≤ frontier)
    (hhandoffFrontier :
      16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) ≤ frontier)
    (hcircuitFrontier :
      2048 * max (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2))
          (max 4 2) ≤ frontier)
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient 1)
    (hnode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanNodeListValidationPrepareRebuildBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitNodesCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure frontier recoveryVerifierDegree)
    (hnat : ∀ request : WeakVerifierRequest,
      PolyBounded
        (canonicalNatValidationRebuildBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitOutputCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure frontier recoveryVerifierDegree)
    (request : WeakVerifierRequest) :
    PolyBounded
      (recoveryOracleCallPrepareRebuildBits (WeakVerifierRequest.length request)
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
  exact (recoveryOracleCallPrepareRebuildBits_polyBounded hlength hstage
    (hcircuitBits_prepareRebuild_at_computableLimits profile copyBound
      oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      frontier parameterCoefficient hcircuitFrontier hparameter hnode hnat
      request)).coefficient_mono (by omega)

end NearCubicWires.ValidatorCircuitPrepareRebuildLedger
