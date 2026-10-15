import Batteries.Tactic.OpenPrivate
import Proof.MachineModel.CanonicalBooleanNodeListRebuildProgram
import Proof.Circuits.ValidatorCanonicalizerRebuildLedger

/-!
# The Boolean circuit validator, rebuilt — and `hcall` re-landed on it

`ValidatorCircuitWidthLedger` §6 states `hcall` at exactly two callee widths,
`booleanNodeListValidationBits` and `canonicalNatValidationBits`.  Both of those
are **refuted**: `ValidatorTraversalWidthLedger.not_polyBounded_canonicalNat-
ValidationBits` shows no coefficient and no degree dominates the second on the
canonical atom family, and `two_pow_le_booleanNodeListValidationBits` floors the
first at `2 ^ (5 · atoms.length)`.  So the premise list of
`hcall_at_computableLimits_of_two_widths` cannot be met by *any* proof: `hcall`
is not open at those names, it is false at them.

Two modules repaired the programs behind those names at unchanged output
contracts:

* `ValidatorCanonicalizerRebuildLedger.canonicalNatValidationRebuildProgram`
  returns `canonicalNatValidationOutput raw`;

* `CanonicalBooleanNodeListRebuildProgram.booleanNodeListValidationRebuild-
  Program` returns `booleanNodeListValidationOutput inputLength raw`.

This module spends both.  It rebuilds the Boolean circuit validator's two
callee stages on them, re-walks `ValidatorCircuitWidthLedger` §3 verbatim, and
carries the result through the native contextual call to `hcall` — whose
premise list is now the two *rebuilt* widths, neither of which carries a
geometric floor.

* §1 the two rebuilt stages.

* §2 the rebuilt Boolean circuit validator, executed.

* §3 the rebuilt circuit width, reduced to two callee widths.

* §4 the reduced charge, in the domination judgement.

* §5 the rebuilt oracle call.

* §6 `hcall`, at the two rebuilt widths.
-/

namespace NearCubicWires.ValidatorCircuitRebuildLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListRebuildProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
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

/-! ## §1 The two rebuilt stages -/

/-- The node-list stage, over the rebuilt node-list validator. -/
def booleanCircuitNodeStageRebuildProgram : NPOracleProgram :=
  preserveRightProgram booleanNodeListValidationRebuildProgram

@[simp] theorem booleanCircuitNodeStageRebuildProgram_oracleFree :
    OracleFree booleanCircuitNodeStageRebuildProgram :=
  preserveRightProgram_oracleFree booleanNodeListValidationRebuildProgram
    booleanNodeListValidationRebuildProgram_oracleFree

def booleanCircuitNodeStageRebuildFuel (inputLength raw : ℕ) : ℕ :=
  preserveRightFuel <|
    booleanNodeListValidationRebuildFuel inputLength
      (booleanCircuitNodesCode raw)

def booleanCircuitNodeStageRebuildBits (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (booleanNodeListValidationRebuildBits inputLength
      (booleanCircuitNodesCode raw))
    (booleanCircuitNodesCode raw)
    (Nat.pair (booleanCircuitOutputCode raw) (booleanCircuitTupleFlag raw))
    (booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw))

theorem run_booleanCircuitNodeStageRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitNodeStageRebuildProgram
        (booleanCircuitNodeStageRebuildBits inputLength raw)
        (booleanCircuitNodeStageRebuildFuel inputLength raw)
        (initialNPOracleState inputLength
          (booleanCircuitFieldProjectionOutput raw)) =
      some (booleanCircuitNodeStageOutput inputLength raw) :=
  run_preserveRightProgram booleanNodeListValidationRebuildProgram inputLength
    (booleanNodeListValidationRebuildBits inputLength
      (booleanCircuitNodesCode raw))
    (booleanNodeListValidationRebuildFuel inputLength
      (booleanCircuitNodesCode raw))
    (booleanCircuitNodesCode raw)
    (Nat.pair (booleanCircuitOutputCode raw) (booleanCircuitTupleFlag raw))
    (booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw))
    (run_booleanNodeListValidationRebuildProgram inputLength
      (booleanCircuitNodesCode raw))

/-- The natural-validation stage, over the rebuilt natural validator. -/
def booleanCircuitNatStageRebuildProgram : NPOracleProgram :=
  preserveRightProgram canonicalNatValidationRebuildProgram

@[simp] theorem booleanCircuitNatStageRebuildProgram_oracleFree :
    OracleFree booleanCircuitNatStageRebuildProgram :=
  preserveRightProgram_oracleFree canonicalNatValidationRebuildProgram
    canonicalNatValidationRebuildProgram_oracleFree

def booleanCircuitNatStageRebuildFuel (inputLength raw : ℕ) : ℕ :=
  preserveRightFuel <|
    canonicalNatValidationRebuildFuel inputLength (booleanCircuitOutputCode raw)

def booleanCircuitNatStageRebuildBits (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (canonicalNatValidationRebuildBits inputLength
      (booleanCircuitOutputCode raw))
    (booleanCircuitOutputCode raw)
    (Nat.pair
      (booleanNodeListValidationOutput inputLength
        (booleanCircuitNodesCode raw))
      (booleanCircuitTupleFlag raw))
    (canonicalNatValidationOutput (booleanCircuitOutputCode raw))

theorem run_booleanCircuitNatStageRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitNatStageRebuildProgram
        (booleanCircuitNatStageRebuildBits inputLength raw)
        (booleanCircuitNatStageRebuildFuel inputLength raw)
        (initialNPOracleState inputLength
          (booleanCircuitNatLoweringOutput inputLength raw)) =
      some (booleanCircuitNatStageOutput inputLength raw) :=
  run_preserveRightProgram canonicalNatValidationRebuildProgram inputLength
    (canonicalNatValidationRebuildBits inputLength
      (booleanCircuitOutputCode raw))
    (canonicalNatValidationRebuildFuel inputLength
      (booleanCircuitOutputCode raw))
    (booleanCircuitOutputCode raw)
    (Nat.pair
      (booleanNodeListValidationOutput inputLength
        (booleanCircuitNodesCode raw))
      (booleanCircuitTupleFlag raw))
    (canonicalNatValidationOutput (booleanCircuitOutputCode raw))
    (run_canonicalNatValidationRebuildProgram inputLength
      (booleanCircuitOutputCode raw))

/-! ## §2 The rebuilt Boolean circuit validator -/

/-- **The public Boolean circuit validator, over the two rebuilt callees.**
Six of the eight stages are the frozen ones; only the two that call another
validator change. -/
def booleanCircuitValidationRebuildProgram : NPOracleProgram :=
  linkPrograms booleanCircuitTupleProgram <|
    linkPrograms booleanCircuitFieldProjectionProgram <|
      linkPrograms booleanCircuitNodeStageRebuildProgram <|
        linkPrograms booleanCircuitNatLoweringProgram <|
          linkPrograms booleanCircuitNatStageRebuildProgram <|
            linkPrograms booleanCircuitLtLoweringProgram <|
              linkPrograms booleanCircuitLtStageProgram
                booleanCircuitValidationGateProgram

@[simp] theorem booleanCircuitValidationRebuildProgram_oracleFree :
    OracleFree booleanCircuitValidationRebuildProgram :=
  oracleFree_linkPrograms booleanCircuitTupleProgram_oracleFree <|
    oracleFree_linkPrograms booleanCircuitFieldProjectionProgram_oracleFree <|
      oracleFree_linkPrograms
        booleanCircuitNodeStageRebuildProgram_oracleFree <|
        oracleFree_linkPrograms booleanCircuitNatLoweringProgram_oracleFree <|
          oracleFree_linkPrograms
            booleanCircuitNatStageRebuildProgram_oracleFree <|
            oracleFree_linkPrograms
              booleanCircuitLtLoweringProgram_oracleFree <|
              oracleFree_linkPrograms booleanCircuitLtStageProgram_oracleFree
                booleanCircuitValidationGateProgram_oracleFree

def booleanCircuitValidationRebuildFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel
      (linkPrograms booleanCircuitFieldProjectionProgram <|
        linkPrograms booleanCircuitNodeStageRebuildProgram <|
          linkPrograms booleanCircuitNatLoweringProgram <|
            linkPrograms booleanCircuitNatStageRebuildProgram <|
              linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
      booleanCircuitTupleFuel <|
    linkFuel
        (linkPrograms booleanCircuitNodeStageRebuildProgram <|
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
          (booleanCircuitNodeStageRebuildFuel inputLength raw) <|
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

/-- **The rebuilt circuit charge.**  Exactly `booleanCircuitValidationBits`
with its two callee entries replaced. -/
def booleanCircuitValidationRebuildBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (booleanCircuitTupleBits inputLength raw) <|
      max (booleanCircuitFieldProjectionBits inputLength raw) <|
        max (booleanCircuitNodeStageRebuildBits inputLength raw) <|
          max (booleanCircuitNatLoweringBits inputLength raw) <|
            max (booleanCircuitNatStageRebuildBits inputLength raw) <|
              max (booleanCircuitLtLoweringBits inputLength raw) <|
                max (booleanCircuitLtStageBits inputLength raw)
                  (booleanCircuitValidationGateBits inputLength raw)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The exact runner links eight independently bounded validation stages.
/-- **The rebuilt circuit validator returns the published verdict.**  Output
contract unchanged from `run_booleanCircuitValidationProgram`. -/
theorem run_booleanCircuitValidationRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitValidationRebuildProgram
        (booleanCircuitValidationRebuildBits inputLength raw)
        (booleanCircuitValidationRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (booleanCircuitValidationOutput inputLength raw) := by
  let maximumBits := booleanCircuitValidationRebuildBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationRebuildBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationRebuildBits]
  have htupleBits : booleanCircuitTupleBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationRebuildBits]
  have hprojectionBits :
      booleanCircuitFieldProjectionBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationRebuildBits]
  have hnodeBits :
      booleanCircuitNodeStageRebuildBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationRebuildBits]
  have hnatLoweringBits :
      booleanCircuitNatLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationRebuildBits]
  have hnatBits :
      booleanCircuitNatStageRebuildBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationRebuildBits]
  have hltLoweringBits :
      booleanCircuitLtLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationRebuildBits]
  have hltBits : booleanCircuitLtStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationRebuildBits]
  have hgateBits :
      booleanCircuitValidationGateBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationRebuildBits]
  have htuple :=
    run_bits_mono (run_booleanCircuitTupleProgram inputLength raw) htupleBits
  have hprojection :=
    run_bits_mono (run_booleanCircuitFieldProjectionProgram inputLength raw)
      hprojectionBits
  have hnode :=
    run_bits_mono (run_booleanCircuitNodeStageRebuildProgram inputLength raw)
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
  simpa [booleanCircuitValidationRebuildProgram,
    booleanCircuitValidationRebuildFuel] using hrun

/-! ## §3 The rebuilt circuit width, reduced to two callee widths -/

set_option maxHeartbeats 1600000 in
-- One `omega` closes a twenty-way maximum over the whole circuit atom cone.
/-- **The rebuilt circuit validator's width, reduced to two callee widths.**
`ValidatorCircuitWidthLedger` §3 verbatim, at the rebuilt callees: the atom
cone is untouched, because the two rebuilt validators return exactly the values
the frozen ones returned. -/
theorem booleanCircuitValidationRebuildBits_le
    {inputLength raw bound : ℕ} (htwo : 2 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    booleanCircuitValidationRebuildBits inputLength raw ≤
      max
        (max
          (booleanNodeListValidationRebuildBits inputLength
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
      booleanCircuitNodeStageRebuildBits inputLength raw ≤
        max
          (booleanNodeListValidationRebuildBits inputLength
            (booleanCircuitNodesCode raw)) (2 * (2 * (32 * bound))) := by
    simp only [booleanCircuitNodeStageRebuildBits]
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
  simp only [booleanCircuitValidationRebuildBits]
  omega

/-! ## §4 The reduced charge, in the domination judgement -/

/-- **The rebuilt circuit validator's width, dominated.**  Two residuals, both
of them rebuilt names. -/
theorem booleanCircuitValidationRebuildBits_polyBounded
    {inputLength raw measure lengthCoefficient rawCoefficient nodeCoefficient
      natCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hraw : PolyBounded (natBitLength raw) measure rawCoefficient degree)
    (hnode :
      PolyBounded
        (booleanNodeListValidationRebuildBits inputLength
          (booleanCircuitNodesCode raw)) measure nodeCoefficient degree)
    (hnat :
      PolyBounded
        (canonicalNatValidationRebuildBits inputLength
          (booleanCircuitOutputCode raw)) measure natCoefficient degree) :
    PolyBounded (booleanCircuitValidationRebuildBits inputLength raw) measure
      (max (max nodeCoefficient natCoefficient)
        (2048 * max lengthCoefficient (max rawCoefficient 2))) degree := by
  have hcone :
      PolyBounded (max (natBitLength inputLength) (max (natBitLength raw) 2))
        measure (max lengthCoefficient (max rawCoefficient 2)) degree :=
    hlength.max (hraw.max (polyBounded_const 2 measure degree))
  refine ((hnode.max hnat).max (hcone.const_mul 2048)).mono ?_
  exact booleanCircuitValidationRebuildBits_le
    (bound := max (natBitLength inputLength) (max (natBitLength raw) 2))
    (by omega) (by omega) (by omega)

/-! ## §5 The rebuilt oracle call -/

/-- **The validator's native contextual call, over the rebuilt callee.** -/
def recoveryOracleCallRebuildProgram : NPOracleProgram :=
  nativeContextCallProgram booleanCircuitValidationRebuildProgram

@[simp] theorem recoveryOracleCallRebuildProgram_oracleFree :
    OracleFree recoveryOracleCallRebuildProgram :=
  nativeContextCallProgram_oracleFree
    booleanCircuitValidationRebuildProgram_oracleFree

def recoveryOracleCallRebuildFuel (handoff : ℕ) : ℕ :=
  nativeContextCallFuel booleanCircuitValidationRebuildProgram
    (booleanCircuitValidationRebuildFuel (handoffOracleArity handoff)
      (handoffOracleCode handoff))
    (handoffOracleArity handoff) (handoffOracleCode handoff)

/-- **The rebuilt oracle call's charge.**  Exactly `recoveryOracleCallBits`
with the callee width replaced. -/
def recoveryOracleCallRebuildBits (inputLength handoff : ℕ) : ℕ :=
  nativeContextCallBits inputLength (handoffOracleArity handoff)
    (handoffOracleCode handoff) handoff (recoveryOracleValidationResult handoff)
    (booleanCircuitValidationRebuildBits (handoffOracleArity handoff)
      (handoffOracleCode handoff))

/-- **The rebuilt oracle call returns the published value.** -/
theorem run_recoveryOracleCallRebuildProgram (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryOracleCallRebuildProgram
        (recoveryOracleCallRebuildBits inputLength handoff)
        (recoveryOracleCallRebuildFuel handoff)
        (initialNPOracleState inputLength (recoveryOracleCallInput handoff)) =
      some (recoveryOracleCallOutput handoff) :=
  run_nativeContextCallProgram booleanCircuitValidationRebuildProgram
    inputLength (handoffOracleArity handoff) (handoffOracleCode handoff) handoff
    (recoveryOracleValidationResult handoff)
    (booleanCircuitValidationRebuildBits (handoffOracleArity handoff)
      (handoffOracleCode handoff))
    (booleanCircuitValidationRebuildFuel (handoffOracleArity handoff)
      (handoffOracleCode handoff))
    (run_booleanCircuitValidationRebuildProgram (handoffOracleArity handoff)
      (handoffOracleCode handoff))

/-- **`hcall`'s rebuilt charge, reduced to the callee's width.**
`ValidatorOracleCallWidth` §2 verbatim, at the rebuilt callee. -/
theorem recoveryOracleCallRebuildBits_le (inputLength handoff : ℕ) :
    recoveryOracleCallRebuildBits inputLength handoff ≤
      max
        (booleanCircuitValidationRebuildBits (handoffOracleArity handoff)
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
    (booleanCircuitValidationRebuildBits (handoffOracleArity handoff)
      (handoffOracleCode handoff))
    (max (natBitLength inputLength) (recoveryOracleStageWidth handoff))
    (by omega) (le_max_left _ _) (by omega) (by omega) (by omega) (by omega)

/-- **`hcall`'s rebuilt charge, dominated.**  One residual: the rebuilt
circuit validator's own register requirement. -/
theorem recoveryOracleCallRebuildBits_polyBounded
    {inputLength handoff measure lengthCoefficient widthCoefficient
      calleeCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hwidth :
      PolyBounded (recoveryOracleStageWidth handoff) measure widthCoefficient
        degree)
    (hcallee :
      PolyBounded
        (booleanCircuitValidationRebuildBits (handoffOracleArity handoff)
          (handoffOracleCode handoff)) measure calleeCoefficient degree) :
    PolyBounded (recoveryOracleCallRebuildBits inputLength handoff) measure
      (max calleeCoefficient (4 * max lengthCoefficient widthCoefficient))
      degree :=
  (hcallee.max ((hlength.max hwidth).const_mul 4)).mono
    (recoveryOracleCallRebuildBits_le inputLength handoff)

/-! ## §6 `hcall`, at the two rebuilt widths -/

/-- **`hcircuitBits`, from the two rebuilt callee widths.** -/
theorem hcircuitBits_rebuild_at_computableLimits
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
        (booleanNodeListValidationRebuildBits
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
      (booleanCircuitValidationRebuildBits
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
  exact (booleanCircuitValidationRebuildBits_polyBounded harity hcode
    (hnode request) (hnat request)).coefficient_mono (by omega)

/-- **`hcall`, from the two rebuilt widths alone.**  This is
`ValidatorCircuitWidthLedger.hcall_at_computableLimits_of_two_widths` with both
callee names replaced by the repaired programs' names.  Every other premise is
published; nothing else survives — no register span, no handoff projection, no
trace ledger, no scalar comparator, and no geometric floor. -/
theorem hcall_rebuild_at_computableLimits
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
        (booleanNodeListValidationRebuildBits
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
      (recoveryOracleCallRebuildBits (WeakVerifierRequest.length request)
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
  exact (recoveryOracleCallRebuildBits_polyBounded hlength hstage
    (hcircuitBits_rebuild_at_computableLimits profile copyBound oracleArity
      oracleSizeCap sumArity symmetricWireCap thresholdWireCap frontier
      parameterCoefficient hcircuitFrontier hparameter hnode hnat
      request)).coefficient_mono (by omega)

end NearCubicWires.ValidatorCircuitRebuildLedger
