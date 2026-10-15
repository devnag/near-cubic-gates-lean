import Proof.MachineModel.CanonicalBalancedFlattenProgram
import Proof.MachineModel.CanonicalBalancedLengthProgram
import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.MachineModel.CanonicalSymmetricRowTableRequestProgram
import Proof.MachineModel.CaseTwoOccurrenceProgram
import Proof.MachineModel.RuntimeCaseTwoOccurrencePacketSplit

namespace NearCubicWires.CaseTwoSubstitutedCircuitEncoder

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedFlattenProgram
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalSymmetricRowTableRequestProgram
open NearCubicWires.CaseOnePadding
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.VerifiedLinker

/-! ## 1. The circuit code is one pair -/

/-- The public circuit code built from its two components. -/
def circuitCode (nodesCode outputCode : ℕ) : ℕ :=
  encodeTaggedList [nodesCode, outputCode]

theorem encodeBooleanCircuit_eq_circuitCode {n : ℕ}
    (circuit : BooleanCircuit n) :
    encodeBooleanCircuit circuit =
      circuitCode (encodeBalancedList (circuit.nodes.map encodeBooleanNode))
        (encodeNat circuit.output.val) :=
  rfl

theorem circuitCode_eq_pair (nodesCode outputCode : ℕ) :
    circuitCode nodesCode outputCode =
      Nat.pair 1
        (Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0))) :=
  rfl

private theorem le_circuitCode_nodes (nodesCode outputCode : ℕ) :
    natBitLength nodesCode ≤ natBitLength (circuitCode nodesCode outputCode) :=
  natBitLength_mono <|
    (Nat.left_le_pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0))).trans
      (Nat.right_le_pair 1 _)

private theorem le_circuitCode_output (nodesCode outputCode : ℕ) :
    natBitLength outputCode ≤
      natBitLength (circuitCode nodesCode outputCode) := by
  refine natBitLength_mono ?_
  refine (Nat.left_le_pair outputCode 0).trans ?_
  refine (Nat.right_le_pair 1 (Nat.pair outputCode 0)).trans ?_
  refine (Nat.right_le_pair nodesCode _).trans ?_
  exact Nat.right_le_pair 1 _

/-! ## 2. Opening and closing the circuit code -/

/-- Split a circuit code into `pair nodes output`. -/
def circuitSplitProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 3 2
  , .unpairRight 2 4 3
  , .unpairRight 4 5 4
  , .unpairLeft 5 6 5
  , .pair 3 6 0 6
  , .halt 0
  ]

@[simp] theorem circuitSplitProgram_oracleFree :
    OracleFree circuitSplitProgram := by
  rfl

def circuitSplitFuel : ℕ := 7

def circuitSplitBits (nodesCode outputCode : ℕ) : ℕ :=
  natBitLength
    (max (circuitCode nodesCode outputCode) (Nat.pair nodesCode outputCode))

theorem run_circuitSplitProgram
    (inputLength nodesCode outputCode maximumBits : ℕ)
    (hbits : circuitSplitBits nodesCode outputCode ≤ maximumBits) :
    runNPOracleProgram circuitSplitProgram maximumBits circuitSplitFuel
        (initialNPOracleState inputLength
          (circuitCode nodesCode outputCode)) =
      some (Nat.pair nodesCode outputCode) := by
  have hcode : natBitLength (circuitCode nodesCode outputCode) ≤ maximumBits :=
    (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
  have hpair : natBitLength (Nat.pair nodesCode outputCode) ≤ maximumBits :=
    (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
  have hinner :
      natBitLength (Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0))) ≤
        maximumBits :=
    (natBitLength_mono (Nat.right_le_pair 1 _)).trans hcode
  have hnodes : natBitLength nodesCode ≤ maximumBits :=
    (le_circuitCode_nodes nodesCode outputCode).trans hcode
  have htail :
      natBitLength (Nat.pair 1 (Nat.pair outputCode 0)) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair nodesCode _)).trans hinner
  have hcell : natBitLength (Nat.pair outputCode 0) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair 1 _)).trans htail
  have houtput : natBitLength outputCode ≤ maximumBits :=
    (le_circuitCode_output nodesCode outputCode).trans hcode
  rw [circuitCode_eq_pair]
  rw [show circuitSplitFuel = 6 + 1 by rfl]
  rw [run_unpairRight_instruction
    (value := Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0)))
    (by rfl) rfl (by simp [initialNPOracleState]) hinner]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := nodesCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnodes]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair 1 (Nat.pair outputCode 0)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair outputCode 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcell]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := outputCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair nodesCode outputCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpair]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpair

/-- Rebuild a circuit code from `pair nodes output`. -/
def circuitJoinProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 0 3
  , .pair 3 4 3 4
  , .set 4 1 5
  , .pair 4 3 3 6
  , .pair 2 3 2 7
  , .pair 4 2 0 8
  , .halt 0
  ]

@[simp] theorem circuitJoinProgram_oracleFree :
    OracleFree circuitJoinProgram := by
  rfl

def circuitJoinFuel : ℕ := 9

def circuitJoinBits (nodesCode outputCode : ℕ) : ℕ :=
  natBitLength
    (max (circuitCode nodesCode outputCode) (Nat.pair nodesCode outputCode))

theorem run_circuitJoinProgram
    (inputLength nodesCode outputCode maximumBits : ℕ)
    (hbits : circuitJoinBits nodesCode outputCode ≤ maximumBits) :
    runNPOracleProgram circuitJoinProgram maximumBits circuitJoinFuel
        (initialNPOracleState inputLength (Nat.pair nodesCode outputCode)) =
      some (circuitCode nodesCode outputCode) := by
  have hcode : natBitLength (circuitCode nodesCode outputCode) ≤ maximumBits :=
    (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
  have hpair : natBitLength (Nat.pair nodesCode outputCode) ≤ maximumBits :=
    (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
  have hinner :
      natBitLength (Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0))) ≤
        maximumBits :=
    (natBitLength_mono (Nat.right_le_pair 1 _)).trans hcode
  have hnodes : natBitLength nodesCode ≤ maximumBits :=
    (le_circuitCode_nodes nodesCode outputCode).trans hcode
  have htail :
      natBitLength (Nat.pair 1 (Nat.pair outputCode 0)) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair nodesCode _)).trans hinner
  have hcell : natBitLength (Nat.pair outputCode 0) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair 1 _)).trans htail
  have houtput : natBitLength outputCode ≤ maximumBits :=
    (le_circuitCode_output nodesCode outputCode).trans hcode
  have hzero : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hnodes
  have hone : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair 1 (Nat.pair outputCode 0))).trans htail
  rw [circuitCode_eq_pair]
  rw [show circuitJoinFuel = 8 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := nodesCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hnodes]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := outputCode) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtput]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair outputCode 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcell]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl hone]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 (Nat.pair outputCode 0))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hinner]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair 1 (Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0))))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hcode]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcode

/-! ## 3. The constant-node generator -/

/-- The code of the unreachable constant node the size padding appends. -/
def falseNodeCode : ℕ :=
  encodeTaggedList [encodeNat 0, encodeNat 0]

theorem encodeBooleanNode_const_false {n : ℕ} :
    encodeBooleanNode (BooleanNode.const false : BooleanNode n) =
      falseNodeCode :=
  rfl

def falseNodeLeafProgram : NPOracleProgram :=
  [ .set 0 falseNodeCode 1
  , .halt 0
  ]

@[simp] theorem falseNodeLeafProgram_oracleFree :
    OracleFree falseNodeLeafProgram := by
  rfl

theorem run_falseNodeLeafProgram
    (inputLength requestCode maximumBits : ℕ)
    (hbits : natBitLength falseNodeCode ≤ maximumBits) :
    runNPOracleProgram falseNodeLeafProgram maximumBits 2
        (initialNPOracleState inputLength requestCode) =
      some falseNodeCode := by
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_set_instruction (value := falseNodeCode) (by rfl) rfl hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

def constantNodePoolProgram : NPOracleProgram :=
  indexedPoolListProgram falseNodeLeafProgram

theorem constantNodePoolProgram_oracleFree :
    OracleFree constantNodePoolProgram :=
  indexedPoolListProgram_oracleFree falseNodeLeafProgram
    falseNodeLeafProgram_oracleFree

def constantNodePoolFuel (inputLength count : ℕ) : ℕ :=
  indexedPoolListFuel falseNodeLeafProgram inputLength count 0 fun _ => 2

def constantNodePoolBits (inputLength count : ℕ) : ℕ :=
  max (indexedPoolListBits inputLength count 0 fun _ => falseNodeCode)
    (natBitLength falseNodeCode)

private theorem map_range_falseNodeCode (count : ℕ) :
    ((List.range count).map fun _ => falseNodeCode) =
      List.replicate count falseNodeCode := by
  simp only [List.map_const', List.length_range]

/-- **The constant-node generator, executed.** -/
theorem run_constantNodePoolProgram
    (inputLength count maximumBits : ℕ)
    (hbits : constantNodePoolBits inputLength count ≤ maximumBits) :
    runNPOracleProgram constantNodePoolProgram maximumBits
        (constantNodePoolFuel inputLength count)
        (initialNPOracleState inputLength (Nat.pair count 0)) =
      some (encodeBalancedList (List.replicate count falseNodeCode)) := by
  have hleafBits : natBitLength falseNodeCode ≤ maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  have hpoolBits :
      indexedPoolListBits inputLength count 0 (fun _ => falseNodeCode) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hrun :=
    run_indexedPoolListProgram falseNodeLeafProgram inputLength count 0
      maximumBits (fun _ => 2) (fun _ => falseNodeCode) hpoolBits
      (fun index _hindex =>
        run_falseNodeLeafProgram inputLength (Nat.pair index 0) maximumBits
          hleafBits)
  rw [map_range_falseNodeCode] at hrun
  exact hrun

/-! ## 4. The arity padder -/

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbound : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbound

/-- Open the circuit code beside the requested arity and duplicate the node
list, so the length stage can consume one copy. -/
def padFrontProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 2 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 4 6 5
  , .unpairRight 6 6 6
  , .unpairLeft 6 6 7
  , .pair 3 6 3 8
  , .pair 5 3 3 9
  , .pair 5 3 0 10
  , .halt 0
  ]

@[simp] theorem padFrontProgram_oracleFree : OracleFree padFrontProgram := by
  rfl

def padFrontFuel : ℕ := 11

def padFrontBits (nodesCode outputCode arity : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair (circuitCode nodesCode outputCode) arity)
      (Nat.pair nodesCode (Nat.pair nodesCode (Nat.pair arity outputCode))))

theorem run_padFrontProgram
    (inputLength nodesCode outputCode arity maximumBits : ℕ)
    (hbits : padFrontBits nodesCode outputCode arity ≤ maximumBits) :
    runNPOracleProgram padFrontProgram maximumBits padFrontFuel
        (initialNPOracleState inputLength
          (Nat.pair (circuitCode nodesCode outputCode) arity)) =
      some
        (Nat.pair nodesCode
          (Nat.pair nodesCode (Nat.pair arity outputCode))) := by
  have hinput :
      natBitLength (Nat.pair (circuitCode nodesCode outputCode) arity) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
  have houtputWord :
      natBitLength
          (Nat.pair nodesCode
            (Nat.pair nodesCode (Nat.pair arity outputCode))) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
  have hcode : natBitLength (circuitCode nodesCode outputCode) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have harity : natBitLength arity ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hcell :
      natBitLength
          (Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0))) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair 1 _) hcode
  have hnodes : natBitLength nodesCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hcell
  have htail :
      natBitLength (Nat.pair 1 (Nat.pair outputCode 0)) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hcell
  have hlast : natBitLength (Nat.pair outputCode 0) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair 1 _) htail
  have houtput : natBitLength outputCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hlast
  have hmid :
      natBitLength (Nat.pair nodesCode (Nat.pair arity outputCode)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputWord
  have hsuffix : natBitLength (Nat.pair arity outputCode) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hmid
  rw [circuitCode_eq_pair]
  rw [show padFrontFuel = 10 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := Nat.pair 1 (Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0))))
    (by rfl) rfl (by simp [initialNPOracleState]) (by rw [← circuitCode_eq_pair]; exact hcode)]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := arity) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    harity]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hcell]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := nodesCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnodes]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair 1 (Nat.pair outputCode 0)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair outputCode 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlast]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := outputCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair arity outputCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsuffix]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair nodesCode (Nat.pair arity outputCode)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmid]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair nodesCode (Nat.pair nodesCode (Nat.pair arity outputCode)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputWord]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputWord

/-- Turn the measured node count into the pool request and retain the node
list beside the output address. -/
def padRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .subtract 6 2 6 7
  , .set 8 0 8
  , .pair 6 8 6 9
  , .pair 4 7 4 10
  , .pair 6 4 0 11
  , .halt 0
  ]

@[simp] theorem padRequestProgram_oracleFree :
    OracleFree padRequestProgram := by
  rfl

def padRequestFuel : ℕ := 12

def padRequestBits (size nodesCode outputCode arity : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair size (Nat.pair nodesCode (Nat.pair arity outputCode)))
      (Nat.pair (Nat.pair (arity - size) 0) (Nat.pair nodesCode outputCode)))

theorem run_padRequestProgram
    (inputLength size nodesCode outputCode arity maximumBits : ℕ)
    (hbits : padRequestBits size nodesCode outputCode arity ≤ maximumBits) :
    runNPOracleProgram padRequestProgram maximumBits padRequestFuel
        (initialNPOracleState inputLength
          (Nat.pair size
            (Nat.pair nodesCode (Nat.pair arity outputCode)))) =
      some
        (Nat.pair (Nat.pair (arity - size) 0)
          (Nat.pair nodesCode outputCode)) := by
  have hinput :
      natBitLength
          (Nat.pair size (Nat.pair nodesCode (Nat.pair arity outputCode))) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
  have houtputWord :
      natBitLength
          (Nat.pair (Nat.pair (arity - size) 0)
            (Nat.pair nodesCode outputCode)) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
  have hsize : natBitLength size ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hrest :
      natBitLength (Nat.pair nodesCode (Nat.pair arity outputCode)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hnodes : natBitLength nodesCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hrest
  have hsuffix : natBitLength (Nat.pair arity outputCode) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hrest
  have harity : natBitLength arity ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hsuffix
  have houtput : natBitLength outputCode ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hsuffix
  have hcount : natBitLength (arity - size) ≤ maximumBits :=
    bits_of_le (Nat.sub_le arity size) harity
  have hzero : natBitLength 0 ≤ maximumBits :=
    bits_of_le (Nat.zero_le arity) harity
  have hrequest : natBitLength (Nat.pair (arity - size) 0) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputWord
  have hretained : natBitLength (Nat.pair nodesCode outputCode) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputWord
  rw [show padRequestFuel = 11 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := size) (by rfl) rfl
    (by simp [initialNPOracleState]) hsize]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair nodesCode (Nat.pair arity outputCode)) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hrest]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := nodesCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnodes]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair arity outputCode)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hsuffix]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := arity) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harity]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := outputCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_subtract_instruction (value := arity - size) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcount]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (arity - size) 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrequest]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair nodesCode outputCode)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hretained]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (Nat.pair (arity - size) 0) (Nat.pair nodesCode outputCode))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputWord]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputWord

/-- Present the node list beside the generated suffix on the append ABI. -/
def padAppendFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 4 2 4 5
  , .pair 4 5 0 6
  , .halt 0
  ]

@[simp] theorem padAppendFrameProgram_oracleFree :
    OracleFree padAppendFrameProgram := by
  rfl

def padAppendFrameFuel : ℕ := 7

def padAppendFrameBits (suffixCode nodesCode outputCode : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair suffixCode (Nat.pair nodesCode outputCode))
      (Nat.pair (Nat.pair nodesCode suffixCode) outputCode))

theorem run_padAppendFrameProgram
    (inputLength suffixCode nodesCode outputCode maximumBits : ℕ)
    (hbits : padAppendFrameBits suffixCode nodesCode outputCode ≤ maximumBits) :
    runNPOracleProgram padAppendFrameProgram maximumBits padAppendFrameFuel
        (initialNPOracleState inputLength
          (Nat.pair suffixCode (Nat.pair nodesCode outputCode))) =
      some (Nat.pair (Nat.pair nodesCode suffixCode) outputCode) := by
  have hinput :
      natBitLength (Nat.pair suffixCode (Nat.pair nodesCode outputCode)) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
  have houtputWord :
      natBitLength (Nat.pair (Nat.pair nodesCode suffixCode) outputCode) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
  have hsuffix : natBitLength suffixCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hretained : natBitLength (Nat.pair nodesCode outputCode) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hnodes : natBitLength nodesCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hretained
  have houtput : natBitLength outputCode ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hretained
  have hpair : natBitLength (Nat.pair nodesCode suffixCode) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputWord
  rw [show padAppendFrameFuel = 6 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := suffixCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hsuffix]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair nodesCode outputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hretained]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := nodesCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnodes]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := outputCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair nodesCode suffixCode)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hpair]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair nodesCode suffixCode) outputCode)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputWord]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputWord

/-! ## 5. The padder, assembled -/

/-- The encoded node list of a circuit. -/
def padArityNodes {n : ℕ} (circuit : BooleanCircuit n) : List ℕ :=
  circuit.nodes.map encodeBooleanNode

/-- The constant suffix the arity padding appends. -/
def padAritySuffix {n : ℕ} (circuit : BooleanCircuit n) : List ℕ :=
  List.replicate (n - circuit.size) falseNodeCode

@[simp] theorem padArityNodes_length {n : ℕ} (circuit : BooleanCircuit n) :
    (padArityNodes circuit).length = circuit.size :=
  List.length_map _

private def padNodesCode {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  encodeBalancedList (padArityNodes circuit)

private def padOutputCode {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  encodeNat circuit.output.val

private def padSuffixCode {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  encodeBalancedList (padAritySuffix circuit)

private def padAppendedCode {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  encodeBalancedList (padArityNodes circuit ++ padAritySuffix circuit)

private def padStageSix : NPOracleProgram :=
  linkPrograms (preserveRightProgram balancedAppendProgram) circuitJoinProgram

private def padStageFive : NPOracleProgram :=
  linkPrograms padAppendFrameProgram padStageSix

private def padStageFour : NPOracleProgram :=
  linkPrograms (preserveRightProgram constantNodePoolProgram) padStageFive

private def padStageThree : NPOracleProgram :=
  linkPrograms padRequestProgram padStageFour

private def padStageTwo : NPOracleProgram :=
  linkPrograms (preserveRightProgram balancedLengthProgram) padStageThree

/-- **The arity padder.**  From the circuit code beside the requested arity,
the code of the circuit padded to that arity. -/
def padArityProgram : NPOracleProgram :=
  linkPrograms padFrontProgram padStageTwo

theorem padArityProgram_oracleFree : OracleFree padArityProgram :=
  oracleFree_linkPrograms padFrontProgram_oracleFree <|
    oracleFree_linkPrograms
      (preserveRightProgram_oracleFree balancedLengthProgram
        balancedLengthProgram_oracleFree) <|
      oracleFree_linkPrograms padRequestProgram_oracleFree <|
        oracleFree_linkPrograms
          (preserveRightProgram_oracleFree constantNodePoolProgram
            constantNodePoolProgram_oracleFree) <|
          oracleFree_linkPrograms padAppendFrameProgram_oracleFree <|
            oracleFree_linkPrograms
              (preserveRightProgram_oracleFree balancedAppendProgram
                balancedAppendProgram_oracleFree)
              circuitJoinProgram_oracleFree

def padArityFuel (inputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  linkFuel padStageTwo padFrontFuel <|
    linkFuel padStageThree
      (preserveRightFuel (balancedLengthFuel (padArityNodes circuit))) <|
      linkFuel padStageFour padRequestFuel <|
        linkFuel padStageFive
          (preserveRightFuel
            (constantNodePoolFuel inputLength (n - circuit.size))) <|
          linkFuel padStageSix padAppendFrameFuel <|
            linkFuel circuitJoinProgram
              (preserveRightFuel
                (balancedAppendFuel inputLength (padArityNodes circuit)
                  (padAritySuffix circuit)))
              circuitJoinFuel

def padArityBits (inputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  occurrenceStageBits inputLength
      (padFrontBits (padNodesCode circuit) (padOutputCode circuit) n) <|
    occurrenceStageBits inputLength
        (preserveRightBits
          (balancedLengthBits inputLength (padArityNodes circuit))
          (padNodesCode circuit)
          (Nat.pair (padNodesCode circuit)
            (Nat.pair n (padOutputCode circuit)))
          circuit.size) <|
      occurrenceStageBits inputLength
          (padRequestBits circuit.size (padNodesCode circuit)
            (padOutputCode circuit) n) <|
        occurrenceStageBits inputLength
            (preserveRightBits
              (constantNodePoolBits inputLength (n - circuit.size))
              (Nat.pair (n - circuit.size) 0)
              (Nat.pair (padNodesCode circuit) (padOutputCode circuit))
              (padSuffixCode circuit)) <|
          occurrenceStageBits inputLength
              (padAppendFrameBits (padSuffixCode circuit)
                (padNodesCode circuit) (padOutputCode circuit)) <|
            occurrenceStageBits inputLength
              (preserveRightBits
                (balancedAppendBits inputLength (padArityNodes circuit)
                  (padAritySuffix circuit))
                (Nat.pair (padNodesCode circuit) (padSuffixCode circuit))
                (padOutputCode circuit) (padAppendedCode circuit))
              (circuitJoinBits (padAppendedCode circuit)
                (padOutputCode circuit))

/-- **The arity padder, executed.**  No premise: the node count is measured by
the canonical length program, the constant suffix is generated by the indexed
pool of §3, and the concatenation is the canonical balanced append. -/
theorem run_padArityProgram (inputLength : ℕ) {n : ℕ}
    (circuit : BooleanCircuit n) :
    runNPOracleProgram padArityProgram (padArityBits inputLength circuit)
        (padArityFuel inputLength circuit)
        (initialNPOracleState inputLength
          (Nat.pair (encodeBooleanCircuit circuit) n)) =
      some (encodeBooleanCircuit circuit.padToArity) := by
  have hcircuit :
      encodeBooleanCircuit circuit =
        circuitCode (padNodesCode circuit) (padOutputCode circuit) :=
    rfl
  have hpadded :
      encodeBooleanCircuit circuit.padToArity =
        circuitCode (padAppendedCode circuit) (padOutputCode circuit) :=
    encodeBooleanCircuit_padToArity circuit
  rw [hcircuit, hpadded, padArityProgram, padArityBits, padArityFuel]
  refine run_occurrenceStage
    (run_padFrontProgram inputLength (padNodesCode circuit)
      (padOutputCode circuit) n _ (le_refl _)) ?_
  refine run_occurrenceStage
    (run_preserveRightProgram balancedLengthProgram inputLength
      (balancedLengthBits inputLength (padArityNodes circuit))
      (balancedLengthFuel (padArityNodes circuit)) (padNodesCode circuit)
      (Nat.pair (padNodesCode circuit) (Nat.pair n (padOutputCode circuit)))
      circuit.size
      (by
        have hrun := run_balancedLengthProgram inputLength (padArityNodes circuit)
        rwa [padArityNodes_length] at hrun)) ?_
  refine run_occurrenceStage
    (run_padRequestProgram inputLength circuit.size (padNodesCode circuit)
      (padOutputCode circuit) n _ (le_refl _)) ?_
  refine run_occurrenceStage
    (run_preserveRightProgram constantNodePoolProgram inputLength
      (constantNodePoolBits inputLength (n - circuit.size))
      (constantNodePoolFuel inputLength (n - circuit.size))
      (Nat.pair (n - circuit.size) 0)
      (Nat.pair (padNodesCode circuit) (padOutputCode circuit))
      (padSuffixCode circuit)
      (run_constantNodePoolProgram inputLength (n - circuit.size) _
        (le_refl _))) ?_
  refine run_occurrenceStage
    (run_padAppendFrameProgram inputLength (padSuffixCode circuit)
      (padNodesCode circuit) (padOutputCode circuit) _ (le_refl _)) ?_
  exact run_occurrenceStage
    (run_preserveRightProgram balancedAppendProgram inputLength
      (balancedAppendBits inputLength (padArityNodes circuit)
        (padAritySuffix circuit))
      (balancedAppendFuel inputLength (padArityNodes circuit)
        (padAritySuffix circuit))
      (Nat.pair (padNodesCode circuit) (padSuffixCode circuit))
      (padOutputCode circuit) (padAppendedCode circuit)
      (run_balancedAppendProgram inputLength _ (padArityNodes circuit)
        (padAritySuffix circuit) (le_refl _)))
    (run_circuitJoinProgram inputLength (padAppendedCode circuit)
      (padOutputCode circuit) _ (le_refl _))

/-! ## 6. The per-node restriction callee -/

/-- The tag field of a node code. -/
def nodeTagCode (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair code).2).1

/-- The tail of a node code after its tag cell. -/
def nodeTailCode (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair code).2).2

/-- The first payload field of a node code. -/
def nodeFirstCode (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (nodeTailCode code)).2).1

/-- The decoded first payload field of a node code. -/
def nodeFirstValue (code : ℕ) : ℕ :=
  (decodeNat (nodeFirstCode code)).getD 0

@[simp] theorem nodeTagCode_cons (value : ℕ) (rest : List ℕ) :
    nodeTagCode (encodeTaggedList (value :: rest)) = value := by
  simp [nodeTagCode, encodeTaggedList]

@[simp] theorem nodeFirstCode_cons (first second : ℕ) (rest : List ℕ) :
    nodeFirstCode (encodeTaggedList (first :: second :: rest)) = second := by
  simp [nodeFirstCode, nodeTailCode, encodeTaggedList]

/-- The per-node transform, as arithmetic on the node code: replace the code by
the constant-node code exactly when the tag is the input tag and the index has
left the native face. -/
def restrictSelect (native first tagCode code : ℕ) : ℕ :=
  if (tagCode - encodeNat 1) + (encodeNat 1 - tagCode) + (native - first) = 0
  then falseNodeCode
  else code

/-- The per-node transform read off one node code. -/
def restrictNodeCode (native code : ℕ) : ℕ :=
  restrictSelect native (nodeFirstValue code) (nodeTagCode code) code

private theorem encodeNat_injective {left right : ℕ}
    (hcode : encodeNat left = encodeNat right) : left = right := by
  have hdecode := congrArg decodeNat hcode
  rwa [decodeNat_encode, decodeNat_encode, Option.some.injEq] at hdecode

private theorem encodeNat_ne_one {value : ℕ} (hvalue : value ≠ 1) :
    encodeNat value ≠ encodeNat 1 :=
  fun hcode => hvalue (encodeNat_injective hcode)

private theorem restrictSelect_of_ne (native first tagCode code : ℕ)
    (htag : tagCode ≠ encodeNat 1) :
    restrictSelect native first tagCode code = code := by
  have hpositive :
      (tagCode - encodeNat 1) + (encodeNat 1 - tagCode) + (native - first) ≠ 0 := by
    rcases Nat.lt_or_ge tagCode (encodeNat 1) with hlt | hge
    · have : 0 < encodeNat 1 - tagCode := by omega
      omega
    · have : 0 < tagCode - encodeNat 1 := by omega
      omega
  simp only [restrictSelect, if_neg hpositive]

private theorem restrictSelect_input (native first code : ℕ) :
    restrictSelect native first (encodeNat 1) code =
      if native ≤ first then falseNodeCode else code := by
  simp only [restrictSelect, Nat.sub_self, Nat.zero_add]
  by_cases hle : native ≤ first
  · rw [if_pos hle, if_pos (by omega)]
  · rw [if_neg hle, if_neg (by omega)]

private theorem finSplitEquiv_symm_lt {core target : ℕ} (hcore : core ≤ target)
    (index : Fin target) (hlt : index.val < core) :
    (finSplitEquiv hcore).symm index = Sum.inl ⟨index.val, hlt⟩ := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [finSplitEquiv]

private theorem finSplitEquiv_symm_ge {core target : ℕ} (hcore : core ≤ target)
    (index : Fin target) (hge : core ≤ index.val) :
    (finSplitEquiv hcore).symm index =
      Sum.inr ⟨index.val - core, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp only [finSplitEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSumFinEquiv_apply_right, Fin.natAdd_mk]
  omega

/-- **Restriction, per node, at the encoding.**  The zero-suffix restriction of
one node is one arithmetic transform of its code. -/
theorem restrictNodeCode_encodeBooleanNode {native padded : ℕ}
    (hwidth : native ≤ padded) (node : BooleanNode padded) :
    restrictNodeCode native (encodeBooleanNode node) =
      encodeBooleanNode
        (restrictBooleanNode hwidth
          (zeroPadding (native := native) (padded := padded)) node) := by
  cases node with
  | const value =>
      have hrestrict :
          restrictBooleanNode hwidth
              (zeroPadding (native := native) (padded := padded))
              (BooleanNode.const value) =
            BooleanNode.const value := rfl
      have htag :
          nodeTagCode
              (encodeBooleanNode
                (BooleanNode.const value : BooleanNode padded)) =
            encodeNat 0 := by
        simp [encodeBooleanNode]
      rw [hrestrict]
      simp only [restrictNodeCode, htag]
      exact restrictSelect_of_ne _ _ _ _ (encodeNat_ne_one (by omega))
  | input index =>
      have htag :
          nodeTagCode
              (encodeBooleanNode
                (BooleanNode.input index : BooleanNode padded)) =
            encodeNat 1 := by
        simp [encodeBooleanNode]
      have hfirst :
          nodeFirstValue
              (encodeBooleanNode
                (BooleanNode.input index : BooleanNode padded)) =
            index.val := by
        simp [nodeFirstValue, encodeBooleanNode]
      simp only [restrictNodeCode, htag, hfirst, restrictSelect_input]
      by_cases hle : native ≤ index.val
      · have hrestrict :
            restrictBooleanNode hwidth
                (zeroPadding (native := native) (padded := padded))
                (BooleanNode.input index) =
              BooleanNode.const false := by
          simp only [restrictBooleanNode,
            finSplitEquiv_symm_ge hwidth index hle]
          rfl
        rw [if_pos hle, hrestrict]
        rfl
      · have hrestrict :
            restrictBooleanNode hwidth
                (zeroPadding (native := native) (padded := padded))
                (BooleanNode.input index) =
              BooleanNode.input ⟨index.val, by omega⟩ := by
          simp only [restrictBooleanNode,
            finSplitEquiv_symm_lt hwidth index (by omega)]
        rw [if_neg hle, hrestrict]
        rfl
  | not child =>
      have hrestrict :
          restrictBooleanNode hwidth
              (zeroPadding (native := native) (padded := padded))
              (BooleanNode.not child) =
            BooleanNode.not child := rfl
      have htag :
          nodeTagCode
              (encodeBooleanNode
                (BooleanNode.not child : BooleanNode padded)) =
            encodeNat 2 := by
        simp [encodeBooleanNode]
      rw [hrestrict]
      simp only [restrictNodeCode, htag]
      exact restrictSelect_of_ne _ _ _ _ (encodeNat_ne_one (by omega))
  | and left right =>
      have hrestrict :
          restrictBooleanNode hwidth
              (zeroPadding (native := native) (padded := padded))
              (BooleanNode.and left right) =
            BooleanNode.and left right := rfl
      have htag :
          nodeTagCode
              (encodeBooleanNode
                (BooleanNode.and left right : BooleanNode padded)) =
            encodeNat 3 := by
        simp [encodeBooleanNode]
      rw [hrestrict]
      simp only [restrictNodeCode, htag]
      exact restrictSelect_of_ne _ _ _ _ (encodeNat_ne_one (by omega))
  | or left right =>
      have hrestrict :
          restrictBooleanNode hwidth
              (zeroPadding (native := native) (padded := padded))
              (BooleanNode.or left right) =
            BooleanNode.or left right := rfl
      have htag :
          nodeTagCode
              (encodeBooleanNode
                (BooleanNode.or left right : BooleanNode padded)) =
            encodeNat 4 := by
        simp [encodeBooleanNode]
      rw [hrestrict]
      simp only [restrictNodeCode, htag]
      exact restrictSelect_of_ne _ _ _ _ (encodeNat_ne_one (by omega))

/-! ## 7. The restriction callee as a program -/

/-- Open a node code into `pair first (pair tag code)`. -/
def restrictSplitProgram : NPOracleProgram :=
  [ .copy 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairRight 5 5 5
  , .unpairLeft 5 5 6
  , .pair 4 2 4 7
  , .pair 5 4 0 8
  , .halt 0
  ]

@[simp] theorem restrictSplitProgram_oracleFree :
    OracleFree restrictSplitProgram := by
  rfl

def restrictSplitFuel : ℕ := 9

def restrictSplitBits (code : ℕ) : ℕ :=
  natBitLength
    (max code
      (Nat.pair (nodeFirstCode code) (Nat.pair (nodeTagCode code) code)))

theorem run_restrictSplitProgram (inputLength code maximumBits : ℕ)
    (hbits : restrictSplitBits code ≤ maximumBits) :
    runNPOracleProgram restrictSplitProgram maximumBits restrictSplitFuel
        (initialNPOracleState inputLength code) =
      some
        (Nat.pair (nodeFirstCode code)
          (Nat.pair (nodeTagCode code) code)) := by
  have hcode : natBitLength code ≤ maximumBits :=
    (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
  have houtputWord :
      natBitLength
          (Nat.pair (nodeFirstCode code) (Nat.pair (nodeTagCode code) code)) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
  have hsecond : natBitLength (Nat.unpair code).2 ≤ maximumBits :=
    bits_of_le (Nat.unpair_right_le code) hcode
  have htag : natBitLength (nodeTagCode code) ≤ maximumBits :=
    bits_of_le
      ((Nat.unpair_left_le _).trans (Nat.unpair_right_le code)) hcode
  have htail : natBitLength (nodeTailCode code) ≤ maximumBits :=
    bits_of_le
      ((Nat.unpair_right_le _).trans (Nat.unpair_right_le code)) hcode
  have hcell :
      natBitLength (Nat.unpair (nodeTailCode code)).2 ≤ maximumBits :=
    bits_of_le (Nat.unpair_right_le _) htail
  have hfirst : natBitLength (nodeFirstCode code) ≤ maximumBits :=
    bits_of_le (Nat.unpair_left_le _) hcell
  have hframe :
      natBitLength (Nat.pair (nodeTagCode code) code) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputWord
  rw [show restrictSplitFuel = 8 + 1 by rfl]
  rw [run_copy_instruction (value := code) (by rfl) rfl
    (by simp [initialNPOracleState]) hcode]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair code).2) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hsecond]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := nodeTagCode code) (by rfl) rfl
    (by simp [nodeTagCode, NPOracleState.write, NPOracleState.jump]) htag]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := nodeTailCode code) (by rfl) rfl
    (by simp [nodeTailCode, NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (nodeTailCode code)).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcell]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := nodeFirstCode code) (by rfl) rfl
    (by simp [nodeFirstCode, NPOracleState.write, NPOracleState.jump]) hfirst]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (nodeTagCode code) code)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hframe]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (nodeFirstCode code) (Nat.pair (nodeTagCode code) code))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputWord]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputWord

/-- The saturating witness that the tag is the input tag and the index has left
the native face. -/
def restrictDelta (native first tagCode : ℕ) : ℕ :=
  (tagCode - encodeNat 1) + (encodeNat 1 - tagCode) + (native - first)

theorem restrictSelect_eq_ite (native first tagCode code : ℕ) :
    restrictSelect native first tagCode code =
      if restrictDelta native first tagCode = 0 then falseNodeCode else code :=
  rfl

/-- Select the constant-node code exactly on the padded input coordinates. -/
def restrictSelectProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .set 6 (encodeNat 1) 5
  , .subtract 4 6 7 6
  , .subtract 6 4 8 7
  , .add 7 8 7 8
  , .subtract 1 2 8 9
  , .add 7 8 7 10
  , .branchZero 7 11 12
  , .set 5 falseNodeCode 12
  , .copy 5 0 13
  , .halt 0
  ]

@[simp] theorem restrictSelectProgram_oracleFree :
    OracleFree restrictSelectProgram := by
  rfl

def restrictSelectFuel : ℕ := 14

def restrictSelectBits (native first tagCode code : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair first (Nat.pair tagCode code))
      (max (encodeNat 1 + tagCode + native) falseNodeCode))

theorem run_restrictSelectProgram
    (native first tagCode code maximumBits : ℕ)
    (hbits : restrictSelectBits native first tagCode code ≤ maximumBits) :
    runNPOracleProgram restrictSelectProgram maximumBits restrictSelectFuel
        (initialNPOracleState native
          (Nat.pair first (Nat.pair tagCode code))) =
      some (restrictSelect native first tagCode code) := by
  have hinput :
      natBitLength (Nat.pair first (Nat.pair tagCode code)) ≤ maximumBits :=
    (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
  have hsum :
      natBitLength (encodeNat 1 + tagCode + native) ≤ maximumBits :=
    (natBitLength_mono
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))).trans hbits
  have hfalse : natBitLength falseNodeCode ≤ maximumBits :=
    (natBitLength_mono
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))).trans hbits
  have hfirst : natBitLength first ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hframe : natBitLength (Nat.pair tagCode code) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have htag : natBitLength tagCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hframe
  have hcode : natBitLength code ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hframe
  have hone : natBitLength (encodeNat 1) ≤ maximumBits :=
    bits_of_le (by omega) hsum
  have hleft : natBitLength (tagCode - encodeNat 1) ≤ maximumBits :=
    bits_of_le (by omega) hsum
  have hright : natBitLength (encodeNat 1 - tagCode) ≤ maximumBits :=
    bits_of_le (by omega) hsum
  have hgap :
      natBitLength
          ((tagCode - encodeNat 1) + (encodeNat 1 - tagCode)) ≤ maximumBits :=
    bits_of_le (by omega) hsum
  have hface : natBitLength (native - first) ≤ maximumBits :=
    bits_of_le (by omega) hsum
  have hdelta :
      natBitLength (restrictDelta native first tagCode) ≤ maximumBits :=
    bits_of_le (by simp only [restrictDelta]; omega) hsum
  rw [restrictSelect_eq_ite]
  rw [show restrictSelectFuel = 13 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := first) (by rfl) rfl
    (by simp [initialNPOracleState]) hfirst]
  rw [show (13 : ℕ) = 12 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair tagCode code) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hframe]
  rw [show (12 : ℕ) = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tagCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htag]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcode]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_set_instruction (value := encodeNat 1) (by rfl) rfl hone]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_subtract_instruction (value := tagCode - encodeNat 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hleft]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_subtract_instruction (value := encodeNat 1 - tagCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hright]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_add_instruction
    (value := (tagCode - encodeNat 1) + (encodeNat 1 - tagCode)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hgap]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_subtract_instruction (value := native - first) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hface]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_add_instruction (value := restrictDelta native first tagCode)
    (by rfl) rfl
    (by simp [restrictDelta, NPOracleState.write, NPOracleState.jump]) hdelta]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_branchZero_instruction (register := 7) (by rfl) rfl]
  by_cases hzero : restrictDelta native first tagCode = 0
  · rw [if_pos hzero, show (3 : ℕ) = 2 + 1 by omega]
    rw [run_set_instruction (pc := 11) (register := 5) (value := falseNodeCode)
      (next := 12) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump, hzero]) hfalse]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_copy_instruction (pc := 12) (source := 5) (destination := 0)
      (next := 13) (value := falseNodeCode) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hfalse]
    exact run_halt_instruction (fuel := 0) (pc := 13) (outputRegister := 0)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hfalse
  · rw [if_neg hzero, show (3 : ℕ) = 2 + 1 by omega]
    rw [run_copy_instruction (pc := 12) (source := 5) (destination := 0)
      (next := 13) (value := code) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump, hzero])
      (by simp [NPOracleState.write, NPOracleState.jump]) hcode]
    exact run_halt_instruction (fuel := 1) (pc := 13) (outputRegister := 0)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcode

/-! ## 8. The restriction map over the node list -/

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-- **The per-node restriction callee.**  One fixed stream from a node code to
the code of its zero-suffix restriction, reading the native width from the
public length register. -/
def restrictNodeProgram : NPOracleProgram :=
  linkPrograms restrictSplitProgram
    (linkPrograms (preserveRightProgram canonicalNatDecodeProgram)
      restrictSelectProgram)

theorem restrictNodeProgram_oracleFree : OracleFree restrictNodeProgram :=
  oracleFree_linkPrograms restrictSplitProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree canonicalNatDecodeProgram
        canonicalNatDecodeProgram_oracleFree)
      restrictSelectProgram_oracleFree)

def restrictNodeFuel (first : ℕ) : ℕ :=
  linkFuel
      (linkPrograms (preserveRightProgram canonicalNatDecodeProgram)
        restrictSelectProgram)
      restrictSplitFuel <|
    linkFuel restrictSelectProgram
      (preserveRightFuel (canonicalNatDecodeFuel first)) restrictSelectFuel

def restrictNodeBits (native code first : ℕ) : ℕ :=
  occurrenceStageBits native (restrictSplitBits code) <|
    occurrenceStageBits native
      (preserveRightBits (canonicalNatDecodeBits native first)
        (nodeFirstCode code) (Nat.pair (nodeTagCode code) code) first)
      (restrictSelectBits native first (nodeTagCode code) code)

/-- **The per-node callee, executed.** -/
theorem run_restrictNodeProgram (native code first : ℕ)
    (hfirst : nodeFirstCode code = encodeNat first) :
    runNPOracleProgram restrictNodeProgram (restrictNodeBits native code first)
        (restrictNodeFuel first) (initialNPOracleState native code) =
      some (restrictNodeCode native code) := by
  have hvalue : nodeFirstValue code = first := by
    simp [nodeFirstValue, hfirst]
  rw [restrictNodeProgram, restrictNodeBits, restrictNodeFuel, restrictNodeCode,
    hvalue]
  refine run_occurrenceStage
    (run_restrictSplitProgram native code _ (le_refl _)) ?_
  exact run_occurrenceStage
    (run_preserveRightProgram canonicalNatDecodeProgram native
      (canonicalNatDecodeBits native first) (canonicalNatDecodeFuel first)
      (nodeFirstCode code) (Nat.pair (nodeTagCode code) code) first
      (by
        rw [hfirst]
        exact run_canonicalNatDecodeProgram native first))
    (run_restrictSelectProgram native first (nodeTagCode code) code _
      (le_refl _))

private theorem nodeFirstCode_encodeBooleanNode {n : ℕ}
    (node : BooleanNode n) :
    nodeFirstCode (encodeBooleanNode node) =
      encodeNat (nodeFirstValue (encodeBooleanNode node)) := by
  cases node <;> simp [nodeFirstValue, encodeBooleanNode]

def restrictMapCalleeFuel (raw : ℕ) : ℕ :=
  restrictNodeFuel (nodeFirstValue (Nat.unpair raw).2)

def restrictMapOutput (native raw : ℕ) : ℕ :=
  restrictNodeCode native (Nat.unpair raw).2

def restrictMapCalleeBits (native : ℕ) (codes : List ℕ) : ℕ :=
  (codes.map fun code =>
    restrictNodeBits native code (nodeFirstValue code)).foldr max 1

def restrictMapCallBits (native : ℕ) (codes : List ℕ) : ℕ :=
  max
    (balancedCallRequiredBits (restrictMapOutput native)
      (codes.map (nativeInputRequest native)))
    (restrictMapCalleeBits native codes)

/-- **The restriction map.**  The request tree beside one balanced call. -/
def restrictMapProgram : NPOracleProgram :=
  linkPrograms nativeInputRequestTreeProgram
    (balancedCallProgram restrictNodeProgram)

theorem restrictMapProgram_oracleFree : OracleFree restrictMapProgram :=
  oracleFree_linkPrograms nativeInputRequestTreeProgram_oracleFree
    (balancedCallProgram_oracleFree restrictNodeProgram_oracleFree)

def restrictMapFuel (native : ℕ) (codes : List ℕ) : ℕ :=
  linkFuel (balancedCallProgram restrictNodeProgram)
    (nativeInputRequestTreeFuel codes)
    (balancedCallFuel restrictNodeProgram restrictMapCalleeFuel
      (codes.map (nativeInputRequest native)))

def restrictMapBits (native : ℕ) (codes : List ℕ) : ℕ :=
  occurrenceStageBits native (nativeInputRequestTreeBits native codes)
    (restrictMapCallBits native codes)

private theorem run_restrictNodeProgram_request {padded : ℕ} (native : ℕ)
    (nodes : List (BooleanNode padded)) (node : BooleanNode padded)
    (hnode : encodeBooleanNode node ∈ nodes.map encodeBooleanNode) :
    runNPOracleProgram restrictNodeProgram
        (restrictMapCallBits native (nodes.map encodeBooleanNode))
        (restrictMapCalleeFuel
          (nativeInputRequest native (encodeBooleanNode node)))
        (initialNPOracleState
          (Nat.unpair (nativeInputRequest native (encodeBooleanNode node))).1
          (Nat.unpair
            (nativeInputRequest native (encodeBooleanNode node))).2) =
      some
        (restrictMapOutput native
          (nativeInputRequest native (encodeBooleanNode node))) := by
  have hleft :
      (Nat.unpair (nativeInputRequest native (encodeBooleanNode node))).1 =
        native := by
    simp [nativeInputRequest]
  have hright :
      (Nat.unpair (nativeInputRequest native (encodeBooleanNode node))).2 =
        encodeBooleanNode node := by
    simp [nativeInputRequest]
  have hmember :
      restrictNodeBits native (encodeBooleanNode node)
          (nodeFirstValue (encodeBooleanNode node)) ∈
        (nodes.map encodeBooleanNode).map fun code =>
          restrictNodeBits native code (nodeFirstValue code) :=
    List.mem_map.mpr ⟨encodeBooleanNode node, hnode, rfl⟩
  have hcalleeBits :
      restrictNodeBits native (encodeBooleanNode node)
          (nodeFirstValue (encodeBooleanNode node)) ≤
        restrictMapCallBits native (nodes.map encodeBooleanNode) := by
    rw [restrictMapCallBits, restrictMapCalleeBits]
    exact le_trans (le_foldr_max_of_mem hmember) (Nat.le_max_right _ _)
  simp only [restrictMapOutput, restrictMapCalleeFuel, hleft, hright]
  exact run_bits_mono
    (run_restrictNodeProgram native (encodeBooleanNode node)
      (nodeFirstValue (encodeBooleanNode node))
      (nodeFirstCode_encodeBooleanNode node))
    hcalleeBits

set_option maxHeartbeats 400000 in
-- The statement carries the whole balanced-call width and fuel envelope at one
-- node list, so elaborating it alone exceeds the default budget.
/-- **The restriction map, executed** on any list of genuine node codes. -/
theorem run_restrictMapProgram {padded : ℕ} (native : ℕ)
    (nodes : List (BooleanNode padded)) :
    runNPOracleProgram restrictMapProgram
        (restrictMapBits native (nodes.map encodeBooleanNode))
        (restrictMapFuel native (nodes.map encodeBooleanNode))
        (initialNPOracleState native
          (encodeBalancedList (nodes.map encodeBooleanNode))) =
      some
        (encodeBalancedList
          ((nodes.map encodeBooleanNode).map (restrictNodeCode native))) := by
  have hmap :
      ((nodes.map encodeBooleanNode).map
            (nativeInputRequest native)).map (restrictMapOutput native) =
        (nodes.map encodeBooleanNode).map (restrictNodeCode native) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro _code _hcode
    simp [restrictMapOutput, nativeInputRequest]
  rw [restrictMapProgram, restrictMapBits, restrictMapFuel, ← hmap]
  refine run_occurrenceStage
    (run_nativeInputRequestTreeProgram native (nodes.map encodeBooleanNode)) ?_
  refine run_balancedCallProgram_from
    (maximumBits := restrictMapCallBits native (nodes.map encodeBooleanNode))
    native ((nodes.map encodeBooleanNode).map (nativeInputRequest native))
    restrictMapCalleeFuel (restrictMapOutput native) (Nat.le_max_left _ _) ?_
  intro request hrequest
  obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hrequest
  obtain ⟨node, _hnode, rfl⟩ := List.mem_map.mp hcode
  exact run_restrictNodeProgram_request native nodes node hcode

/-! ## 9. Restricting a whole oracle circuit -/

/-- Open the circuit code beside the native width and present the node list on
the explicit-input call ABI. -/
def restrictFrontProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 2 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 4 6 5
  , .unpairRight 6 6 6
  , .unpairLeft 6 6 7
  , .pair 3 5 3 8
  , .pair 3 6 0 9
  , .halt 0
  ]

@[simp] theorem restrictFrontProgram_oracleFree :
    OracleFree restrictFrontProgram := by
  rfl

def restrictFrontFuel : ℕ := 10

def restrictFrontBits (nodesCode outputCode native : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair (circuitCode nodesCode outputCode) native)
      (Nat.pair (Nat.pair native nodesCode) outputCode))

theorem run_restrictFrontProgram
    (inputLength nodesCode outputCode native maximumBits : ℕ)
    (hbits : restrictFrontBits nodesCode outputCode native ≤ maximumBits) :
    runNPOracleProgram restrictFrontProgram maximumBits restrictFrontFuel
        (initialNPOracleState inputLength
          (Nat.pair (circuitCode nodesCode outputCode) native)) =
      some
        (Nat.pair (nativeInputRequest native nodesCode) outputCode) := by
  have hinput :
      natBitLength (Nat.pair (circuitCode nodesCode outputCode) native) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
  have houtputWord :
      natBitLength (Nat.pair (Nat.pair native nodesCode) outputCode) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
  have hcode : natBitLength (circuitCode nodesCode outputCode) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hnative : natBitLength native ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hcell :
      natBitLength
          (Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0))) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair 1 _) hcode
  have hnodes : natBitLength nodesCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hcell
  have htail :
      natBitLength (Nat.pair 1 (Nat.pair outputCode 0)) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hcell
  have hlast : natBitLength (Nat.pair outputCode 0) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair 1 _) htail
  have houtput : natBitLength outputCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hlast
  have hrequest : natBitLength (Nat.pair native nodesCode) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputWord
  rw [nativeInputRequest, circuitCode_eq_pair]
  rw [show restrictFrontFuel = 9 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value :=
      Nat.pair 1 (Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0))))
    (by rfl) rfl (by simp [initialNPOracleState])
    (by rw [← circuitCode_eq_pair]; exact hcode)]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := native) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hnative]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair nodesCode (Nat.pair 1 (Nat.pair outputCode 0)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hcell]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := nodesCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnodes]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair 1 (Nat.pair outputCode 0)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair outputCode 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlast]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := outputCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair native nodesCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrequest]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair native nodesCode) outputCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputWord]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputWord

private def restrictMappedCode (native : ℕ) {padded : ℕ}
    (circuit : BooleanCircuit padded) : ℕ :=
  encodeBalancedList ((padArityNodes circuit).map (restrictNodeCode native))

/-- **The oracle restriction.**  From the circuit code beside the native width,
the code of the circuit restricted to the native face. -/
def restrictOracleProgram : NPOracleProgram :=
  linkPrograms restrictFrontProgram
    (linkPrograms (preserveRightProgram (nativeCallProgram restrictMapProgram))
      circuitJoinProgram)

theorem restrictOracleProgram_oracleFree : OracleFree restrictOracleProgram :=
  oracleFree_linkPrograms restrictFrontProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree (nativeCallProgram restrictMapProgram)
        (nativeCallProgram_oracleFree restrictMapProgram_oracleFree))
      circuitJoinProgram_oracleFree)

def restrictOracleFuel (native : ℕ) {padded : ℕ}
    (circuit : BooleanCircuit padded) : ℕ :=
  linkFuel
      (linkPrograms
        (preserveRightProgram (nativeCallProgram restrictMapProgram))
        circuitJoinProgram)
      restrictFrontFuel <|
    linkFuel circuitJoinProgram
      (preserveRightFuel
        (nativeCallFuel restrictMapProgram
          (restrictMapFuel native (padArityNodes circuit)) native
          (encodeBalancedList (padArityNodes circuit))))
      circuitJoinFuel

def restrictOracleBits (inputLength native : ℕ) {padded : ℕ}
    (circuit : BooleanCircuit padded) : ℕ :=
  occurrenceStageBits inputLength
      (restrictFrontBits (encodeBalancedList (padArityNodes circuit))
        (encodeNat circuit.output.val) native) <|
    occurrenceStageBits inputLength
      (preserveRightBits
        (nativeCallBits inputLength native
          (encodeBalancedList (padArityNodes circuit))
          (restrictMappedCode native circuit)
          (restrictMapBits native (padArityNodes circuit)))
        (nativeInputRequest native
          (encodeBalancedList (padArityNodes circuit)))
        (encodeNat circuit.output.val) (restrictMappedCode native circuit))
      (circuitJoinBits (restrictMappedCode native circuit)
        (encodeNat circuit.output.val))

private theorem map_restrictNodeCode {native padded : ℕ}
    (hwidth : native ≤ padded) (nodes : List (BooleanNode padded)) :
    (nodes.map encodeBooleanNode).map (restrictNodeCode native) =
      nodes.map fun node =>
        encodeBooleanNode
          (restrictBooleanNode hwidth
            (zeroPadding (native := native) (padded := padded)) node) := by
  induction nodes with
  | nil => rfl
  | cons node rest inductionHypothesis =>
      simp only [List.map_cons, inductionHypothesis,
        restrictNodeCode_encodeBooleanNode hwidth node]

private theorem restrictMappedCode_eq {native padded : ℕ}
    (hwidth : native ≤ padded) (circuit : BooleanCircuit padded) :
    encodeBooleanCircuit (restrictPaddedOracle circuit hwidth) =
      circuitCode (restrictMappedCode native circuit)
        (encodeNat circuit.output.val) := by
  rw [encodeBooleanCircuit_restrictPaddedOracle circuit hwidth,
    restrictMappedCode, padArityNodes, map_restrictNodeCode hwidth,
    circuitCode]

set_option maxHeartbeats 400000 in
-- The statement carries the explicit-input call envelope and the whole node
-- map at one circuit, so elaborating it alone exceeds the default budget.
/-- **The oracle restriction, executed.**  No premise: the per-node callee runs
at the native input length, so the padded index comparison is a register read
rather than a target-derived immediate. -/
theorem run_restrictOracleProgram (inputLength : ℕ) {native padded : ℕ}
    (hwidth : native ≤ padded) (circuit : BooleanCircuit padded) :
    runNPOracleProgram restrictOracleProgram
        (restrictOracleBits inputLength native circuit)
        (restrictOracleFuel native circuit)
        (initialNPOracleState inputLength
          (Nat.pair (encodeBooleanCircuit circuit) native)) =
      some (encodeBooleanCircuit (restrictPaddedOracle circuit hwidth)) := by
  have hcircuit :
      encodeBooleanCircuit circuit =
        circuitCode (encodeBalancedList (padArityNodes circuit))
          (encodeNat circuit.output.val) :=
    rfl
  rw [hcircuit, restrictMappedCode_eq hwidth circuit, restrictOracleProgram,
    restrictOracleBits, restrictOracleFuel]
  refine run_occurrenceStage
    (run_restrictFrontProgram inputLength
      (encodeBalancedList (padArityNodes circuit))
      (encodeNat circuit.output.val) native _ (le_refl _)) ?_
  exact run_occurrenceStage
    (run_preserveRightProgram (nativeCallProgram restrictMapProgram) inputLength
      (nativeCallBits inputLength native
        (encodeBalancedList (padArityNodes circuit))
        (restrictMappedCode native circuit)
        (restrictMapBits native (padArityNodes circuit)))
      (nativeCallFuel restrictMapProgram
        (restrictMapFuel native (padArityNodes circuit)) native
        (encodeBalancedList (padArityNodes circuit)))
      (nativeInputRequest native (encodeBalancedList (padArityNodes circuit)))
      (encodeNat circuit.output.val) (restrictMappedCode native circuit)
      (run_nativeCallProgram restrictMapProgram inputLength native
        (encodeBalancedList (padArityNodes circuit))
        (restrictMappedCode native circuit)
        (restrictMapBits native (padArityNodes circuit))
        (restrictMapFuel native (padArityNodes circuit))
        (run_restrictMapProgram native circuit.nodes)))
    (run_circuitJoinProgram inputLength (restrictMappedCode native circuit)
      (encodeNat circuit.output.val) _ (le_refl _))

/-! ## 10. The substituted circuit, end to end -/

/-- Pair the oracle code with the native width for the restriction stage. -/
def substFrontProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .pair 2 4 2 4
  , .pair 2 3 0 5
  , .halt 0
  ]

@[simp] theorem substFrontProgram_oracleFree :
    OracleFree substFrontProgram := by
  rfl

def substFrontFuel : ℕ := 6

def substFrontBits (oracleCode native arity word : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair oracleCode (Nat.pair native (Nat.pair arity word)))
      (Nat.pair (Nat.pair oracleCode native)
        (Nat.pair native (Nat.pair arity word))))

theorem run_substFrontProgram
    (inputLength oracleCode native arity word maximumBits : ℕ)
    (hbits : substFrontBits oracleCode native arity word ≤ maximumBits) :
    runNPOracleProgram substFrontProgram maximumBits substFrontFuel
        (initialNPOracleState inputLength
          (Nat.pair oracleCode (Nat.pair native (Nat.pair arity word)))) =
      some
        (Nat.pair (Nat.pair oracleCode native)
          (Nat.pair native (Nat.pair arity word))) := by
  have hinput :
      natBitLength
          (Nat.pair oracleCode (Nat.pair native (Nat.pair arity word))) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
  have houtputWord :
      natBitLength
          (Nat.pair (Nat.pair oracleCode native)
            (Nat.pair native (Nat.pair arity word))) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
  have horacle : natBitLength oracleCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hrest :
      natBitLength (Nat.pair native (Nat.pair arity word)) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hnative : natBitLength native ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hrest
  have hframe : natBitLength (Nat.pair oracleCode native) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputWord
  rw [show substFrontFuel = 5 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := oracleCode) (by rfl) rfl
    (by simp [initialNPOracleState]) horacle]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair native (Nat.pair arity word)) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hrest]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := native) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnative]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair oracleCode native) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hframe]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (Nat.pair oracleCode native)
        (Nat.pair native (Nat.pair arity word)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputWord]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputWord

/-- Assemble the substitution runner's own request beside the native width. -/
def substRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 7 2 7 7
  , .pair 6 7 7 8
  , .pair 6 7 7 9
  , .pair 7 4 0 10
  , .halt 0
  ]

@[simp] theorem substRequestProgram_oracleFree :
    OracleFree substRequestProgram := by
  rfl

def substRequestFuel : ℕ := 11

def substRequestBits (restrictedCode native arity word : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair restrictedCode (Nat.pair native (Nat.pair arity word)))
      (Nat.pair
        (Nat.pair arity (Nat.pair arity (Nat.pair word restrictedCode)))
        native))

theorem run_substRequestProgram
    (inputLength restrictedCode native arity word maximumBits : ℕ)
    (hbits : substRequestBits restrictedCode native arity word ≤ maximumBits) :
    runNPOracleProgram substRequestProgram maximumBits substRequestFuel
        (initialNPOracleState inputLength
          (Nat.pair restrictedCode (Nat.pair native (Nat.pair arity word)))) =
      some
        (Nat.pair
          (nativeInputRequest arity
            (Nat.pair arity (Nat.pair word restrictedCode)))
          native) := by
  have hinput :
      natBitLength
          (Nat.pair restrictedCode (Nat.pair native (Nat.pair arity word))) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
  have houtputWord :
      natBitLength
          (Nat.pair
            (Nat.pair arity (Nat.pair arity (Nat.pair word restrictedCode)))
            native) ≤
        maximumBits :=
    (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
  have hrestricted : natBitLength restrictedCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hrest :
      natBitLength (Nat.pair native (Nat.pair arity word)) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hnative : natBitLength native ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hrest
  have hpair : natBitLength (Nat.pair arity word) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hrest
  have harity : natBitLength arity ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hpair
  have hword : natBitLength word ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hpair
  have hrequestCode :
      natBitLength (Nat.pair arity (Nat.pair word restrictedCode)) ≤
        maximumBits :=
    bits_of_le
      ((Nat.right_le_pair arity _).trans (Nat.left_le_pair _ native))
      houtputWord
  have hbody : natBitLength (Nat.pair word restrictedCode) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair arity _) hrequestCode
  have hframed :
      natBitLength
          (Nat.pair arity (Nat.pair arity (Nat.pair word restrictedCode))) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputWord
  rw [nativeInputRequest]
  rw [show substRequestFuel = 10 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := restrictedCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hrestricted]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair native (Nat.pair arity word)) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hrest]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := native) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnative]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair arity word) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpair]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := arity) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harity]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := word) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hword]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair word restrictedCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbody]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair arity (Nat.pair word restrictedCode)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrequestCode]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair arity (Nat.pair arity (Nat.pair word restrictedCode)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hframed]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (Nat.pair arity (Nat.pair arity (Nat.pair word restrictedCode)))
        native)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputWord]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputWord

/-- The substitution runner's own request at a restricted oracle. -/
def substRequest
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {pcp : ExecutableProjectionPCP machine timeBound}
    {arity : ℕ} (input : BitInput arity) {padded : ℕ}
    (oracle : BooleanCircuit padded)
    (hwidth : pcp.nativeWidth arity ≤ padded) :
    ProjectionSubstitutionRequest pcp where
  inputArity := arity
  input := input
  oracle := restrictPaddedOracle oracle hwidth

/-- **The substituted circuit's encoder.**  Restrict, substitute, pad. -/
def substitutedEncodingProgram (runner : NPOracleProgram) : NPOracleProgram :=
  linkPrograms substFrontProgram <|
    linkPrograms (preserveRightProgram restrictOracleProgram) <|
      linkPrograms substRequestProgram <|
        linkPrograms (preserveRightProgram (nativeCallProgram runner))
          padArityProgram

private def substTailProgram (runner : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (preserveRightProgram (nativeCallProgram runner))
    padArityProgram

private def substMidProgram (runner : NPOracleProgram) : NPOracleProgram :=
  linkPrograms substRequestProgram (substTailProgram runner)

private def substBodyProgram (runner : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (preserveRightProgram restrictOracleProgram)
    (substMidProgram runner)

def substitutedEncodingFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {pcp : ExecutableProjectionPCP machine timeBound}
    (substitution : ExecutableProjectionSubstitution pcp)
    (inputLength : ℕ) {arity : ℕ} (input : BitInput arity) {padded : ℕ}
    (oracle : BooleanCircuit padded)
    (hwidth : pcp.nativeWidth arity ≤ padded) : ℕ :=
  linkFuel (substBodyProgram substitution.runner.program) substFrontFuel <|
    linkFuel (substMidProgram substitution.runner.program)
        (preserveRightFuel
          (restrictOracleFuel (pcp.nativeWidth arity) oracle)) <|
      linkFuel (substTailProgram substitution.runner.program)
          substRequestFuel <|
        linkFuel padArityProgram
          (preserveRightFuel
            (nativeCallFuel substitution.runner.program
              (substitution.runner.budget (substRequest input oracle hwidth))
              arity
              (ProjectionSubstitutionRequest.code
                (substRequest input oracle hwidth))))
          (padArityFuel inputLength
            (substitution.circuit (substRequest input oracle hwidth)))

def substitutedEncodingBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {pcp : ExecutableProjectionPCP machine timeBound}
    (substitution : ExecutableProjectionSubstitution pcp)
    (inputLength : ℕ) {arity : ℕ} (input : BitInput arity) {padded : ℕ}
    (oracle : BooleanCircuit padded)
    (hwidth : pcp.nativeWidth arity ≤ padded) : ℕ :=
  occurrenceStageBits inputLength
      (substFrontBits (encodeBooleanCircuit oracle) (pcp.nativeWidth arity)
        arity (encodeBitInput input)) <|
    occurrenceStageBits inputLength
        (preserveRightBits
          (restrictOracleBits inputLength (pcp.nativeWidth arity) oracle)
          (Nat.pair (encodeBooleanCircuit oracle) (pcp.nativeWidth arity))
          (Nat.pair (pcp.nativeWidth arity)
            (Nat.pair arity (encodeBitInput input)))
          (encodeBooleanCircuit (restrictPaddedOracle oracle hwidth))) <|
      occurrenceStageBits inputLength
          (substRequestBits
            (encodeBooleanCircuit (restrictPaddedOracle oracle hwidth))
            (pcp.nativeWidth arity) arity (encodeBitInput input)) <|
        occurrenceStageBits inputLength
          (preserveRightBits
            (nativeCallBits inputLength arity
              (ProjectionSubstitutionRequest.code
                (substRequest input oracle hwidth))
              (encodeBooleanCircuit
                (substitution.circuit (substRequest input oracle hwidth)))
              (substitution.runner.budget (substRequest input oracle hwidth)))
            (nativeInputRequest arity
              (ProjectionSubstitutionRequest.code
                (substRequest input oracle hwidth)))
            (pcp.nativeWidth arity)
            (encodeBooleanCircuit
              (substitution.circuit (substRequest input oracle hwidth))))
          (padArityBits inputLength
            (substitution.circuit (substRequest input oracle hwidth)))

set_option maxHeartbeats 400000 in
-- The statement carries four linked envelopes and the substitution runner's own
-- budget at one request, so elaborating it alone exceeds the default budget.
/-- **The substituted circuit's encoder, executed.**  From the recovered
oracle's own code, the native width, the input arity and the refuter word, the
fixed stream emits the encoding of the padded substituted circuit.  The only
imported execution is the published substitution runner's `computes`. -/
theorem run_substitutedEncodingProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {pcp : ExecutableProjectionPCP machine timeBound}
    (substitution : ExecutableProjectionSubstitution pcp)
    (inputLength : ℕ) {arity : ℕ} (input : BitInput arity) {padded : ℕ}
    (oracle : BooleanCircuit padded)
    (hwidth : pcp.nativeWidth arity ≤ padded) :
    runNPOracleProgram
        (substitutedEncodingProgram substitution.runner.program)
        (substitutedEncodingBits substitution inputLength input oracle hwidth)
        (substitutedEncodingFuel substitution inputLength input oracle hwidth)
        (initialNPOracleState inputLength
          (Nat.pair (encodeBooleanCircuit oracle)
            (Nat.pair (pcp.nativeWidth arity)
              (Nat.pair arity (encodeBitInput input))))) =
      some
        (encodeBooleanCircuit
          (substitution.circuit (substRequest input oracle hwidth)).padToArity) := by
  rw [substitutedEncodingProgram, substitutedEncodingBits,
    substitutedEncodingFuel]
  refine run_occurrenceStage
    (run_substFrontProgram inputLength (encodeBooleanCircuit oracle)
      (pcp.nativeWidth arity) arity (encodeBitInput input) _ (le_refl _)) ?_
  refine run_occurrenceStage
    (run_preserveRightProgram restrictOracleProgram inputLength
      (restrictOracleBits inputLength (pcp.nativeWidth arity) oracle)
      (restrictOracleFuel (pcp.nativeWidth arity) oracle)
      (Nat.pair (encodeBooleanCircuit oracle) (pcp.nativeWidth arity))
      (Nat.pair (pcp.nativeWidth arity)
        (Nat.pair arity (encodeBitInput input)))
      (encodeBooleanCircuit (restrictPaddedOracle oracle hwidth))
      (run_restrictOracleProgram inputLength hwidth oracle)) ?_
  refine run_occurrenceStage
    (run_substRequestProgram inputLength
      (encodeBooleanCircuit (restrictPaddedOracle oracle hwidth))
      (pcp.nativeWidth arity) arity (encodeBitInput input) _ (le_refl _)) ?_
  exact run_occurrenceStage
    (run_preserveRightProgram (nativeCallProgram substitution.runner.program)
      inputLength
      (nativeCallBits inputLength arity
        (ProjectionSubstitutionRequest.code (substRequest input oracle hwidth))
        (encodeBooleanCircuit
          (substitution.circuit (substRequest input oracle hwidth)))
        (substitution.runner.budget (substRequest input oracle hwidth)))
      (nativeCallFuel substitution.runner.program
        (substitution.runner.budget (substRequest input oracle hwidth)) arity
        (ProjectionSubstitutionRequest.code (substRequest input oracle hwidth)))
      (nativeInputRequest arity
        (ProjectionSubstitutionRequest.code (substRequest input oracle hwidth)))
      (pcp.nativeWidth arity)
      (encodeBooleanCircuit
        (substitution.circuit (substRequest input oracle hwidth)))
      (run_nativeCallProgram substitution.runner.program inputLength arity
        (ProjectionSubstitutionRequest.code (substRequest input oracle hwidth))
        (encodeBooleanCircuit
          (substitution.circuit (substRequest input oracle hwidth)))
        (substitution.runner.budget (substRequest input oracle hwidth))
        (substitution.runner.budget (substRequest input oracle hwidth))
        (substitution.computes (substRequest input oracle hwidth))))
    (run_padArityProgram inputLength
      (substitution.circuit (substRequest input oracle hwidth)))

end NearCubicWires.CaseTwoSubstitutedCircuitEncoder
