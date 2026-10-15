import Proof.MachineModel.BitInputPrefixProgram
import Proof.MachineModel.CanonicalBooleanRangeAggregationProgram
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

namespace NearCubicWires.CanonicalFourfoldRangeRequestProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Runtime shift by the public arity -/

def variableRightShiftInput (amount value : ℕ) : ℕ :=
  Nat.pair amount value

def variableRightShiftProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .branchZero 2 5 3
  , .decrement 2 4
  , .shiftRight 3 1 3 2
  , .copy 3 0 6
  , .halt 0
  ]

def variableRightShiftFuel (amount : ℕ) : ℕ :=
  3 * amount + 5

def variableRightShiftBits (amount value : ℕ) : ℕ :=
  natBitLength (variableRightShiftInput amount value + 1)

@[simp] theorem variableRightShiftProgram_oracleFree :
    OracleFree variableRightShiftProgram := by
  rfl

private theorem shiftedOneThen
    (value remaining : ℕ) :
    (value >>> 1) >>> remaining = value >>> (remaining + 1) := by
  rw [← Nat.shiftRight_add]
  congr 1
  omega

private theorem run_variableRightShiftLoop
    (remaining current maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 2)
    (hremaining : state.registers 2 = remaining)
    (hcurrent : state.registers 3 = current)
    (hremainingBits : natBitLength remaining ≤ maximumBits)
    (hcurrentBits : natBitLength current ≤ maximumBits) :
    runNPOracleProgram variableRightShiftProgram maximumBits
        (3 * remaining + 3) state =
      some (current >>> remaining) := by
  induction remaining generalizing current state with
  | zero =>
      rw [show 3 * 0 + 3 = 2 + 1 by omega]
      rw [run_branchZero_instruction (fuel := 2)
        (by rfl) hpc]
      rw [hremaining, if_pos rfl]
      rw [show 2 = 1 + 1 by omega]
      rw [run_copy_instruction (fuel := 1) (value := current)
        (by rfl) rfl
        (by simp [NPOracleState.jump, hcurrent])
        hcurrentBits]
      exact run_halt_instruction (fuel := 0) (value := current)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        hcurrentBits
  | succ remaining inductionHypothesis =>
      let shifted := current >>> 1
      have hremainingPredBits :
          natBitLength remaining ≤ maximumBits := by
        exact (natBitLength_mono (by omega)).trans hremainingBits
      have hshiftedBits :
          natBitLength shifted ≤ maximumBits := by
        exact (shiftRight_bits_le current 1).trans hcurrentBits
      rw [show 3 * (remaining + 1) + 3 =
        (3 * remaining + 5) + 1 by omega]
      rw [run_branchZero_instruction (fuel := 3 * remaining + 5)
        (by rfl) hpc]
      rw [hremaining, if_neg (Nat.succ_ne_zero remaining)]
      rw [show 3 * remaining + 5 =
        (3 * remaining + 4) + 1 by omega]
      rw [run_decrement_instruction
        (fuel := 3 * remaining + 4)
        (value := remaining) (by rfl) rfl
        (by simp [NPOracleState.jump, hremaining])
        hremainingPredBits]
      rw [show 3 * remaining + 4 =
        (3 * remaining + 3) + 1 by omega]
      rw [run_shiftRight_instruction
        (fuel := 3 * remaining + 3)
        (value := shifted) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump,
          hcurrent, shifted])
        hshiftedBits]
      rw [inductionHypothesis shifted
        ((((state.jump 3).write 2 remaining).jump 4).write 3 shifted
          |>.jump 2)
        rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        (by simp [NPOracleState.write, NPOracleState.jump])
        hremainingPredBits hshiftedBits]
      exact congrArg some (shiftedOneThen current remaining)

theorem run_variableRightShiftProgram
    (inputLength amount value : ℕ) :
    runNPOracleProgram variableRightShiftProgram
        (variableRightShiftBits amount value)
        (variableRightShiftFuel amount)
        (initialNPOracleState inputLength
          (variableRightShiftInput amount value)) =
      some (value >>> amount) := by
  let input := variableRightShiftInput amount value
  let maximumBits := variableRightShiftBits amount value
  have hinput : natBitLength input ≤ maximumBits := by
    exact natBitLength_mono (Nat.le_add_right input 1)
  have hamount : natBitLength amount ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair amount value)).trans hinput
  have hvalue : natBitLength value ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair amount value)).trans hinput
  rw [show variableRightShiftFuel amount =
    (3 * amount + 4) + 1 by
      simp [variableRightShiftFuel]]
  rw [run_unpairLeft_instruction
    (fuel := 3 * amount + 4) (value := amount)
    (by rfl) rfl
    (by simp [initialNPOracleState, variableRightShiftInput])
    hamount]
  rw [show 3 * amount + 4 = (3 * amount + 3) + 1 by omega]
  rw [run_unpairRight_instruction
    (fuel := 3 * amount + 3) (value := value)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, variableRightShiftInput])
    hvalue]
  exact run_variableRightShiftLoop amount value maximumBits
    ((((initialNPOracleState inputLength input).write 2 amount).jump 1
      |>.write 3 value).jump 2)
    rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump])
    hamount hvalue

/-! ## Fixed five-field canonical packer -/

def fourfoldRowRequestNativeInput
    (modeCode q envelopeCode rowIndex inputCode : ℕ) : ℕ :=
  Nat.pair modeCode <|
    Nat.pair q <|
      Nat.pair envelopeCode <|
        Nat.pair rowIndex inputCode

def canonicalFourfoldRowRequestCode
    (modeCode q envelopeCode rowIndex inputCode : ℕ) : ℕ :=
  encodeBalancedList
    [modeCode, q, envelopeCode, rowIndex, inputCode]

@[simp] theorem canonicalFourfoldRowRequestCode_mode
    (mode : SupplierEstimator.NormalizedEstimatorMode)
    (q envelopeCode rowIndex inputCode : ℕ) :
    canonicalFourfoldRowRequestCode
        (normalizedEstimatorModeCode mode)
        q envelopeCode rowIndex inputCode =
      (FourfoldRowRequest.mk mode q envelopeCode rowIndex inputCode).code := by
  rfl

def canonicalFourfoldRowRequestPackerProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .set 15 1 9
  , .set 16 2 10
  , .pair 15 2 17 11
  , .pair 15 4 18 12
  , .pair 15 6 19 13
  , .pair 15 8 20 14
  , .pair 15 9 21 15
  , .pair 17 18 22 16
  , .pair 16 22 23 17
  , .pair 23 19 24 18
  , .pair 16 24 25 19
  , .pair 20 21 26 20
  , .pair 16 26 27 21
  , .pair 25 27 28 22
  , .pair 16 28 0 23
  , .halt 0
  ]

@[simp] theorem canonicalFourfoldRowRequestPackerProgram_oracleFree :
    OracleFree canonicalFourfoldRowRequestPackerProgram := by
  rfl

def canonicalFourfoldRowRequestPackerValues
    (modeCode q envelopeCode rowIndex inputCode : ℕ) : List ℕ :=
  let mode := modeCode
  let arity := q
  let envelope := envelopeCode
  let row := rowIndex
  let input := inputCode
  let modeLeaf := Nat.pair 1 mode
  let arityLeaf := Nat.pair 1 arity
  let envelopeLeaf := Nat.pair 1 envelope
  let rowLeaf := Nat.pair 1 row
  let inputLeaf := Nat.pair 1 input
  let modeArityPayload := Nat.pair modeLeaf arityLeaf
  let modeArityNode := Nat.pair 2 modeArityPayload
  let leftPayload := Nat.pair modeArityNode envelopeLeaf
  let leftNode := Nat.pair 2 leftPayload
  let rightPayload := Nat.pair rowLeaf inputLeaf
  let rightNode := Nat.pair 2 rightPayload
  let rootPayload := Nat.pair leftNode rightNode
  let output := Nat.pair 2 rootPayload
  [ fourfoldRowRequestNativeInput
      modeCode q envelopeCode rowIndex inputCode
  , modeCode, q, envelopeCode, rowIndex, inputCode
  , mode, arity, envelope, row, input
  , 1, 2
  , modeLeaf, arityLeaf, envelopeLeaf, rowLeaf, inputLeaf
  , modeArityPayload, modeArityNode, leftPayload, leftNode
  , rightPayload, rightNode, rootPayload, output
  ]

def canonicalFourfoldRowRequestPackerBits
    (modeCode q envelopeCode rowIndex inputCode : ℕ) : ℕ :=
  ((canonicalFourfoldRowRequestPackerValues
      modeCode q envelopeCode rowIndex inputCode).map natBitLength).foldr max 1

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ}
    (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (le_max_right _ _)

private theorem canonicalFourfoldRowRequestPackerBits_of_mem
    {modeCode q envelopeCode rowIndex inputCode value : ℕ}
    (hvalue :
      value ∈ canonicalFourfoldRowRequestPackerValues
        modeCode q envelopeCode rowIndex inputCode) :
    natBitLength value ≤
      canonicalFourfoldRowRequestPackerBits
        modeCode q envelopeCode rowIndex inputCode := by
  unfold canonicalFourfoldRowRequestPackerBits
  apply le_foldr_max_of_mem
  exact List.mem_map.mpr ⟨value, hvalue, rfl⟩

theorem run_canonicalFourfoldRowRequestPackerProgram
    (inputLength modeCode q envelopeCode rowIndex inputCode : ℕ) :
    runNPOracleProgram canonicalFourfoldRowRequestPackerProgram
        (canonicalFourfoldRowRequestPackerBits
          modeCode q envelopeCode rowIndex inputCode)
        24
        (initialNPOracleState inputLength
          (fourfoldRowRequestNativeInput
            modeCode q envelopeCode rowIndex inputCode)) =
      some
        (canonicalFourfoldRowRequestCode
          modeCode q envelopeCode rowIndex inputCode) := by
  let raw :=
    fourfoldRowRequestNativeInput
      modeCode q envelopeCode rowIndex inputCode
  let mode := modeCode
  let arity := q
  let envelope := envelopeCode
  let row := rowIndex
  let input := inputCode
  let modeLeaf := Nat.pair 1 mode
  let arityLeaf := Nat.pair 1 arity
  let envelopeLeaf := Nat.pair 1 envelope
  let rowLeaf := Nat.pair 1 row
  let inputLeaf := Nat.pair 1 input
  let modeArityPayload := Nat.pair modeLeaf arityLeaf
  let modeArityNode := Nat.pair 2 modeArityPayload
  let leftPayload := Nat.pair modeArityNode envelopeLeaf
  let leftNode := Nat.pair 2 leftPayload
  let rightPayload := Nat.pair rowLeaf inputLeaf
  let rightNode := Nat.pair 2 rightPayload
  let rootPayload := Nat.pair leftNode rightNode
  let output := Nat.pair 2 rootPayload
  let maximumBits :=
    canonicalFourfoldRowRequestPackerBits
      modeCode q envelopeCode rowIndex inputCode
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ canonicalFourfoldRowRequestPackerValues
          modeCode q envelopeCode rowIndex inputCode) :
      natBitLength value ≤ maximumBits :=
    canonicalFourfoldRowRequestPackerBits_of_mem hvalue
  have hraw : natBitLength raw ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, raw]
  have hmodeCode : natBitLength modeCode ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues]
  have hq : natBitLength q ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues]
  have henvelopeCode : natBitLength envelopeCode ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues]
  have hrowIndex : natBitLength rowIndex ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues]
  have hinputCode : natBitLength inputCode ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues]
  have hmode : natBitLength mode ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, mode]
  have harity : natBitLength arity ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, arity]
  have henvelope : natBitLength envelope ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, envelope]
  have hrow : natBitLength row ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, row]
  have hinput : natBitLength input ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, input]
  have hone : natBitLength 1 ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues]
  have htwo : natBitLength 2 ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues]
  have hmodeLeaf : natBitLength modeLeaf ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, modeLeaf, mode]
  have harityLeaf : natBitLength arityLeaf ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, arityLeaf, arity]
  have henvelopeLeaf : natBitLength envelopeLeaf ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, envelopeLeaf, envelope]
  have hrowLeaf : natBitLength rowLeaf ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, rowLeaf, row]
  have hinputLeaf : natBitLength inputLeaf ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, inputLeaf, input]
  have hmodeArityPayload :
      natBitLength modeArityPayload ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, modeArityPayload,
      modeLeaf, arityLeaf, mode, arity]
  have hmodeArityNode :
      natBitLength modeArityNode ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, modeArityNode,
      modeArityPayload, modeLeaf, arityLeaf, mode, arity]
  have hleftPayload : natBitLength leftPayload ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, leftPayload,
      modeArityNode, modeArityPayload, modeLeaf, arityLeaf,
      envelopeLeaf, mode, arity, envelope]
  have hleftNode : natBitLength leftNode ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, leftNode, leftPayload,
      modeArityNode, modeArityPayload, modeLeaf, arityLeaf,
      envelopeLeaf, mode, arity, envelope]
  have hrightPayload : natBitLength rightPayload ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, rightPayload,
      rowLeaf, inputLeaf, row, input]
  have hrightNode : natBitLength rightNode ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, rightNode, rightPayload,
      rowLeaf, inputLeaf, row, input]
  have hrootPayload : natBitLength rootPayload ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, rootPayload,
      leftNode, leftPayload, modeArityNode, modeArityPayload,
      modeLeaf, arityLeaf, envelopeLeaf, rightNode, rightPayload,
      rowLeaf, inputLeaf, mode, arity, envelope, row, input]
  have houtput : natBitLength output ≤ maximumBits := by
    apply bits_of_member
    simp [canonicalFourfoldRowRequestPackerValues, output, rootPayload,
      leftNode, leftPayload, modeArityNode, modeArityPayload,
      modeLeaf, arityLeaf, envelopeLeaf, rightNode, rightPayload,
      rowLeaf, inputLeaf, mode, arity, envelope, row, input]
  have houtputEq :
      canonicalFourfoldRowRequestCode
          modeCode q envelopeCode rowIndex inputCode =
        output := by
    simp [canonicalFourfoldRowRequestCode, encodeBalancedList, output,
      rootPayload, leftNode, leftPayload, modeArityNode, modeArityPayload,
      modeLeaf, arityLeaf, envelopeLeaf, rightNode, rightPayload,
      rowLeaf, inputLeaf, mode, arity, envelope, row, input]
  dsimp only [raw, mode, arity, envelope, row, input, modeLeaf,
    arityLeaf, envelopeLeaf, rowLeaf, inputLeaf, modeArityPayload,
    modeArityNode, leftPayload, leftNode, rightPayload, rightNode,
    rootPayload, output] at *
  rw [show 24 = 23 + 1 by omega]
  rw [run_unpairLeft_instruction (value := modeCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, fourfoldRowRequestNativeInput])
    hmodeCode]
  rw [show 23 = 22 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair q (Nat.pair envelopeCode (Nat.pair rowIndex inputCode)))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, fourfoldRowRequestNativeInput])
    (by
      exact
        (natBitLength_mono
          (Nat.right_le_pair modeCode
            (Nat.pair q
              (Nat.pair envelopeCode
                (Nat.pair rowIndex inputCode))))).trans hraw)]
  rw [show 22 = 21 + 1 by omega]
  rw [run_unpairLeft_instruction (value := q)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hq]
  rw [show 21 = 20 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair envelopeCode (Nat.pair rowIndex inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by
      exact
        (natBitLength_mono
          (Nat.right_le_pair q
            (Nat.pair envelopeCode
              (Nat.pair rowIndex inputCode)))).trans <|
          (natBitLength_mono
            (Nat.right_le_pair modeCode
              (Nat.pair q
                (Nat.pair envelopeCode
                  (Nat.pair rowIndex inputCode))))).trans hraw)]
  rw [show 20 = 19 + 1 by omega]
  rw [run_unpairLeft_instruction (value := envelopeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    henvelopeCode]
  rw [show 19 = 18 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair rowIndex inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by
      exact
        (natBitLength_mono
          (Nat.right_le_pair envelopeCode
            (Nat.pair rowIndex inputCode))).trans <|
          (natBitLength_mono
            (Nat.right_le_pair q
              (Nat.pair envelopeCode
                (Nat.pair rowIndex inputCode)))).trans <|
            (natBitLength_mono
              (Nat.right_le_pair modeCode
                (Nat.pair q
                  (Nat.pair envelopeCode
                    (Nat.pair rowIndex inputCode))))).trans hraw)]
  rw [show 18 = 17 + 1 by omega]
  rw [run_unpairLeft_instruction (value := rowIndex)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrowIndex]
  rw [show 17 = 16 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinputCode]
  rw [show 16 = 15 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl hone]
  rw [show 15 = 14 + 1 by omega]
  rw [run_set_instruction (value := 2) (by rfl) rfl htwo]
  rw [show 14 = 13 + 1 by omega]
  rw [run_pair_instruction (value := modeLeaf)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, modeLeaf, mode])
    hmodeLeaf]; simp only [mode, modeLeaf]
  rw [show 13 = 12 + 1 by omega]
  rw [run_pair_instruction (value := arityLeaf)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityLeaf, arity])
    harityLeaf]; simp only [arity, arityLeaf]
  rw [show 12 = 11 + 1 by omega]
  rw [run_pair_instruction (value := envelopeLeaf)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, envelopeLeaf,
      envelope])
    henvelopeLeaf]; simp only [envelope, envelopeLeaf]
  rw [show 11 = 10 + 1 by omega]
  rw [run_pair_instruction (value := rowLeaf)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowLeaf, row])
    hrowLeaf]; simp only [row, rowLeaf]
  rw [show 10 = 9 + 1 by omega]
  rw [run_pair_instruction (value := inputLeaf)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, inputLeaf, input])
    hinputLeaf]; simp only [input, inputLeaf]
  rw [show 9 = 8 + 1 by omega]
  rw [run_pair_instruction (value := modeArityPayload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, modeArityPayload,
      modeLeaf, arityLeaf, mode, arity])
    hmodeArityPayload];
      simp only [mode, arity, modeLeaf, arityLeaf, modeArityPayload]
  rw [show 8 = 7 + 1 by omega]
  rw [run_pair_instruction (value := modeArityNode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, modeArityNode,
      modeArityPayload, modeLeaf, arityLeaf, mode, arity])
    hmodeArityNode];
      simp only [mode, arity, modeLeaf, arityLeaf, modeArityPayload,
        modeArityNode]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction (value := leftPayload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, leftPayload,
      modeArityNode, modeArityPayload, modeLeaf, arityLeaf,
      envelopeLeaf, mode, arity, envelope])
    hleftPayload];
      simp only [mode, arity, envelope, modeLeaf, arityLeaf,
        envelopeLeaf, modeArityPayload, modeArityNode, leftPayload]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := leftNode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, leftNode,
      leftPayload, modeArityNode, modeArityPayload, modeLeaf, arityLeaf,
      envelopeLeaf, mode, arity, envelope])
    hleftNode];
      simp only [mode, arity, envelope, modeLeaf, arityLeaf,
        envelopeLeaf, modeArityPayload, modeArityNode, leftPayload,
        leftNode]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := rightPayload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rightPayload,
      rowLeaf, inputLeaf, row, input])
    hrightPayload];
      simp only [row, input, rowLeaf, inputLeaf, rightPayload]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := rightNode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rightNode,
      rightPayload, rowLeaf, inputLeaf, row, input])
    hrightNode];
      simp only [row, input, rowLeaf, inputLeaf, rightPayload, rightNode]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := rootPayload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rootPayload,
      leftNode, leftPayload, modeArityNode, modeArityPayload, modeLeaf,
      arityLeaf, envelopeLeaf, rightNode, rightPayload, rowLeaf,
      inputLeaf, mode, arity, envelope, row, input])
    hrootPayload];
      simp only [mode, arity, envelope, row, input, modeLeaf, arityLeaf,
        envelopeLeaf, rowLeaf, inputLeaf, modeArityPayload,
        modeArityNode, leftPayload, leftNode, rightPayload, rightNode,
        rootPayload]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      rootPayload, leftNode, leftPayload, modeArityNode,
      modeArityPayload, modeLeaf, arityLeaf, envelopeLeaf, rightNode,
      rightPayload, rowLeaf, inputLeaf, mode, arity, envelope, row,
      input])
    houtput];
      simp only [mode, arity, envelope, row, input, modeLeaf, arityLeaf,
        envelopeLeaf, rowLeaf, inputLeaf, modeArityPayload,
        modeArityNode, leftPayload, leftNode, rightPayload, rightNode,
        rootPayload, output]
  apply run_halt_instruction
    (program := canonicalFourfoldRowRequestPackerProgram)
    (pc := 23) (outputRegister := 0) (fuel := 0)
    (value :=
      canonicalFourfoldRowRequestCode
        modeCode q envelopeCode rowIndex inputCode)
  · rfl
  · rfl
  · simp [houtputEq]
  · simpa only [houtputEq] using houtput

/-! ## Flat range atom to prefix request -/

def fourfoldRangeRowContext
    (modeCode envelopeCode : ℕ) : ℕ :=
  Nat.pair modeCode envelopeCode

def fourfoldRangeComponentContext
    (denominatorTail modeCode envelopeCode : ℕ) : ℕ :=
  fixedBooleanRangeComponentContext denominatorTail
    (fourfoldRangeRowContext modeCode envelopeCode)

def fourfoldRangeAtomInput
    (flat denominatorTail modeCode envelopeCode : ℕ) : ℕ :=
  Nat.pair flat <|
    fourfoldRangeComponentContext
      denominatorTail modeCode envelopeCode

def fourfoldRangePrefixAdapterOutput
    (q flat denominatorTail modeCode envelopeCode : ℕ) : ℕ :=
  Nat.pair (bitInputPrefixInput q flat) <|
    Nat.pair flat <|
      fourfoldRangeComponentContext
        denominatorTail modeCode envelopeCode

/-- Retain the flat coordinate and the complete aggregation context while the
verified low-bit prefix program computes `flat % 2^q`. -/
def fourfoldRangePrefixAdapterProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 1 2 4 3
  , .pair 2 3 5 4
  , .pair 4 5 0 5
  , .halt 0
  ]

@[simp] theorem fourfoldRangePrefixAdapterProgram_oracleFree :
    OracleFree fourfoldRangePrefixAdapterProgram := by
  rfl

def fourfoldRangePrefixAdapterValues
    (q flat denominatorTail modeCode envelopeCode : ℕ) : List ℕ :=
  let context :=
    fourfoldRangeComponentContext
      denominatorTail modeCode envelopeCode
  let input := Nat.pair flat context
  let prefixInput := bitInputPrefixInput q flat
  let retained := Nat.pair flat context
  let output := Nat.pair prefixInput retained
  [q, flat, context, input, prefixInput, retained, output]

def fourfoldRangePrefixAdapterBits
    (q flat denominatorTail modeCode envelopeCode : ℕ) : ℕ :=
  ((fourfoldRangePrefixAdapterValues
    q flat denominatorTail modeCode envelopeCode).map natBitLength).foldr max 1

private theorem fourfoldRangePrefixAdapterBits_of_mem
    {q flat denominatorTail modeCode envelopeCode value : ℕ}
    (hvalue :
      value ∈ fourfoldRangePrefixAdapterValues
        q flat denominatorTail modeCode envelopeCode) :
    natBitLength value ≤
      fourfoldRangePrefixAdapterBits
        q flat denominatorTail modeCode envelopeCode := by
  unfold fourfoldRangePrefixAdapterBits
  apply le_foldr_max_of_mem
  exact List.mem_map.mpr ⟨value, hvalue, rfl⟩

theorem run_fourfoldRangePrefixAdapterProgram
    (q flat denominatorTail modeCode envelopeCode : ℕ) :
    runNPOracleProgram fourfoldRangePrefixAdapterProgram
        (fourfoldRangePrefixAdapterBits
          q flat denominatorTail modeCode envelopeCode)
        6
        (initialNPOracleState q
          (fourfoldRangeAtomInput
            flat denominatorTail modeCode envelopeCode)) =
      some
        (fourfoldRangePrefixAdapterOutput
          q flat denominatorTail modeCode envelopeCode) := by
  let context :=
    fourfoldRangeComponentContext
      denominatorTail modeCode envelopeCode
  let input := Nat.pair flat context
  let prefixInput := bitInputPrefixInput q flat
  let retained := Nat.pair flat context
  let output := Nat.pair prefixInput retained
  let maximumBits :=
    fourfoldRangePrefixAdapterBits
      q flat denominatorTail modeCode envelopeCode
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ fourfoldRangePrefixAdapterValues
          q flat denominatorTail modeCode envelopeCode) :
      natBitLength value ≤ maximumBits :=
    fourfoldRangePrefixAdapterBits_of_mem hvalue
  have hq : natBitLength q ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangePrefixAdapterValues]
  have hflat : natBitLength flat ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangePrefixAdapterValues]
  have hcontext : natBitLength context ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangePrefixAdapterValues, context]
  have hprefixInput : natBitLength prefixInput ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangePrefixAdapterValues, prefixInput]
  have hretained : natBitLength retained ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangePrefixAdapterValues, retained, context]
  have houtput : natBitLength output ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangePrefixAdapterValues, output, prefixInput,
      retained, context]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := flat)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, fourfoldRangeAtomInput,
        fourfoldRangeComponentContext])
    hflat]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, fourfoldRangeAtomInput, context,
        fourfoldRangeComponentContext])
    hcontext]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := prefixInput)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, prefixInput,
        bitInputPrefixInput])
    hprefixInput]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := retained)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, retained])
    hretained]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

/-! ## Prefix result to runtime-shift request -/

def fourfoldRangePrefixPreservedOutput
    (inputCode flat denominatorTail modeCode envelopeCode : ℕ) : ℕ :=
  Nat.pair inputCode <|
    Nat.pair flat <|
      fourfoldRangeComponentContext
        denominatorTail modeCode envelopeCode

def fourfoldRangeShiftAdapterOutput
    (q inputCode flat denominatorTail modeCode envelopeCode : ℕ) : ℕ :=
  Nat.pair (variableRightShiftInput q flat) <|
    Nat.pair inputCode <|
      fourfoldRangeComponentContext
        denominatorTail modeCode envelopeCode

/-- Turn the retained flat coordinate into the native input for
`variableRightShiftProgram`, while moving the low-bit prefix and row context
to the preserved right branch. -/
def fourfoldRangeShiftAdapterProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 1 4 6 5
  , .pair 2 5 7 6
  , .pair 6 7 0 7
  , .halt 0
  ]

@[simp] theorem fourfoldRangeShiftAdapterProgram_oracleFree :
    OracleFree fourfoldRangeShiftAdapterProgram := by
  rfl

def fourfoldRangeShiftAdapterBits
    (q inputCode flat denominatorTail modeCode envelopeCode : ℕ) : ℕ :=
  natBitLength <|
    max
      (fourfoldRangePrefixPreservedOutput
        inputCode flat denominatorTail modeCode envelopeCode)
      (fourfoldRangeShiftAdapterOutput
        q inputCode flat denominatorTail modeCode envelopeCode) + 1

theorem run_fourfoldRangeShiftAdapterProgram
    (q inputCode flat denominatorTail modeCode envelopeCode : ℕ) :
    runNPOracleProgram fourfoldRangeShiftAdapterProgram
        (fourfoldRangeShiftAdapterBits
          q inputCode flat denominatorTail modeCode envelopeCode)
        8
        (initialNPOracleState q
          (fourfoldRangePrefixPreservedOutput
            inputCode flat denominatorTail modeCode envelopeCode)) =
      some
        (fourfoldRangeShiftAdapterOutput
          q inputCode flat denominatorTail modeCode envelopeCode) := by
  let context :=
    fourfoldRangeComponentContext
      denominatorTail modeCode envelopeCode
  let flatContext := Nat.pair flat context
  let input := Nat.pair inputCode flatContext
  let shiftInput := variableRightShiftInput q flat
  let retained := Nat.pair inputCode context
  let output := Nat.pair shiftInput retained
  let bound := max input output + 1
  let maximumBits :=
    fourfoldRangeShiftAdapterBits
      q inputCode flat denominatorTail modeCode envelopeCode
  have hmaximumBits : natBitLength bound = maximumBits := by
    rfl
  have bits_of_le {value : ℕ} (hvalue : value ≤ bound) :
      natBitLength value ≤ maximumBits := by
    rw [← hmaximumBits]
    exact natBitLength_mono hvalue
  have hinput : natBitLength input ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_left _ _).trans (Nat.le_add_right _ _)
  have houtput : natBitLength output ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
  have hinputCode : natBitLength inputCode ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair inputCode flatContext)).trans hinput
  have hflatContext : natBitLength flatContext ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair inputCode flatContext)).trans hinput
  have hflat : natBitLength flat ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair flat context)).trans hflatContext
  have hcontext : natBitLength context ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair flat context)).trans hflatContext
  have hshiftInput : natBitLength shiftInput ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair shiftInput retained)).trans houtput
  have hretained : natBitLength retained ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair shiftInput retained)).trans houtput
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputCode)
    (by rfl) rfl
    (by
      simp [initialNPOracleState,
        fourfoldRangePrefixPreservedOutput])
    hinputCode]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := flatContext)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, fourfoldRangePrefixPreservedOutput,
        flatContext, context])
    hflatContext]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := flat)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, flatContext])
    hflat]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, flatContext])
    hcontext]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := shiftInput)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, shiftInput, variableRightShiftInput])
    hshiftInput]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := retained)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, retained])
    hretained]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

/-! ## Shift result to canonical packer input -/

def fourfoldRangeShiftPreservedOutput
    (rowIndex inputCode denominatorTail modeCode envelopeCode : ℕ) : ℕ :=
  Nat.pair rowIndex <|
    Nat.pair inputCode <|
      fourfoldRangeComponentContext
        denominatorTail modeCode envelopeCode

/-- Decode the fixed aggregation context and construct the native
right-associated input expected by the five-field canonical packer.
`denominatorTail` intentionally does not cross the row-callee boundary. -/
def fourfoldRangeNativeHandoffProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .pair 2 4 10 9
  , .pair 9 10 11 10
  , .pair 1 11 12 11
  , .pair 8 12 0 12
  , .halt 0
  ]

@[simp] theorem fourfoldRangeNativeHandoffProgram_oracleFree :
    OracleFree fourfoldRangeNativeHandoffProgram := by
  rfl

def fourfoldRangeNativeHandoffBits
    (q rowIndex inputCode denominatorTail modeCode envelopeCode : ℕ) : ℕ :=
  natBitLength <|
    max
      (fourfoldRangeShiftPreservedOutput
        rowIndex inputCode denominatorTail modeCode envelopeCode)
      (fourfoldRowRequestNativeInput
        modeCode q envelopeCode rowIndex inputCode) + 1

theorem run_fourfoldRangeNativeHandoffProgram
    (q rowIndex inputCode denominatorTail modeCode envelopeCode : ℕ) :
    runNPOracleProgram fourfoldRangeNativeHandoffProgram
        (fourfoldRangeNativeHandoffBits
          q rowIndex inputCode denominatorTail modeCode envelopeCode)
        13
        (initialNPOracleState q
          (fourfoldRangeShiftPreservedOutput
            rowIndex inputCode denominatorTail modeCode envelopeCode)) =
      some
        (fourfoldRowRequestNativeInput
          modeCode q envelopeCode rowIndex inputCode) := by
  let rowContext := fourfoldRangeRowContext modeCode envelopeCode
  let context :=
    fourfoldRangeComponentContext
      denominatorTail modeCode envelopeCode
  let inputRest := Nat.pair inputCode context
  let input := Nat.pair rowIndex inputRest
  let rowInput := Nat.pair rowIndex inputCode
  let envelopeRows := Nat.pair envelopeCode rowInput
  let qEnvelopeRows := Nat.pair q envelopeRows
  let output := Nat.pair modeCode qEnvelopeRows
  let bound := max input output + 1
  let maximumBits :=
    fourfoldRangeNativeHandoffBits
      q rowIndex inputCode denominatorTail modeCode envelopeCode
  have hmaximumBits : natBitLength bound = maximumBits := by
    rfl
  have bits_of_le {value : ℕ} (hvalue : value ≤ bound) :
      natBitLength value ≤ maximumBits := by
    rw [← hmaximumBits]
    exact natBitLength_mono hvalue
  have hinput : natBitLength input ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_left _ _).trans (Nat.le_add_right _ _)
  have houtput : natBitLength output ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
  have hrowIndex : natBitLength rowIndex ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair rowIndex inputRest)).trans hinput
  have hinputRest : natBitLength inputRest ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair rowIndex inputRest)).trans hinput
  have hinputCode : natBitLength inputCode ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair inputCode context)).trans hinputRest
  have hcontext : natBitLength context ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair inputCode context)).trans hinputRest
  have hdenominatorTail : natBitLength denominatorTail ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair denominatorTail rowContext)).trans hcontext
  have hrowContext : natBitLength rowContext ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair denominatorTail rowContext)).trans hcontext
  have hmodeCode : natBitLength modeCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair modeCode envelopeCode)).trans hrowContext
  have henvelopeCode : natBitLength envelopeCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair modeCode envelopeCode)).trans hrowContext
  have hrowInput : natBitLength rowInput ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair envelopeCode rowInput)).trans <|
        (natBitLength_mono
          (Nat.right_le_pair q envelopeRows)).trans <|
            (natBitLength_mono
              (Nat.right_le_pair modeCode qEnvelopeRows)).trans houtput
  have henvelopeRows : natBitLength envelopeRows ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair q envelopeRows)).trans <|
        (natBitLength_mono
          (Nat.right_le_pair modeCode qEnvelopeRows)).trans houtput
  have hqEnvelopeRows : natBitLength qEnvelopeRows ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair modeCode qEnvelopeRows)).trans houtput
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := rowIndex)
    (by rfl) rfl
    (by
      simp [initialNPOracleState,
        fourfoldRangeShiftPreservedOutput])
    hrowIndex]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputRest)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, fourfoldRangeShiftPreservedOutput,
        inputRest, context])
    hinputRest]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, inputRest])
    hinputCode]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, inputRest])
    hcontext]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := denominatorTail)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, context,
        fourfoldRangeComponentContext,
        fixedBooleanRangeComponentContext])
    hdenominatorTail]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := rowContext)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, context,
        rowContext, fourfoldRangeComponentContext,
        fixedBooleanRangeComponentContext])
    hrowContext]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := modeCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rowContext,
        fourfoldRangeRowContext])
    hmodeCode]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := envelopeCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rowContext,
        fourfoldRangeRowContext])
    henvelopeCode]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := rowInput)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rowInput])
    hrowInput]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := envelopeRows)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, envelopeRows])
    henvelopeRows]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := qEnvelopeRows)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, qEnvelopeRows])
    hqEnvelopeRows]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

/-! ## Closed flat-atom lowering -/

private def fourfoldRangePackingTailProgram : NPOracleProgram :=
  linkPrograms fourfoldRangeNativeHandoffProgram
    canonicalFourfoldRowRequestPackerProgram

private def fourfoldRangeShiftExecutionTailProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram variableRightShiftProgram)
    fourfoldRangePackingTailProgram

private def fourfoldRangeShiftAdapterTailProgram : NPOracleProgram :=
  linkPrograms fourfoldRangeShiftAdapterProgram
    fourfoldRangeShiftExecutionTailProgram

private def fourfoldRangePrefixExecutionTailProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitInputPrefixProgram)
    fourfoldRangeShiftAdapterTailProgram

/-- The sole production lowering from a row-major range atom to the canonical
`FourfoldRowRequest` code consumed by a statically linked row evaluator. -/
def fourfoldRangeRequestProgram : NPOracleProgram :=
  linkPrograms fourfoldRangePrefixAdapterProgram
    fourfoldRangePrefixExecutionTailProgram

def fourfoldRangeRequestStageBits
    (q flat denominatorTail modeCode envelopeCode : ℕ) : List ℕ :=
  let context :=
    fourfoldRangeComponentContext
      denominatorTail modeCode envelopeCode
  let prefixCode := bitInputPrefix q flat
  [ 1
  , natBitLength q
  , fourfoldRangePrefixAdapterBits
      q flat denominatorTail modeCode envelopeCode
  , preserveRightBits
      (bitInputPrefixBits q flat)
      (bitInputPrefixInput q flat)
      (Nat.pair flat context)
      prefixCode
  , fourfoldRangeShiftAdapterBits
      q prefixCode flat denominatorTail modeCode envelopeCode
  , preserveRightBits
      (variableRightShiftBits q flat)
      (variableRightShiftInput q flat)
      (Nat.pair prefixCode context)
      (flat >>> q)
  , fourfoldRangeNativeHandoffBits
      q (flat >>> q) prefixCode denominatorTail modeCode envelopeCode
  , canonicalFourfoldRowRequestPackerBits
      modeCode q envelopeCode (flat >>> q) prefixCode
  ]

def fourfoldRangeRequestBits
    (q flat denominatorTail modeCode envelopeCode : ℕ) : ℕ :=
  ((fourfoldRangeRequestStageBits
      q flat denominatorTail modeCode envelopeCode).foldr max 1)

def fourfoldRangeRequestFuel (q flat : ℕ) : ℕ :=
  linkFuel fourfoldRangePrefixExecutionTailProgram 6 <|
    linkFuel fourfoldRangeShiftAdapterTailProgram
      (preserveRightFuel (bitInputPrefixFuel q flat)) <|
      linkFuel fourfoldRangeShiftExecutionTailProgram 8 <|
        linkFuel fourfoldRangePackingTailProgram
          (preserveRightFuel (variableRightShiftFuel q)) <|
          linkFuel canonicalFourfoldRowRequestPackerProgram 13 24

theorem fourfoldRangeRequestProgram_oracleFree :
    OracleFree fourfoldRangeRequestProgram := by
  unfold fourfoldRangeRequestProgram
  apply oracleFree_linkPrograms
  · exact fourfoldRangePrefixAdapterProgram_oracleFree
  unfold fourfoldRangePrefixExecutionTailProgram
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree _
      bitInputPrefixProgram_oracleFree
  unfold fourfoldRangeShiftAdapterTailProgram
  apply oracleFree_linkPrograms
  · exact fourfoldRangeShiftAdapterProgram_oracleFree
  unfold fourfoldRangeShiftExecutionTailProgram
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree _
      variableRightShiftProgram_oracleFree
  unfold fourfoldRangePackingTailProgram
  exact oracleFree_linkPrograms
    fourfoldRangeNativeHandoffProgram_oracleFree
    canonicalFourfoldRowRequestPackerProgram_oracleFree

theorem run_fourfoldRangeRequestProgram
    (q flat denominatorTail modeCode envelopeCode : ℕ) :
    runNPOracleProgram fourfoldRangeRequestProgram
        (fourfoldRangeRequestBits
          q flat denominatorTail modeCode envelopeCode)
        (fourfoldRangeRequestFuel q flat)
        (initialNPOracleState q
          (fourfoldRangeAtomInput
            flat denominatorTail modeCode envelopeCode)) =
      some
        (canonicalFourfoldRowRequestCode
          modeCode q envelopeCode
          (flat >>> q) (bitInputPrefix q flat)) := by
  let context :=
    fourfoldRangeComponentContext
      denominatorTail modeCode envelopeCode
  let inputPrefix := bitInputPrefix q flat
  let rowIndex := flat >>> q
  let prefixRequest :=
    fourfoldRangePrefixAdapterOutput
      q flat denominatorTail modeCode envelopeCode
  let prefixOutput :=
    fourfoldRangePrefixPreservedOutput
      inputPrefix flat denominatorTail modeCode envelopeCode
  let shiftRequest :=
    fourfoldRangeShiftAdapterOutput
      q inputPrefix flat denominatorTail modeCode envelopeCode
  let shiftOutput :=
    fourfoldRangeShiftPreservedOutput
      rowIndex inputPrefix denominatorTail modeCode envelopeCode
  let nativeInput :=
    fourfoldRowRequestNativeInput
      modeCode q envelopeCode rowIndex inputPrefix
  let output :=
    canonicalFourfoldRowRequestCode
      modeCode q envelopeCode rowIndex inputPrefix
  let maximumBits :=
    fourfoldRangeRequestBits
      q flat denominatorTail modeCode envelopeCode
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ fourfoldRangeRequestStageBits
          q flat denominatorTail modeCode envelopeCode) :
      value ≤ maximumBits := by
    dsimp only [maximumBits, fourfoldRangeRequestBits]
    exact le_foldr_max_of_mem hvalue
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeRequestStageBits]
  have hq : natBitLength q ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeRequestStageBits]
  have hprefixAdapterBits :
      fourfoldRangePrefixAdapterBits
          q flat denominatorTail modeCode envelopeCode ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeRequestStageBits]
  have hprefixExecutionBits :
      preserveRightBits
          (bitInputPrefixBits q flat)
          (bitInputPrefixInput q flat)
          (Nat.pair flat context)
          inputPrefix ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeRequestStageBits, context, inputPrefix]
  have hshiftAdapterBits :
      fourfoldRangeShiftAdapterBits
          q inputPrefix flat denominatorTail modeCode envelopeCode ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeRequestStageBits, inputPrefix]
  have hshiftExecutionBits :
      preserveRightBits
          (variableRightShiftBits q flat)
          (variableRightShiftInput q flat)
          (Nat.pair inputPrefix context)
          rowIndex ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeRequestStageBits, context, inputPrefix, rowIndex]
  have hnativeHandoffBits :
      fourfoldRangeNativeHandoffBits
          q rowIndex inputPrefix denominatorTail modeCode envelopeCode ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeRequestStageBits, inputPrefix, rowIndex]
  have hpackerBits :
      canonicalFourfoldRowRequestPackerBits
          modeCode q envelopeCode rowIndex inputPrefix ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeRequestStageBits, inputPrefix, rowIndex]
  have hprefixAdapter :
      runNPOracleProgram fourfoldRangePrefixAdapterProgram
          maximumBits 6
          (initialNPOracleState q
            (fourfoldRangeAtomInput
              flat denominatorTail modeCode envelopeCode)) =
        some prefixRequest := by
    apply run_bits_mono
      (run_fourfoldRangePrefixAdapterProgram
        q flat denominatorTail modeCode envelopeCode)
      hprefixAdapterBits
  have hprefixSource :
      runNPOracleProgram bitInputPrefixProgram
          (bitInputPrefixBits q flat)
          (bitInputPrefixFuel q flat)
          (initialNPOracleState q (bitInputPrefixInput q flat)) =
        some inputPrefix := by
    simpa [inputPrefix] using
      (run_bitInputPrefixProgram q q flat
        (bitInputPrefixBits q flat) 0 (le_refl _))
  have hprefixExecution :
      runNPOracleProgram
          (preserveRightProgram bitInputPrefixProgram)
          maximumBits
          (preserveRightFuel (bitInputPrefixFuel q flat))
          (initialNPOracleState q prefixRequest) =
        some prefixOutput := by
    have hexact :=
      run_preserveRightProgram bitInputPrefixProgram
        q (bitInputPrefixBits q flat)
        (bitInputPrefixFuel q flat)
        (bitInputPrefixInput q flat)
        (Nat.pair flat context)
        inputPrefix hprefixSource
    apply run_bits_mono
      (by
        simpa [prefixRequest, prefixOutput, context, inputPrefix,
          fourfoldRangePrefixAdapterOutput,
          fourfoldRangePrefixPreservedOutput] using hexact)
      hprefixExecutionBits
  have hshiftAdapter :
      runNPOracleProgram fourfoldRangeShiftAdapterProgram
          maximumBits 8
          (initialNPOracleState q prefixOutput) =
        some shiftRequest := by
    apply run_bits_mono
      (by
        simpa [prefixOutput, shiftRequest, inputPrefix] using
          run_fourfoldRangeShiftAdapterProgram
            q inputPrefix flat denominatorTail modeCode envelopeCode)
      hshiftAdapterBits
  have hshiftSource :
      runNPOracleProgram variableRightShiftProgram
          (variableRightShiftBits q flat)
          (variableRightShiftFuel q)
          (initialNPOracleState q (variableRightShiftInput q flat)) =
        some rowIndex := by
    simpa [rowIndex] using run_variableRightShiftProgram q q flat
  have hshiftExecution :
      runNPOracleProgram
          (preserveRightProgram variableRightShiftProgram)
          maximumBits
          (preserveRightFuel (variableRightShiftFuel q))
          (initialNPOracleState q shiftRequest) =
        some shiftOutput := by
    have hexact :=
      run_preserveRightProgram variableRightShiftProgram
        q (variableRightShiftBits q flat)
        (variableRightShiftFuel q)
        (variableRightShiftInput q flat)
        (Nat.pair inputPrefix context)
        rowIndex hshiftSource
    apply run_bits_mono
      (by
        simpa [shiftRequest, shiftOutput, context, inputPrefix, rowIndex,
          fourfoldRangeShiftAdapterOutput,
          fourfoldRangeShiftPreservedOutput] using hexact)
      hshiftExecutionBits
  have hnativeHandoff :
      runNPOracleProgram fourfoldRangeNativeHandoffProgram
          maximumBits 13
          (initialNPOracleState q shiftOutput) =
        some nativeInput := by
    apply run_bits_mono
      (by
        simpa [shiftOutput, nativeInput, inputPrefix, rowIndex] using
          run_fourfoldRangeNativeHandoffProgram
            q rowIndex inputPrefix denominatorTail modeCode envelopeCode)
      hnativeHandoffBits
  have hpacker :
      runNPOracleProgram canonicalFourfoldRowRequestPackerProgram
          maximumBits 24
          (initialNPOracleState q nativeInput) =
        some output := by
    apply run_bits_mono
      (by
        simpa [nativeInput, output, inputPrefix, rowIndex] using
          run_canonicalFourfoldRowRequestPackerProgram
            q modeCode q envelopeCode rowIndex inputPrefix)
      hpackerBits
  have hpackingTail :
      runNPOracleProgram fourfoldRangePackingTailProgram
          maximumBits
          (linkFuel canonicalFourfoldRowRequestPackerProgram 13 24)
          (initialNPOracleState q shiftOutput) =
        some output := by
    simpa [fourfoldRangePackingTailProgram] using
      run_linkPrograms hpositive hq hnativeHandoff hpacker
  have hshiftExecutionTail :
      runNPOracleProgram fourfoldRangeShiftExecutionTailProgram
          maximumBits
          (linkFuel fourfoldRangePackingTailProgram
            (preserveRightFuel (variableRightShiftFuel q))
            (linkFuel canonicalFourfoldRowRequestPackerProgram 13 24))
          (initialNPOracleState q shiftRequest) =
        some output := by
    simpa [fourfoldRangeShiftExecutionTailProgram] using
      run_linkPrograms hpositive hq hshiftExecution hpackingTail
  have hshiftAdapterTail :
      runNPOracleProgram fourfoldRangeShiftAdapterTailProgram
          maximumBits
          (linkFuel fourfoldRangeShiftExecutionTailProgram 8
            (linkFuel fourfoldRangePackingTailProgram
              (preserveRightFuel (variableRightShiftFuel q))
              (linkFuel canonicalFourfoldRowRequestPackerProgram 13 24)))
          (initialNPOracleState q prefixOutput) =
        some output := by
    simpa [fourfoldRangeShiftAdapterTailProgram] using
      run_linkPrograms hpositive hq hshiftAdapter hshiftExecutionTail
  have hprefixExecutionTail :
      runNPOracleProgram fourfoldRangePrefixExecutionTailProgram
          maximumBits
          (linkFuel fourfoldRangeShiftAdapterTailProgram
            (preserveRightFuel (bitInputPrefixFuel q flat))
            (linkFuel fourfoldRangeShiftExecutionTailProgram 8
              (linkFuel fourfoldRangePackingTailProgram
                (preserveRightFuel (variableRightShiftFuel q))
                (linkFuel canonicalFourfoldRowRequestPackerProgram 13 24))))
          (initialNPOracleState q prefixRequest) =
        some output := by
    simpa [fourfoldRangePrefixExecutionTailProgram] using
      run_linkPrograms hpositive hq hprefixExecution hshiftAdapterTail
  have hrun :=
    run_linkPrograms hpositive hq hprefixAdapter hprefixExecutionTail
  simpa [fourfoldRangeRequestProgram, fourfoldRangeRequestFuel,
    output, inputPrefix, rowIndex] using hrun

theorem run_fourfoldRangeRequestProgram_mode
    (q flat denominatorTail envelopeCode : ℕ)
    (mode : SupplierEstimator.NormalizedEstimatorMode) :
    runNPOracleProgram fourfoldRangeRequestProgram
        (fourfoldRangeRequestBits q flat denominatorTail
          (normalizedEstimatorModeCode mode) envelopeCode)
        (fourfoldRangeRequestFuel q flat)
        (initialNPOracleState q
          (fourfoldRangeAtomInput flat denominatorTail
            (normalizedEstimatorModeCode mode) envelopeCode)) =
      some
        (FourfoldRowRequest.mk mode q envelopeCode
          (flat >>> q) (bitInputPrefix q flat)).code := by
  simpa only [canonicalFourfoldRowRequestCode_mode] using
    run_fourfoldRangeRequestProgram q flat denominatorTail
      (normalizedEstimatorModeCode mode) envelopeCode

end NearCubicWires.CanonicalFourfoldRangeRequestProgram
