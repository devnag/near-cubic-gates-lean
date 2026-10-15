import Proof.MachineModel.CanonicalDescriptionFieldProgram
import Proof.CaseAnalysis.CaseTwoCanonicalCircuitEncoder
import Proof.CaseAnalysis.CaseTwoSubstitutedCircuitEncoder

namespace NearCubicWires.CanonicalDescriptionGroupingDecoder

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalDescriptionFieldProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalSymmetricRowTableRequestProgram
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoSubstitutedCircuitEncoder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbound : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbound

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) : value ≤ values.foldr max 1 := by
  induction values with
  | nil => exact absurd hmem List.not_mem_nil
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · exact hhead ▸ Nat.le_max_left _ _
      · exact (ih htail).trans (Nat.le_max_right _ _)

/-! ## 1. The row layout words -/

/-- The shared context of every row: the field limit, the row width, the
description's length and its balanced code. -/
def descriptionRowContext (limit width len code : ℕ) : ℕ :=
  Nat.pair limit (Nat.pair width (Nat.pair len code))

/-- The layout word the decoder builds once: the row count beside the row
context. -/
def descriptionLayoutWord (rowCount limit width len code : ℕ) : ℕ :=
  Nat.pair rowCount (descriptionRowContext limit width len code)

/-- The word every field stage of one row starts from: the row's base offset
beside the field limit, the length and the code. -/
def descriptionRowBaseWord (base limit len code : ℕ) : ℕ :=
  Nat.pair base (Nat.pair limit (Nat.pair len code))

/-! ## 2. The fixed straight-line stages -/

/-- Register ABI: `r2` the row index and then `pair row width`, `r4` the field
limit and then the retained tail. -/
def descriptionRowBasePrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 2 6 2 7
  , .pair 4 7 4 8
  , .pair 2 4 0 9
  , .halt 0
  ]

@[simp] theorem descriptionRowBasePrepProgram_oracleFree :
    OracleFree descriptionRowBasePrepProgram := by
  rfl

def descriptionRowBasePrepFuel : ℕ := 10

def descriptionRowBasePrepOutput (row limit width len code : ℕ) : ℕ :=
  Nat.pair (bitSerialMulInput row width) (Nat.pair limit (Nat.pair len code))

def descriptionRowBasePrepBits (row limit width len code : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair row (descriptionRowContext limit width len code))
      (descriptionRowBasePrepOutput row limit width len code))

theorem run_descriptionRowBasePrepProgram
    (inputLength row limit width len code : ℕ) :
    runNPOracleProgram descriptionRowBasePrepProgram
        (descriptionRowBasePrepBits row limit width len code)
        descriptionRowBasePrepFuel
        (initialNPOracleState inputLength
          (Nat.pair row (descriptionRowContext limit width len code))) =
      some (descriptionRowBasePrepOutput row limit width len code) := by
  have hinput :
      natBitLength (Nat.pair row (descriptionRowContext limit width len code)) ≤
        descriptionRowBasePrepBits row limit width len code :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput :
      natBitLength (descriptionRowBasePrepOutput row limit width len code) ≤
        descriptionRowBasePrepBits row limit width len code :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hrow : natBitLength row ≤
      descriptionRowBasePrepBits row limit width len code :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hcontext :
      natBitLength (descriptionRowContext limit width len code) ≤
        descriptionRowBasePrepBits row limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hlimit : natBitLength limit ≤
      descriptionRowBasePrepBits row limit width len code :=
    bits_of_le (Nat.left_le_pair _ _) hcontext
  have hwidthTail :
      natBitLength (Nat.pair width (Nat.pair len code)) ≤
        descriptionRowBasePrepBits row limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) hcontext
  have hwidth : natBitLength width ≤
      descriptionRowBasePrepBits row limit width len code :=
    bits_of_le (Nat.left_le_pair _ _) hwidthTail
  have htail : natBitLength (Nat.pair len code) ≤
      descriptionRowBasePrepBits row limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) hwidthTail
  have hproduct : natBitLength (bitSerialMulInput row width) ≤
      descriptionRowBasePrepBits row limit width len code :=
    bits_of_le (Nat.left_le_pair _ _) houtput
  have hkept : natBitLength (Nat.pair limit (Nat.pair len code)) ≤
      descriptionRowBasePrepBits row limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) houtput
  rw [show descriptionRowBasePrepFuel = 9 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := row) (by rfl) rfl
    (by simp [initialNPOracleState]) hrow]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := descriptionRowContext limit width len code) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := limit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionRowContext])
    hlimit]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair width (Nat.pair len code))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionRowContext])
    hwidthTail]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair len code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := bitSerialMulInput row width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSerialMulInput])
    hproduct]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair limit (Nat.pair len code))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hkept]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := descriptionRowBasePrepOutput row limit width len code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      descriptionRowBasePrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- **The row base.**  Multiply the row index by the row width and keep the
field limit, the length and the code. -/
def descriptionRowBaseProgram : NPOracleProgram :=
  linkPrograms descriptionRowBasePrepProgram
    (preserveRightProgram bitSerialMulProgram)

def descriptionRowBaseFuel (width : ℕ) : ℕ :=
  linkFuel (preserveRightProgram bitSerialMulProgram)
    descriptionRowBasePrepFuel (preserveRightFuel (bitSerialMulFuel width))

def descriptionRowBaseBits (inputLength row limit width len code : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (descriptionRowBasePrepBits row limit width len code)
    (preserveRightBits (bitSerialMulBits inputLength row width)
      (bitSerialMulInput row width) (Nat.pair limit (Nat.pair len code))
      (row * width))

theorem run_descriptionRowBaseProgram
    (inputLength row limit width len code : ℕ) :
    runNPOracleProgram descriptionRowBaseProgram
        (descriptionRowBaseBits inputLength row limit width len code)
        (descriptionRowBaseFuel width)
        (initialNPOracleState inputLength
          (Nat.pair row (descriptionRowContext limit width len code))) =
      some (descriptionRowBaseWord (row * width) limit len code) :=
  run_occurrenceStage
    (run_descriptionRowBasePrepProgram inputLength row limit width len code)
    (run_preserveRightProgram bitSerialMulProgram inputLength
      (bitSerialMulBits inputLength row width) (bitSerialMulFuel width)
      (bitSerialMulInput row width) (Nat.pair limit (Nat.pair len code))
      (row * width) (run_bitSerialMulProgram inputLength row width))

/-! ## 3. The four block requests -/

/-- The tag block: six cells at the row's own base. -/
def descriptionTagPostProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .pair 2 4 2 4
  , .set 5 6 5
  , .pair 5 2 0 6
  , .halt 0
  ]

@[simp] theorem descriptionTagPostProgram_oracleFree :
    OracleFree descriptionTagPostProgram := by
  rfl

/-- The first field block: `limit` cells six past the row's base. -/
def descriptionFirstPostProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .set 6 6 5
  , .add 2 6 2 6
  , .pair 2 5 2 7
  , .pair 4 2 0 8
  , .halt 0
  ]

@[simp] theorem descriptionFirstPostProgram_oracleFree :
    OracleFree descriptionFirstPostProgram := by
  rfl

/-- The second field block: `limit` cells past the first field. -/
def descriptionSecondPostProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .set 6 6 5
  , .add 2 6 2 6
  , .add 2 4 2 7
  , .pair 2 5 2 8
  , .pair 4 2 0 9
  , .halt 0
  ]

@[simp] theorem descriptionSecondPostProgram_oracleFree :
    OracleFree descriptionSecondPostProgram := by
  rfl

/-- The node indicator: the single cell four past the row's base. -/
def descriptionCountPostProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .set 5 4 4
  , .add 2 5 2 5
  , .pair 2 4 2 6
  , .set 5 1 7
  , .pair 5 2 0 8
  , .halt 0
  ]

@[simp] theorem descriptionCountPostProgram_oracleFree :
    OracleFree descriptionCountPostProgram := by
  rfl

def descriptionTagPostFuel : ℕ := 7

def descriptionFirstPostFuel : ℕ := 9

def descriptionSecondPostFuel : ℕ := 10

def descriptionCountPostFuel : ℕ := 9

/-- One width budget for all four block requests: the started word, the emitted
range request and the largest immediate. -/
def descriptionPostBits (base limit len code count offset : ℕ) : ℕ :=
  natBitLength
    (max 6
      (max (descriptionRowBaseWord base limit len code)
        (generatedBalancedRangeInput count
          (descriptionSlotContext (base + offset) len code))))

private theorem post_bits_input (base limit len code count offset : ℕ) :
    natBitLength (descriptionRowBaseWord base limit len code) ≤
      descriptionPostBits base limit len code count offset :=
  bits_of_le ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
    (Nat.le_refl _)

private theorem post_bits_output (base limit len code count offset : ℕ) :
    natBitLength
        (generatedBalancedRangeInput count
          (descriptionSlotContext (base + offset) len code)) ≤
      descriptionPostBits base limit len code count offset :=
  bits_of_le ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
    (Nat.le_refl _)

private theorem post_bits_six (base limit len code count offset : ℕ) :
    natBitLength 6 ≤ descriptionPostBits base limit len code count offset :=
  bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)

theorem run_descriptionTagPostProgram
    (inputLength base limit len code : ℕ) :
    runNPOracleProgram descriptionTagPostProgram
        (descriptionPostBits base limit len code 6 0)
        descriptionTagPostFuel
        (initialNPOracleState inputLength
          (descriptionRowBaseWord base limit len code)) =
      some
        (generatedBalancedRangeInput 6
          (descriptionSlotContext base len code)) := by
  have hinput := post_bits_input base limit len code 6 0
  have houtput := post_bits_output base limit len code 6 0
  simp only [Nat.add_zero] at houtput
  have hsix := post_bits_six base limit len code 6 0
  have hbase : natBitLength base ≤ descriptionPostBits base limit len code 6 0 :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hmiddle : natBitLength (Nat.pair limit (Nat.pair len code)) ≤
      descriptionPostBits base limit len code 6 0 :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have htail : natBitLength (Nat.pair len code) ≤
      descriptionPostBits base limit len code 6 0 :=
    bits_of_le (Nat.right_le_pair _ _) hmiddle
  have hslot : natBitLength (descriptionSlotContext base len code) ≤
      descriptionPostBits base limit len code 6 0 := by
    refine bits_of_le (Nat.right_le_pair 6 _) ?_
    simpa only [generatedBalancedRangeInput] using houtput
  rw [show descriptionTagPostFuel = 6 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := base) (by rfl) rfl
    (by simp [initialNPOracleState, descriptionRowBaseWord]) hbase]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair limit (Nat.pair len code))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      descriptionRowBaseWord])
    hmiddle]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair len code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := descriptionSlotContext base len code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionSlotContext])
    hslot]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_set_instruction (value := 6) (by rfl) rfl hsix]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := generatedBalancedRangeInput 6 (descriptionSlotContext base len code))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      generatedBalancedRangeInput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

theorem run_descriptionFirstPostProgram
    (inputLength base limit len code : ℕ) :
    runNPOracleProgram descriptionFirstPostProgram
        (descriptionPostBits base limit len code limit 6)
        descriptionFirstPostFuel
        (initialNPOracleState inputLength
          (descriptionRowBaseWord base limit len code)) =
      some
        (generatedBalancedRangeInput limit
          (descriptionSlotContext (base + 6) len code)) := by
  have hinput := post_bits_input base limit len code limit 6
  have houtput := post_bits_output base limit len code limit 6
  have hsix := post_bits_six base limit len code limit 6
  have hbase : natBitLength base ≤
      descriptionPostBits base limit len code limit 6 :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hmiddle : natBitLength (Nat.pair limit (Nat.pair len code)) ≤
      descriptionPostBits base limit len code limit 6 :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hlimit : natBitLength limit ≤
      descriptionPostBits base limit len code limit 6 :=
    bits_of_le (Nat.left_le_pair _ _) hmiddle
  have htail : natBitLength (Nat.pair len code) ≤
      descriptionPostBits base limit len code limit 6 :=
    bits_of_le (Nat.right_le_pair _ _) hmiddle
  have hslot : natBitLength (descriptionSlotContext (base + 6) len code) ≤
      descriptionPostBits base limit len code limit 6 := by
    refine bits_of_le (Nat.right_le_pair limit _) ?_
    simpa only [generatedBalancedRangeInput] using houtput
  have hshift : natBitLength (base + 6) ≤
      descriptionPostBits base limit len code limit 6 :=
    bits_of_le (Nat.left_le_pair _ _) hslot
  rw [show descriptionFirstPostFuel = 8 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := base) (by rfl) rfl
    (by simp [initialNPOracleState, descriptionRowBaseWord]) hbase]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair limit (Nat.pair len code))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      descriptionRowBaseWord])
    hmiddle]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := limit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlimit]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair len code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_set_instruction (value := 6) (by rfl) rfl hsix]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_add_instruction (value := base + 6) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hshift]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := descriptionSlotContext (base + 6) len code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionSlotContext])
    hslot]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      generatedBalancedRangeInput limit
        (descriptionSlotContext (base + 6) len code))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      generatedBalancedRangeInput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

theorem run_descriptionSecondPostProgram
    (inputLength base limit len code : ℕ) :
    runNPOracleProgram descriptionSecondPostProgram
        (descriptionPostBits base limit len code limit (6 + limit))
        descriptionSecondPostFuel
        (initialNPOracleState inputLength
          (descriptionRowBaseWord base limit len code)) =
      some
        (generatedBalancedRangeInput limit
          (descriptionSlotContext (base + (6 + limit)) len code)) := by
  have hinput := post_bits_input base limit len code limit (6 + limit)
  have houtput := post_bits_output base limit len code limit (6 + limit)
  have hsix := post_bits_six base limit len code limit (6 + limit)
  have hbase : natBitLength base ≤
      descriptionPostBits base limit len code limit (6 + limit) :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hmiddle : natBitLength (Nat.pair limit (Nat.pair len code)) ≤
      descriptionPostBits base limit len code limit (6 + limit) :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hlimit : natBitLength limit ≤
      descriptionPostBits base limit len code limit (6 + limit) :=
    bits_of_le (Nat.left_le_pair _ _) hmiddle
  have htail : natBitLength (Nat.pair len code) ≤
      descriptionPostBits base limit len code limit (6 + limit) :=
    bits_of_le (Nat.right_le_pair _ _) hmiddle
  have hslot :
      natBitLength (descriptionSlotContext (base + (6 + limit)) len code) ≤
        descriptionPostBits base limit len code limit (6 + limit) := by
    refine bits_of_le (Nat.right_le_pair limit _) ?_
    simpa only [generatedBalancedRangeInput] using houtput
  have hfull : natBitLength (base + (6 + limit)) ≤
      descriptionPostBits base limit len code limit (6 + limit) :=
    bits_of_le (Nat.left_le_pair _ _) hslot
  have hshift : natBitLength (base + 6) ≤
      descriptionPostBits base limit len code limit (6 + limit) :=
    bits_of_le (by omega) hfull
  rw [show descriptionSecondPostFuel = 9 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := base) (by rfl) rfl
    (by simp [initialNPOracleState, descriptionRowBaseWord]) hbase]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair limit (Nat.pair len code))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      descriptionRowBaseWord])
    hmiddle]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := limit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlimit]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair len code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_set_instruction (value := 6) (by rfl) rfl hsix]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_add_instruction (value := base + 6) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hshift]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_add_instruction (value := base + (6 + limit)) (by rfl) rfl
    (by
      simp only [NPOracleState.write, NPOracleState.jump]
      simp
      omega)
    hfull]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := descriptionSlotContext (base + (6 + limit)) len code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionSlotContext])
    hslot]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      generatedBalancedRangeInput limit
        (descriptionSlotContext (base + (6 + limit)) len code))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      generatedBalancedRangeInput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

theorem run_descriptionCountPostProgram
    (inputLength base limit len code : ℕ) :
    runNPOracleProgram descriptionCountPostProgram
        (descriptionPostBits base limit len code 1 4)
        descriptionCountPostFuel
        (initialNPOracleState inputLength
          (descriptionRowBaseWord base limit len code)) =
      some
        (generatedBalancedRangeInput 1
          (descriptionSlotContext (base + 4) len code)) := by
  have hinput := post_bits_input base limit len code 1 4
  have houtput := post_bits_output base limit len code 1 4
  have hsix := post_bits_six base limit len code 1 4
  have hfour : natBitLength 4 ≤ descriptionPostBits base limit len code 1 4 :=
    bits_of_le (by omega) hsix
  have hone : natBitLength 1 ≤ descriptionPostBits base limit len code 1 4 :=
    bits_of_le (by omega) hsix
  have hbase : natBitLength base ≤ descriptionPostBits base limit len code 1 4 :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hmiddle : natBitLength (Nat.pair limit (Nat.pair len code)) ≤
      descriptionPostBits base limit len code 1 4 :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have htail : natBitLength (Nat.pair len code) ≤
      descriptionPostBits base limit len code 1 4 :=
    bits_of_le (Nat.right_le_pair _ _) hmiddle
  have hslot : natBitLength (descriptionSlotContext (base + 4) len code) ≤
      descriptionPostBits base limit len code 1 4 := by
    refine bits_of_le (Nat.right_le_pair 1 _) ?_
    simpa only [generatedBalancedRangeInput] using houtput
  have hshift : natBitLength (base + 4) ≤
      descriptionPostBits base limit len code 1 4 :=
    bits_of_le (Nat.left_le_pair _ _) hslot
  rw [show descriptionCountPostFuel = 8 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := base) (by rfl) rfl
    (by simp [initialNPOracleState, descriptionRowBaseWord]) hbase]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair limit (Nat.pair len code))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      descriptionRowBaseWord])
    hmiddle]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair len code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_set_instruction (value := 4) (by rfl) rfl hfour]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_add_instruction (value := base + 4) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hshift]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := descriptionSlotContext (base + 4) len code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionSlotContext])
    hslot]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl hone]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      generatedBalancedRangeInput 1 (descriptionSlotContext (base + 4) len code))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      generatedBalancedRangeInput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 4. Two one-word adapters -/

/-- The node indicator: one minus the fifth tag digit. -/
def descriptionComplementProgram : NPOracleProgram :=
  [ .set 2 1 1
  , .subtract 2 0 0 2
  , .halt 0
  ]

@[simp] theorem descriptionComplementProgram_oracleFree :
    OracleFree descriptionComplementProgram := by
  rfl

def descriptionComplementFuel : ℕ := 3

def descriptionComplementBits (value : ℕ) : ℕ :=
  natBitLength (max 1 value)

theorem run_descriptionComplementProgram (inputLength value : ℕ) :
    runNPOracleProgram descriptionComplementProgram
        (descriptionComplementBits value) descriptionComplementFuel
        (initialNPOracleState inputLength value) =
      some (1 - value) := by
  have hone : natBitLength 1 ≤ descriptionComplementBits value :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput : natBitLength (1 - value) ≤ descriptionComplementBits value :=
    bits_of_le (by omega) hone
  rw [show descriptionComplementFuel = 2 + 1 by rfl]
  rw [run_set_instruction (value := 1) (by rfl) rfl hone]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_subtract_instruction (value := 1 - value) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- The canonical binary encoding of one word. -/
def descriptionEncodeNatProgram : NPOracleProgram :=
  [ .encodeNat 0 0 1
  , .halt 0
  ]

@[simp] theorem descriptionEncodeNatProgram_oracleFree :
    OracleFree descriptionEncodeNatProgram := by
  rfl

def descriptionEncodeNatFuel : ℕ := 2

def descriptionEncodeNatBits (value : ℕ) : ℕ :=
  natBitLength (encodeNat value)

theorem run_descriptionEncodeNatProgram (inputLength value : ℕ) :
    runNPOracleProgram descriptionEncodeNatProgram
        (descriptionEncodeNatBits value) descriptionEncodeNatFuel
        (initialNPOracleState inputLength value) =
      some (encodeNat value) := by
  have houtput : natBitLength (encodeNat value) ≤
      descriptionEncodeNatBits value := Nat.le_refl _
  rw [show descriptionEncodeNatFuel = 1 + 1 by rfl]
  rw [run_encodeNat_instruction (value := value) (by rfl) rfl
    (by simp [initialNPOracleState]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 5. The same-input pair combinator -/

/-- Run two stages on the same word and pair their outputs. -/
def descriptionSamePairProgram (left right : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms duplicateProgram <|
    linkPrograms (preserveRightProgram left) <|
      linkPrograms swapPairProgram <|
        linkPrograms (preserveRightProgram right) swapPairProgram

theorem descriptionSamePairProgram_oracleFree
    {left right : NPOracleProgram}
    (hleft : OracleFree left) (hright : OracleFree right) :
    OracleFree (descriptionSamePairProgram left right) :=
  oracleFree_linkPrograms duplicateProgram_oracleFree
    (oracleFree_linkPrograms (preserveRightProgram_oracleFree _ hleft)
      (oracleFree_linkPrograms swapPairProgram_oracleFree
        (oracleFree_linkPrograms (preserveRightProgram_oracleFree _ hright)
          swapPairProgram_oracleFree)))

def descriptionSamePairFuel (left right : NPOracleProgram)
    (leftFuel rightFuel : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram left)
      (linkPrograms swapPairProgram
        (linkPrograms (preserveRightProgram right) swapPairProgram)))
    2 <|
    linkFuel
      (linkPrograms swapPairProgram
        (linkPrograms (preserveRightProgram right) swapPairProgram))
      (preserveRightFuel leftFuel) <|
      linkFuel (linkPrograms (preserveRightProgram right) swapPairProgram) 4 <|
        linkFuel swapPairProgram (preserveRightFuel rightFuel) 4

def descriptionSamePairBits
    (inputLength leftBits rightBits inputCode leftOutput rightOutput : ℕ) :
    ℕ :=
  occurrenceStageBits inputLength (duplicateBits inputCode) <|
    occurrenceStageBits inputLength
      (preserveRightBits leftBits inputCode inputCode leftOutput) <|
      occurrenceStageBits inputLength (swapPairBits leftOutput inputCode) <|
        occurrenceStageBits inputLength
          (preserveRightBits rightBits inputCode leftOutput rightOutput)
          (swapPairBits rightOutput leftOutput)

/-- **The two stages, paired.** -/
theorem run_descriptionSamePairProgram (left right : NPOracleProgram)
    (inputLength leftBits leftFuel rightBits rightFuel inputCode leftOutput
      rightOutput : ℕ)
    (hleft :
      runNPOracleProgram left leftBits leftFuel
        (initialNPOracleState inputLength inputCode) = some leftOutput)
    (hright :
      runNPOracleProgram right rightBits rightFuel
        (initialNPOracleState inputLength inputCode) = some rightOutput) :
    runNPOracleProgram (descriptionSamePairProgram left right)
        (descriptionSamePairBits inputLength leftBits rightBits inputCode
          leftOutput rightOutput)
        (descriptionSamePairFuel left right leftFuel rightFuel)
        (initialNPOracleState inputLength inputCode) =
      some (Nat.pair leftOutput rightOutput) :=
  run_occurrenceStage (run_duplicateProgram inputLength inputCode)
    (run_occurrenceStage
      (run_preserveRightProgram left inputLength leftBits leftFuel inputCode
        inputCode leftOutput hleft)
      (run_occurrenceStage (run_swapPairProgram inputLength leftOutput inputCode)
        (run_occurrenceStage
          (run_preserveRightProgram right inputLength rightBits rightFuel
            inputCode leftOutput rightOutput hright)
          (run_swapPairProgram inputLength rightOutput leftOutput))))

/-! ## 6. The node encoder -/

/-- The public code of the node a row describes.  The tag selects between the
two-field and the three-field shapes and nothing else: `encodeBooleanNode`
writes the same cells in the same order for every constructor. -/
def descriptionNodeCode (tag first second : ℕ) : ℕ :=
  if tag ≤ 2 then encodeTaggedList [encodeNat tag, encodeNat first]
  else encodeTaggedList [encodeNat tag, encodeNat first, encodeNat second]

/-- Register ABI:

* `r2`/`r4`/`r5`: the tag, the first field and the second field;
* `r6`: the saturating test `tag - 2` that selects the shape;
* `r7`: the growing tail, `0` on the two-field path;
* `r8`: the constant one every tagged cell carries;
* `r9`: the encoded field being consed on. -/
def descriptionNodeCodeProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .set 6 2 5
  , .subtract 2 6 6 6
  , .set 7 0 7
  , .set 8 1 8
  , .branchZero 6 12 9
  , .encodeNat 5 9 10
  , .pair 9 7 9 11
  , .pair 8 9 7 12
  , .encodeNat 4 9 13
  , .pair 9 7 9 14
  , .pair 8 9 7 15
  , .encodeNat 2 9 16
  , .pair 9 7 9 17
  , .pair 8 9 0 18
  , .halt 0
  ]

@[simp] theorem descriptionNodeCodeProgram_oracleFree :
    OracleFree descriptionNodeCodeProgram := by
  rfl

def descriptionNodeCodeFuel : ℕ := 19

def descriptionNodeCodeBits (tag first second : ℕ) : ℕ :=
  natBitLength
    (max (max 2 (Nat.pair tag (Nat.pair first second)))
      (max (encodeTaggedList [encodeNat tag, encodeNat first, encodeNat second])
        (encodeTaggedList [encodeNat tag, encodeNat first])))

/-- The common last seven instructions: cons the first field and the tag onto
whatever tail the shape branch produced. -/
private theorem run_nodeCodeTail (tag first tail maximumBits remaining : ℕ)
    (state : NPOracleState) (hpc : state.pc = 12)
    (htag : state.registers 2 = tag) (hfirst : state.registers 4 = first)
    (htail : state.registers 7 = tail) (hone : state.registers 8 = 1)
    (hresult :
      natBitLength
          (Nat.pair 1
            (Nat.pair (encodeNat tag)
              (Nat.pair 1 (Nat.pair (encodeNat first) tail)))) ≤
        maximumBits) :
    runNPOracleProgram descriptionNodeCodeProgram maximumBits (remaining + 7)
        state =
      some
        (Nat.pair 1
          (Nat.pair (encodeNat tag)
            (Nat.pair 1 (Nat.pair (encodeNat first) tail)))) := by
  have houter :
      natBitLength
          (Nat.pair (encodeNat tag)
            (Nat.pair 1 (Nat.pair (encodeNat first) tail))) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hresult
  have htagCode : natBitLength (encodeNat tag) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houter
  have hinner :
      natBitLength (Nat.pair 1 (Nat.pair (encodeNat first) tail)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houter
  have hcell : natBitLength (Nat.pair (encodeNat first) tail) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinner
  have hfirstCode : natBitLength (encodeNat first) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hcell
  rw [show remaining + 7 = (remaining + 6) + 1 by omega]
  rw [run_encodeNat_instruction (value := first) (by rfl) hpc hfirst hfirstCode]
  rw [show remaining + 6 = (remaining + 5) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (encodeNat first) tail)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, htail]) hcell]
  rw [show remaining + 5 = (remaining + 4) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair 1 (Nat.pair (encodeNat first) tail)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hone]) hinner]
  rw [show remaining + 4 = (remaining + 3) + 1 by omega]
  rw [run_encodeNat_instruction (value := tag) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, htag]) htagCode]
  rw [show remaining + 3 = (remaining + 2) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (encodeNat tag) (Nat.pair 1 (Nat.pair (encodeNat first) tail)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houter]
  rw [show remaining + 2 = (remaining + 1) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair 1
        (Nat.pair (encodeNat tag)
          (Nat.pair 1 (Nat.pair (encodeNat first) tail))))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hone]) hresult]
  exact run_halt_instruction (fuel := remaining) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hresult

/-- The shape branch and everything after it. -/
private theorem run_nodeCodeBranch (tag first second maximumBits : ℕ)
    (state : NPOracleState) (hpc : state.pc = 8)
    (htag : state.registers 2 = tag) (hfirst : state.registers 4 = first)
    (hsecond : state.registers 5 = second)
    (hdiff : state.registers 6 = tag - 2) (hzero : state.registers 7 = 0)
    (hone : state.registers 8 = 1)
    (hbits : descriptionNodeCodeBits tag first second ≤ maximumBits) :
    runNPOracleProgram descriptionNodeCodeProgram maximumBits 11 state =
      some (descriptionNodeCode tag first second) := by
  have hthree :
      natBitLength
          (encodeTaggedList
            [encodeNat tag, encodeNat first, encodeNat second]) ≤
        maximumBits :=
    bits_of_le ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
      (Nat.le_refl _) |>.trans hbits
  have htwo :
      natBitLength (encodeTaggedList [encodeNat tag, encodeNat first]) ≤
        maximumBits :=
    bits_of_le ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
      (Nat.le_refl _) |>.trans hbits
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) hpc, hdiff]
  by_cases hsmall : tag ≤ 2
  · rw [if_pos (by omega)]
    rw [show descriptionNodeCode tag first second =
        Nat.pair 1
          (Nat.pair (encodeNat tag)
            (Nat.pair 1 (Nat.pair (encodeNat first) 0))) by
      rw [descriptionNodeCode, if_pos hsmall]
      rfl]
    refine run_nodeCodeTail tag first 0 maximumBits 3 _ rfl ?_ ?_ ?_ ?_ ?_
    · simpa [NPOracleState.jump] using htag
    · simpa [NPOracleState.jump] using hfirst
    · simpa [NPOracleState.jump] using hzero
    · simpa [NPOracleState.jump] using hone
    · exact htwo
  · rw [if_neg (by omega)]
    have hsecondBody :
        natBitLength
            (Nat.pair 1
              (Nat.pair (encodeNat tag)
                (Nat.pair 1
                  (Nat.pair (encodeNat first)
                    (Nat.pair 1 (Nat.pair (encodeNat second) 0)))))) ≤
          maximumBits := hthree
    have hcons :
        natBitLength (Nat.pair 1 (Nat.pair (encodeNat second) 0)) ≤
          maximumBits := by
      refine bits_of_le ?_ hthree
      refine (Nat.right_le_pair (encodeNat first) _).trans ?_
      refine (Nat.right_le_pair 1 _).trans ?_
      refine (Nat.right_le_pair (encodeNat tag) _).trans ?_
      exact Nat.right_le_pair 1 _
    have hcell : natBitLength (Nat.pair (encodeNat second) 0) ≤ maximumBits :=
      bits_of_le (Nat.right_le_pair _ _) hcons
    have hsecondCode : natBitLength (encodeNat second) ≤ maximumBits :=
      bits_of_le (Nat.left_le_pair _ _) hcell
    rw [show (10 : ℕ) = 9 + 1 by omega]
    rw [run_encodeNat_instruction (value := second) (by rfl) rfl
      (by simpa [NPOracleState.jump] using hsecond) hsecondCode]
    rw [show (9 : ℕ) = 8 + 1 by omega]
    rw [run_pair_instruction (value := Nat.pair (encodeNat second) 0) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hzero]) hcell]
    rw [show (8 : ℕ) = 7 + 1 by omega]
    rw [run_pair_instruction
      (value := Nat.pair 1 (Nat.pair (encodeNat second) 0)) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hone]) hcons]
    rw [show descriptionNodeCode tag first second =
        Nat.pair 1
          (Nat.pair (encodeNat tag)
            (Nat.pair 1
              (Nat.pair (encodeNat first)
                (Nat.pair 1 (Nat.pair (encodeNat second) 0))))) by
      rw [descriptionNodeCode, if_neg hsmall]
      rfl]
    refine run_nodeCodeTail tag first
      (Nat.pair 1 (Nat.pair (encodeNat second) 0)) maximumBits 0 _ rfl ?_ ?_ ?_
      ?_ hsecondBody
    · simpa [NPOracleState.write, NPOracleState.jump] using htag
    · simpa [NPOracleState.write, NPOracleState.jump] using hfirst
    · simp [NPOracleState.write, NPOracleState.jump]
    · simpa [NPOracleState.write, NPOracleState.jump] using hone

/-- **The node encoder, executed.**  From the three thermometer fields of one
row the fixed stream returns that row's public node code. -/
theorem run_descriptionNodeCodeProgram (inputLength tag first second : ℕ) :
    runNPOracleProgram descriptionNodeCodeProgram
        (descriptionNodeCodeBits tag first second) descriptionNodeCodeFuel
        (initialNPOracleState inputLength
          (Nat.pair tag (Nat.pair first second))) =
      some (descriptionNodeCode tag first second) := by
  have hbits : descriptionNodeCodeBits tag first second ≤
      descriptionNodeCodeBits tag first second := Nat.le_refl _
  have hconst : natBitLength 2 ≤ descriptionNodeCodeBits tag first second :=
    bits_of_le ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _))
      (Nat.le_refl _)
  have hinput :
      natBitLength (Nat.pair tag (Nat.pair first second)) ≤
        descriptionNodeCodeBits tag first second :=
    bits_of_le ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
      (Nat.le_refl _)
  have htag : natBitLength tag ≤ descriptionNodeCodeBits tag first second :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hpair : natBitLength (Nat.pair first second) ≤
      descriptionNodeCodeBits tag first second :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hfirst : natBitLength first ≤ descriptionNodeCodeBits tag first second :=
    bits_of_le (Nat.left_le_pair _ _) hpair
  have hsecond : natBitLength second ≤
      descriptionNodeCodeBits tag first second :=
    bits_of_le (Nat.right_le_pair _ _) hpair
  have hzero : natBitLength 0 ≤ descriptionNodeCodeBits tag first second :=
    bits_of_le (by omega) hconst
  have hone : natBitLength 1 ≤ descriptionNodeCodeBits tag first second :=
    bits_of_le (by omega) hconst
  have hdiff : natBitLength (tag - 2) ≤
      descriptionNodeCodeBits tag first second :=
    bits_of_le (by omega) htag
  rw [show descriptionNodeCodeFuel = 18 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := tag) (by rfl) rfl
    (by simp [initialNPOracleState]) htag]
  rw [show (18 : ℕ) = 17 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair first second) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpair]
  rw [show (17 : ℕ) = 16 + 1 by omega]
  rw [run_unpairLeft_instruction (value := first) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfirst]
  rw [show (16 : ℕ) = 15 + 1 by omega]
  rw [run_unpairRight_instruction (value := second) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsecond]
  rw [show (15 : ℕ) = 14 + 1 by omega]
  rw [run_set_instruction (value := 2) (by rfl) rfl hconst]
  rw [show (14 : ℕ) = 13 + 1 by omega]
  rw [run_subtract_instruction (value := tag - 2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdiff]
  rw [show (13 : ℕ) = 12 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show (12 : ℕ) = 11 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl hone]
  refine run_nodeCodeBranch tag first second _ _ rfl ?_ ?_ ?_ ?_ ?_ ?_ hbits
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]

/-! ## 7. The three field stages of one row -/

/-- The tag of one row: six cells summed at the row's base. -/
def descriptionTagStageProgram : NPOracleProgram :=
  linkPrograms descriptionRowBaseProgram
    (linkPrograms descriptionTagPostProgram descriptionBlockSumProgram)

/-- The first field of one row. -/
def descriptionFirstStageProgram : NPOracleProgram :=
  linkPrograms descriptionRowBaseProgram
    (linkPrograms descriptionFirstPostProgram descriptionBlockSumProgram)

/-- The second field of one row. -/
def descriptionSecondStageProgram : NPOracleProgram :=
  linkPrograms descriptionRowBaseProgram
    (linkPrograms descriptionSecondPostProgram descriptionBlockSumProgram)

def descriptionFieldStageFuel (inputLength : ℕ) (values : List ℕ)
    (post : NPOracleProgram) (postFuel base count width : ℕ) : ℕ :=
  linkFuel (linkPrograms post descriptionBlockSumProgram)
    (descriptionRowBaseFuel width)
    (linkFuel descriptionBlockSumProgram postFuel
      (descriptionBlockSumFuel inputLength values base count))

def descriptionFieldStageBits (inputLength : ℕ) (values : List ℕ)
    (row limit width count offset : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (descriptionRowBaseBits inputLength row limit width values.length
      (encodeBalancedList values))
    (occurrenceStageBits inputLength
      (descriptionPostBits (row * width) limit values.length
        (encodeBalancedList values) count offset)
      (descriptionBlockSumBits inputLength values (row * width + offset) count))

theorem run_descriptionTagStageProgram (inputLength : ℕ) (values : List ℕ)
    (row limit width : ℕ) (hfit : row * width + 0 + 6 ≤ values.length) :
    runNPOracleProgram descriptionTagStageProgram
        (descriptionFieldStageBits inputLength values row limit width 6 0)
        (descriptionFieldStageFuel inputLength values descriptionTagPostProgram
          descriptionTagPostFuel (row * width + 0) 6 width)
        (initialNPOracleState inputLength
          (Nat.pair row
            (descriptionRowContext limit width values.length
              (encodeBalancedList values)))) =
      some (descriptionBlockValues values (row * width + 0) 6).sum := by
  refine run_occurrenceStage
    (run_descriptionRowBaseProgram inputLength row limit width values.length
      (encodeBalancedList values)) ?_
  refine run_occurrenceStage ?_
    (run_descriptionBlockSumProgram inputLength values (row * width + 0) 6 hfit)
  simpa only [Nat.add_zero] using
    run_descriptionTagPostProgram inputLength (row * width) limit values.length
      (encodeBalancedList values)

theorem run_descriptionFirstStageProgram (inputLength : ℕ) (values : List ℕ)
    (row limit width : ℕ) (hfit : row * width + 6 + limit ≤ values.length) :
    runNPOracleProgram descriptionFirstStageProgram
        (descriptionFieldStageBits inputLength values row limit width limit 6)
        (descriptionFieldStageFuel inputLength values
          descriptionFirstPostProgram descriptionFirstPostFuel
          (row * width + 6) limit width)
        (initialNPOracleState inputLength
          (Nat.pair row
            (descriptionRowContext limit width values.length
              (encodeBalancedList values)))) =
      some (descriptionBlockValues values (row * width + 6) limit).sum :=
  run_occurrenceStage
    (run_descriptionRowBaseProgram inputLength row limit width values.length
      (encodeBalancedList values))
    (run_occurrenceStage
      (run_descriptionFirstPostProgram inputLength (row * width) limit
        values.length (encodeBalancedList values))
      (run_descriptionBlockSumProgram inputLength values (row * width + 6) limit
        hfit))

theorem run_descriptionSecondStageProgram (inputLength : ℕ) (values : List ℕ)
    (row limit width : ℕ)
    (hfit : row * width + (6 + limit) + limit ≤ values.length) :
    runNPOracleProgram descriptionSecondStageProgram
        (descriptionFieldStageBits inputLength values row limit width limit
          (6 + limit))
        (descriptionFieldStageFuel inputLength values
          descriptionSecondPostProgram descriptionSecondPostFuel
          (row * width + (6 + limit)) limit width)
        (initialNPOracleState inputLength
          (Nat.pair row
            (descriptionRowContext limit width values.length
              (encodeBalancedList values)))) =
      some
        (descriptionBlockValues values (row * width + (6 + limit)) limit).sum :=
  run_occurrenceStage
    (run_descriptionRowBaseProgram inputLength row limit width values.length
      (encodeBalancedList values))
    (run_occurrenceStage
      (run_descriptionSecondPostProgram inputLength (row * width) limit
        values.length (encodeBalancedList values))
      (run_descriptionBlockSumProgram inputLength values
        (row * width + (6 + limit)) limit hfit))

def descriptionRowLeafProgram : NPOracleProgram :=
  linkPrograms
    (descriptionSamePairProgram descriptionTagStageProgram
      (descriptionSamePairProgram descriptionFirstStageProgram
        descriptionSecondStageProgram))
    descriptionNodeCodeProgram

def descriptionRowFields (values : List ℕ) (row limit width : ℕ) :
    ℕ × ℕ × ℕ :=
  ((descriptionBlockValues values (row * width + 0) 6).sum,
    (descriptionBlockValues values (row * width + 6) limit).sum,
    (descriptionBlockValues values (row * width + (6 + limit)) limit).sum)

def descriptionRowLeafFuel (inputLength : ℕ) (values : List ℕ)
    (row limit width : ℕ) : ℕ :=
  linkFuel descriptionNodeCodeProgram
    (descriptionSamePairFuel descriptionTagStageProgram
      (descriptionSamePairProgram descriptionFirstStageProgram
        descriptionSecondStageProgram)
      (descriptionFieldStageFuel inputLength values descriptionTagPostProgram
        descriptionTagPostFuel (row * width + 0) 6 width)
      (descriptionSamePairFuel descriptionFirstStageProgram
        descriptionSecondStageProgram
        (descriptionFieldStageFuel inputLength values
          descriptionFirstPostProgram descriptionFirstPostFuel
          (row * width + 6) limit width)
        (descriptionFieldStageFuel inputLength values
          descriptionSecondPostProgram descriptionSecondPostFuel
          (row * width + (6 + limit)) limit width)))
    descriptionNodeCodeFuel

def descriptionRowLeafBits (inputLength : ℕ) (values : List ℕ)
    (row limit width : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (descriptionSamePairBits inputLength
      (descriptionFieldStageBits inputLength values row limit width 6 0)
      (descriptionSamePairBits inputLength
        (descriptionFieldStageBits inputLength values row limit width limit 6)
        (descriptionFieldStageBits inputLength values row limit width limit
          (6 + limit))
        (Nat.pair row
          (descriptionRowContext limit width values.length
            (encodeBalancedList values)))
        (descriptionRowFields values row limit width).2.1
        (descriptionRowFields values row limit width).2.2)
      (Nat.pair row
        (descriptionRowContext limit width values.length
          (encodeBalancedList values)))
      (descriptionRowFields values row limit width).1
      (Nat.pair (descriptionRowFields values row limit width).2.1
        (descriptionRowFields values row limit width).2.2))
    (descriptionNodeCodeBits (descriptionRowFields values row limit width).1
      (descriptionRowFields values row limit width).2.1
      (descriptionRowFields values row limit width).2.2)

set_option maxHeartbeats 800000 in
-- The statement carries three nested pair combinators over the same row word,
-- so elaborating it alone exceeds the default budget.

theorem run_descriptionRowLeafProgram (inputLength : ℕ) (values : List ℕ)
    (row limit width : ℕ)
    (hfit : row * width + (6 + limit) + limit ≤ values.length) :
    runNPOracleProgram descriptionRowLeafProgram
        (descriptionRowLeafBits inputLength values row limit width)
        (descriptionRowLeafFuel inputLength values row limit width)
        (initialNPOracleState inputLength
          (Nat.pair row
            (descriptionRowContext limit width values.length
              (encodeBalancedList values)))) =
      some
        (descriptionNodeCode (descriptionRowFields values row limit width).1
          (descriptionRowFields values row limit width).2.1
          (descriptionRowFields values row limit width).2.2) := by
  have htagFit : row * width + 0 + 6 ≤ values.length := by omega
  have hfirstFit : row * width + 6 + limit ≤ values.length := by omega
  refine run_occurrenceStage ?_
    (run_descriptionNodeCodeProgram inputLength _ _ _)
  exact run_descriptionSamePairProgram descriptionTagStageProgram
    (descriptionSamePairProgram descriptionFirstStageProgram
      descriptionSecondStageProgram)
    inputLength _ _ _ _ _ _ _
    (run_descriptionTagStageProgram inputLength values row limit width htagFit)
    (run_descriptionSamePairProgram descriptionFirstStageProgram
      descriptionSecondStageProgram inputLength _ _ _ _ _ _ _
      (run_descriptionFirstStageProgram inputLength values row limit width
        hfirstFit)
      (run_descriptionSecondStageProgram inputLength values row limit width
        hfit))

def descriptionCountLeafProgram : NPOracleProgram :=
  linkPrograms descriptionRowBaseProgram
    (linkPrograms descriptionCountPostProgram
      (linkPrograms descriptionBlockSumProgram descriptionComplementProgram))

def descriptionCountLeafValue (values : List ℕ) (row width : ℕ) : ℕ :=
  1 - (descriptionBlockValues values (row * width + 4) 1).sum

def descriptionCountLeafFuel (inputLength : ℕ) (values : List ℕ)
    (row width : ℕ) : ℕ :=
  linkFuel
    (linkPrograms descriptionCountPostProgram
      (linkPrograms descriptionBlockSumProgram descriptionComplementProgram))
    (descriptionRowBaseFuel width)
    (linkFuel (linkPrograms descriptionBlockSumProgram
        descriptionComplementProgram)
      descriptionCountPostFuel
      (linkFuel descriptionComplementProgram
        (descriptionBlockSumFuel inputLength values (row * width + 4) 1)
        descriptionComplementFuel))

def descriptionCountLeafBits (inputLength : ℕ) (values : List ℕ)
    (row limit width : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (descriptionRowBaseBits inputLength row limit width values.length
      (encodeBalancedList values))
    (occurrenceStageBits inputLength
      (descriptionPostBits (row * width) limit values.length
        (encodeBalancedList values) 1 4)
      (occurrenceStageBits inputLength
        (descriptionBlockSumBits inputLength values (row * width + 4) 1)
        (descriptionComplementBits
          (descriptionBlockValues values (row * width + 4) 1).sum)))

theorem run_descriptionCountLeafProgram (inputLength : ℕ) (values : List ℕ)
    (row limit width : ℕ) (hfit : row * width + 4 + 1 ≤ values.length) :
    runNPOracleProgram descriptionCountLeafProgram
        (descriptionCountLeafBits inputLength values row limit width)
        (descriptionCountLeafFuel inputLength values row width)
        (initialNPOracleState inputLength
          (Nat.pair row
            (descriptionRowContext limit width values.length
              (encodeBalancedList values)))) =
      some (descriptionCountLeafValue values row width) :=
  run_occurrenceStage
    (run_descriptionRowBaseProgram inputLength row limit width values.length
      (encodeBalancedList values))
    (run_occurrenceStage
      (run_descriptionCountPostProgram inputLength (row * width) limit
        values.length (encodeBalancedList values))
      (run_occurrenceStage
        (run_descriptionBlockSumProgram inputLength values (row * width + 4) 1
          hfit)
        (run_descriptionComplementProgram inputLength
          (descriptionBlockValues values (row * width + 4) 1).sum)))

/-! ## 9. The layout stage -/

private theorem rowWidth_eq (n bound : ℕ) :
    boundedCircuitFieldLimit n bound + boundedCircuitFieldLimit n bound + 6 =
      rowWidth n bound := by
  have hwidth : rowWidth n bound = 6 + 2 * boundedCircuitFieldLimit n bound :=
    rfl
  omega

/-- Register ABI: `r6` the field limit, `r7` the row width, `r5` the row count,
`r2` the balanced code. -/
def descriptionLayoutPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .add 4 5 6 5
  , .increment 6 6
  , .add 6 6 7 7
  , .set 8 6 8
  , .add 7 8 7 9
  , .increment 5 10
  , .pair 5 7 9 11
  , .pair 7 2 10 12
  , .pair 6 10 10 13
  , .pair 5 10 10 14
  , .pair 9 10 0 15
  , .halt 0
  ]

@[simp] theorem descriptionLayoutPrepProgram_oracleFree :
    OracleFree descriptionLayoutPrepProgram := by
  rfl

def descriptionLayoutPrepFuel : ℕ := 16

def descriptionLayoutPrepOutput (n bound code : ℕ) : ℕ :=
  Nat.pair (bitSerialMulInput (bound + 1) (rowWidth n bound))
    (Nat.pair (bound + 1)
      (Nat.pair (boundedCircuitFieldLimit n bound)
        (Nat.pair (rowWidth n bound) code)))

def descriptionLayoutPrepBits (n bound code : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair code (Nat.pair n bound))
      (descriptionLayoutPrepOutput n bound code))

set_option maxHeartbeats 400000 in
-- The layout word nests five pairings over three derived numerals, so
-- elaborating the width chain alone exceeds the default budget.
theorem run_descriptionLayoutPrepProgram (inputLength n bound code : ℕ) :
    runNPOracleProgram descriptionLayoutPrepProgram
        (descriptionLayoutPrepBits n bound code) descriptionLayoutPrepFuel
        (initialNPOracleState inputLength
          (Nat.pair code (Nat.pair n bound))) =
      some (descriptionLayoutPrepOutput n bound code) := by
  have hlimit : boundedCircuitFieldLimit n bound = n + bound + 1 := rfl
  have hwidth : rowWidth n bound = 6 + 2 * boundedCircuitFieldLimit n bound :=
    rfl
  have hinput :
      natBitLength (Nat.pair code (Nat.pair n bound)) ≤
        descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput :
      natBitLength (descriptionLayoutPrepOutput n bound code) ≤
        descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hcode : natBitLength code ≤ descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hshape : natBitLength (Nat.pair n bound) ≤
      descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have harity : natBitLength n ≤ descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.left_le_pair _ _) hshape
  have hbound : natBitLength bound ≤ descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.right_le_pair _ _) hshape
  have hcount :
      natBitLength
          (Nat.pair (bound + 1)
            (Nat.pair (boundedCircuitFieldLimit n bound)
              (Nat.pair (rowWidth n bound) code))) ≤
        descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.right_le_pair _ _) houtput
  have hrows : natBitLength (bound + 1) ≤
      descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.left_le_pair _ _) hcount
  have hcontext :
      natBitLength
          (Nat.pair (boundedCircuitFieldLimit n bound)
            (Nat.pair (rowWidth n bound) code)) ≤
        descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.right_le_pair _ _) hcount
  have hfield : natBitLength (boundedCircuitFieldLimit n bound) ≤
      descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.left_le_pair _ _) hcontext
  have hpairWidth : natBitLength (Nat.pair (rowWidth n bound) code) ≤
      descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.right_le_pair _ _) hcontext
  have hrowWidth : natBitLength (rowWidth n bound) ≤
      descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.left_le_pair _ _) hpairWidth
  have hproduct :
      natBitLength (bitSerialMulInput (bound + 1) (rowWidth n bound)) ≤
        descriptionLayoutPrepBits n bound code :=
    bits_of_le (Nat.left_le_pair _ _) houtput
  have hsum : natBitLength (n + bound) ≤
      descriptionLayoutPrepBits n bound code :=
    bits_of_le (by omega) hfield
  have hdouble :
      natBitLength
          (boundedCircuitFieldLimit n bound + boundedCircuitFieldLimit n bound) ≤
        descriptionLayoutPrepBits n bound code :=
    bits_of_le (by omega) hrowWidth
  have hsix : natBitLength 6 ≤ descriptionLayoutPrepBits n bound code :=
    bits_of_le (by omega) hrowWidth
  rw [show descriptionLayoutPrepFuel = 15 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := code) (by rfl) rfl
    (by simp [initialNPOracleState]) hcode]
  rw [show (15 : ℕ) = 14 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair n bound) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hshape]
  rw [show (14 : ℕ) = 13 + 1 by omega]
  rw [run_unpairLeft_instruction (value := n) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harity]
  rw [show (13 : ℕ) = 12 + 1 by omega]
  rw [run_unpairRight_instruction (value := bound) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbound]
  rw [show (12 : ℕ) = 11 + 1 by omega]
  rw [run_add_instruction (value := n + bound) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsum]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_increment_instruction (value := boundedCircuitFieldLimit n bound)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hlimit]) hfield]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_add_instruction
    (value := boundedCircuitFieldLimit n bound + boundedCircuitFieldLimit n bound)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdouble]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_set_instruction (value := 6) (by rfl) rfl hsix]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_add_instruction (value := rowWidth n bound) (by rfl) rfl
    (by
      rw [← rowWidth_eq n bound]
      simp [NPOracleState.write, NPOracleState.jump])
    hrowWidth]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_increment_instruction (value := bound + 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrows]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_pair_instruction
    (value := bitSerialMulInput (bound + 1) (rowWidth n bound)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSerialMulInput])
    hproduct]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (rowWidth n bound) code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpairWidth]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit n bound)
        (Nat.pair (rowWidth n bound) code)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcontext]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (bound + 1)
        (Nat.pair (boundedCircuitFieldLimit n bound)
          (Nat.pair (rowWidth n bound) code))) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcount]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := descriptionLayoutPrepOutput n bound code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      descriptionLayoutPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Reorder the multiplied length into the decoder's layout word. -/
def descriptionLayoutPostProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .pair 2 9 2 9
  , .pair 8 2 2 10
  , .pair 6 2 2 11
  , .pair 4 2 0 12
  , .halt 0
  ]

@[simp] theorem descriptionLayoutPostProgram_oracleFree :
    OracleFree descriptionLayoutPostProgram := by
  rfl

def descriptionLayoutPostFuel : ℕ := 13

def descriptionLayoutPostInput (rowCount limit width len code : ℕ) : ℕ :=
  Nat.pair len (Nat.pair rowCount (Nat.pair limit (Nat.pair width code)))

def descriptionLayoutPostBits (rowCount limit width len code : ℕ) : ℕ :=
  natBitLength
    (max (descriptionLayoutPostInput rowCount limit width len code)
      (descriptionLayoutWord rowCount limit width len code))

set_option maxHeartbeats 400000 in
-- The statement carries both five-deep layout words, so elaborating the width
-- chain alone exceeds the default budget.
theorem run_descriptionLayoutPostProgram
    (inputLength rowCount limit width len code : ℕ) :
    runNPOracleProgram descriptionLayoutPostProgram
        (descriptionLayoutPostBits rowCount limit width len code)
        descriptionLayoutPostFuel
        (initialNPOracleState inputLength
          (descriptionLayoutPostInput rowCount limit width len code)) =
      some (descriptionLayoutWord rowCount limit width len code) := by
  have hinput :
      natBitLength (descriptionLayoutPostInput rowCount limit width len code) ≤
        descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput :
      natBitLength (descriptionLayoutWord rowCount limit width len code) ≤
        descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hlen : natBitLength len ≤
      descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hrest :
      natBitLength (Nat.pair rowCount (Nat.pair limit (Nat.pair width code))) ≤
        descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hrows : natBitLength rowCount ≤
      descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.left_le_pair _ _) hrest
  have hmiddle : natBitLength (Nat.pair limit (Nat.pair width code)) ≤
      descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) hrest
  have hlimit : natBitLength limit ≤
      descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.left_le_pair _ _) hmiddle
  have hpairWidth : natBitLength (Nat.pair width code) ≤
      descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) hmiddle
  have hwidth : natBitLength width ≤
      descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.left_le_pair _ _) hpairWidth
  have hcode : natBitLength code ≤
      descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) hpairWidth
  have hcontext :
      natBitLength (descriptionRowContext limit width len code) ≤
        descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) houtput
  have htail : natBitLength (Nat.pair width (Nat.pair len code)) ≤
      descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) hcontext
  have hcell : natBitLength (Nat.pair len code) ≤
      descriptionLayoutPostBits rowCount limit width len code :=
    bits_of_le (Nat.right_le_pair _ _) htail
  rw [show descriptionLayoutPostFuel = 12 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := len) (by rfl) rfl
    (by simp [initialNPOracleState, descriptionLayoutPostInput]) hlen]
  rw [show (12 : ℕ) = 11 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair rowCount (Nat.pair limit (Nat.pair width code)))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      descriptionLayoutPostInput])
    hrest]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := rowCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrows]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair limit (Nat.pair width code))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmiddle]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := limit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlimit]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair width code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpairWidth]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcode]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair len code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcell]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair width (Nat.pair len code))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := descriptionRowContext limit width len code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionRowContext])
    hcontext]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := descriptionLayoutWord rowCount limit width len code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionLayoutWord])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- **The layout stage.**  Derive the field limit, the row width, the row count
and the description length from the two request numerals. -/
def descriptionLayoutProgram : NPOracleProgram :=
  linkPrograms descriptionLayoutPrepProgram
    (linkPrograms (preserveRightProgram bitSerialMulProgram)
      descriptionLayoutPostProgram)

def descriptionLayoutFuel (n bound : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram bitSerialMulProgram)
      descriptionLayoutPostProgram)
    descriptionLayoutPrepFuel
    (linkFuel descriptionLayoutPostProgram
      (preserveRightFuel (bitSerialMulFuel (rowWidth n bound)))
      descriptionLayoutPostFuel)

def descriptionLayoutBits (inputLength n bound code : ℕ) : ℕ :=
  occurrenceStageBits inputLength (descriptionLayoutPrepBits n bound code)
    (occurrenceStageBits inputLength
      (preserveRightBits
        (bitSerialMulBits inputLength (bound + 1) (rowWidth n bound))
        (bitSerialMulInput (bound + 1) (rowWidth n bound))
        (Nat.pair (bound + 1)
          (Nat.pair (boundedCircuitFieldLimit n bound)
            (Nat.pair (rowWidth n bound) code)))
        ((bound + 1) * rowWidth n bound))
      (descriptionLayoutPostBits (bound + 1)
        (boundedCircuitFieldLimit n bound) (rowWidth n bound)
        ((bound + 1) * rowWidth n bound) code))

/-- **The layout stage, executed.** -/
theorem run_descriptionLayoutProgram (inputLength n bound code : ℕ) :
    runNPOracleProgram descriptionLayoutProgram
        (descriptionLayoutBits inputLength n bound code)
        (descriptionLayoutFuel n bound)
        (initialNPOracleState inputLength
          (Nat.pair code (Nat.pair n bound))) =
      some
        (descriptionLayoutWord (bound + 1)
          (boundedCircuitFieldLimit n bound) (rowWidth n bound)
          ((bound + 1) * rowWidth n bound) code) :=
  run_occurrenceStage
    (run_descriptionLayoutPrepProgram inputLength n bound code)
    (run_occurrenceStage
      (run_preserveRightProgram bitSerialMulProgram inputLength
        (bitSerialMulBits inputLength (bound + 1) (rowWidth n bound))
        (bitSerialMulFuel (rowWidth n bound))
        (bitSerialMulInput (bound + 1) (rowWidth n bound))
        (Nat.pair (bound + 1)
          (Nat.pair (boundedCircuitFieldLimit n bound)
            (Nat.pair (rowWidth n bound) code)))
        ((bound + 1) * rowWidth n bound)
        (run_bitSerialMulProgram inputLength (bound + 1) (rowWidth n bound)))
      (run_descriptionLayoutPostProgram inputLength (bound + 1)
        (boundedCircuitFieldLimit n bound) (rowWidth n bound)
        ((bound + 1) * rowWidth n bound) code))

/-! ## 10. The rows of a canonical description -/

private theorem descriptionRowAt_node {n bound : ℕ} (circuit : BooleanCircuit n)
    (row : ℕ) (hrow : row < circuit.nodes.length) :
    descriptionRowAt bound circuit row =
      boundedNodeDescriptionBits bound (circuit.nodes[row]'hrow) := by
  rw [descriptionRowAt]
  rw [List.getD_eq_getElem _ _ (by
    simp only [canonicalDescriptionRows, List.length_append, List.length_map,
      List.length_singleton, List.length_replicate]
    omega)]
  simpa only [List.get_eq_getElem] using
    canonicalDescriptionRows_get_node (bound := bound) circuit ⟨row, hrow⟩

private theorem descriptionRowAt_output {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    descriptionRowAt bound circuit circuit.nodes.length =
      boundedOutputDescriptionBits n bound circuit.output.val := by
  rw [descriptionRowAt]
  rw [List.getD_eq_getElem _ _ (by
    rw [canonicalDescriptionRows_length circuit hsize]
    simpa only [BooleanCircuit.size] using Nat.lt_succ_of_le hsize)]
  exact canonicalDescriptionRows_get_output circuit hsize

private theorem descriptionRowAt_padding {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) (row : ℕ)
    (hlow : circuit.nodes.length < row) (hhigh : row < bound + 1) :
    descriptionRowAt bound circuit row =
      boundedPaddingDescriptionBits n bound := by
  obtain ⟨offset, hoffset⟩ :
      ∃ offset, row = circuit.nodes.length + 1 + offset :=
    ⟨row - circuit.nodes.length - 1, by omega⟩
  subst hoffset
  have hbound : offset < bound - circuit.size := by
    simp only [BooleanCircuit.size] at hsize ⊢
    omega
  rw [descriptionRowAt]
  rw [List.getD_eq_getElem _ _ (by
    rw [canonicalDescriptionRows_length circuit hsize]
    exact hhigh)]
  exact canonicalDescriptionRows_get_padding circuit hsize ⟨offset, hbound⟩

private theorem row_fit {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) (row : ℕ) (hrow : row < bound + 1) :
    row * rowWidth n bound + (6 + boundedCircuitFieldLimit n bound) +
        boundedCircuitFieldLimit n bound ≤
      (descriptionBits bound circuit).length := by
  have hwidth : rowWidth n bound = 6 + 2 * boundedCircuitFieldLimit n bound :=
    rfl
  have hdesc : descriptionWidth n bound = (bound + 1) * rowWidth n bound := rfl
  have hstep : row * rowWidth n bound + rowWidth n bound =
      (row + 1) * rowWidth n bound := by ring
  have hmul : (row + 1) * rowWidth n bound ≤ (bound + 1) * rowWidth n bound :=
    Nat.mul_le_mul_right _ (by omega)
  rw [descriptionBits_length circuit hsize, hdesc]
  omega

/-- The three field sums of a row whose bits are a known encoded row. -/
private theorem descriptionRowFields_eq {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) (row : ℕ)
    (hrow : row < bound + 1) (tag first second : ℕ)
    (hrowEq :
      descriptionRowAt bound circuit row =
        encodedDescriptionRow n bound tag first second)
    (htag : tag ≤ 6) (hfirst : first ≤ boundedCircuitFieldLimit n bound)
    (hsecond : second ≤ boundedCircuitFieldLimit n bound) :
    descriptionRowFields (descriptionBits bound circuit) row
        (boundedCircuitFieldLimit n bound) (rowWidth n bound) =
      (tag, first, second) := by
  obtain ⟨htagSum, hfirstSum, hsecondSum⟩ :=
    descriptionField_encodedRow circuit hsize row hrow tag first second hrowEq
  rw [descriptionRowFields, descriptionBlockValues_sum, descriptionBlockValues_sum,
    descriptionBlockValues_sum, htagSum, hfirstSum, hsecondSum,
    Nat.min_eq_left htag, Nat.min_eq_left hfirst, Nat.min_eq_left hsecond]

/-- The node indicator of a row whose bits are a known encoded row. -/
private theorem descriptionCountLeafValue_eq {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) (row : ℕ)
    (hrow : row < bound + 1) (tag first second : ℕ)
    (hrowEq :
      descriptionRowAt bound circuit row =
        encodedDescriptionRow n bound tag first second) :
    descriptionCountLeafValue (descriptionBits bound circuit) row
        (rowWidth n bound) =
      1 - (decide (4 < tag)).toNat := by
  rw [descriptionCountLeafValue, descriptionBlockValues_sum,
    descriptionField_tagDigit circuit hsize row hrow tag first second hrowEq]

/-- **The node code of one node row.** -/
theorem descriptionNodeCode_node {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) (row : ℕ)
    (hrow : row < circuit.nodes.length) :
    descriptionNodeCode
        (descriptionRowFields (descriptionBits bound circuit) row
          (boundedCircuitFieldLimit n bound) (rowWidth n bound)).1
        (descriptionRowFields (descriptionBits bound circuit) row
          (boundedCircuitFieldLimit n bound) (rowWidth n bound)).2.1
        (descriptionRowFields (descriptionBits bound circuit) row
          (boundedCircuitFieldLimit n bound) (rowWidth n bound)).2.2 =
      encodeBooleanNode (circuit.nodes[row]'hrow) := by
  have hlimit : boundedCircuitFieldLimit n bound = n + bound + 1 := rfl
  have hnodes : circuit.nodes.length ≤ bound := by
    simpa only [BooleanCircuit.size] using hsize
  have hrowLt : row < bound + 1 := by omega
  have hwf : (circuit.nodes[row]'hrow).WellFormedAt row := by
    simpa only [List.get_eq_getElem] using circuit.wellFormed ⟨row, hrow⟩
  have hbits := descriptionRowAt_node (bound := bound) circuit row hrow
  obtain ⟨node, hnode⟩ : ∃ node, circuit.nodes[row]'hrow = node := ⟨_, rfl⟩
  rw [hnode] at hwf hbits ⊢
  cases node with
  | const value =>
      rw [descriptionRowFields_eq circuit hsize row hrowLt 0 value.toNat 0
        (by rw [hbits, boundedNodeDescriptionBits_eq_encoded]) (by omega)
        (by
          have hone : value.toNat ≤ 1 := by cases value <;> decide
          omega)
        (by omega)]
      rw [descriptionNodeCode, if_pos (by omega)]
      rfl
  | input index =>
      have hindex : index.val < n := index.isLt
      rw [descriptionRowFields_eq circuit hsize row hrowLt 1 index.val 0
        (by rw [hbits, boundedNodeDescriptionBits_eq_encoded]) (by omega)
        (by omega) (by omega)]
      rw [descriptionNodeCode, if_pos (by omega)]
      rfl
  | not child =>
      have hchild : child < row := hwf
      rw [descriptionRowFields_eq circuit hsize row hrowLt 2 child 0
        (by rw [hbits, boundedNodeDescriptionBits_eq_encoded]) (by omega)
        (by omega) (by omega)]
      rw [descriptionNodeCode, if_pos (by omega)]
      rfl
  | and left right =>
      obtain ⟨hleft, hright⟩ := hwf
      rw [descriptionRowFields_eq circuit hsize row hrowLt 3 left right
        (by rw [hbits, boundedNodeDescriptionBits_eq_encoded]) (by omega)
        (by omega) (by omega)]
      rw [descriptionNodeCode, if_neg (by omega)]
      rfl
  | or left right =>
      obtain ⟨hleft, hright⟩ := hwf
      rw [descriptionRowFields_eq circuit hsize row hrowLt 4 left right
        (by rw [hbits, boundedNodeDescriptionBits_eq_encoded]) (by omega)
        (by omega) (by omega)]
      rw [descriptionNodeCode, if_neg (by omega)]
      rfl

/-- **The node list.**  The pool over the counted rows is exactly the circuit's
own balanced node list. -/
theorem descriptionNodeList_eq {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    (List.range circuit.nodes.length).map (fun row =>
        descriptionNodeCode
          (descriptionRowFields (descriptionBits bound circuit) row
            (boundedCircuitFieldLimit n bound) (rowWidth n bound)).1
          (descriptionRowFields (descriptionBits bound circuit) row
            (boundedCircuitFieldLimit n bound) (rowWidth n bound)).2.1
          (descriptionRowFields (descriptionBits bound circuit) row
            (boundedCircuitFieldLimit n bound) (rowWidth n bound)).2.2) =
      circuit.nodes.map encodeBooleanNode := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro index hleft _hright
    have hindex : index < circuit.nodes.length := by
      simpa only [List.length_map, List.length_range] using hleft
    simp only [List.getElem_map, List.getElem_range]
    exact descriptionNodeCode_node circuit hsize index hindex

private theorem sum_range_indicator (len value : ℕ) :
    ((List.range len).map fun index => if index < value then 1 else 0).sum =
      min value len := by
  induction len with
  | zero => simp
  | succ len ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      by_cases hlen : len < value
      · rw [if_pos hlen]
        omega
      · rw [if_neg hlen]
        omega

/-- **The node count.**  The fifth tag digit is zero exactly on the rows that
carry a node, so the pooled indicator sums to the circuit's own size. -/
theorem descriptionNodeCount_eq {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    ((List.range (bound + 1)).map fun row =>
        descriptionCountLeafValue (descriptionBits bound circuit) row
          (rowWidth n bound)).sum =
      circuit.nodes.length := by
  have hnodes : circuit.nodes.length ≤ bound := by
    simpa only [BooleanCircuit.size] using hsize
  have hmap :
      ((List.range (bound + 1)).map fun row =>
          descriptionCountLeafValue (descriptionBits bound circuit) row
            (rowWidth n bound)) =
        (List.range (bound + 1)).map fun row =>
          if row < circuit.nodes.length then 1 else 0 := by
    refine List.map_congr_left ?_
    intro row hrow
    have hrowLt : row < bound + 1 := List.mem_range.mp hrow
    rcases Nat.lt_trichotomy row circuit.nodes.length with hlt | heq | hgt
    · have hnode := descriptionRowAt_node (bound := bound) circuit row hlt
      obtain ⟨node, hnodeEq⟩ : ∃ node, circuit.nodes[row]'hlt = node := ⟨_, rfl⟩
      rw [hnodeEq] at hnode
      rw [if_pos hlt]
      cases node with
      | const value =>
          rw [descriptionCountLeafValue_eq circuit hsize row hrowLt 0
            value.toNat 0
            (by rw [hnode, boundedNodeDescriptionBits_eq_encoded])]
          rfl
      | input index =>
          rw [descriptionCountLeafValue_eq circuit hsize row hrowLt 1 index.val 0
            (by rw [hnode, boundedNodeDescriptionBits_eq_encoded])]
          rfl
      | not child =>
          rw [descriptionCountLeafValue_eq circuit hsize row hrowLt 2 child 0
            (by rw [hnode, boundedNodeDescriptionBits_eq_encoded])]
          rfl
      | and left right =>
          rw [descriptionCountLeafValue_eq circuit hsize row hrowLt 3 left right
            (by rw [hnode, boundedNodeDescriptionBits_eq_encoded])]
          rfl
      | or left right =>
          rw [descriptionCountLeafValue_eq circuit hsize row hrowLt 4 left right
            (by rw [hnode, boundedNodeDescriptionBits_eq_encoded])]
          rfl
    · rw [if_neg (by omega)]
      rw [descriptionCountLeafValue_eq circuit hsize row hrowLt 5
        circuit.output.val 0
        (by rw [heq, descriptionRowAt_output circuit hsize,
          boundedOutputDescriptionBits_eq_encoded])]
      rfl
    · rw [if_neg (by omega)]
      rw [descriptionCountLeafValue_eq circuit hsize row hrowLt 6 0 0
        (by rw [descriptionRowAt_padding circuit hsize row hgt hrowLt,
          boundedPaddingDescriptionBits_eq_encoded])]
      rfl
  rw [hmap, sum_range_indicator]
  omega

/-- **The output address.**  The first field of the output row is the circuit's
own distinguished output. -/
theorem descriptionOutputField_eq {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    (descriptionRowFields (descriptionBits bound circuit) circuit.nodes.length
      (boundedCircuitFieldLimit n bound) (rowWidth n bound)).2.1 =
      circuit.output.val := by
  have hlimit : boundedCircuitFieldLimit n bound = n + bound + 1 := rfl
  have hnodes : circuit.nodes.length ≤ bound := by
    simpa only [BooleanCircuit.size] using hsize
  have houtput : circuit.output.val < circuit.nodes.length := circuit.output.isLt
  rw [descriptionRowFields_eq circuit hsize circuit.nodes.length (by omega) 5
    circuit.output.val 0
    (by rw [descriptionRowAt_output circuit hsize,
      boundedOutputDescriptionBits_eq_encoded])
    (by omega) (by omega) (by omega)]

/-! ## 11. The three pooled stages -/

/-- **The node count.**  One pool over every row's node indicator, summed. -/
def canonicalDescriptionNodeCountProgram : NPOracleProgram :=
  balancedNatSumAfterProgram (indexedPoolListProgram descriptionCountLeafProgram)

def descriptionCountValues (values : List ℕ) (rowCount width : ℕ) : List ℕ :=
  (List.range rowCount).map fun row => descriptionCountLeafValue values row width

def canonicalDescriptionNodeCountPoolFuel (inputLength : ℕ) (values : List ℕ)
    (rowCount limit width : ℕ) : ℕ :=
  indexedPoolListFuel descriptionCountLeafProgram inputLength rowCount
    (descriptionRowContext limit width values.length
      (encodeBalancedList values))
    (fun row => descriptionCountLeafFuel inputLength values row width)

def canonicalDescriptionNodeCountPoolBits (inputLength : ℕ) (values : List ℕ)
    (rowCount limit width : ℕ) : ℕ :=
  max
    (indexedPoolListBits inputLength rowCount
      (descriptionRowContext limit width values.length
        (encodeBalancedList values))
      (fun row => descriptionCountLeafValue values row width))
    (((List.range rowCount).map fun row =>
      descriptionCountLeafBits inputLength values row limit width).foldr max 1)

def canonicalDescriptionNodeCountFuel (inputLength : ℕ) (values : List ℕ)
    (rowCount limit width : ℕ) : ℕ :=
  balancedNatSumAfterFuel
    (canonicalDescriptionNodeCountPoolFuel inputLength values rowCount limit
      width)
    (descriptionCountValues values rowCount width)

def canonicalDescriptionNodeCountBits (inputLength : ℕ) (values : List ℕ)
    (rowCount limit width : ℕ) : ℕ :=
  balancedNatSumAfterBits inputLength
    (canonicalDescriptionNodeCountPoolBits inputLength values rowCount limit
      width)
    (descriptionCountValues values rowCount width)

theorem run_canonicalDescriptionNodeCountProgram (inputLength : ℕ)
    (values : List ℕ) (rowCount limit width : ℕ)
    (hfit : ∀ row : ℕ, row < rowCount → row * width + 4 + 1 ≤ values.length) :
    runNPOracleProgram canonicalDescriptionNodeCountProgram
        (canonicalDescriptionNodeCountBits inputLength values rowCount limit
          width)
        (canonicalDescriptionNodeCountFuel inputLength values rowCount limit
          width)
        (initialNPOracleState inputLength
          (descriptionLayoutWord rowCount limit width values.length
            (encodeBalancedList values))) =
      some (descriptionCountValues values rowCount width).sum := by
  have hpool :
      runNPOracleProgram (indexedPoolListProgram descriptionCountLeafProgram)
          (canonicalDescriptionNodeCountPoolBits inputLength values rowCount
            limit width)
          (canonicalDescriptionNodeCountPoolFuel inputLength values rowCount
            limit width)
          (initialNPOracleState inputLength
            (descriptionLayoutWord rowCount limit width values.length
              (encodeBalancedList values))) =
        some
          (encodeBalancedList
            (descriptionCountValues values rowCount width)) := by
    refine run_indexedPoolListProgram descriptionCountLeafProgram inputLength
      rowCount
      (descriptionRowContext limit width values.length
        (encodeBalancedList values))
      (canonicalDescriptionNodeCountPoolBits inputLength values rowCount limit
        width)
      (fun row => descriptionCountLeafFuel inputLength values row width)
      (fun row => descriptionCountLeafValue values row width)
      (Nat.le_max_left _ _) ?_
    intro row hrow
    refine run_bits_mono
      (run_descriptionCountLeafProgram inputLength values row limit width
        (hfit row hrow)) ?_
    refine le_trans (le_foldr_max_of_mem ?_) (Nat.le_max_right _ _)
    exact List.mem_map_of_mem (List.mem_range.mpr hrow)
  exact run_balancedNatSumAfterProgram
    (indexedPoolListProgram descriptionCountLeafProgram) inputLength _
    (canonicalDescriptionNodeCountPoolBits inputLength values rowCount limit
      width)
    (canonicalDescriptionNodeCountPoolFuel inputLength values rowCount limit
      width)
    (descriptionCountValues values rowCount width) hpool

/-- **The node list.**  One pool over the counted rows. -/
def canonicalDescriptionNodesProgram : NPOracleProgram :=
  indexedPoolListProgram descriptionRowLeafProgram

def descriptionNodeCodes (values : List ℕ) (count limit width : ℕ) : List ℕ :=
  (List.range count).map fun row =>
    descriptionNodeCode (descriptionRowFields values row limit width).1
      (descriptionRowFields values row limit width).2.1
      (descriptionRowFields values row limit width).2.2

def canonicalDescriptionNodesFuel (inputLength : ℕ) (values : List ℕ)
    (count limit width : ℕ) : ℕ :=
  indexedPoolListFuel descriptionRowLeafProgram inputLength count
    (descriptionRowContext limit width values.length
      (encodeBalancedList values))
    (fun row => descriptionRowLeafFuel inputLength values row limit width)

def canonicalDescriptionNodesBits (inputLength : ℕ) (values : List ℕ)
    (count limit width : ℕ) : ℕ :=
  max
    (indexedPoolListBits inputLength count
      (descriptionRowContext limit width values.length
        (encodeBalancedList values))
      (fun row =>
        descriptionNodeCode (descriptionRowFields values row limit width).1
          (descriptionRowFields values row limit width).2.1
          (descriptionRowFields values row limit width).2.2))
    (((List.range count).map fun row =>
      descriptionRowLeafBits inputLength values row limit width).foldr max 1)

theorem run_canonicalDescriptionNodesProgram (inputLength : ℕ)
    (values : List ℕ) (count limit width : ℕ)
    (hfit : ∀ row : ℕ, row < count →
      row * width + (6 + limit) + limit ≤ values.length) :
    runNPOracleProgram canonicalDescriptionNodesProgram
        (canonicalDescriptionNodesBits inputLength values count limit width)
        (canonicalDescriptionNodesFuel inputLength values count limit width)
        (initialNPOracleState inputLength
          (descriptionLayoutWord count limit width values.length
            (encodeBalancedList values))) =
      some
        (encodeBalancedList (descriptionNodeCodes values count limit width)) := by
  refine run_indexedPoolListProgram descriptionRowLeafProgram inputLength count
    (descriptionRowContext limit width values.length (encodeBalancedList values))
    (canonicalDescriptionNodesBits inputLength values count limit width)
    (fun row => descriptionRowLeafFuel inputLength values row limit width)
    (fun row =>
      descriptionNodeCode (descriptionRowFields values row limit width).1
        (descriptionRowFields values row limit width).2.1
        (descriptionRowFields values row limit width).2.2)
    (Nat.le_max_left _ _) ?_
  intro row hrow
  refine run_bits_mono
    (run_descriptionRowLeafProgram inputLength values row limit width
      (hfit row hrow)) ?_
  refine le_trans (le_foldr_max_of_mem ?_) (Nat.le_max_right _ _)
  exact List.mem_map_of_mem (List.mem_range.mpr hrow)

/-- **The output address.**  The first field of the counted row, encoded. -/
def canonicalDescriptionOutputProgram : NPOracleProgram :=
  linkPrograms descriptionFirstStageProgram descriptionEncodeNatProgram

def canonicalDescriptionOutputFuel (inputLength : ℕ) (values : List ℕ)
    (count limit width : ℕ) : ℕ :=
  linkFuel descriptionEncodeNatProgram
    (descriptionFieldStageFuel inputLength values descriptionFirstPostProgram
      descriptionFirstPostFuel (count * width + 6) limit width)
    descriptionEncodeNatFuel

def canonicalDescriptionOutputBits (inputLength : ℕ) (values : List ℕ)
    (count limit width : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (descriptionFieldStageBits inputLength values count limit width limit 6)
    (descriptionEncodeNatBits
      (descriptionBlockValues values (count * width + 6) limit).sum)

theorem run_canonicalDescriptionOutputProgram (inputLength : ℕ)
    (values : List ℕ) (count limit width : ℕ)
    (hfit : count * width + 6 + limit ≤ values.length) :
    runNPOracleProgram canonicalDescriptionOutputProgram
        (canonicalDescriptionOutputBits inputLength values count limit width)
        (canonicalDescriptionOutputFuel inputLength values count limit width)
        (initialNPOracleState inputLength
          (descriptionLayoutWord count limit width values.length
            (encodeBalancedList values))) =
      some
        (encodeNat
          (descriptionBlockValues values (count * width + 6) limit).sum) :=
  run_occurrenceStage
    (run_descriptionFirstStageProgram inputLength values count limit width hfit)
    (run_descriptionEncodeNatProgram inputLength
      (descriptionBlockValues values (count * width + 6) limit).sum)

/-! ## 12. The decoder -/

/-- Drop the row count once the node count is known. -/
def descriptionDropCountProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .pair 2 4 0 4
  , .halt 0
  ]

@[simp] theorem descriptionDropCountProgram_oracleFree :
    OracleFree descriptionDropCountProgram := by
  rfl

def descriptionDropCountFuel : ℕ := 5

def descriptionDropCountBits (count rowCount context : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair count (Nat.pair rowCount context))
      (Nat.pair count context))

theorem run_descriptionDropCountProgram
    (inputLength count rowCount context : ℕ) :
    runNPOracleProgram descriptionDropCountProgram
        (descriptionDropCountBits count rowCount context)
        descriptionDropCountFuel
        (initialNPOracleState inputLength
          (Nat.pair count (Nat.pair rowCount context))) =
      some (Nat.pair count context) := by
  have hinput :
      natBitLength (Nat.pair count (Nat.pair rowCount context)) ≤
        descriptionDropCountBits count rowCount context :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput :
      natBitLength (Nat.pair count context) ≤
        descriptionDropCountBits count rowCount context :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hcount : natBitLength count ≤
      descriptionDropCountBits count rowCount context :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have htail : natBitLength (Nat.pair rowCount context) ≤
      descriptionDropCountBits count rowCount context :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hcontext : natBitLength context ≤
      descriptionDropCountBits count rowCount context :=
    bits_of_le (Nat.right_le_pair _ _) htail
  rw [show descriptionDropCountFuel = 4 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := count) (by rfl) rfl
    (by simp [initialNPOracleState]) hcount]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair rowCount context)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htail]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := context) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcontext]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair count context) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

private def decoderStage8 : NPOracleProgram :=
  linkPrograms swapPairProgram circuitJoinProgram

private def decoderStage7 : NPOracleProgram :=
  linkPrograms (preserveRightProgram canonicalDescriptionOutputProgram)
    decoderStage8

private def decoderStage6 : NPOracleProgram :=
  linkPrograms swapPairProgram decoderStage7

private def decoderStage5 : NPOracleProgram :=
  linkPrograms (preserveRightProgram canonicalDescriptionNodesProgram)
    decoderStage6

private def decoderStage4 : NPOracleProgram :=
  linkPrograms duplicateProgram decoderStage5

private def decoderStage3 : NPOracleProgram :=
  linkPrograms descriptionDropCountProgram decoderStage4

private def decoderStage2 : NPOracleProgram :=
  linkPrograms (preserveRightProgram canonicalDescriptionNodeCountProgram)
    decoderStage3

private def decoderStage1 : NPOracleProgram :=
  linkPrograms duplicateProgram decoderStage2

/-- **The grouping decoder.**  One fixed oracle-free stream: derive the row
layout, count the node rows, pool their codes, read the output address, and
close the circuit code. -/
def canonicalDescriptionDecoderProgram : NPOracleProgram :=
  linkPrograms descriptionLayoutProgram decoderStage1

/-- The decoder's clock at one description. -/
def canonicalDescriptionDecoderFuelAt (inputLength : ℕ) (values : List ℕ)
    (n bound count : ℕ) : ℕ :=
  linkFuel decoderStage1 (descriptionLayoutFuel n bound) <|
    linkFuel decoderStage2 2 <|
      linkFuel decoderStage3
        (preserveRightFuel
          (canonicalDescriptionNodeCountFuel inputLength values (bound + 1)
            (boundedCircuitFieldLimit n bound) (rowWidth n bound))) <|
        linkFuel decoderStage4 descriptionDropCountFuel <|
          linkFuel decoderStage5 2 <|
            linkFuel decoderStage6
              (preserveRightFuel
                (canonicalDescriptionNodesFuel inputLength values count
                  (boundedCircuitFieldLimit n bound) (rowWidth n bound))) <|
              linkFuel decoderStage7 4 <|
                linkFuel decoderStage8
                  (preserveRightFuel
                    (canonicalDescriptionOutputFuel inputLength values count
                      (boundedCircuitFieldLimit n bound) (rowWidth n bound)))
                  (linkFuel circuitJoinProgram 4 circuitJoinFuel)

/-- The decoder's width at one description. -/
def canonicalDescriptionDecoderBitsAt (inputLength : ℕ) (values : List ℕ)
    (n bound count nodesCode outputCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
      (descriptionLayoutBits inputLength n bound (encodeBalancedList values)) <|
    occurrenceStageBits inputLength
        (duplicateBits
          (descriptionLayoutWord (bound + 1)
            (boundedCircuitFieldLimit n bound) (rowWidth n bound)
            values.length (encodeBalancedList values))) <|
      occurrenceStageBits inputLength
          (preserveRightBits
            (canonicalDescriptionNodeCountBits inputLength values (bound + 1)
              (boundedCircuitFieldLimit n bound) (rowWidth n bound))
            (descriptionLayoutWord (bound + 1)
              (boundedCircuitFieldLimit n bound) (rowWidth n bound)
              values.length (encodeBalancedList values))
            (descriptionLayoutWord (bound + 1)
              (boundedCircuitFieldLimit n bound) (rowWidth n bound)
              values.length (encodeBalancedList values))
            count) <|
        occurrenceStageBits inputLength
            (descriptionDropCountBits count (bound + 1)
              (descriptionRowContext (boundedCircuitFieldLimit n bound)
                (rowWidth n bound) values.length
                (encodeBalancedList values))) <|
          occurrenceStageBits inputLength
              (duplicateBits
                (descriptionLayoutWord count
                  (boundedCircuitFieldLimit n bound) (rowWidth n bound)
                  values.length (encodeBalancedList values))) <|
            occurrenceStageBits inputLength
                (preserveRightBits
                  (canonicalDescriptionNodesBits inputLength values count
                    (boundedCircuitFieldLimit n bound) (rowWidth n bound))
                  (descriptionLayoutWord count
                    (boundedCircuitFieldLimit n bound) (rowWidth n bound)
                    values.length (encodeBalancedList values))
                  (descriptionLayoutWord count
                    (boundedCircuitFieldLimit n bound) (rowWidth n bound)
                    values.length (encodeBalancedList values))
                  nodesCode) <|
              occurrenceStageBits inputLength
                  (swapPairBits nodesCode
                    (descriptionLayoutWord count
                      (boundedCircuitFieldLimit n bound) (rowWidth n bound)
                      values.length (encodeBalancedList values))) <|
                occurrenceStageBits inputLength
                    (preserveRightBits
                      (canonicalDescriptionOutputBits inputLength values count
                        (boundedCircuitFieldLimit n bound) (rowWidth n bound))
                      (descriptionLayoutWord count
                        (boundedCircuitFieldLimit n bound) (rowWidth n bound)
                        values.length (encodeBalancedList values))
                      nodesCode outputCode) <|
                  occurrenceStageBits inputLength
                    (swapPairBits outputCode nodesCode)
                    (circuitJoinBits nodesCode outputCode)

set_option maxHeartbeats 1600000 in
-- The statement carries the whole nine-stage stream at one description, so
-- elaborating it alone exceeds the default budget.
/-- **The decoder, executed at one canonical description.** -/
theorem run_canonicalDescriptionDecoderProgram {n : ℕ} (inputLength bound : ℕ)
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    runNPOracleProgram canonicalDescriptionDecoderProgram
        (canonicalDescriptionDecoderBitsAt inputLength
          (descriptionBits bound circuit) n bound circuit.nodes.length
          (encodeBalancedList (circuit.nodes.map encodeBooleanNode))
          (encodeNat circuit.output.val))
        (canonicalDescriptionDecoderFuelAt inputLength
          (descriptionBits bound circuit) n bound circuit.nodes.length)
        (initialNPOracleState inputLength
          (canonicalDescriptionRequest bound circuit)) =
      some (encodeBooleanCircuit circuit) := by
  have hnodes : circuit.nodes.length ≤ bound := by
    simpa only [BooleanCircuit.size] using hsize
  have hlength : (descriptionBits bound circuit).length =
      (bound + 1) * rowWidth n bound := by
    rw [descriptionBits_length circuit hsize]
    rfl
  have hcountFit : ∀ row : ℕ, row < bound + 1 →
      row * rowWidth n bound + 4 + 1 ≤ (descriptionBits bound circuit).length := by
    intro row hrow
    have := row_fit circuit hsize row hrow
    have hlimit : 1 ≤ boundedCircuitFieldLimit n bound := by
      have hdef : boundedCircuitFieldLimit n bound = n + bound + 1 := rfl
      omega
    omega
  have hnodeFit : ∀ row : ℕ, row < circuit.nodes.length →
      row * rowWidth n bound + (6 + boundedCircuitFieldLimit n bound) +
        boundedCircuitFieldLimit n bound ≤
      (descriptionBits bound circuit).length := by
    intro row hrow
    exact row_fit circuit hsize row (by omega)
  have houtputFit :
      circuit.nodes.length * rowWidth n bound + 6 +
          boundedCircuitFieldLimit n bound ≤
        (descriptionBits bound circuit).length := by
    have := row_fit circuit hsize circuit.nodes.length (by omega)
    omega
  have hcount :
      (descriptionCountValues (descriptionBits bound circuit) (bound + 1)
          (rowWidth n bound)).sum = circuit.nodes.length :=
    descriptionNodeCount_eq circuit hsize
  have hnodeList :
      descriptionNodeCodes (descriptionBits bound circuit)
          circuit.nodes.length (boundedCircuitFieldLimit n bound)
          (rowWidth n bound) =
        circuit.nodes.map encodeBooleanNode :=
    descriptionNodeList_eq circuit hsize
  have houtput :
      (descriptionBlockValues (descriptionBits bound circuit)
          (circuit.nodes.length * rowWidth n bound + 6)
          (boundedCircuitFieldLimit n bound)).sum = circuit.output.val := by
    simpa only [descriptionRowFields] using descriptionOutputField_eq circuit hsize
  have hlayout :
      runNPOracleProgram descriptionLayoutProgram
          (descriptionLayoutBits inputLength n bound
            (encodeBalancedList (descriptionBits bound circuit)))
          (descriptionLayoutFuel n bound)
          (initialNPOracleState inputLength
            (canonicalDescriptionRequest bound circuit)) =
        some
          (descriptionLayoutWord (bound + 1)
            (boundedCircuitFieldLimit n bound) (rowWidth n bound)
            (descriptionBits bound circuit).length
            (encodeBalancedList (descriptionBits bound circuit))) := by
    rw [hlength]
    exact run_descriptionLayoutProgram inputLength n bound
      (encodeBalancedList (descriptionBits bound circuit))
  have hcountRun :
      runNPOracleProgram canonicalDescriptionNodeCountProgram
          (canonicalDescriptionNodeCountBits inputLength
            (descriptionBits bound circuit) (bound + 1)
            (boundedCircuitFieldLimit n bound) (rowWidth n bound))
          (canonicalDescriptionNodeCountFuel inputLength
            (descriptionBits bound circuit) (bound + 1)
            (boundedCircuitFieldLimit n bound) (rowWidth n bound))
          (initialNPOracleState inputLength
            (descriptionLayoutWord (bound + 1)
              (boundedCircuitFieldLimit n bound) (rowWidth n bound)
              (descriptionBits bound circuit).length
              (encodeBalancedList (descriptionBits bound circuit)))) =
        some circuit.nodes.length := by
    rw [← hcount]
    exact run_canonicalDescriptionNodeCountProgram inputLength
      (descriptionBits bound circuit) (bound + 1)
      (boundedCircuitFieldLimit n bound) (rowWidth n bound) hcountFit
  have hnodesRun :
      runNPOracleProgram canonicalDescriptionNodesProgram
          (canonicalDescriptionNodesBits inputLength
            (descriptionBits bound circuit) circuit.nodes.length
            (boundedCircuitFieldLimit n bound) (rowWidth n bound))
          (canonicalDescriptionNodesFuel inputLength
            (descriptionBits bound circuit) circuit.nodes.length
            (boundedCircuitFieldLimit n bound) (rowWidth n bound))
          (initialNPOracleState inputLength
            (descriptionLayoutWord circuit.nodes.length
              (boundedCircuitFieldLimit n bound) (rowWidth n bound)
              (descriptionBits bound circuit).length
              (encodeBalancedList (descriptionBits bound circuit)))) =
        some (encodeBalancedList (circuit.nodes.map encodeBooleanNode)) := by
    rw [← hnodeList]
    exact run_canonicalDescriptionNodesProgram inputLength
      (descriptionBits bound circuit) circuit.nodes.length
      (boundedCircuitFieldLimit n bound) (rowWidth n bound) hnodeFit
  have houtputRun :
      runNPOracleProgram canonicalDescriptionOutputProgram
          (canonicalDescriptionOutputBits inputLength
            (descriptionBits bound circuit) circuit.nodes.length
            (boundedCircuitFieldLimit n bound) (rowWidth n bound))
          (canonicalDescriptionOutputFuel inputLength
            (descriptionBits bound circuit) circuit.nodes.length
            (boundedCircuitFieldLimit n bound) (rowWidth n bound))
          (initialNPOracleState inputLength
            (descriptionLayoutWord circuit.nodes.length
              (boundedCircuitFieldLimit n bound) (rowWidth n bound)
              (descriptionBits bound circuit).length
              (encodeBalancedList (descriptionBits bound circuit)))) =
        some (encodeNat circuit.output.val) := by
    rw [← houtput]
    exact run_canonicalDescriptionOutputProgram inputLength
      (descriptionBits bound circuit) circuit.nodes.length
      (boundedCircuitFieldLimit n bound) (rowWidth n bound) houtputFit
  have hjoin :
      runNPOracleProgram circuitJoinProgram
          (circuitJoinBits
            (encodeBalancedList (circuit.nodes.map encodeBooleanNode))
            (encodeNat circuit.output.val))
          circuitJoinFuel
          (initialNPOracleState inputLength
            (Nat.pair
              (encodeBalancedList (circuit.nodes.map encodeBooleanNode))
              (encodeNat circuit.output.val))) =
        some (encodeBooleanCircuit circuit) := by
    rw [encodeBooleanCircuit_eq_circuitCode]
    exact run_circuitJoinProgram inputLength
      (encodeBalancedList (circuit.nodes.map encodeBooleanNode))
      (encodeNat circuit.output.val) _ (Nat.le_refl _)
  exact run_occurrenceStage hlayout
    (run_occurrenceStage
      (run_duplicateProgram inputLength
        (descriptionLayoutWord (bound + 1) (boundedCircuitFieldLimit n bound)
          (rowWidth n bound) (descriptionBits bound circuit).length
          (encodeBalancedList (descriptionBits bound circuit))))
      (run_occurrenceStage
        (run_preserveRightProgram canonicalDescriptionNodeCountProgram
          inputLength _ _ _ _ _ hcountRun)
        (run_occurrenceStage
          (run_descriptionDropCountProgram inputLength circuit.nodes.length
            (bound + 1)
            (descriptionRowContext (boundedCircuitFieldLimit n bound)
              (rowWidth n bound) (descriptionBits bound circuit).length
              (encodeBalancedList (descriptionBits bound circuit))))
          (run_occurrenceStage
            (run_duplicateProgram inputLength
              (descriptionLayoutWord circuit.nodes.length
                (boundedCircuitFieldLimit n bound) (rowWidth n bound)
                (descriptionBits bound circuit).length
                (encodeBalancedList (descriptionBits bound circuit))))
            (run_occurrenceStage
              (run_preserveRightProgram canonicalDescriptionNodesProgram
                inputLength _ _ _ _ _ hnodesRun)
              (run_occurrenceStage
                (run_swapPairProgram inputLength
                  (encodeBalancedList (circuit.nodes.map encodeBooleanNode))
                  (descriptionLayoutWord circuit.nodes.length
                    (boundedCircuitFieldLimit n bound) (rowWidth n bound)
                    (descriptionBits bound circuit).length
                    (encodeBalancedList (descriptionBits bound circuit))))
                (run_occurrenceStage
                  (run_preserveRightProgram canonicalDescriptionOutputProgram
                    inputLength _ _ _ _ _ houtputRun)
                  (run_occurrenceStage
                    (run_swapPairProgram inputLength
                      (encodeNat circuit.output.val)
                      (encodeBalancedList
                        (circuit.nodes.map encodeBooleanNode)))
                    hjoin))))))))

/-! ## 13. The premise, discharged -/

theorem descriptionNodeCodes_eq {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    descriptionNodeCodes (descriptionBits bound circuit) circuit.nodes.length
        (boundedCircuitFieldLimit n bound) (rowWidth n bound) =
      circuit.nodes.map encodeBooleanNode :=
  descriptionNodeList_eq circuit hsize

theorem descriptionOutputBlock_eq {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    (descriptionBlockValues (descriptionBits bound circuit)
        (circuit.nodes.length * rowWidth n bound + 6)
        (boundedCircuitFieldLimit n bound)).sum = circuit.output.val := by
  simpa only [descriptionRowFields] using descriptionOutputField_eq circuit hsize

/-- The description bits a decoder request carries. -/
def descriptionRequestValues (request : ℕ) : List ℕ :=
  (decodeBalancedList (Nat.unpair request).1).getD []

/-- The coordinate count a decoder request carries. -/
def descriptionRequestArity (request : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair request).2).1

/-- The size bound a decoder request carries. -/
def descriptionRequestBound (request : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair request).2).2

/-- The node count a decoder request describes. -/
def descriptionRequestNodeCount (request : ℕ) : ℕ :=
  (descriptionCountValues (descriptionRequestValues request)
    (descriptionRequestBound request + 1)
    (rowWidth (descriptionRequestArity request)
      (descriptionRequestBound request))).sum

/-- The balanced node list a decoder request describes. -/
def descriptionRequestNodesCode (request : ℕ) : ℕ :=
  encodeBalancedList
    (descriptionNodeCodes (descriptionRequestValues request)
      (descriptionRequestNodeCount request)
      (boundedCircuitFieldLimit (descriptionRequestArity request)
        (descriptionRequestBound request))
      (rowWidth (descriptionRequestArity request)
        (descriptionRequestBound request)))

/-- The encoded output address a decoder request describes. -/
def descriptionRequestOutputCode (request : ℕ) : ℕ :=
  encodeNat
    (descriptionBlockValues (descriptionRequestValues request)
      (descriptionRequestNodeCount request *
          rowWidth (descriptionRequestArity request)
            (descriptionRequestBound request) + 6)
      (boundedCircuitFieldLimit (descriptionRequestArity request)
        (descriptionRequestBound request))).sum

def canonicalDescriptionDecoderFuel (inputLength request : ℕ) : ℕ :=
  canonicalDescriptionDecoderFuelAt inputLength
    (descriptionRequestValues request) (descriptionRequestArity request)
    (descriptionRequestBound request) (descriptionRequestNodeCount request)

def canonicalDescriptionDecoderBits (inputLength request : ℕ) : ℕ :=
  canonicalDescriptionDecoderBitsAt inputLength
    (descriptionRequestValues request) (descriptionRequestArity request)
    (descriptionRequestBound request) (descriptionRequestNodeCount request)
    (descriptionRequestNodesCode request) (descriptionRequestOutputCode request)

private theorem descriptionRequestValues_eq {n : ℕ} (bound : ℕ)
    (circuit : BooleanCircuit n) :
    descriptionRequestValues (canonicalDescriptionRequest bound circuit) =
      descriptionBits bound circuit := by
  simp only [descriptionRequestValues, canonicalDescriptionRequest,
    Nat.unpair_pair, descriptionBits, decodeBalancedList_encode,
    Option.getD_some]

private theorem descriptionRequestArity_eq {n : ℕ} (bound : ℕ)
    (circuit : BooleanCircuit n) :
    descriptionRequestArity (canonicalDescriptionRequest bound circuit) = n := by
  simp only [descriptionRequestArity, canonicalDescriptionRequest,
    Nat.unpair_pair]

private theorem descriptionRequestBound_eq {n : ℕ} (bound : ℕ)
    (circuit : BooleanCircuit n) :
    descriptionRequestBound (canonicalDescriptionRequest bound circuit) =
      bound := by
  simp only [descriptionRequestBound, canonicalDescriptionRequest,
    Nat.unpair_pair]

set_option maxHeartbeats 1600000 in
-- The statement is the whole closed decoder obligation, so elaborating it
-- alone exceeds the default budget.
/-- **The grouping decoder, discharged.**  The last constructive premise of
`CaseTwoCanonicalCircuitEncoder.run_canonicalCircuitEncoderProgram` is a
theorem: one fixed oracle-free stream reads every canonical bounded-circuit
description back as `encodeBooleanCircuit`. -/
theorem canonicalDescriptionDecoder_holds :
    CanonicalDescriptionDecoder canonicalDescriptionDecoderProgram
      canonicalDescriptionDecoderBits canonicalDescriptionDecoderFuel := by
  intro inputLength bound n circuit hsize
  have hvalues := descriptionRequestValues_eq (n := n) bound circuit
  have harity := descriptionRequestArity_eq (n := n) bound circuit
  have hbound := descriptionRequestBound_eq (n := n) bound circuit
  have hcount :
      descriptionRequestNodeCount (canonicalDescriptionRequest bound circuit) =
        circuit.nodes.length := by
    rw [descriptionRequestNodeCount, hvalues, harity, hbound]
    exact descriptionNodeCount_eq circuit hsize
  have hnodes :
      descriptionRequestNodesCode (canonicalDescriptionRequest bound circuit) =
        encodeBalancedList (circuit.nodes.map encodeBooleanNode) := by
    rw [descriptionRequestNodesCode, hvalues, harity, hbound, hcount,
      descriptionNodeCodes_eq circuit hsize]
  have houtput :
      descriptionRequestOutputCode (canonicalDescriptionRequest bound circuit) =
        encodeNat circuit.output.val := by
    rw [descriptionRequestOutputCode, hvalues, harity, hbound, hcount,
      descriptionOutputBlock_eq circuit hsize]
  rw [canonicalDescriptionDecoderBits, canonicalDescriptionDecoderFuel, hvalues,
    harity, hbound, hcount, hnodes, houtput]
  exact run_canonicalDescriptionDecoderProgram inputLength bound circuit hsize

/-! ## 14. The decoder is oracle free -/

theorem descriptionRowBaseProgram_oracleFree :
    OracleFree descriptionRowBaseProgram :=
  oracleFree_linkPrograms descriptionRowBasePrepProgram_oracleFree
    (preserveRightProgram_oracleFree _ bitSerialMulProgram_oracleFree)

theorem descriptionTagStageProgram_oracleFree :
    OracleFree descriptionTagStageProgram :=
  oracleFree_linkPrograms descriptionRowBaseProgram_oracleFree
    (oracleFree_linkPrograms descriptionTagPostProgram_oracleFree
      descriptionBlockSumProgram_oracleFree)

theorem descriptionFirstStageProgram_oracleFree :
    OracleFree descriptionFirstStageProgram :=
  oracleFree_linkPrograms descriptionRowBaseProgram_oracleFree
    (oracleFree_linkPrograms descriptionFirstPostProgram_oracleFree
      descriptionBlockSumProgram_oracleFree)

theorem descriptionSecondStageProgram_oracleFree :
    OracleFree descriptionSecondStageProgram :=
  oracleFree_linkPrograms descriptionRowBaseProgram_oracleFree
    (oracleFree_linkPrograms descriptionSecondPostProgram_oracleFree
      descriptionBlockSumProgram_oracleFree)

theorem descriptionRowLeafProgram_oracleFree :
    OracleFree descriptionRowLeafProgram :=
  oracleFree_linkPrograms
    (descriptionSamePairProgram_oracleFree descriptionTagStageProgram_oracleFree
      (descriptionSamePairProgram_oracleFree
        descriptionFirstStageProgram_oracleFree
        descriptionSecondStageProgram_oracleFree))
    descriptionNodeCodeProgram_oracleFree

theorem descriptionCountLeafProgram_oracleFree :
    OracleFree descriptionCountLeafProgram :=
  oracleFree_linkPrograms descriptionRowBaseProgram_oracleFree
    (oracleFree_linkPrograms descriptionCountPostProgram_oracleFree
      (oracleFree_linkPrograms descriptionBlockSumProgram_oracleFree
        descriptionComplementProgram_oracleFree))

theorem descriptionLayoutProgram_oracleFree :
    OracleFree descriptionLayoutProgram :=
  oracleFree_linkPrograms descriptionLayoutPrepProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _ bitSerialMulProgram_oracleFree)
      descriptionLayoutPostProgram_oracleFree)

/-- **The decoder is oracle free.**  No SAT query, no public length and no
schedule enters the grouping decoder. -/
theorem canonicalDescriptionDecoderProgram_oracleFree :
    OracleFree canonicalDescriptionDecoderProgram :=
  oracleFree_linkPrograms descriptionLayoutProgram_oracleFree
    (oracleFree_linkPrograms duplicateProgram_oracleFree
      (oracleFree_linkPrograms
        (preserveRightProgram_oracleFree _
          (balancedNatSumAfterProgram_oracleFree _
            (indexedPoolListProgram_oracleFree _
              descriptionCountLeafProgram_oracleFree)))
        (oracleFree_linkPrograms descriptionDropCountProgram_oracleFree
          (oracleFree_linkPrograms duplicateProgram_oracleFree
            (oracleFree_linkPrograms
              (preserveRightProgram_oracleFree _
                (indexedPoolListProgram_oracleFree _
                  descriptionRowLeafProgram_oracleFree))
              (oracleFree_linkPrograms swapPairProgram_oracleFree
                (oracleFree_linkPrograms
                  (preserveRightProgram_oracleFree _
                    (oracleFree_linkPrograms
                      descriptionFirstStageProgram_oracleFree
                      descriptionEncodeNatProgram_oracleFree))
                  (oracleFree_linkPrograms swapPairProgram_oracleFree
                    circuitJoinProgram_oracleFree))))))))

end NearCubicWires.CanonicalDescriptionGroupingDecoder
