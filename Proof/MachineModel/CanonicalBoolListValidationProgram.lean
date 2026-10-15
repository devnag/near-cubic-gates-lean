import Proof.MachineModel.CanonicalBalancedValidationMapProgram
import Proof.Foundations.CanonicalBinaryProgram

namespace NearCubicWires.CanonicalBoolListValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-! ## One Boolean code -/

def boolCodeValidationOutput (code : ℕ) : ℕ :=
  if code = 0 ∨ code = 1 then 1 else 0

def boolCodeValidationProgram : NPOracleProgram :=
  [ .branchZero 0 4 1
  , .decrement 0 2
  , .branchZero 0 4 3
  , .set 0 0 5
  , .set 0 1 5
  , .halt 0
  ]

@[simp] theorem boolCodeValidationProgram_oracleFree :
    OracleFree boolCodeValidationProgram := by
  rfl

def boolCodeValidationFuel : ℕ := 6

def boolCodeValidationBits (code : ℕ) : ℕ :=
  max (natBitLength code) (natBitLength 1)

theorem run_boolCodeValidationProgram
    (inputLength code : ℕ) :
    runNPOracleProgram boolCodeValidationProgram
        (boolCodeValidationBits code)
        boolCodeValidationFuel
        (initialNPOracleState inputLength code) =
      some (boolCodeValidationOutput code) := by
  by_cases hzero : code = 0
  · subst code
    norm_num [boolCodeValidationProgram, boolCodeValidationFuel,
      boolCodeValidationBits, boolCodeValidationOutput,
      runNPOracleProgram, initialNPOracleState,
      NPOracleState.boundedWrite, NPOracleState.write,
      NPOracleState.jump, natBitLength]
  · by_cases hone : code = 1
    · subst code
      norm_num [boolCodeValidationProgram, boolCodeValidationFuel,
        boolCodeValidationBits, boolCodeValidationOutput,
        runNPOracleProgram, initialNPOracleState,
        NPOracleState.boundedWrite, NPOracleState.write,
        NPOracleState.jump, natBitLength]
    · have hpred : code - 1 ≠ 0 := by omega
      have hpredBits :
          natBitLength (code - 1) ≤ boolCodeValidationBits code := by
        exact
          (natBitLength_mono (Nat.sub_le code 1)).trans
            (Nat.le_max_left _ _)
      have hzeroBits :
          natBitLength 0 ≤ boolCodeValidationBits code := by
        exact
          (natBitLength_mono (Nat.zero_le code)).trans
            (Nat.le_max_left _ _)
      rw [show boolCodeValidationFuel = 5 + 1 by rfl]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show
        (initialNPOracleState inputLength code).registers 0 = code by
          simp [initialNPOracleState]]
      rw [if_neg hzero]
      rw [show 5 = 4 + 1 by omega]
      rw [run_decrement_instruction (value := code - 1)
        (by rfl) rfl
        (by simp [initialNPOracleState, NPOracleState.jump])
        hpredBits]
      rw [show 4 = 3 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show
        ((((initialNPOracleState inputLength code).jump 1).write 0
            (code - 1)).jump 2).registers 0 = code - 1 by
          simp [NPOracleState.write, NPOracleState.jump]]
      rw [if_neg hpred]
      rw [show 3 = 2 + 1 by omega]
      rw [run_set_instruction (value := 0)
        (by rfl) rfl hzeroBits]
      rw [show boolCodeValidationOutput code = 0 by
        simp [boolCodeValidationOutput, hzero, hone]]
      apply run_halt_instruction (fuel := 1) (pc := 5)
        (program := boolCodeValidationProgram)
        (outputRegister := 0) (value := 0) (by rfl)
      · rfl
      · simp [NPOracleState.write, NPOracleState.jump]
      · exact hzeroBits

theorem boolCodeValidationOutput_ne_zero_iff
    (code : ℕ) :
    boolCodeValidationOutput code ≠ 0 ↔
      (decodeBoolCode code).isSome := by
  by_cases hzero : code = 0
  · simp [hzero, boolCodeValidationOutput, decodeBoolCode]
  · by_cases hone : code = 1
    · simp [hone, boolCodeValidationOutput, decodeBoolCode]
    · simp [hzero, hone, boolCodeValidationOutput, decodeBoolCode]

/-! ## Shared balanced map instance -/

def boolCodeRequestBits (request : ℕ) : ℕ :=
  boolCodeValidationBits (Nat.unpair request).2

def boolCodeRequestFuel (_request : ℕ) : ℕ :=
  boolCodeValidationFuel

def boolCodeRequestOutput (request : ℕ) : ℕ :=
  boolCodeValidationOutput (Nat.unpair request).2

def canonicalBoolListValidationProgram : NPOracleProgram :=
  balancedValidationAllProgram boolCodeValidationProgram

@[simp] theorem canonicalBoolListValidationProgram_oracleFree :
    OracleFree canonicalBoolListValidationProgram := by
  exact balancedValidationAllProgram_oracleFree boolCodeValidationProgram
    boolCodeValidationProgram_oracleFree

def canonicalBoolListValidationOutput
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationAllOutput inputLength raw boolCodeRequestOutput

def canonicalBoolListValidationFuel
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationAllFuel boolCodeValidationProgram
    boolCodeRequestFuel inputLength raw boolCodeRequestOutput

def canonicalBoolListValidationBits
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationAllBits boolCodeRequestBits
    boolCodeRequestOutput inputLength raw

theorem run_canonicalBoolListValidationProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram canonicalBoolListValidationProgram
        (canonicalBoolListValidationBits inputLength raw)
        (canonicalBoolListValidationFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (canonicalBoolListValidationOutput inputLength raw) := by
  apply run_balancedValidationAllProgram
  intro request _
  exact
    run_boolCodeValidationProgram
      (Nat.unpair request).1 (Nat.unpair request).2

/-! ## Exact codec semantics -/

private theorem decodeBoolCodes_isSome_iff
    (codes : List ℕ) :
    (decodeBoolCodes codes).isSome ↔
      ∀ code, code ∈ codes → (decodeBoolCode code).isSome := by
  induction codes with
  | nil =>
      simp [decodeBoolCodes]
  | cons code codes inductionHypothesis =>
      cases hcode : decodeBoolCode code with
      | none =>
          simp [decodeBoolCodes, hcode]
      | some value =>
          cases hcodes : decodeBoolCodes codes with
          | none =>
              have hnotAll :
                  ¬∀ candidate, candidate ∈ codes →
                    (decodeBoolCode candidate).isSome := by
                simpa [hcodes] using
                  (not_congr inductionHypothesis).mp (by simp [hcodes])
              simp [decodeBoolCodes, hcode, hcodes, hnotAll]
          | some values =>
              have hall :
                  ∀ candidate, candidate ∈ codes →
                    (decodeBoolCode candidate).isSome :=
                inductionHypothesis.mp (by simp [hcodes])
              constructor
              · intro _ candidate hcandidate
                rcases List.mem_cons.mp hcandidate with rfl | htail
                · simp [hcode]
                · exact hall candidate htail
              · intro _
                simp [decodeBoolCodes, hcode, hcodes]

private theorem boolCode_of_decode
    {code : ℕ} {value : Bool}
    (hdecode : decodeBoolCode code = some value) :
    boolCode value = code := by
  by_cases hzero : code = 0
  · subst code
    cases value <;> simp [decodeBoolCode, boolCode] at hdecode ⊢
  · by_cases hone : code = 1
    · subst code
      cases value <;> simp [decodeBoolCode, boolCode] at hdecode ⊢
    · simp [decodeBoolCode, hzero, hone] at hdecode

private theorem encodeBoolCodes_of_decode
    {codes : List ℕ} {values : List Bool}
    (hdecode : decodeBoolCodes codes = some values) :
    codes = values.map boolCode := by
  induction codes generalizing values with
  | nil =>
      simp [decodeBoolCodes] at hdecode
      subst values
      rfl
  | cons code codes inductionHypothesis =>
      cases hcode : decodeBoolCode code with
      | none =>
          simp [decodeBoolCodes, hcode] at hdecode
      | some value =>
          cases hcodes : decodeBoolCodes codes with
          | none =>
              simp [decodeBoolCodes, hcode, hcodes] at hdecode
          | some tail =>
              have hvalues : value :: tail = values := by
                simpa [decodeBoolCodes, hcode, hcodes] using hdecode
              subst values
              congr
              · exact (boolCode_of_decode hcode).symm
              · exact inductionHypothesis hcodes

theorem decodeBoolList_isSome_iff
    (raw : ℕ) :
    (decodeBoolList raw).isSome ↔
      ∃ codes,
        decodeBalancedList raw = some codes ∧
          ∀ code, code ∈ codes → (decodeBoolCode code).isSome := by
  constructor
  · intro hlist
    unfold decodeBoolList at hlist
    cases hcandidate : decodeBoolListCandidate raw with
    | none =>
        simp [hcandidate] at hlist
    | some values =>
        unfold decodeBoolListCandidate at hcandidate
        cases hbalanced : decodeBalancedList raw with
        | none =>
            simp [hbalanced] at hcandidate
        | some codes =>
            have hcodes :
                decodeBoolCodes codes = some values := by
              simpa [hbalanced] using hcandidate
            refine ⟨codes, rfl, ?_⟩
            exact (decodeBoolCodes_isSome_iff codes).1 (by
              simp [hcodes])
  · rintro ⟨codes, hbalanced, hall⟩
    have hcodesSome :
        (decodeBoolCodes codes).isSome :=
      (decodeBoolCodes_isSome_iff codes).2 hall
    cases hcodes : decodeBoolCodes codes with
    | none =>
        simp [hcodes] at hcodesSome
    | some values =>
        have hcodeList : codes = values.map boolCode :=
          encodeBoolCodes_of_decode hcodes
        have hcanonical : encodeBoolList values = raw := by
          rw [encodeBoolList, ← hcodeList]
          exact encodeBalancedList_of_decode hbalanced
        unfold decodeBoolList decodeBoolListCandidate
        simp [hbalanced, hcodes, hcanonical]

theorem canonicalBoolListValidationOutput_ne_zero_iff_decodeBoolList
    (inputLength raw : ℕ) :
    canonicalBoolListValidationOutput inputLength raw ≠ 0 ↔
      (decodeBoolList raw).isSome := by
  unfold canonicalBoolListValidationOutput
  rw [balancedValidationAllOutput_ne_zero_iff,
    decodeBoolList_isSome_iff]
  constructor
  · rintro ⟨codes, hdecode, hall⟩
    refine ⟨codes, hdecode, ?_⟩
    intro code hcode
    have hvalid := hall code hcode
    have hraw : boolCodeValidationOutput code ≠ 0 := by
      simpa [boolCodeRequestOutput, nativeInputRequest] using hvalid
    exact (boolCodeValidationOutput_ne_zero_iff code).1 hraw
  · rintro ⟨codes, hdecode, hall⟩
    refine ⟨codes, hdecode, ?_⟩
    intro code hcode
    have hvalid :=
      (boolCodeValidationOutput_ne_zero_iff code).2 (hall code hcode)
    change
      boolCodeRequestOutput (nativeInputRequest inputLength code) ≠ 0
    simpa [boolCodeRequestOutput, nativeInputRequest] using hvalid

end NearCubicWires.CanonicalBoolListValidationProgram
