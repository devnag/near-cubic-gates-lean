import Proof.MachineModel.CanonicalBalancedValidationMapProgram
import Proof.Foundations.CanonicalBinaryProgram
import Proof.MachineModel.CanonicalRationalValidationProgram
import Proof.Circuits.CanonicalWitnessCodec

/-!
# Canonical integer-list validation

Integer atoms reuse the canonical-rational validator at denominator one.  This
keeps signed canonicality on the same executable path used by legal
coefficients; no second signed-integer parser is introduced.
-/

namespace NearCubicWires.CanonicalIntListValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

def unitRationalCode (integerCode : ℕ) : ℕ :=
  encodeTaggedList [integerCode, encodeNat 1]

theorem unitRationalCode_eq_encode
    {integerCode : ℕ} {value : ℤ}
    (hdecode : decodeInt integerCode = some value) :
    unitRationalCode integerCode =
      encodeCanonicalRational (value : ℚ) := by
  have hcode : encodeInt value = integerCode :=
    encodeInt_of_decode hdecode
  simp [unitRationalCode, encodeCanonicalRational, hcode]

theorem decodeCanonicalRational_unitRationalCode_isSome_iff
    (integerCode : ℕ) :
    (decodeCanonicalRational (unitRationalCode integerCode)).isSome ↔
      (decodeInt integerCode).isSome := by
  constructor
  · intro hrational
    cases hdecode :
        decodeCanonicalRational (unitRationalCode integerCode) with
    | none =>
        simp [hdecode] at hrational
    | some coefficient =>
        have hcanonical :
            encodeCanonicalRational coefficient =
              unitRationalCode integerCode :=
          encodeCanonicalRational_of_decode hdecode
        have hfields := congrArg decodeTaggedList hcanonical
        have hinteger :
            integerCode = encodeInt coefficient.num := by
          symm
          simpa [encodeCanonicalRational, unitRationalCode] using
            congrArg (fun fields => (fields.getD []).headD 0) hfields
        rw [hinteger, decodeInt_encode]
        rfl
  · intro hinteger
    cases hdecode : decodeInt integerCode with
    | none =>
        simp [hdecode] at hinteger
    | some value =>
        rw [unitRationalCode_eq_encode hdecode,
          decodeCanonicalRational_encode]
        rfl

/-! ## Fixed denominator-one lowering -/

def unitRationalLoweringProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .set 3 (encodeNat 1) 2
  , .pair 3 2 4 3
  , .set 5 1 4
  , .pair 5 4 6 5
  , .pair 0 6 7 6
  , .pair 5 7 0 7
  , .halt 0
  ]

@[simp] theorem unitRationalLoweringProgram_oracleFree :
    OracleFree unitRationalLoweringProgram := by
  rfl

def unitRationalLoweringFuel : ℕ := 8

private def unitRationalLoweringValues (integerCode : ℕ) : List ℕ :=
  let denominator := encodeNat 1
  let denominatorPayload := Nat.pair denominator 0
  let denominatorCell := Nat.pair 1 denominatorPayload
  let numeratorPayload := Nat.pair integerCode denominatorCell
  [ integerCode
  , 0
  , 1
  , denominator
  , denominatorPayload
  , denominatorCell
  , numeratorPayload
  , unitRationalCode integerCode
  ]

def unitRationalLoweringBits (integerCode : ℕ) : ℕ :=
  (unitRationalLoweringValues integerCode).map natBitLength
    |>.foldr max 1

private theorem bitLength_le_foldr_max_of_mem
    {values : List ℕ} {value : ℕ} (hvalue : value ∈ values) :
    natBitLength value ≤
      (values.map natBitLength).foldr max 1 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hvalue
      simp only [List.map_cons, List.foldr_cons]
      rcases hvalue with rfl | htail
      · exact le_max_left _ _
      · exact (inductionHypothesis htail).trans (le_max_right _ _)

theorem run_unitRationalLoweringProgram
    (inputLength integerCode : ℕ) :
    runNPOracleProgram unitRationalLoweringProgram
        (unitRationalLoweringBits integerCode)
        unitRationalLoweringFuel
        (initialNPOracleState inputLength integerCode) =
      some (unitRationalCode integerCode) := by
  let denominator := encodeNat 1
  let denominatorPayload := Nat.pair denominator 0
  let denominatorCell := Nat.pair 1 denominatorPayload
  let numeratorPayload := Nat.pair integerCode denominatorCell
  let maximumBits := unitRationalLoweringBits integerCode
  have hbits :
      ∀ value ∈ unitRationalLoweringValues integerCode,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact bitLength_le_foldr_max_of_mem hvalue
  have hzero := hbits 0 (by
    simp [unitRationalLoweringValues])
  have hone := hbits 1 (by
    simp [unitRationalLoweringValues])
  have hdenominator := hbits denominator (by
    simp [unitRationalLoweringValues, denominator])
  have hdenominatorPayload := hbits denominatorPayload (by
    simp [unitRationalLoweringValues, denominatorPayload, denominator])
  have hdenominatorCell := hbits denominatorCell (by
    simp [unitRationalLoweringValues, denominatorCell,
      denominatorPayload, denominator])
  have hnumeratorPayload := hbits numeratorPayload (by
    simp [unitRationalLoweringValues, numeratorPayload, denominatorCell,
      denominatorPayload, denominator])
  have houtput := hbits (unitRationalCode integerCode) (by
    simp [unitRationalLoweringValues])
  rw [show unitRationalLoweringFuel = 7 + 1 by rfl]
  rw [run_set_instruction
    (program := unitRationalLoweringProgram)
    (maximumBits := maximumBits) (fuel := 7)
    (pc := 0) (register := 2) (value := 0) (next := 1)
    (by rfl) rfl hzero]
  rw [show 7 = 6 + 1 by omega]
  rw [run_set_instruction
    (program := unitRationalLoweringProgram)
    (maximumBits := maximumBits) (fuel := 6)
    (pc := 1) (register := 3) (value := denominator) (next := 2)
    (by rfl) rfl hdenominator]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction
    (program := unitRationalLoweringProgram)
    (maximumBits := maximumBits) (fuel := 5)
    (pc := 2) (left := 3) (right := 2) (destination := 4) (next := 3)
    (value := denominatorPayload) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, denominatorPayload]) hdenominatorPayload]
  rw [show 5 = 4 + 1 by omega]
  rw [run_set_instruction
    (program := unitRationalLoweringProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 3) (register := 5) (value := 1) (next := 4)
    (by rfl) rfl hone]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (program := unitRationalLoweringProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 4) (left := 5) (right := 4) (destination := 6) (next := 5)
    (value := denominatorCell) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      denominatorCell]) hdenominatorCell]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (program := unitRationalLoweringProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 5) (left := 0) (right := 6) (destination := 7) (next := 6)
    (value := numeratorPayload) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, numeratorPayload]) hnumeratorPayload]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := unitRationalLoweringProgram)
    (maximumBits := maximumBits) (fuel := 1)
    (pc := 6) (left := 5) (right := 7) (destination := 0) (next := 7)
    (value := unitRationalCode integerCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      unitRationalCode, encodeTaggedList, numeratorPayload,
      denominatorCell, denominatorPayload, denominator]) houtput]
  exact run_halt_instruction
    (program := unitRationalLoweringProgram)
    (maximumBits := maximumBits) (fuel := 0)
    (pc := 7) (outputRegister := 0)
    (value := unitRationalCode integerCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## Direct rational-validator composition -/

/-- Validate one canonical signed integer by lowering it to the unique
denominator-one rational representation and invoking the public rational
validator.  This is the sole integer-validation path. -/
def unitRationalValidationProgram : NPOracleProgram :=
  linkPrograms unitRationalLoweringProgram rationalValidationProgram

@[simp] theorem unitRationalValidationProgram_oracleFree :
    OracleFree unitRationalValidationProgram := by
  exact oracleFree_linkPrograms unitRationalLoweringProgram_oracleFree
    rationalValidationProgram_oracleFree

def unitRationalValidationOutput (integerCode : ℕ) : ℕ :=
  rationalValidationOutput (unitRationalCode integerCode)

def unitRationalValidationFuel
    (inputLength integerCode : ℕ) : ℕ :=
  linkFuel rationalValidationProgram unitRationalLoweringFuel
    (rationalValidationFuel inputLength
      (unitRationalCode integerCode))

def unitRationalValidationBits
    (inputLength integerCode : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (unitRationalLoweringBits integerCode)
      (rationalValidationBits inputLength
        (unitRationalCode integerCode))

theorem run_unitRationalValidationProgram
    (inputLength integerCode : ℕ) :
    runNPOracleProgram unitRationalValidationProgram
        (unitRationalValidationBits inputLength integerCode)
        (unitRationalValidationFuel inputLength integerCode)
        (initialNPOracleState inputLength integerCode) =
      some (unitRationalValidationOutput integerCode) := by
  let maximumBits :=
    unitRationalValidationBits inputLength integerCode
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, unitRationalValidationBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, unitRationalValidationBits]
  have hloweringBits :
      unitRationalLoweringBits integerCode ≤ maximumBits := by
    simp [maximumBits, unitRationalValidationBits]
  have hrationalBits :
      rationalValidationBits inputLength
          (unitRationalCode integerCode) ≤ maximumBits := by
    simp [maximumBits, unitRationalValidationBits]
  have hlowering :=
    run_bits_mono
      (run_unitRationalLoweringProgram inputLength integerCode)
      hloweringBits
  have hrational :=
    run_bits_mono
      (run_rationalValidationProgram inputLength
        (unitRationalCode integerCode))
      hrationalBits
  have hrun :=
    run_linkPrograms hpositive hlength hlowering hrational
  simpa [unitRationalValidationProgram,
    unitRationalValidationFuel, unitRationalValidationOutput] using hrun

/-! ## One balanced validation path -/

def unitRationalRequestBits (request : ℕ) : ℕ :=
  unitRationalValidationBits
    (Nat.unpair request).1 (Nat.unpair request).2

def unitRationalRequestFuel (request : ℕ) : ℕ :=
  unitRationalValidationFuel
    (Nat.unpair request).1 (Nat.unpair request).2

def unitRationalRequestOutput (request : ℕ) : ℕ :=
  unitRationalValidationOutput (Nat.unpair request).2

def canonicalIntListValidationProgram : NPOracleProgram :=
  balancedValidationAllProgram unitRationalValidationProgram

@[simp] theorem canonicalIntListValidationProgram_oracleFree :
    OracleFree canonicalIntListValidationProgram := by
  exact balancedValidationAllProgram_oracleFree
    unitRationalValidationProgram
    unitRationalValidationProgram_oracleFree

def canonicalIntListValidationOutput
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationAllOutput inputLength raw
    unitRationalRequestOutput

def canonicalIntListValidationFuel
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationAllFuel unitRationalValidationProgram
    unitRationalRequestFuel inputLength raw unitRationalRequestOutput

def canonicalIntListValidationBits
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationAllBits unitRationalRequestBits
    unitRationalRequestOutput inputLength raw

theorem run_canonicalIntListValidationProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram canonicalIntListValidationProgram
        (canonicalIntListValidationBits inputLength raw)
        (canonicalIntListValidationFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (canonicalIntListValidationOutput inputLength raw) := by
  apply run_balancedValidationAllProgram
  intro request _
  exact
    run_unitRationalValidationProgram
      (Nat.unpair request).1 (Nat.unpair request).2

/-! ## Exact list semantics -/

private theorem decodeIntCodes_isSome_iff
    (codes : List ℕ) :
    (decodeIntCodes codes).isSome ↔
      ∀ code, code ∈ codes → (decodeInt code).isSome := by
  induction codes with
  | nil =>
      simp [decodeIntCodes]
  | cons code codes inductionHypothesis =>
      cases hcode : decodeInt code with
      | none =>
          simp [decodeIntCodes, hcode]
      | some value =>
          cases hcodes : decodeIntCodes codes with
          | none =>
              have hnotAll :
                  ¬∀ candidate, candidate ∈ codes →
                    (decodeInt candidate).isSome := by
                simpa [hcodes] using
                  (not_congr inductionHypothesis).mp (by simp [hcodes])
              simp [decodeIntCodes, hcode, hcodes, hnotAll]
          | some values =>
              have hall :
                  ∀ candidate, candidate ∈ codes →
                    (decodeInt candidate).isSome :=
                inductionHypothesis.mp (by simp [hcodes])
              constructor
              · intro _ candidate hcandidate
                rcases List.mem_cons.mp hcandidate with rfl | htail
                · simp [hcode]
                · exact hall candidate htail
              · intro _
                simp [decodeIntCodes, hcode, hcodes]

private theorem encodeIntCodes_of_decode
    {codes : List ℕ} {values : List ℤ}
    (hdecode : decodeIntCodes codes = some values) :
    codes = values.map encodeInt := by
  induction codes generalizing values with
  | nil =>
      simp [decodeIntCodes] at hdecode
      subst values
      rfl
  | cons code codes inductionHypothesis =>
      cases hcode : decodeInt code with
      | none =>
          simp [decodeIntCodes, hcode] at hdecode
      | some value =>
          cases hcodes : decodeIntCodes codes with
          | none =>
              simp [decodeIntCodes, hcode, hcodes] at hdecode
          | some tail =>
              have hvalues : value :: tail = values := by
                simpa [decodeIntCodes, hcode, hcodes] using hdecode
              subst values
              congr
              · exact (encodeInt_of_decode hcode).symm
              · exact inductionHypothesis hcodes

theorem decodeIntList_isSome_iff
    (raw : ℕ) :
    (decodeIntList raw).isSome ↔
      ∃ codes,
        decodeBalancedList raw = some codes ∧
          ∀ code, code ∈ codes → (decodeInt code).isSome := by
  constructor
  · intro hlist
    unfold decodeIntList at hlist
    cases hcandidate : decodeIntListCandidate raw with
    | none =>
        simp [hcandidate] at hlist
    | some values =>
        have hcanonical : encodeIntList values = raw := by
          simpa [hcandidate] using hlist
        unfold decodeIntListCandidate at hcandidate
        cases hbalanced : decodeBalancedList raw with
        | none =>
            simp [hbalanced] at hcandidate
        | some codes =>
            have hcodes :
                decodeIntCodes codes = some values := by
              simpa [hbalanced] using hcandidate
            refine ⟨codes, rfl, ?_⟩
            exact (decodeIntCodes_isSome_iff codes).1 (by
              simp [hcodes])
  · rintro ⟨codes, hbalanced, hall⟩
    have hcodesSome :
        (decodeIntCodes codes).isSome :=
      (decodeIntCodes_isSome_iff codes).2 hall
    cases hcodes : decodeIntCodes codes with
    | none =>
        simp [hcodes] at hcodesSome
    | some values =>
        have hcodeList : codes = values.map encodeInt :=
          encodeIntCodes_of_decode hcodes
        have hcanonical : encodeIntList values = raw := by
          rw [encodeIntList, ← hcodeList]
          exact encodeBalancedList_of_decode hbalanced
        unfold decodeIntList decodeIntListCandidate
        simp [hbalanced, hcodes, hcanonical]

theorem balancedValidationAllOutput_unitRational_iff_decodeIntList
    (inputLength raw : ℕ) (output : ℕ → ℕ)
    (houtput :
      ∀ integerCode,
        output (nativeInputRequest inputLength integerCode) ≠ 0 ↔
          (decodeCanonicalRational
            (unitRationalCode integerCode)).isSome) :
    balancedValidationAllOutput inputLength raw output ≠ 0 ↔
      (decodeIntList raw).isSome := by
  rw [balancedValidationAllOutput_ne_zero_iff,
    decodeIntList_isSome_iff]
  constructor
  · rintro ⟨codes, hdecode, hall⟩
    refine ⟨codes, hdecode, ?_⟩
    intro code hcode
    have hrational := (houtput code).1 (hall code hcode)
    exact
      (decodeCanonicalRational_unitRationalCode_isSome_iff code).1
        hrational
  · rintro ⟨codes, hdecode, hall⟩
    refine ⟨codes, hdecode, ?_⟩
    intro code hcode
    apply (houtput code).2
    exact
      (decodeCanonicalRational_unitRationalCode_isSome_iff code).2
        (hall code hcode)

theorem unitRationalValidationOutput_ne_zero_iff
    (integerCode : ℕ) :
    unitRationalValidationOutput integerCode ≠ 0 ↔
      (decodeInt integerCode).isSome := by
  rw [unitRationalValidationOutput,
    rationalValidationOutput_ne_zero_iff_isSome,
    decodeCanonicalRational_unitRationalCode_isSome_iff]

theorem canonicalIntListValidationOutput_ne_zero_iff_decodeIntList
    (inputLength raw : ℕ) :
    canonicalIntListValidationOutput inputLength raw ≠ 0 ↔
      (decodeIntList raw).isSome := by
  unfold canonicalIntListValidationOutput
  apply balancedValidationAllOutput_unitRational_iff_decodeIntList
  intro integerCode
  simpa [unitRationalRequestOutput, nativeInputRequest,
    unitRationalValidationOutput] using
      (rationalValidationOutput_ne_zero_iff_isSome
        (unitRationalCode integerCode))

end NearCubicWires.CanonicalIntListValidationProgram
