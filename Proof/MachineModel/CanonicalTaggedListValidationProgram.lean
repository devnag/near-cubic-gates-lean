import Proof.Foundations.CanonicalBinaryProgram

/-!
# Total canonical tagged-list validation

Tagged streams are the sole private linear-list format used between fixed
compiler stages.  This loop checks the exact nonzero cell tag `1`, follows
only the canonical tail, and returns one precisely for a successful public
`decodeTaggedList`.  It is fixed code: no expected length, callback, or
caller-provided recursion limit enters the request.
-/

namespace NearCubicWires.CanonicalTaggedListValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

def taggedListValid (code : ℕ) : Bool :=
  if code = 0 then
    true
  else
    let outer := Nat.unpair code
    if outer.1 = 1 then
      taggedListValid (Nat.unpair outer.2).2
    else
      false
termination_by code
decreasing_by
  have houter :
      outer.2 < code := by
    have hsum : outer.1 + outer.2 ≤ code := by
      simpa only [outer] using Nat.unpair_add_le code
    omega
  exact (Nat.unpair_right_le outer.2).trans_lt houter

@[simp] theorem taggedListValid_encode (values : List ℕ) :
    taggedListValid (encodeTaggedList values) = true := by
  induction values with
  | nil =>
      simp [taggedListValid, encodeTaggedList]
  | cons value values inductionHypothesis =>
      have hnonzero :
          Nat.pair 1 (Nat.pair value (encodeTaggedList values)) ≠ 0 := by
        have := Nat.left_le_pair 1
          (Nat.pair value (encodeTaggedList values))
        omega
      rw [taggedListValid]
      simp [encodeTaggedList, hnonzero, inductionHypothesis]

theorem taggedListValid_eq_true_iff_exists_encode (code : ℕ) :
    taggedListValid code = true ↔
      ∃ values, encodeTaggedList values = code := by
  constructor
  · induction code using Nat.strong_induction_on with
    | h code inductionHypothesis =>
        intro hvalid
        by_cases hzero : code = 0
        · exact ⟨[], hzero.symm⟩
        · rw [taggedListValid, if_neg hzero] at hvalid
          let outer := Nat.unpair code
          by_cases htag : outer.1 = 1
          · rw [if_pos htag] at hvalid
            let payload := Nat.unpair outer.2
            have houterRightLt : outer.2 < code := by
              have hsum : outer.1 + outer.2 ≤ code := by
                simpa only [outer] using Nat.unpair_add_le code
              omega
            have htailLt : payload.2 < code :=
              (Nat.unpair_right_le outer.2).trans_lt houterRightLt
            rcases inductionHypothesis payload.2 htailLt hvalid with
              ⟨values, hvalues⟩
            refine ⟨payload.1 :: values, ?_⟩
            rw [encodeTaggedList, hvalues]
            calc
              Nat.pair 1 (Nat.pair payload.1 payload.2) =
                  Nat.pair outer.1 outer.2 := by
                rw [htag, Nat.pair_unpair]
              _ = code := Nat.pair_unpair code
          · have htagRaw : (Nat.unpair code).1 ≠ 1 := by
              simpa only [outer] using htag
            simp [htagRaw] at hvalid
  · rintro ⟨values, rfl⟩
    exact taggedListValid_encode values

theorem taggedListValid_eq_true_iff_decode (code : ℕ) :
    taggedListValid code = true ↔
      (decodeTaggedList code).isSome := by
  rw [taggedListValid_eq_true_iff_exists_encode]
  constructor
  · rintro ⟨values, rfl⟩
    simp
  · intro hdecode
    cases hdecoded : decodeTaggedList code with
    | none =>
        simp [hdecoded] at hdecode
    | some values =>
        exact ⟨values, encodeTaggedList_of_decode hdecoded⟩

/-! ## Fixed validation loop -/

def taggedListValidationProgram : NPOracleProgram :=
  [ .branchZero 0 7 1
  , .unpairLeft 0 2 2
  , .branchZero 2 8 3
  , .decrement 2 4
  , .branchZero 2 5 8
  , .unpairRight 0 3 6
  , .unpairRight 3 0 0
  , .set 0 1 9
  , .set 0 0 9
  , .halt 0
  ]

@[simp] theorem taggedListValidationProgram_oracleFree :
    OracleFree taggedListValidationProgram := by
  rfl

def taggedListValidationFuel (code : ℕ) : ℕ :=
  if code = 0 then
    3
  else
    let outer := Nat.unpair code
    if outer.1 = 0 then
      5
    else if outer.1 = 1 then
      7 + taggedListValidationFuel (Nat.unpair outer.2).2
    else
      7
termination_by code
decreasing_by
  have houter :
      outer.2 < code := by
    have hsum : outer.1 + outer.2 ≤ code := by
      simpa only [outer] using Nat.unpair_add_le code
    omega
  exact (Nat.unpair_right_le outer.2).trans_lt houter

def taggedListValidationBits (code : ℕ) : ℕ :=
  max 1 (natBitLength code)

private theorem run_taggedListValidationProgram_from
    (root code : ℕ) (state : NPOracleState)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = code)
    (hcodeRoot : code ≤ root) :
    runNPOracleProgram taggedListValidationProgram
        (taggedListValidationBits root)
        (taggedListValidationFuel code) state =
      some (taggedListValid code).toNat := by
  induction code using Nat.strong_induction_on generalizing state with
  | h code inductionHypothesis =>
      let maximumBits := taggedListValidationBits root
      have hone : natBitLength 1 ≤ maximumBits := by
        rw [show natBitLength 1 = 1 by
          norm_num [natBitLength]]
        exact Nat.le_max_left _ _
      have hzero : natBitLength 0 ≤ maximumBits := by
        exact (show natBitLength 0 ≤ 1 by rfl).trans hone
      have hcode :
          natBitLength code ≤ maximumBits := by
        exact
          (natBitLength_mono hcodeRoot).trans
            (Nat.le_max_right _ _)
      by_cases hzeroCode : code = 0
      · rw [taggedListValidationFuel, if_pos hzeroCode]
        rw [show (3 : ℕ) = 2 + 1 by omega]
        rw [run_branchZero_instruction
          (program := taggedListValidationProgram)
          (maximumBits := maximumBits) (fuel := 2)
          (pc := 0) (register := 0) (zeroTarget := 7)
          (nonzeroTarget := 1) (by rfl) hpc]
        rw [if_pos (by simpa [hcurrent] using hzeroCode)]
        rw [show (2 : ℕ) = 1 + 1 by omega]
        rw [run_set_instruction
          (program := taggedListValidationProgram)
          (maximumBits := maximumBits) (fuel := 1)
          (pc := 7) (register := 0) (value := 1) (next := 9)
          (by rfl) (by rfl) hone]
        rw [show taggedListValid code = true by
          simp [taggedListValid, hzeroCode]]
        exact run_halt_instruction
          (program := taggedListValidationProgram)
          (maximumBits := maximumBits) (fuel := 0)
          (pc := 9) (outputRegister := 0) (value := 1)
          (by rfl) (by rfl) (by simp) hone
      · let outer := Nat.unpair code
        have htag :
            natBitLength outer.1 ≤ maximumBits := by
          exact
            (natBitLength_mono (Nat.unpair_left_le code)).trans hcode
        rw [taggedListValidationFuel, if_neg hzeroCode]
        rw [taggedListValid, if_neg hzeroCode]
        by_cases htagZero : outer.1 = 0
        · simp only [outer, htagZero, if_pos]
          rw [show (5 : ℕ) = 4 + 1 by omega]
          rw [run_branchZero_instruction
            (program := taggedListValidationProgram)
            (maximumBits := maximumBits) (fuel := 4)
            (pc := 0) (register := 0) (zeroTarget := 7)
            (nonzeroTarget := 1) (by rfl) hpc]
          rw [if_neg (by simpa [hcurrent] using hzeroCode)]
          rw [show (4 : ℕ) = 3 + 1 by omega]
          rw [run_unpairLeft_instruction
            (program := taggedListValidationProgram)
            (maximumBits := maximumBits) (fuel := 3)
            (pc := 1) (source := 0) (destination := 2) (next := 2)
            (value := outer.1) (by rfl) (by rfl)
            (by simp [hcurrent, outer]) htag]
          rw [show (3 : ℕ) = 2 + 1 by omega]
          rw [run_branchZero_instruction
            (program := taggedListValidationProgram)
            (maximumBits := maximumBits) (fuel := 2)
            (pc := 2) (register := 2) (zeroTarget := 8)
            (nonzeroTarget := 3) (by rfl) (by rfl)]
          rw [if_pos (by simp [htagZero])]
          rw [show (2 : ℕ) = 1 + 1 by omega]
          rw [run_set_instruction
            (program := taggedListValidationProgram)
            (maximumBits := maximumBits) (fuel := 1)
            (pc := 8) (register := 0) (value := 0) (next := 9)
            (by rfl) (by rfl) hzero]
          exact run_halt_instruction
            (program := taggedListValidationProgram)
            (maximumBits := maximumBits) (fuel := 0)
            (pc := 9) (outputRegister := 0) (value := 0)
            (by rfl) (by rfl) (by simp) hzero
        · by_cases htagOne : outer.1 = 1
          · simp only [outer, htagOne, if_pos]
            let payload := Nat.unpair outer.2
            let tail := payload.2
            have houterRight :
                natBitLength outer.2 ≤ maximumBits := by
              exact
                (natBitLength_mono
                  (Nat.unpair_right_le code)).trans hcode
            have htail :
                natBitLength tail ≤ maximumBits := by
              exact
                (natBitLength_mono
                  (Nat.unpair_right_le outer.2)).trans houterRight
            have houterRightLt : outer.2 < code := by
              have hsum : outer.1 + outer.2 ≤ code := by
                simpa only [outer] using Nat.unpair_add_le code
              omega
            have htailLt : tail < code :=
              (Nat.unpair_right_le outer.2).trans_lt houterRightLt
            have htailRoot : tail ≤ root :=
              htailLt.le.trans hcodeRoot
            simp only [one_ne_zero, if_false]
            change
              runNPOracleProgram taggedListValidationProgram
                  (taggedListValidationBits root)
                  (7 + taggedListValidationFuel tail) state =
                some (taggedListValid tail).toNat
            rw [show 7 + taggedListValidationFuel tail =
                (6 + taggedListValidationFuel tail) + 1 by omega]
            rw [run_branchZero_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits)
              (fuel := 6 + taggedListValidationFuel tail)
              (pc := 0) (register := 0) (zeroTarget := 7)
              (nonzeroTarget := 1) (by rfl) hpc]
            rw [if_neg (by simpa [hcurrent] using hzeroCode)]
            rw [show 6 + taggedListValidationFuel tail =
                (5 + taggedListValidationFuel tail) + 1 by omega]
            rw [run_unpairLeft_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits)
              (fuel := 5 + taggedListValidationFuel tail)
              (pc := 1) (source := 0) (destination := 2) (next := 2)
              (value := outer.1) (by rfl) (by rfl)
              (by simp [hcurrent, outer]) htag]
            rw [show 5 + taggedListValidationFuel tail =
                (4 + taggedListValidationFuel tail) + 1 by omega]
            rw [run_branchZero_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits)
              (fuel := 4 + taggedListValidationFuel tail)
              (pc := 2) (register := 2) (zeroTarget := 8)
              (nonzeroTarget := 3) (by rfl) (by rfl)]
            rw [if_neg (by simp [htagOne])]
            have hpred :
                natBitLength 0 ≤ maximumBits := hzero
            rw [show 4 + taggedListValidationFuel tail =
                (3 + taggedListValidationFuel tail) + 1 by omega]
            rw [run_decrement_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits)
              (fuel := 3 + taggedListValidationFuel tail)
              (pc := 3) (register := 2) (next := 4) (value := 0)
              (by rfl) (by rfl) (by simp [htagOne]) hpred]
            rw [show 3 + taggedListValidationFuel tail =
                (2 + taggedListValidationFuel tail) + 1 by omega]
            rw [run_branchZero_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits)
              (fuel := 2 + taggedListValidationFuel tail)
              (pc := 4) (register := 2) (zeroTarget := 5)
              (nonzeroTarget := 8) (by rfl) (by rfl)]
            rw [if_pos (by simp)]
            rw [show 2 + taggedListValidationFuel tail =
                (1 + taggedListValidationFuel tail) + 1 by omega]
            rw [run_unpairRight_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits)
              (fuel := 1 + taggedListValidationFuel tail)
              (pc := 5) (source := 0) (destination := 3) (next := 6)
              (value := outer.2) (by rfl) (by rfl)
              (by simp [hcurrent, outer]) houterRight]
            rw [show 1 + taggedListValidationFuel tail =
                taggedListValidationFuel tail + 1 by omega]
            rw [run_unpairRight_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits)
              (fuel := taggedListValidationFuel tail)
              (pc := 6) (source := 3) (destination := 0) (next := 0)
              (value := tail) (by rfl) (by rfl)
              (by simp [tail, payload]) htail]
            apply inductionHypothesis tail htailLt
            · rfl
            · simp [tail, payload]
            · exact htailRoot
          · have htagZeroRaw : (Nat.unpair code).1 ≠ 0 := by
              simpa only [outer] using htagZero
            have htagOneRaw : (Nat.unpair code).1 ≠ 1 := by
              simpa only [outer] using htagOne
            rw [if_neg htagZeroRaw, if_neg htagOneRaw]
            simp only [htagOneRaw]
            have htagPred :
                natBitLength outer.1.pred ≤ maximumBits :=
              (decrement_bits_le outer.1).trans htag
            change
              runNPOracleProgram taggedListValidationProgram
                  (taggedListValidationBits root) 7 state =
                some 0
            rw [show (7 : ℕ) = 6 + 1 by omega]
            rw [run_branchZero_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits) (fuel := 6)
              (pc := 0) (register := 0) (zeroTarget := 7)
              (nonzeroTarget := 1) (by rfl) hpc]
            rw [if_neg (by simpa [hcurrent] using hzeroCode)]
            rw [show (6 : ℕ) = 5 + 1 by omega]
            rw [run_unpairLeft_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits) (fuel := 5)
              (pc := 1) (source := 0) (destination := 2) (next := 2)
              (value := outer.1) (by rfl) (by rfl)
              (by simp [hcurrent, outer]) htag]
            rw [show (5 : ℕ) = 4 + 1 by omega]
            rw [run_branchZero_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits) (fuel := 4)
              (pc := 2) (register := 2) (zeroTarget := 8)
              (nonzeroTarget := 3) (by rfl) (by rfl)]
            rw [if_neg (by simp [htagZero])]
            rw [show (4 : ℕ) = 3 + 1 by omega]
            rw [run_decrement_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits) (fuel := 3)
              (pc := 3) (register := 2) (next := 4)
              (value := outer.1.pred)
              (by rfl) (by rfl) (by simp) htagPred]
            rw [show (3 : ℕ) = 2 + 1 by omega]
            rw [run_branchZero_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits) (fuel := 2)
              (pc := 4) (register := 2) (zeroTarget := 5)
              (nonzeroTarget := 8) (by rfl) (by rfl)]
            have hpredNonzero : outer.1.pred ≠ 0 :=
              by
                simp only [Nat.pred_eq_sub_one]
                omega
            rw [if_neg (by
              simpa [Nat.pred_eq_sub_one] using hpredNonzero)]
            rw [show (2 : ℕ) = 1 + 1 by omega]
            rw [run_set_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits) (fuel := 1)
              (pc := 8) (register := 0) (value := 0) (next := 9)
              (by rfl) (by rfl) hzero]
            exact run_halt_instruction
              (program := taggedListValidationProgram)
              (maximumBits := maximumBits) (fuel := 0)
              (pc := 9) (outputRegister := 0) (value := 0)
              (by rfl) (by rfl) (by simp) hzero

theorem run_taggedListValidationProgram (inputLength code : ℕ) :
    runNPOracleProgram taggedListValidationProgram
        (taggedListValidationBits code)
        (taggedListValidationFuel code)
        (initialNPOracleState inputLength code) =
      some (taggedListValid code).toNat := by
  exact run_taggedListValidationProgram_from code code
    (initialNPOracleState inputLength code) rfl
    (by simp [initialNPOracleState]) (le_refl _)

theorem taggedListValidation_accepts_iff (code : ℕ) :
    (taggedListValid code).toNat = 1 ↔
      (decodeTaggedList code).isSome := by
  rw [← taggedListValid_eq_true_iff_decode]
  cases taggedListValid code <;> simp

theorem taggedListValidation_rejects_iff (code : ℕ) :
    (taggedListValid code).toNat = 0 ↔
      decodeTaggedList code = none := by
  cases hdecoded : decodeTaggedList code with
  | none =>
      have hvalid : taggedListValid code = false := by
        cases hresult : taggedListValid code with
        | false => rfl
        | true =>
            have :=
              (taggedListValid_eq_true_iff_decode code).mp hresult
            simp [hdecoded] at this
      simp [hvalid]
  | some values =>
      have hvalid : taggedListValid code = true :=
        (taggedListValid_eq_true_iff_decode code).mpr
          (by simp [hdecoded])
      simp [hvalid]

end NearCubicWires.CanonicalTaggedListValidationProgram
