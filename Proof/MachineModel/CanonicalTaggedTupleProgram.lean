import Proof.MachineModel.CanonicalTaggedListValidationProgram
import Proof.Circuits.RegisterBounds

/-!
# Fixed-arity canonical tagged tuples

All fixed records in the recovery witness use the same tagged-list codec.  This
module deconstructs exactly `arity` canonical cells in one pass and returns the
fields in a private reverse-pair accumulator.  The arity is an immediate in
the program text, never caller data; malformed tags, short/long lists, and
nonzero terminators all reach the single zero result.
-/

namespace NearCubicWires.CanonicalTaggedTupleProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds

/-- Private reverse-pair representation used only between fixed compiler
stages.  It is not an accepted public witness encoding. -/
def reversePairFields : List ℕ → ℕ :=
  List.foldl Nat.pair 0

/-- Total semantic view of the fixed tuple loop. -/
def decodeTaggedTupleAux :
    ℕ → ℕ → ℕ → Option ℕ
  | 0, cursor, accumulator =>
      if cursor = 0 then some accumulator else none
  | remaining + 1, cursor, accumulator =>
      if cursor = 0 then
        none
      else
        let outer := Nat.unpair cursor
        if outer.1 = 1 then
          let payload := Nat.unpair outer.2
          decodeTaggedTupleAux remaining payload.2
            (Nat.pair accumulator payload.1)
        else
          none

def decodeTaggedTuple (arity raw : ℕ) : Option ℕ :=
  decodeTaggedTupleAux arity raw 0

def taggedTupleOutput (arity raw : ℕ) : ℕ :=
  match decodeTaggedTuple arity raw with
  | some fields => Nat.pair 1 fields
  | none => 0

@[simp] theorem decodeTaggedTupleAux_encode
    (values : List ℕ) (accumulator : ℕ) :
    decodeTaggedTupleAux values.length (encodeTaggedList values)
        accumulator =
      some (values.foldl Nat.pair accumulator) := by
  induction values generalizing accumulator with
  | nil =>
      simp [decodeTaggedTupleAux, encodeTaggedList]
  | cons value values inductionHypothesis =>
      have hnonzero :
          Nat.pair 1 (Nat.pair value (encodeTaggedList values)) ≠ 0 := by
        have hleft :=
          Nat.left_le_pair 1
            (Nat.pair value (encodeTaggedList values))
        omega
      simp [encodeTaggedList, decodeTaggedTupleAux, hnonzero,
        inductionHypothesis]

@[simp] theorem decodeTaggedTuple_encode (values : List ℕ) :
    decodeTaggedTuple values.length (encodeTaggedList values) =
      some (reversePairFields values) := by
  exact decodeTaggedTupleAux_encode values 0

private theorem decodeTaggedTupleAux_eq_some_iff
    (arity raw accumulator fields : ℕ) :
    decodeTaggedTupleAux arity raw accumulator = some fields ↔
      ∃ values,
        values.length = arity ∧
        encodeTaggedList values = raw ∧
        values.foldl Nat.pair accumulator = fields := by
  constructor
  · induction arity generalizing raw accumulator fields with
    | zero =>
        intro hdecode
        simp only [decodeTaggedTupleAux] at hdecode
        split at hdecode
        · rename_i hzero
          simp only [Option.some.injEq] at hdecode
          subst fields
          exact ⟨[], rfl, hzero.symm, rfl⟩
        · simp at hdecode
    | succ arity inductionHypothesis =>
        intro hdecode
        simp only [decodeTaggedTupleAux] at hdecode
        split at hdecode
        · simp at hdecode
        · rename_i hcursor
          split at hdecode
          · rename_i htag
            let outer := Nat.unpair raw
            let payload := Nat.unpair outer.2
            obtain ⟨values, hlength, hcode, hfields⟩ :=
              (inductionHypothesis
                (raw := payload.2)
                (accumulator := Nat.pair accumulator payload.1)
                (fields := fields))
                hdecode
            refine
              ⟨payload.1 :: values, by simp [hlength], ?_, ?_⟩
            · rw [encodeTaggedList, hcode]
              calc
                Nat.pair 1
                    (Nat.pair payload.1 payload.2) =
                    Nat.pair outer.1 outer.2 := by
                  rw [htag, Nat.pair_unpair]
                _ = raw := Nat.pair_unpair raw
            · simpa using hfields
          · simp at hdecode
  · rintro ⟨values, hlength, hcode, hfields⟩
    subst arity
    subst raw
    rw [decodeTaggedTupleAux_encode, hfields]

theorem decodeTaggedTuple_eq_some_iff
    (arity raw fields : ℕ) :
    decodeTaggedTuple arity raw = some fields ↔
      ∃ values,
        values.length = arity ∧
        encodeTaggedList values = raw ∧
        reversePairFields values = fields := by
  simpa [decodeTaggedTuple, reversePairFields] using
    decodeTaggedTupleAux_eq_some_iff arity raw 0 fields

theorem taggedTupleOutput_ne_zero_iff
    (arity raw : ℕ) :
    taggedTupleOutput arity raw ≠ 0 ↔
      ∃ values,
        values.length = arity ∧ encodeTaggedList values = raw := by
  constructor
  · intro hnonzero
    cases hdecode : decodeTaggedTuple arity raw with
    | none =>
        simp [taggedTupleOutput, hdecode] at hnonzero
    | some fields =>
        obtain ⟨values, hlength, hcode, _⟩ :=
          (decodeTaggedTuple_eq_some_iff arity raw fields).mp hdecode
        exact ⟨values, hlength, hcode⟩
  · rintro ⟨values, hlength, hcode⟩
    have hdecode :
        decodeTaggedTuple arity raw =
          some (reversePairFields values) := by
      subst arity
      subst raw
      exact decodeTaggedTuple_encode values
    simp only [taggedTupleOutput, hdecode]
    have hpositive :
        0 < Nat.pair 1 (reversePairFields values) :=
      (show 0 < 1 by omega).trans_le
        (Nat.left_le_pair 1 (reversePairFields values))
    exact hpositive.ne'

theorem taggedTupleOutput_ne_zero_iff_decodeTaggedList
    (arity raw : ℕ) :
    taggedTupleOutput arity raw ≠ 0 ↔
      ∃ values,
        decodeTaggedList raw = some values ∧ values.length = arity := by
  rw [taggedTupleOutput_ne_zero_iff]
  constructor
  · rintro ⟨values, hlength, rfl⟩
    exact ⟨values, decodeTaggedList_encode values, hlength⟩
  · rintro ⟨values, hdecode, hlength⟩
    exact ⟨values, hlength, encodeTaggedList_of_decode hdecode⟩

/-! ## Fixed tuple deconstructor -/

/-- Register ABI:

* `r0`: current tagged cursor, then output;
* `r2`: cells remaining;
* `r3`: reverse-pair accumulator;
* `r4`-`r6`: tag, payload, and head scratch.
-/
def taggedTupleProgram (arity : ℕ) : NPOracleProgram :=
  [ .set 2 arity 1
  , .set 3 0 2
  , .branchZero 2 13 3
  , .branchZero 0 15 4
  , .unpairLeft 0 4 5
  , .branchZero 4 15 6
  , .decrement 4 7
  , .branchZero 4 8 15
  , .unpairRight 0 5 9
  , .unpairLeft 5 6 10
  , .pair 3 6 3 11
  , .unpairRight 5 0 12
  , .decrement 2 2
  , .branchZero 0 14 15
  , .set 4 1 16
  , .set 0 0 17
  , .pair 4 3 0 17
  , .halt 0
  ]

@[simp] theorem taggedTupleProgram_oracleFree (arity : ℕ) :
    OracleFree (taggedTupleProgram arity) := by
  rfl

/-- Exact worst-case fuel.  Rejection may halt early; the interpreter does not
charge unreachable suffix fuel after a halt. -/
def taggedTupleFuel (arity : ℕ) : ℕ :=
  11 * arity + 7

/-- A uniform interpreter bound.  `pairIter` is deliberately charged from the
actual raw word and fixed arity, so no caller supplies a register cap. -/
def taggedTupleBits (inputLength arity raw : ℕ) : ℕ :=
  natBitLength <|
    pairIter (arity + 1)
      (max 1 (max inputLength (max arity raw)))

private def taggedTupleLoopFuel (remaining : ℕ) : ℕ :=
  11 * remaining + 5

private theorem pairIter_mono_depth
    {smaller larger value : ℕ} (hle : smaller ≤ larger) :
    pairIter smaller value ≤ pairIter larger value := by
  calc
    pairIter smaller value ≤
        pairIter (larger - smaller) (pairIter smaller value) :=
      value_le_pairIter _ _
    _ = pairIter (smaller + (larger - smaller)) value := by
      rw [pairIter_add]
    _ = pairIter larger value := by
      congr
      omega

private theorem taggedTuple_value_bits
    {total base value maximumBits : ℕ}
    (hvalue : value ≤ pairIter (total + 1) base)
    (hbits :
      natBitLength (pairIter (total + 1) base) ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

private theorem run_taggedTupleLoop
    (fixedArity total consumed remaining cursor accumulator
      maximumBits base : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 2)
    (hremaining : state.registers 2 = remaining)
    (hcursor : state.registers 0 = cursor)
    (haccumulator : state.registers 3 = accumulator)
    (hpartition : consumed + remaining = total)
    (hbase : 1 ≤ base)
    (htotalBound : total ≤ base)
    (hcursorBound : cursor ≤ base)
    (haccumulatorBound :
      accumulator ≤ pairIter consumed base)
    (hbits :
      natBitLength
          (pairIter (total + 1) base) ≤
        maximumBits) :
    runNPOracleProgram (taggedTupleProgram fixedArity) maximumBits
        (taggedTupleLoopFuel remaining) state =
      some
        (match decodeTaggedTupleAux remaining cursor accumulator with
        | some fields => Nat.pair 1 fields
        | none => 0) := by
  have hsmallBits :
      ∀ value, value ≤ base → natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact taggedTuple_value_bits
      (hvalue.trans (value_le_pairIter (total + 1) base)) hbits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    hsmallBits 0 (Nat.zero_le _)
  induction remaining generalizing consumed cursor accumulator state with
  | zero =>
      have hconsumed : consumed = total := by omega
      have honeBits : natBitLength 1 ≤ maximumBits :=
        hsmallBits 1 hbase
      have houtputBound :
          Nat.pair 1 accumulator ≤ pairIter (total + 1) base := by
        subst consumed
        rw [pairIter_succ_right]
        exact pair_mono
          (one_le_pairIter total hbase) haccumulatorBound
      have houtputBits :
          natBitLength (Nat.pair 1 accumulator) ≤ maximumBits :=
        taggedTuple_value_bits houtputBound hbits
      simp only [taggedTupleLoopFuel, Nat.mul_zero, Nat.zero_add]
      rw [show (5 : ℕ) = 4 + 1 by omega]
      rw [run_branchZero_instruction
        (program := taggedTupleProgram fixedArity)
        (maximumBits := maximumBits) (fuel := 4)
        (pc := 2) (register := 2) (zeroTarget := 13)
        (nonzeroTarget := 3) (by rfl) hpc]
      rw [if_pos (by simp [hremaining])]
      rw [show (4 : ℕ) = 3 + 1 by omega]
      rw [run_branchZero_instruction
        (program := taggedTupleProgram fixedArity)
        (maximumBits := maximumBits) (fuel := 3)
        (pc := 13) (register := 0) (zeroTarget := 14)
        (nonzeroTarget := 15) (by rfl) (by rfl)]
      by_cases hcursorZero : cursor = 0
      · rw [if_pos (by simpa [hcursor] using hcursorZero)]
        rw [show (3 : ℕ) = 2 + 1 by omega]
        rw [run_set_instruction
          (program := taggedTupleProgram fixedArity)
          (maximumBits := maximumBits) (fuel := 2)
          (pc := 14) (register := 4) (value := 1) (next := 16)
          (by rfl) (by rfl) honeBits]
        rw [show (2 : ℕ) = 1 + 1 by omega]
        rw [run_pair_instruction
          (program := taggedTupleProgram fixedArity)
          (maximumBits := maximumBits) (fuel := 1)
          (pc := 16) (left := 4) (right := 3)
          (destination := 0) (next := 17)
          (value := Nat.pair 1 accumulator)
          (by rfl) (by rfl)
          (by simp [haccumulator]) houtputBits]
        simp only [decodeTaggedTupleAux, hcursorZero, if_pos]
        exact run_halt_instruction
          (program := taggedTupleProgram fixedArity)
          (maximumBits := maximumBits) (fuel := 0)
          (pc := 17) (outputRegister := 0)
          (value := Nat.pair 1 accumulator)
          (by rfl) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          houtputBits
      · rw [if_neg (by simpa [hcursor] using hcursorZero)]
        rw [show (3 : ℕ) = 2 + 1 by omega]
        rw [run_set_instruction
          (program := taggedTupleProgram fixedArity)
          (maximumBits := maximumBits) (fuel := 2)
          (pc := 15) (register := 0) (value := 0) (next := 17)
          (by rfl) (by rfl) hzeroBits]
        simp only [decodeTaggedTupleAux, hcursorZero, if_false]
        exact run_halt_instruction
          (program := taggedTupleProgram fixedArity)
          (maximumBits := maximumBits) (fuel := 1)
          (pc := 17) (outputRegister := 0) (value := 0)
          (by rfl) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          hzeroBits
  | succ remaining inductionHypothesis =>
      let outer := Nat.unpair cursor
      let payload := Nat.unpair outer.2
      let nextAccumulator := Nat.pair accumulator payload.1
      have htagBound : outer.1 ≤ base :=
        (Nat.unpair_left_le cursor).trans hcursorBound
      have hpayloadCodeBound : outer.2 ≤ base :=
        (Nat.unpair_right_le cursor).trans hcursorBound
      have hheadBound : payload.1 ≤ base :=
        (Nat.unpair_left_le outer.2).trans hpayloadCodeBound
      have htailBound : payload.2 ≤ base :=
        (Nat.unpair_right_le outer.2).trans hpayloadCodeBound
      have htagBits := hsmallBits outer.1 htagBound
      have htagPredBits :=
        hsmallBits outer.1.pred (outer.1.pred_le.trans htagBound)
      have hpayloadCodeBits :=
        hsmallBits outer.2 hpayloadCodeBound
      have hheadBits := hsmallBits payload.1 hheadBound
      have htailBits := hsmallBits payload.2 htailBound
      have hremainingBits :
          natBitLength remaining ≤ maximumBits := by
        apply hsmallBits
        exact (by omega : remaining ≤ total).trans htotalBound
      have hnextAccumulatorBound :
          nextAccumulator ≤ pairIter (consumed + 1) base := by
        rw [pairIter_succ_right]
        exact pair_mono
          haccumulatorBound
          (hheadBound.trans (value_le_pairIter consumed base))
      have hnextAccumulatorBits :
          natBitLength nextAccumulator ≤ maximumBits := by
        apply taggedTuple_value_bits
          (hnextAccumulatorBound.trans
            (pairIter_mono_depth (by omega)))
          hbits
      let state₀ := state.jump 3
      let state₁ := state₀.jump 4
      let state₂ := (state₁.write 4 outer.1).jump 5
      let state₃ := state₂.jump 6
      let state₄ := (state₃.write 4 outer.1.pred).jump 7
      let state₅ := state₄.jump 8
      let state₆ := (state₅.write 5 outer.2).jump 9
      let state₇ := (state₆.write 6 payload.1).jump 10
      let state₈ := (state₇.write 3 nextAccumulator).jump 11
      let state₉ := (state₈.write 0 payload.2).jump 12
      let state₁₀ := (state₉.write 2 remaining).jump 2
      rw [taggedTupleLoopFuel]
      rw [show 11 * (remaining + 1) + 5 =
          (10 + taggedTupleLoopFuel remaining) + 1 by
        simp [taggedTupleLoopFuel]
        omega]
      rw [run_branchZero_instruction
        (program := taggedTupleProgram fixedArity)
        (maximumBits := maximumBits)
        (fuel := 10 + taggedTupleLoopFuel remaining)
        (pc := 2) (register := 2) (zeroTarget := 13)
        (nonzeroTarget := 3) (by rfl) hpc]
      rw [if_neg (by simp [hremaining])]
      change
        runNPOracleProgram (taggedTupleProgram fixedArity) maximumBits
            (10 + taggedTupleLoopFuel remaining) state₀ = _
      rw [show 10 + taggedTupleLoopFuel remaining =
          (9 + taggedTupleLoopFuel remaining) + 1 by omega]
      rw [run_branchZero_instruction
        (program := taggedTupleProgram fixedArity)
        (maximumBits := maximumBits)
        (fuel := 9 + taggedTupleLoopFuel remaining)
        (pc := 3) (register := 0) (zeroTarget := 15)
        (nonzeroTarget := 4) (by rfl) (by rfl)]
      by_cases hcursorZero : cursor = 0
      · rw [if_pos (by simpa [state₀, hcursor] using hcursorZero)]
        rw [show 9 + taggedTupleLoopFuel remaining =
            (8 + taggedTupleLoopFuel remaining) + 1 by omega]
        rw [run_set_instruction
          (program := taggedTupleProgram fixedArity)
          (maximumBits := maximumBits)
          (fuel := 8 + taggedTupleLoopFuel remaining)
          (pc := 15) (register := 0) (value := 0) (next := 17)
          (by rfl) (by rfl) hzeroBits]
        simp only [decodeTaggedTupleAux, hcursorZero, if_true]
        rw [show 8 + taggedTupleLoopFuel remaining =
            (7 + taggedTupleLoopFuel remaining) + 1 by omega]
        exact run_halt_instruction
          (program := taggedTupleProgram fixedArity)
          (maximumBits := maximumBits)
          (fuel := 7 + taggedTupleLoopFuel remaining)
          (state := ((state₀.jump 15).write 0 0).jump 17)
          (pc := 17) (outputRegister := 0) (value := 0)
          (by rfl) (by rfl)
          (by simp [state₀, NPOracleState.write, NPOracleState.jump])
          hzeroBits
      · rw [if_neg (by simpa [state₀, hcursor] using hcursorZero)]
        change
          runNPOracleProgram (taggedTupleProgram fixedArity) maximumBits
              (9 + taggedTupleLoopFuel remaining) state₁ = _
        rw [show 9 + taggedTupleLoopFuel remaining =
            (8 + taggedTupleLoopFuel remaining) + 1 by omega]
        rw [run_unpairLeft_instruction
          (program := taggedTupleProgram fixedArity)
          (maximumBits := maximumBits)
          (fuel := 8 + taggedTupleLoopFuel remaining)
          (pc := 4) (source := 0) (destination := 4) (next := 5)
          (value := outer.1) (by rfl) (by rfl)
          (by simp [state₁, state₀, hcursor, outer]) htagBits]
        change
          runNPOracleProgram (taggedTupleProgram fixedArity) maximumBits
              (8 + taggedTupleLoopFuel remaining) state₂ = _
        rw [show 8 + taggedTupleLoopFuel remaining =
            (7 + taggedTupleLoopFuel remaining) + 1 by omega]
        rw [run_branchZero_instruction
          (program := taggedTupleProgram fixedArity)
          (maximumBits := maximumBits)
          (fuel := 7 + taggedTupleLoopFuel remaining)
          (pc := 5) (register := 4) (zeroTarget := 15)
          (nonzeroTarget := 6) (by rfl) (by rfl)]
        by_cases htagZero : outer.1 = 0
        · rw [if_pos (by simpa [state₂] using htagZero)]
          rw [show 7 + taggedTupleLoopFuel remaining =
              (6 + taggedTupleLoopFuel remaining) + 1 by omega]
          rw [run_set_instruction
            (program := taggedTupleProgram fixedArity)
            (maximumBits := maximumBits)
            (fuel := 6 + taggedTupleLoopFuel remaining)
            (pc := 15) (register := 0) (value := 0) (next := 17)
            (by rfl) (by rfl) hzeroBits]
          have htagNotOne : outer.1 ≠ 1 := by omega
          rw [show
            (match decodeTaggedTupleAux (remaining + 1) cursor accumulator with
            | some fields => Nat.pair 1 fields
            | none => 0) = 0 by
              simp [decodeTaggedTupleAux, hcursorZero, outer,
                htagNotOne]]
          rw [show 6 + taggedTupleLoopFuel remaining =
              (5 + taggedTupleLoopFuel remaining) + 1 by omega]
          exact run_halt_instruction
            (program := taggedTupleProgram fixedArity)
            (maximumBits := maximumBits)
            (fuel := 5 + taggedTupleLoopFuel remaining)
            (state := ((state₂.jump 15).write 0 0).jump 17)
            (pc := 17) (outputRegister := 0) (value := 0)
            (by rfl) (by rfl)
            (by simp [state₂, state₁, state₀,
              NPOracleState.write, NPOracleState.jump])
            hzeroBits
        · rw [if_neg (by simpa [state₂] using htagZero)]
          change
            runNPOracleProgram (taggedTupleProgram fixedArity) maximumBits
                (7 + taggedTupleLoopFuel remaining) state₃ = _
          rw [show 7 + taggedTupleLoopFuel remaining =
              (6 + taggedTupleLoopFuel remaining) + 1 by omega]
          rw [run_decrement_instruction
            (program := taggedTupleProgram fixedArity)
            (maximumBits := maximumBits)
            (fuel := 6 + taggedTupleLoopFuel remaining)
            (pc := 6) (register := 4) (next := 7)
            (value := outer.1.pred) (by rfl) (by rfl)
            (by simp [state₃, state₂]) htagPredBits]
          change
            runNPOracleProgram (taggedTupleProgram fixedArity) maximumBits
                (6 + taggedTupleLoopFuel remaining) state₄ = _
          rw [show 6 + taggedTupleLoopFuel remaining =
              (5 + taggedTupleLoopFuel remaining) + 1 by omega]
          rw [run_branchZero_instruction
            (program := taggedTupleProgram fixedArity)
            (maximumBits := maximumBits)
            (fuel := 5 + taggedTupleLoopFuel remaining)
            (pc := 7) (register := 4) (zeroTarget := 8)
            (nonzeroTarget := 15) (by rfl) (by rfl)]
          by_cases htagOne : outer.1 = 1
          · have hpredZero : outer.1.pred = 0 := by simp [htagOne]
            rw [if_pos (by simpa [state₄] using hpredZero)]
            change
              runNPOracleProgram (taggedTupleProgram fixedArity)
                  maximumBits
                  (5 + taggedTupleLoopFuel remaining) state₅ = _
            rw [show 5 + taggedTupleLoopFuel remaining =
                (4 + taggedTupleLoopFuel remaining) + 1 by omega]
            rw [run_unpairRight_instruction
              (program := taggedTupleProgram fixedArity)
              (maximumBits := maximumBits)
              (fuel := 4 + taggedTupleLoopFuel remaining)
              (pc := 8) (source := 0) (destination := 5) (next := 9)
              (value := outer.2) (by rfl) (by rfl)
              (by simp [state₅, state₄, state₃, state₂, state₁,
                state₀, hcursor, outer])
              hpayloadCodeBits]
            change
              runNPOracleProgram (taggedTupleProgram fixedArity)
                  maximumBits
                  (4 + taggedTupleLoopFuel remaining) state₆ = _
            rw [show 4 + taggedTupleLoopFuel remaining =
                (3 + taggedTupleLoopFuel remaining) + 1 by omega]
            rw [run_unpairLeft_instruction
              (program := taggedTupleProgram fixedArity)
              (maximumBits := maximumBits)
              (fuel := 3 + taggedTupleLoopFuel remaining)
              (pc := 9) (source := 5) (destination := 6) (next := 10)
              (value := payload.1) (by rfl) (by rfl)
              (by simp [state₆, payload]) hheadBits]
            change
              runNPOracleProgram (taggedTupleProgram fixedArity)
                  maximumBits
                  (3 + taggedTupleLoopFuel remaining) state₇ = _
            rw [show 3 + taggedTupleLoopFuel remaining =
                (2 + taggedTupleLoopFuel remaining) + 1 by omega]
            rw [run_pair_instruction
              (program := taggedTupleProgram fixedArity)
              (maximumBits := maximumBits)
              (fuel := 2 + taggedTupleLoopFuel remaining)
              (pc := 10) (left := 3) (right := 6)
              (destination := 3) (next := 11)
              (value := nextAccumulator)
              (by rfl) (by rfl)
              (by simp [state₇, state₆, state₅, state₄, state₃,
                state₂, state₁, state₀, haccumulator,
                nextAccumulator])
              hnextAccumulatorBits]
            change
              runNPOracleProgram (taggedTupleProgram fixedArity)
                  maximumBits
                  (2 + taggedTupleLoopFuel remaining) state₈ = _
            rw [show 2 + taggedTupleLoopFuel remaining =
                (1 + taggedTupleLoopFuel remaining) + 1 by omega]
            rw [run_unpairRight_instruction
              (program := taggedTupleProgram fixedArity)
              (maximumBits := maximumBits)
              (fuel := 1 + taggedTupleLoopFuel remaining)
              (pc := 11) (source := 5) (destination := 0) (next := 12)
              (value := payload.2) (by rfl) (by rfl)
              (by simp [state₈, state₇, state₆, payload]) htailBits]
            change
              runNPOracleProgram (taggedTupleProgram fixedArity)
                  maximumBits
                  (1 + taggedTupleLoopFuel remaining) state₉ = _
            rw [show 1 + taggedTupleLoopFuel remaining =
                taggedTupleLoopFuel remaining + 1 by omega]
            rw [run_decrement_instruction
              (program := taggedTupleProgram fixedArity)
              (maximumBits := maximumBits)
              (fuel := taggedTupleLoopFuel remaining)
              (pc := 12) (register := 2) (next := 2)
              (value := remaining) (by rfl) (by rfl)
              (by simp [state₉, state₈, state₇, state₆, state₅,
                state₄, state₃, state₂, state₁, state₀,
                hremaining])
              hremainingBits]
            have hrecursive :=
              inductionHypothesis
                (consumed := consumed + 1)
                (cursor := payload.2)
                (accumulator := nextAccumulator)
                (state := state₁₀)
                rfl
                (by simp [state₁₀])
                (by simp [state₁₀, state₉])
                (by simp [state₁₀, state₉, state₈])
                (by omega)
                htailBound hnextAccumulatorBound
            simpa [decodeTaggedTupleAux, hcursorZero, htagOne,
              outer, payload, nextAccumulator] using hrecursive
          · have hpredNonzero : outer.1.pred ≠ 0 := by
              simp only [Nat.pred_eq_sub_one]
              omega
            rw [if_neg (by simpa [state₄] using hpredNonzero)]
            rw [show 5 + taggedTupleLoopFuel remaining =
                (4 + taggedTupleLoopFuel remaining) + 1 by omega]
            rw [run_set_instruction
              (program := taggedTupleProgram fixedArity)
              (maximumBits := maximumBits)
              (fuel := 4 + taggedTupleLoopFuel remaining)
              (pc := 15) (register := 0) (value := 0) (next := 17)
              (by rfl) (by rfl) hzeroBits]
            rw [show
              (match
                decodeTaggedTupleAux (remaining + 1) cursor accumulator with
              | some fields => Nat.pair 1 fields
              | none => 0) = 0 by
                simp [decodeTaggedTupleAux, hcursorZero, outer,
                  htagOne]]
            rw [show 4 + taggedTupleLoopFuel remaining =
                (3 + taggedTupleLoopFuel remaining) + 1 by omega]
            exact run_halt_instruction
              (program := taggedTupleProgram fixedArity)
              (maximumBits := maximumBits)
              (fuel := 3 + taggedTupleLoopFuel remaining)
              (state := ((state₄.jump 15).write 0 0).jump 17)
              (pc := 17) (outputRegister := 0) (value := 0)
              (by rfl) (by rfl)
              (by simp [state₄, state₃, state₂, state₁, state₀,
                NPOracleState.write, NPOracleState.jump])
              hzeroBits

theorem run_taggedTupleProgram
    (inputLength arity raw : ℕ) :
    runNPOracleProgram (taggedTupleProgram arity)
        (taggedTupleBits inputLength arity raw)
        (taggedTupleFuel arity)
        (initialNPOracleState inputLength raw) =
      some (taggedTupleOutput arity raw) := by
  let base := max 1 (max inputLength (max arity raw))
  let maximumBits := taggedTupleBits inputLength arity raw
  have hbase : 1 ≤ base := by
    simp [base]
  have harityBound : arity ≤ base := by
    simp [base]
  have hrawBound : raw ≤ base := by
    simp [base]
  have harityBits :
      natBitLength arity ≤ maximumBits := by
    unfold maximumBits taggedTupleBits
    exact natBitLength_mono <|
      harityBound.trans (value_le_pairIter (arity + 1) base)
  have hzeroBits :
      natBitLength 0 ≤ maximumBits := by
    unfold maximumBits taggedTupleBits
    exact natBitLength_mono (Nat.zero_le _)
  rw [show taggedTupleFuel arity =
      (taggedTupleLoopFuel arity + 1) + 1 by
    simp [taggedTupleFuel, taggedTupleLoopFuel]]
  rw [run_set_instruction
    (program := taggedTupleProgram arity)
    (maximumBits := maximumBits)
    (fuel := taggedTupleLoopFuel arity + 1)
    (pc := 0) (register := 2) (value := arity) (next := 1)
    (by rfl) (by rfl) harityBits]
  rw [show taggedTupleLoopFuel arity + 1 =
      taggedTupleLoopFuel arity + 1 by rfl]
  rw [run_set_instruction
    (program := taggedTupleProgram arity)
    (maximumBits := maximumBits)
    (fuel := taggedTupleLoopFuel arity)
    (pc := 1) (register := 3) (value := 0) (next := 2)
    (by rfl) (by rfl) hzeroBits]
  have hrun :=
    run_taggedTupleLoop arity arity 0 arity raw 0
      maximumBits base
      ((((initialNPOracleState inputLength raw).write 2 arity).jump 1
        |>.write 3 0).jump 2)
      rfl
      (by simp)
      (by simp [initialNPOracleState])
      (by simp)
      (by omega)
      hbase harityBound hrawBound (by simp [pairIter])
      (by
        unfold maximumBits taggedTupleBits
        exact le_rfl)
  simpa [taggedTupleOutput, decodeTaggedTuple] using hrun

end NearCubicWires.CanonicalTaggedTupleProgram
