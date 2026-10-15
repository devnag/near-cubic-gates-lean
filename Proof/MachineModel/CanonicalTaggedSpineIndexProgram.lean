import Proof.Foundations.CanonicalBinaryProgram

/-!
# Indexed access to one tagged spine

`CanonicalBalancedBuilder.taggedToBalancedProgram` is the tree's only route from
a tagged field list to the balanced ABI, and its published charge
`taggedToBalancedRegisterBitsFor` is `natBitLength` of a `pairIter` clock at the
builder's own fuel.  `ValidatorWidthCombinatorLedger.natBitLength_pairIter_le`
puts that at `2 ^ (42 · fields.length + 14) ·` the input width, and the tagged
codec's own counting ledger only gives `2 ^ fields.length ≤ natBitLength code`,
so the frozen conversion sits at degree `43` over the record's width.  It cannot
be re-charged: the builder's run theorem carries the clock inside its induction
invariant.

`CanonicalBalancedMidpointRebuildProgram` solved the same problem for the
*balanced* codec by replacing the builder with **count, generate one request per
index, then select**.  This module supplies the two tagged-codec leaves that
route needs, at charges that are `natBitLength` of values the machine
demonstrably holds:

* §1 the spine's structural length and lookup, as total functions;

* §2 `taggedSpineLengthProgram` — one five-instruction cell loop, returning the
  field count paired with the code it counted, which is exactly
  `GeneratedBalancedRangeProgram.generatedBalancedRangeInput`;

* §3 `taggedSpineSelectProgram` — the same cell loop counted down by an index,
  returning the selected field, at the request ABI a balanced call hands its
  callee (`inputLength` is the index, register zero is the code).

Neither charge is a clock.  `taggedSpineLengthBits` is the width of the returned
pair and `taggedSpineSelectBits` is the width of the code and the index, so both
are linear in the record's own width.
-/

namespace NearCubicWires.CanonicalTaggedSpineIndexProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

private theorem natBitLength_zero' : natBitLength 0 = 1 := by
  simp [natBitLength]

private theorem one_le_natBitLength' (value : ℕ) : 1 ≤ natBitLength value := by
  unfold natBitLength
  omega

private theorem pair_one_positive (value : ℕ) : 1 ≤ Nat.pair 1 value :=
  Nat.left_le_pair 1 value

/-! ## §1 The spine's structural length and lookup -/

/-- Total structural length of a tagged spine.  Cells are `Nat.pair 1 (Nat.pair
head tail)`; anything else terminates the walk. -/
def taggedSpineLength (code : ℕ) : ℕ :=
  if code = 0 then
    0
  else
    let outer := Nat.unpair code
    if outer.1 = 1 then
      1 + taggedSpineLength (Nat.unpair outer.2).2
    else
      0
termination_by code
decreasing_by
  have houter : outer.2 < code := by
    have hsum : outer.1 + outer.2 ≤ code := by
      simpa only [outer] using Nat.unpair_add_le code
    omega
  exact (Nat.unpair_right_le outer.2).trans_lt houter

/-- Total structural lookup in a tagged spine, with `0` past the end. -/
def taggedSpineGetD (code index : ℕ) : ℕ :=
  if code = 0 then
    0
  else
    let outer := Nat.unpair code
    if outer.1 = 1 then
      let payload := Nat.unpair outer.2
      if index = 0 then payload.1 else taggedSpineGetD payload.2 (index - 1)
    else
      0
termination_by code
decreasing_by
  have houter : outer.2 < code := by
    have hsum : outer.1 + outer.2 ≤ code := by
      simpa only [outer] using Nat.unpair_add_le code
    omega
  exact (Nat.unpair_right_le outer.2).trans_lt houter

@[simp] theorem taggedSpineLength_encodeTaggedList (values : List ℕ) :
    taggedSpineLength (encodeTaggedList values) = values.length := by
  induction values with
  | nil => simp [taggedSpineLength, encodeTaggedList]
  | cons value rest inductionHypothesis =>
      have hcode :
          encodeTaggedList (value :: rest) =
            Nat.pair 1 (Nat.pair value (encodeTaggedList rest)) := rfl
      have hpositive : 1 ≤ encodeTaggedList (value :: rest) := by
        rw [hcode]
        exact pair_one_positive _
      rw [taggedSpineLength, if_neg (by omega)]
      simp only [hcode, Nat.unpair_pair]
      simp only [if_true, inductionHypothesis, List.length_cons]
      omega

@[simp] theorem taggedSpineGetD_encodeTaggedList (values : List ℕ) (index : ℕ) :
    taggedSpineGetD (encodeTaggedList values) index = values.getD index 0 := by
  induction values generalizing index with
  | nil => simp [taggedSpineGetD, encodeTaggedList]
  | cons value rest inductionHypothesis =>
      have hcode :
          encodeTaggedList (value :: rest) =
            Nat.pair 1 (Nat.pair value (encodeTaggedList rest)) := rfl
      have hpositive : 1 ≤ encodeTaggedList (value :: rest) := by
        rw [hcode]
        exact pair_one_positive _
      rw [taggedSpineGetD, if_neg (by omega)]
      simp only [hcode, Nat.unpair_pair]
      cases index with
      | zero => simp
      | succ index => simpa using inductionHypothesis index

/-! ## §2 The spine counter

Register ABI: `r0` holds the code throughout and the returned pair at the end,
`r2` is the cursor, `r3` is the accumulated count and `r4` is the peeled cell.
-/

/-- **The tagged spine counter.**  Five instructions per cell. -/
def taggedSpineLengthProgram : NPOracleProgram :=
  [ .copy 0 2 1
  , .set 3 0 2
  , .branchZero 2 7 3
  , .unpairRight 2 4 4
  , .unpairRight 4 2 5
  , .increment 3 6
  , .branchZero 4 2 2
  , .pair 3 0 0 8
  , .halt 0
  ]

@[simp] theorem taggedSpineLengthProgram_oracleFree :
    OracleFree taggedSpineLengthProgram := by
  rfl

/-- Steps from the loop head with `count` cells left to walk. -/
def taggedSpineLengthLoopFuel (count : ℕ) : ℕ := 5 * count + 3

/-- Total steps of the counter. -/
def taggedSpineLengthFuel (code : ℕ) : ℕ :=
  taggedSpineLengthLoopFuel (taggedSpineLength code) + 2

/-- The counter's charge: the width of the pair it returns.  No clock. -/
def taggedSpineLengthBits (code : ℕ) : ℕ :=
  natBitLength (Nat.pair (taggedSpineLength code) code)

private theorem run_taggedSpineLengthLoop
    (values : List ℕ) (code accumulator maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 2)
    (hcursor : state.registers 2 = encodeTaggedList values)
    (haccumulator : state.registers 3 = accumulator)
    (hcode : state.registers 0 = code)
    (hcursorBits : natBitLength (encodeTaggedList values) ≤ maximumBits)
    (hcountBits : natBitLength (accumulator + values.length) ≤ maximumBits)
    (hresultBits :
      natBitLength (Nat.pair (accumulator + values.length) code) ≤
        maximumBits) :
    runNPOracleProgram taggedSpineLengthProgram maximumBits
        (taggedSpineLengthLoopFuel values.length) state =
      some (Nat.pair (accumulator + values.length) code) := by
  induction values generalizing accumulator state with
  | nil =>
      have hzero : state.registers 2 = 0 := by
        simpa [encodeTaggedList] using hcursor
      have hpairBits : natBitLength (Nat.pair accumulator code) ≤ maximumBits := by
        simpa using hresultBits
      simp only [List.length_nil, Nat.add_zero] at hresultBits ⊢
      rw [show taggedSpineLengthLoopFuel 0 = 2 + 1 by
        simp [taggedSpineLengthLoopFuel]]
      rw [run_branchZero_instruction (by rfl) hpc, hzero, if_pos rfl]
      rw [show (2 : ℕ) = 1 + 1 by omega]
      rw [run_pair_instruction (value := Nat.pair accumulator code)
        (by rfl) rfl
        (by simp [NPOracleState.jump, haccumulator, hcode]) hpairBits]
      exact run_halt_instruction (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hpairBits
  | cons value rest inductionHypothesis =>
      have hcodeCell :
          encodeTaggedList (value :: rest) =
            Nat.pair 1 (Nat.pair value (encodeTaggedList rest)) := rfl
      have hcell : state.registers 2 ≠ 0 := by
        rw [hcursor, hcodeCell]
        have := pair_one_positive (Nat.pair value (encodeTaggedList rest))
        omega
      have hpayloadLe :
          Nat.pair value (encodeTaggedList rest) ≤
            encodeTaggedList (value :: rest) := by
        rw [hcodeCell]
        exact Nat.right_le_pair 1 _
      have htailLe : encodeTaggedList rest ≤ encodeTaggedList (value :: rest) :=
        le_trans (Nat.right_le_pair value (encodeTaggedList rest)) hpayloadLe
      have hpayloadBits :
          natBitLength (Nat.pair value (encodeTaggedList rest)) ≤ maximumBits :=
        (natBitLength_mono hpayloadLe).trans hcursorBits
      have htailBits :
          natBitLength (encodeTaggedList rest) ≤ maximumBits :=
        (natBitLength_mono htailLe).trans hcursorBits
      have hnextCount :
          accumulator + (value :: rest).length =
            accumulator + 1 + rest.length := by
        simp only [List.length_cons]
        omega
      have hsuccBits : natBitLength (accumulator + 1) ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hcountBits
        rw [hnextCount]
        omega
      have hnextCountBits :
          natBitLength (accumulator + 1 + rest.length) ≤ maximumBits := by
        rw [← hnextCount]
        exact hcountBits
      have hnextResultBits :
          natBitLength (Nat.pair (accumulator + 1 + rest.length) code) ≤
            maximumBits := by
        rw [← hnextCount]
        exact hresultBits
      let state1 := ((state.jump 3).write 4
        (Nat.pair value (encodeTaggedList rest))).jump 4
      let state2 := (state1.write 2 (encodeTaggedList rest)).jump 5
      let state3 := (state2.write 3 (accumulator + 1)).jump 6
      rw [show taggedSpineLengthLoopFuel (value :: rest).length =
        (4 + taggedSpineLengthLoopFuel rest.length) + 1 by
          simp only [taggedSpineLengthLoopFuel, List.length_cons]
          omega]
      rw [run_branchZero_instruction (by rfl) hpc, if_neg hcell]
      rw [show 4 + taggedSpineLengthLoopFuel rest.length =
        (3 + taggedSpineLengthLoopFuel rest.length) + 1 by omega]
      rw [run_unpairRight_instruction
        (value := Nat.pair value (encodeTaggedList rest)) (by rfl) rfl
        (by simp [NPOracleState.jump, hcursor, hcodeCell]) hpayloadBits]
      change
        runNPOracleProgram taggedSpineLengthProgram maximumBits
            (3 + taggedSpineLengthLoopFuel rest.length) state1 =
          some (Nat.pair (accumulator + (value :: rest).length) code)
      rw [show 3 + taggedSpineLengthLoopFuel rest.length =
        (2 + taggedSpineLengthLoopFuel rest.length) + 1 by omega]
      rw [run_unpairRight_instruction (value := encodeTaggedList rest)
        (by rfl) rfl (by simp [state1]) htailBits]
      change
        runNPOracleProgram taggedSpineLengthProgram maximumBits
            (2 + taggedSpineLengthLoopFuel rest.length) state2 =
          some (Nat.pair (accumulator + (value :: rest).length) code)
      rw [show 2 + taggedSpineLengthLoopFuel rest.length =
        (1 + taggedSpineLengthLoopFuel rest.length) + 1 by omega]
      rw [run_increment_instruction (value := accumulator + 1)
        (by rfl) rfl (by simp [state2, state1, haccumulator]) hsuccBits]
      change
        runNPOracleProgram taggedSpineLengthProgram maximumBits
            (1 + taggedSpineLengthLoopFuel rest.length) state3 =
          some (Nat.pair (accumulator + (value :: rest).length) code)
      rw [show 1 + taggedSpineLengthLoopFuel rest.length =
        taggedSpineLengthLoopFuel rest.length + 1 by omega]
      rw [run_branchZero_instruction (by rfl) (rfl : state3.pc = 6)]
      simp only [ite_self]
      rw [hnextCount]
      exact inductionHypothesis (accumulator + 1) (state3.jump 2) rfl
        (by simp [state3, state2, state1]) (by simp [state3, state2])
        (by simp [state3, state2, state1, hcode])
        htailBits hnextCountBits hnextResultBits

/-- **The counter returns the field count paired with its own input.**  That
pair is `generatedBalancedRangeInput`, so the indexed request generator takes it
verbatim. -/
theorem run_taggedSpineLengthProgram (inputLength : ℕ) (values : List ℕ) :
    runNPOracleProgram taggedSpineLengthProgram
        (taggedSpineLengthBits (encodeTaggedList values))
        (taggedSpineLengthFuel (encodeTaggedList values))
        (initialNPOracleState inputLength (encodeTaggedList values)) =
      some (Nat.pair values.length (encodeTaggedList values)) := by
  let maximumBits := taggedSpineLengthBits (encodeTaggedList values)
  have hresultBits :
      natBitLength (Nat.pair values.length (encodeTaggedList values)) ≤
        maximumBits := by
    simp [maximumBits, taggedSpineLengthBits]
  have hcodeBits :
      natBitLength (encodeTaggedList values) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair values.length (encodeTaggedList values))).trans
      hresultBits
  have hcountBits : natBitLength values.length ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair values.length (encodeTaggedList values))).trans
      hresultBits
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    have := one_le_natBitLength' (Nat.pair values.length (encodeTaggedList values))
    rw [natBitLength_zero']
    simpa [maximumBits, taggedSpineLengthBits] using this
  rw [show taggedSpineLengthFuel (encodeTaggedList values) =
    (taggedSpineLengthLoopFuel values.length + 1) + 1 by
      simp [taggedSpineLengthFuel, taggedSpineLengthLoopFuel]]
  rw [run_copy_instruction (value := encodeTaggedList values)
    (by rfl) rfl (by simp [initialNPOracleState]) hcodeBits]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  simpa only [Nat.zero_add] using
    run_taggedSpineLengthLoop values (encodeTaggedList values) 0 maximumBits
      (((((initialNPOracleState inputLength
        (encodeTaggedList values)).write 2
          (encodeTaggedList values)).jump 1).write 3 0).jump 2)
      rfl
      (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
      hcodeBits (by simpa using hcountBits) (by simpa using hresultBits)

/-! ## §3 The spine selector

Register ABI: `r0` is the cursor and then the result, `r2` is the index
countdown, `r3` is the peeled cell.  The entry state is the one a balanced call
hands its callee: the request's left component is the public length and its
right component is register zero.
-/

/-- **The tagged spine selector.**  Five instructions per skipped cell. -/
def taggedSpineSelectProgram : NPOracleProgram :=
  [ .copy 1 2 1
  , .branchZero 0 7 2
  , .branchZero 2 5 3
  , .unpairRight 0 3 4
  , .unpairRight 3 0 8
  , .unpairRight 0 3 6
  , .unpairLeft 3 0 9
  , .set 0 0 9
  , .decrement 2 1
  , .halt 0
  ]

@[simp] theorem taggedSpineSelectProgram_oracleFree :
    OracleFree taggedSpineSelectProgram := by
  rfl

/-- Steps from the loop head with `index` cells still to skip. -/
def taggedSpineSelectLoopFuel (index : ℕ) : ℕ := 5 * index + 5

/-- Total steps of the selector. -/
def taggedSpineSelectFuel (index : ℕ) : ℕ := taggedSpineSelectLoopFuel index + 1

/-- The selector's charge: the widths of the index and of the code it walks. -/
def taggedSpineSelectBits (index : ℕ) (values : List ℕ) : ℕ :=
  max (natBitLength index) (natBitLength (encodeTaggedList values))

private theorem run_taggedSpineSelectLoop
    (values : List ℕ) (index maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 1)
    (hcursor : state.registers 0 = encodeTaggedList values)
    (hindex : state.registers 2 = index)
    (hcursorBits : natBitLength (encodeTaggedList values) ≤ maximumBits)
    (hindexBits : natBitLength index ≤ maximumBits) :
    runNPOracleProgram taggedSpineSelectProgram maximumBits
        (taggedSpineSelectLoopFuel index) state =
      some (values.getD index 0) := by
  induction values generalizing index state with
  | nil =>
      have hzeroCursor : state.registers 0 = 0 := by
        simpa [encodeTaggedList] using hcursor
      have hzeroBits : natBitLength 0 ≤ maximumBits := by
        have hone := one_le_natBitLength' index
        rw [natBitLength_zero']
        omega
      rw [show taggedSpineSelectLoopFuel index = (5 * index + 4) + 1 by
        simp [taggedSpineSelectLoopFuel]]
      rw [run_branchZero_instruction (by rfl) hpc, hzeroCursor, if_pos rfl]
      rw [show 5 * index + 4 = (5 * index + 3) + 1 by omega]
      rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
      rw [show 5 * index + 3 = (5 * index + 2) + 1 by omega]
      simpa using
        run_halt_instruction (program := taggedSpineSelectProgram)
          (maximumBits := maximumBits) (fuel := 5 * index + 2) (pc := 9)
          (outputRegister := 0) (value := 0) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump]) hzeroBits
  | cons value rest inductionHypothesis =>
      have hcodeCell :
          encodeTaggedList (value :: rest) =
            Nat.pair 1 (Nat.pair value (encodeTaggedList rest)) := rfl
      have hcell : state.registers 0 ≠ 0 := by
        rw [hcursor, hcodeCell]
        have := pair_one_positive (Nat.pair value (encodeTaggedList rest))
        omega
      have hpayloadLe :
          Nat.pair value (encodeTaggedList rest) ≤
            encodeTaggedList (value :: rest) := by
        rw [hcodeCell]
        exact Nat.right_le_pair 1 _
      have hpayloadBits :
          natBitLength (Nat.pair value (encodeTaggedList rest)) ≤ maximumBits :=
        (natBitLength_mono hpayloadLe).trans hcursorBits
      have htailBits :
          natBitLength (encodeTaggedList rest) ≤ maximumBits :=
        (natBitLength_mono
          (le_trans (Nat.right_le_pair value (encodeTaggedList rest))
            hpayloadLe)).trans hcursorBits
      have hheadBits : natBitLength value ≤ maximumBits :=
        (natBitLength_mono
          (le_trans (Nat.left_le_pair value (encodeTaggedList rest))
            hpayloadLe)).trans hcursorBits
      rw [show taggedSpineSelectLoopFuel index = (5 * index + 4) + 1 by
        simp [taggedSpineSelectLoopFuel]]
      rw [run_branchZero_instruction (by rfl) hpc, if_neg hcell]
      cases index with
      | zero =>
          rw [show 5 * 0 + 4 = 3 + 1 by omega]
          rw [run_branchZero_instruction (by rfl) (rfl : (state.jump 2).pc = 2)]
          rw [show ((state.jump 2).registers 2) = 0 by
            simpa [NPOracleState.jump] using hindex]
          rw [if_pos rfl]
          rw [show (3 : ℕ) = 2 + 1 by omega]
          rw [run_unpairRight_instruction
            (value := Nat.pair value (encodeTaggedList rest)) (by rfl) rfl
            (by simp [NPOracleState.jump, hcursor, hcodeCell]) hpayloadBits]
          rw [show (2 : ℕ) = 1 + 1 by omega]
          rw [run_unpairLeft_instruction (value := value) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump]) hheadBits]
          simpa using
            run_halt_instruction (program := taggedSpineSelectProgram)
              (maximumBits := maximumBits) (fuel := 0) (pc := 9)
              (outputRegister := 0) (value := value) (by rfl)
              (by simp [NPOracleState.write, NPOracleState.jump])
              (by simp [NPOracleState.write, NPOracleState.jump]) hheadBits
      | succ index =>
          have hindexBits' : natBitLength index ≤ maximumBits :=
            (natBitLength_mono (Nat.le_succ index)).trans hindexBits
          let state1 := (((state.jump 2).jump 3).write 3
            (Nat.pair value (encodeTaggedList rest))).jump 4
          let state2 := (state1.write 0 (encodeTaggedList rest)).jump 8
          rw [show 5 * (index + 1) + 4 = (5 * index + 8) + 1 by omega]
          rw [run_branchZero_instruction (by rfl) (rfl : (state.jump 2).pc = 2)]
          rw [show ((state.jump 2).registers 2) = index + 1 by
            simpa [NPOracleState.jump] using hindex]
          rw [if_neg (Nat.succ_ne_zero index)]
          rw [show 5 * index + 8 = (5 * index + 7) + 1 by omega]
          rw [run_unpairRight_instruction
            (value := Nat.pair value (encodeTaggedList rest)) (by rfl) rfl
            (by simp [NPOracleState.jump, hcursor, hcodeCell]) hpayloadBits]
          change
            runNPOracleProgram taggedSpineSelectProgram maximumBits
                (5 * index + 7) state1 =
              some ((value :: rest).getD (index + 1) 0)
          rw [show 5 * index + 7 = (5 * index + 6) + 1 by omega]
          rw [run_unpairRight_instruction (value := encodeTaggedList rest)
            (by rfl) rfl (by simp [state1]) htailBits]
          change
            runNPOracleProgram taggedSpineSelectProgram maximumBits
                (5 * index + 6) state2 =
              some ((value :: rest).getD (index + 1) 0)
          rw [show 5 * index + 6 = (5 * index + 5) + 1 by omega]
          rw [run_decrement_instruction (value := index) (by rfl) rfl
            (by simp [state2, state1, hindex]) hindexBits']
          rw [show (value :: rest).getD (index + 1) 0 = rest.getD index 0 by simp]
          refine inductionHypothesis index
            ((state2.write 2 index).jump 1) ?_ ?_ ?_ htailBits hindexBits'
          · simp
          · simp [state2, state1]
          · simp

theorem run_taggedSpineSelectProgram (index : ℕ) (values : List ℕ) :
    runNPOracleProgram taggedSpineSelectProgram
        (taggedSpineSelectBits index values)
        (taggedSpineSelectFuel index)
        (initialNPOracleState index (encodeTaggedList values)) =
      some (values.getD index 0) := by
  let maximumBits := taggedSpineSelectBits index values
  have hindexBits : natBitLength index ≤ maximumBits := Nat.le_max_left _ _
  have hcodeBits :
      natBitLength (encodeTaggedList values) ≤ maximumBits :=
    Nat.le_max_right _ _
  rw [show taggedSpineSelectFuel index = taggedSpineSelectLoopFuel index + 1 by
    rfl]
  rw [run_copy_instruction (value := index) (by rfl) rfl
    (by simp [initialNPOracleState]) hindexBits]
  exact run_taggedSpineSelectLoop values index maximumBits
    (((initialNPOracleState index (encodeTaggedList values)).write 2
      index).jump 1)
    rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcodeBits hindexBits

end NearCubicWires.CanonicalTaggedSpineIndexProgram
