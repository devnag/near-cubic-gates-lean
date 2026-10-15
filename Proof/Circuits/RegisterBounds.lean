import Proof.Foundations.PolynomialClock

/-!
# Uniform register bounds for fixed weak-machine programs

The weak machine charges every write by binary width.  This module packages
the monotone bound used by executable compiler proofs: one machine step may
replace a register bound `b` by `Nat.pair b b`, and `pairIter` reserves that
growth for an exact number of remaining steps.
-/

namespace NearCubicWires.RegisterBounds

open NearCubicWires
open NearCubicWires.PolynomialClock

def StateBoundedBy (bound : ℕ) (state : NPOracleState) : Prop :=
  ∀ register, state.registers register ≤ bound

theorem pairIter_add (first second value : ℕ) :
    pairIter (first + second) value =
      pairIter second (pairIter first value) := by
  induction first generalizing value with
  | zero => simp [pairIter]
  | succ first ih =>
      simp only [Nat.succ_add, pairIter]
      rw [ih]

theorem pairIter_succ_right (steps value : ℕ) :
    pairIter (steps + 1) value =
      Nat.pair (pairIter steps value) (pairIter steps value) := by
  rw [pairIter_add]
  rfl

theorem pairIter_cap_suffix
    {total consumed remaining bound maximumBits : ℕ}
    (htotal : total = consumed + remaining)
    (hbits : natBitLength (pairIter total bound) ≤ maximumBits) :
    natBitLength (pairIter remaining (pairIter consumed bound)) ≤
      maximumBits := by
  rwa [htotal, pairIter_add] at hbits

theorem stateBoundedBy_jump {bound pc : ℕ} {state : NPOracleState}
    (hstate : StateBoundedBy bound state) :
    StateBoundedBy bound (state.jump pc) := by
  exact hstate

theorem stateBoundedBy_mono {left right : ℕ} {state : NPOracleState}
    (hstate : StateBoundedBy left state) (hbound : left ≤ right) :
    StateBoundedBy right state := by
  intro register
  exact (hstate register).trans hbound

theorem stateBoundedBy_write {bound register value : ℕ}
    {state : NPOracleState}
    (hstate : StateBoundedBy bound state) (hvalue : value ≤ bound) :
    StateBoundedBy bound (state.write register value) := by
  intro candidate
  simp only [NPOracleState.write]
  split
  · exact hvalue
  · exact hstate candidate

theorem pair_mono {left right bound : ℕ}
    (hleft : left ≤ bound) (hright : right ≤ bound) :
    Nat.pair left right ≤ Nat.pair bound bound := by
  calc
    Nat.pair left right ≤ Nat.pair bound right := by
      rcases hleft.eq_or_lt with h | h
      · simp [h]
      · exact (Nat.pair_lt_pair_left right h).le
    _ ≤ Nat.pair bound bound := by
      rcases hright.eq_or_lt with h | h
      · simp [h]
      · exact (Nat.pair_lt_pair_right bound h).le

theorem bound_le_pairSelf (bound : ℕ) :
    bound ≤ Nat.pair bound bound :=
  Nat.left_le_pair bound bound

theorem one_le_pairSelf {bound : ℕ} (hbound : 1 ≤ bound) :
    1 ≤ Nat.pair bound bound :=
  hbound.trans (bound_le_pairSelf bound)

theorem one_le_pairIter (steps : ℕ) {bound : ℕ}
    (hbound : 1 ≤ bound) :
    1 ≤ pairIter steps bound := by
  induction steps generalizing bound with
  | zero => simpa [pairIter] using hbound
  | succ steps ih =>
      simpa [pairIter] using ih (one_le_pairSelf hbound)

theorem increment_le_pairSelf {value bound : ℕ}
    (hvalue : value ≤ bound) (hbound : 1 ≤ bound) :
    value + 1 ≤ Nat.pair bound bound := by
  have hadd := Nat.add_le_pair bound bound
  omega

theorem predecessor_le_pairSelf {value bound : ℕ}
    (hvalue : value ≤ bound) :
    value.pred ≤ Nat.pair bound bound :=
  value.pred_le.trans (hvalue.trans (bound_le_pairSelf bound))

theorem unpairLeft_le_pairSelf {value bound : ℕ}
    (hvalue : value ≤ bound) :
    (Nat.unpair value).1 ≤ Nat.pair bound bound :=
  (Nat.unpair_left_le value).trans
    (hvalue.trans (bound_le_pairSelf bound))

theorem unpairRight_le_pairSelf {value bound : ℕ}
    (hvalue : value ≤ bound) :
    (Nat.unpair value).2 ≤ Nat.pair bound bound :=
  (Nat.unpair_right_le value).trans
    (hvalue.trans (bound_le_pairSelf bound))

theorem shiftRight_le_pairSelf {value bound amount : ℕ}
    (hvalue : value ≤ bound) :
    Nat.shiftRight value amount ≤ Nat.pair bound bound := by
  simpa only [Nat.shiftRight_eq'] using
    (Nat.shiftRight_le value amount).trans
      (hvalue.trans (bound_le_pairSelf bound))

theorem write_fits_pairClock
    {maximumBits fuel bound register value : ℕ}
    {state : NPOracleState}
    (hvalue : value ≤ Nat.pair bound bound)
    (hbits :
      natBitLength (pairIter (fuel + 1) bound) ≤ maximumBits) :
    state.boundedWrite maximumBits register value =
      some (state.write register value) := by
  unfold NPOracleState.boundedWrite
  rw [if_pos]
  exact
    (natBitLength_mono
      (hvalue.trans
        (value_le_pairIter fuel (Nat.pair bound bound)))).trans hbits

theorem boundedAfterSet {bound register value next : ℕ}
    {state : NPOracleState}
    (hstate : StateBoundedBy bound state) (hvalue : value ≤ bound) :
    StateBoundedBy (Nat.pair bound bound)
      ((state.write register value).jump next) := by
  apply stateBoundedBy_jump
  apply stateBoundedBy_write
    (stateBoundedBy_mono hstate (bound_le_pairSelf bound))
  exact hvalue.trans (bound_le_pairSelf bound)

theorem boundedAfterCopy {bound source destination next : ℕ}
    {state : NPOracleState}
    (hstate : StateBoundedBy bound state) :
    StateBoundedBy (Nat.pair bound bound)
      ((state.write destination (state.registers source)).jump next) :=
  boundedAfterSet hstate (hstate source)

theorem boundedAfterIncrement {bound register next : ℕ}
    {state : NPOracleState}
    (hstate : StateBoundedBy bound state) (hbound : 1 ≤ bound) :
    StateBoundedBy (Nat.pair bound bound)
      ((state.write register (state.registers register + 1)).jump next) := by
  apply stateBoundedBy_jump
  apply stateBoundedBy_write
    (stateBoundedBy_mono hstate (bound_le_pairSelf bound))
  exact increment_le_pairSelf (hstate register) hbound

theorem boundedAfterDecrement {bound register next : ℕ}
    {state : NPOracleState}
    (hstate : StateBoundedBy bound state) :
    StateBoundedBy (Nat.pair bound bound)
      ((state.write register (state.registers register).pred).jump next) := by
  apply stateBoundedBy_jump
  apply stateBoundedBy_write
    (stateBoundedBy_mono hstate (bound_le_pairSelf bound))
  exact predecessor_le_pairSelf (hstate register)

theorem boundedAfterPair {bound left right destination next : ℕ}
    {state : NPOracleState}
    (hstate : StateBoundedBy bound state) :
    StateBoundedBy (Nat.pair bound bound)
      ((state.write destination
        (Nat.pair (state.registers left) (state.registers right))).jump
          next) := by
  apply stateBoundedBy_jump
  apply stateBoundedBy_write
    (stateBoundedBy_mono hstate (bound_le_pairSelf bound))
  exact pair_mono (hstate left) (hstate right)

theorem boundedAfterUnpairLeft {bound source destination next : ℕ}
    {state : NPOracleState}
    (hstate : StateBoundedBy bound state) :
    StateBoundedBy (Nat.pair bound bound)
      ((state.write destination
        (Nat.unpair (state.registers source)).1).jump next) := by
  apply boundedAfterSet hstate
  exact (Nat.unpair_left_le (state.registers source)).trans (hstate source)

theorem boundedAfterUnpairRight {bound source destination next : ℕ}
    {state : NPOracleState}
    (hstate : StateBoundedBy bound state) :
    StateBoundedBy (Nat.pair bound bound)
      ((state.write destination
        (Nat.unpair (state.registers source)).2).jump next) := by
  apply boundedAfterSet hstate
  exact (Nat.unpair_right_le (state.registers source)).trans (hstate source)

theorem boundedAfterShiftRight
    {bound source amount destination next : ℕ}
    {state : NPOracleState}
    (hstate : StateBoundedBy bound state) :
    StateBoundedBy (Nat.pair bound bound)
      ((state.write destination
        (Nat.shiftRight (state.registers source) amount)).jump next) := by
  apply stateBoundedBy_jump
  apply stateBoundedBy_write
    (stateBoundedBy_mono hstate (bound_le_pairSelf bound))
  exact shiftRight_le_pairSelf (hstate source)

theorem boundedAfterBranch
    {bound register zeroTarget nonzeroTarget : ℕ}
    {state : NPOracleState}
    (hstate : StateBoundedBy bound state) :
    StateBoundedBy (Nat.pair bound bound)
      (state.jump (if state.registers register = 0 then
        zeroTarget else nonzeroTarget)) := by
  apply stateBoundedBy_mono (stateBoundedBy_jump hstate)
  exact bound_le_pairSelf bound

/-! ## Clocked one-step rules

These rules deliberately combine operational reduction with the register
invariant.  Compiler proofs can therefore chain exact instruction traces
without re-proving the same bounded-write side condition at every program
counter. -/

theorem runBranchZeroClocked
    {program : NPOracleProgram}
    {maximumBits fuel bound pc register zeroTarget nonzeroTarget : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? =
      some (.branchZero register zeroTarget nonzeroTarget))
    (hpc : state.pc = pc)
    (hstate : StateBoundedBy bound state) :
    let nextState :=
      state.jump (if state.registers register = 0 then
        zeroTarget else nonzeroTarget)
    runNPOracleProgram program maximumBits (fuel + 1) state =
        runNPOracleProgram program maximumBits fuel nextState ∧
      StateBoundedBy (Nat.pair bound bound) nextState := by
  dsimp only
  constructor
  · simp only [runNPOracleProgram]
    rw [hpc, hat]
  · exact boundedAfterBranch hstate

theorem runSetClocked
    {program : NPOracleProgram}
    {maximumBits fuel bound pc register value next : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.set register value next))
    (hpc : state.pc = pc)
    (hstate : StateBoundedBy bound state)
    (hvalue : value ≤ bound)
    (hbits :
      natBitLength (pairIter (fuel + 1) bound) ≤ maximumBits) :
    let nextState := (state.write register value).jump next
    runNPOracleProgram program maximumBits (fuel + 1) state =
        runNPOracleProgram program maximumBits fuel nextState ∧
      StateBoundedBy (Nat.pair bound bound) nextState := by
  dsimp only
  constructor
  · simp only [runNPOracleProgram]
    rw [hpc, hat]
    simp only
    rw [write_fits_pairClock
      (hvalue.trans (bound_le_pairSelf bound)) hbits]
  · exact boundedAfterSet hstate hvalue

theorem runCopyClocked
    {program : NPOracleProgram}
    {maximumBits fuel bound pc source destination next : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.copy source destination next))
    (hpc : state.pc = pc)
    (hstate : StateBoundedBy bound state)
    (hbits :
      natBitLength (pairIter (fuel + 1) bound) ≤ maximumBits) :
    let nextState :=
      (state.write destination (state.registers source)).jump next
    runNPOracleProgram program maximumBits (fuel + 1) state =
        runNPOracleProgram program maximumBits fuel nextState ∧
      StateBoundedBy (Nat.pair bound bound) nextState := by
  dsimp only
  constructor
  · simp only [runNPOracleProgram]
    rw [hpc, hat]
    simp only
    rw [write_fits_pairClock
      ((hstate source).trans (bound_le_pairSelf bound)) hbits]
  · exact boundedAfterCopy hstate

theorem runIncrementClocked
    {program : NPOracleProgram}
    {maximumBits fuel bound pc register next : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.increment register next))
    (hpc : state.pc = pc)
    (hstate : StateBoundedBy bound state)
    (hbound : 1 ≤ bound)
    (hbits :
      natBitLength (pairIter (fuel + 1) bound) ≤ maximumBits) :
    let nextState :=
      (state.write register (state.registers register + 1)).jump next
    runNPOracleProgram program maximumBits (fuel + 1) state =
        runNPOracleProgram program maximumBits fuel nextState ∧
      StateBoundedBy (Nat.pair bound bound) nextState := by
  dsimp only
  constructor
  · simp only [runNPOracleProgram]
    rw [hpc, hat]
    simp only
    rw [write_fits_pairClock
      (increment_le_pairSelf (hstate register) hbound) hbits]
  · exact boundedAfterIncrement hstate hbound

theorem runDecrementClocked
    {program : NPOracleProgram}
    {maximumBits fuel bound pc register next : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.decrement register next))
    (hpc : state.pc = pc)
    (hstate : StateBoundedBy bound state)
    (hbits :
      natBitLength (pairIter (fuel + 1) bound) ≤ maximumBits) :
    let nextState :=
      (state.write register (state.registers register).pred).jump next
    runNPOracleProgram program maximumBits (fuel + 1) state =
        runNPOracleProgram program maximumBits fuel nextState ∧
      StateBoundedBy (Nat.pair bound bound) nextState := by
  dsimp only
  constructor
  · simp only [runNPOracleProgram]
    rw [hpc, hat]
    simp only
    rw [write_fits_pairClock
      (predecessor_le_pairSelf (hstate register)) hbits]
  · exact boundedAfterDecrement hstate

theorem runPairClocked
    {program : NPOracleProgram}
    {maximumBits fuel bound pc left right destination next : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.pair left right destination next))
    (hpc : state.pc = pc)
    (hstate : StateBoundedBy bound state)
    (hbits :
      natBitLength (pairIter (fuel + 1) bound) ≤ maximumBits) :
    let nextState :=
      (state.write destination
        (Nat.pair (state.registers left) (state.registers right))).jump next
    runNPOracleProgram program maximumBits (fuel + 1) state =
        runNPOracleProgram program maximumBits fuel nextState ∧
      StateBoundedBy (Nat.pair bound bound) nextState := by
  dsimp only
  constructor
  · simp only [runNPOracleProgram]
    rw [hpc, hat]
    simp only
    rw [write_fits_pairClock
      (pair_mono (hstate left) (hstate right)) hbits]
  · exact boundedAfterPair hstate

theorem runUnpairLeftClocked
    {program : NPOracleProgram}
    {maximumBits fuel bound pc source destination next : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.unpairLeft source destination next))
    (hpc : state.pc = pc)
    (hstate : StateBoundedBy bound state)
    (hbits :
      natBitLength (pairIter (fuel + 1) bound) ≤ maximumBits) :
    let nextState :=
      (state.write destination
        (Nat.unpair (state.registers source)).1).jump next
    runNPOracleProgram program maximumBits (fuel + 1) state =
        runNPOracleProgram program maximumBits fuel nextState ∧
      StateBoundedBy (Nat.pair bound bound) nextState := by
  dsimp only
  constructor
  · simp only [runNPOracleProgram]
    rw [hpc, hat]
    simp only
    rw [write_fits_pairClock
      (unpairLeft_le_pairSelf (hstate source)) hbits]
  · exact boundedAfterUnpairLeft hstate

theorem runUnpairRightClocked
    {program : NPOracleProgram}
    {maximumBits fuel bound pc source destination next : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.unpairRight source destination next))
    (hpc : state.pc = pc)
    (hstate : StateBoundedBy bound state)
    (hbits :
      natBitLength (pairIter (fuel + 1) bound) ≤ maximumBits) :
    let nextState :=
      (state.write destination
        (Nat.unpair (state.registers source)).2).jump next
    runNPOracleProgram program maximumBits (fuel + 1) state =
        runNPOracleProgram program maximumBits fuel nextState ∧
      StateBoundedBy (Nat.pair bound bound) nextState := by
  dsimp only
  constructor
  · simp only [runNPOracleProgram]
    rw [hpc, hat]
    simp only
    rw [write_fits_pairClock
      (unpairRight_le_pairSelf (hstate source)) hbits]
  · exact boundedAfterUnpairRight hstate

theorem runShiftRightClocked
    {program : NPOracleProgram}
    {maximumBits fuel bound pc source amount destination next : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? =
      some (.shiftRight source amount destination next))
    (hpc : state.pc = pc)
    (hstate : StateBoundedBy bound state)
    (hbits :
      natBitLength (pairIter (fuel + 1) bound) ≤ maximumBits) :
    let nextState :=
      (state.write destination
        (Nat.shiftRight (state.registers source) amount)).jump next
    runNPOracleProgram program maximumBits (fuel + 1) state =
        runNPOracleProgram program maximumBits fuel nextState ∧
      StateBoundedBy (Nat.pair bound bound) nextState := by
  dsimp only
  constructor
  · simp only [runNPOracleProgram]
    rw [hpc, hat]
    simp only
    rw [write_fits_pairClock
      (shiftRight_le_pairSelf (hstate source)) hbits]
  · exact boundedAfterShiftRight hstate

theorem runHaltClocked
    {program : NPOracleProgram}
    {maximumBits bound pc outputRegister : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.halt outputRegister))
    (hpc : state.pc = pc)
    (hstate : StateBoundedBy bound state)
    (hbits : natBitLength (pairIter 1 bound) ≤ maximumBits) :
    runNPOracleProgram program maximumBits 1 state =
      some (state.registers outputRegister) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [if_pos]
  exact
    (natBitLength_mono
      ((hstate outputRegister).trans
        (value_le_pairIter 1 bound))).trans hbits

end NearCubicWires.RegisterBounds
