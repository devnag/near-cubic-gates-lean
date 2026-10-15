import Proof.Foundations.VerifiedLinker

/-!
# Canonical callable-program relocation

A fixed callee can be embedded in a larger controller while preserving its
interpreter trace, isolating its register bank, and replacing its halt with one
accumulating return.  This module is independent of any sequence encoding or
controller, so the balanced public ABI and other fixed callers share one
relocation proof.
-/

namespace NearCubicWires.CallableRelocation

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

def callableInstruction (pcOffset registerOffset accumulatorRegister
    returnPc : ℕ) : NPOracleInstruction → NPOracleInstruction
  | .halt output =>
      .pair accumulatorRegister (registerOffset + output)
        accumulatorRegister returnPc
  | instruction => relocateInstruction pcOffset registerOffset instruction

def ProgramCallableAt (whole source : NPOracleProgram)
    (pcOffset registerOffset accumulatorRegister returnPc : ℕ) : Prop :=
  ∀ pc instruction, source[pc]? = some instruction →
    whole[pcOffset + pc]? =
      some (callableInstruction pcOffset registerOffset accumulatorRegister
        returnPc instruction)

@[simp] theorem callableInstruction_sat (pcOffset registerOffset
    accumulatorRegister returnPc : ℕ) (instruction : NPOracleInstruction) :
    (match callableInstruction pcOffset registerOffset accumulatorRegister
        returnPc instruction with
      | .sat _ _ _ => true
      | _ => false) =
    (match instruction with
      | .sat _ _ _ => true
      | _ => false) := by
  cases instruction <;> rfl

theorem any_callableInstruction (program : NPOracleProgram)
    (pcOffset registerOffset accumulatorRegister returnPc : ℕ) :
    program.any (fun instruction =>
      match callableInstruction pcOffset registerOffset accumulatorRegister
          returnPc instruction with
      | .sat _ _ _ => true
      | _ => false) =
    program.any (fun instruction => match instruction with
      | .sat _ _ _ => true
      | _ => false) := by
  induction program with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.any_cons]
      rw [ih]
      cases instruction <;> rfl

theorem relocateState_below {pcOffset registerOffset candidate : ℕ}
    {lowerRegisters : ℕ → ℕ} {state : NPOracleState}
    (hbelow : candidate < registerOffset) :
    (relocateState pcOffset registerOffset lowerRegisters state).registers
      candidate = lowerRegisters candidate := by
  simp [relocateState, show ¬registerOffset ≤ candidate by omega]

theorem run_callable {whole source : NPOracleProgram}
    {pcOffset registerOffset accumulatorRegister returnPc maximumBits fuel
      output extraFuel finalOutput : ℕ}
    {state : NPOracleState} (lowerRegisters : ℕ → ℕ)
    (haccumulator : accumulatorRegister < registerOffset)
    (hat : ProgramCallableAt whole source pcOffset registerOffset
      accumulatorRegister returnPc)
    (hexec :
      runNPOracleProgram source maximumBits fuel state = some output)
    (hpairBits :
      natBitLength (Nat.pair (lowerRegisters accumulatorRegister) output) ≤
        maximumBits)
    (hreturn : ∀ (haltState : NPOracleState) (unused : ℕ),
      runNPOracleProgram whole maximumBits (unused + extraFuel)
        (((relocateState pcOffset registerOffset lowerRegisters haltState).write
          accumulatorRegister
            (Nat.pair (lowerRegisters accumulatorRegister) output)).jump
              returnPc) = some finalOutput) :
    runNPOracleProgram whole maximumBits (fuel + extraFuel)
      (relocateState pcOffset registerOffset lowerRegisters state) =
        some finalOutput := by
  induction fuel generalizing state lowerRegisters with
  | zero => simp [runNPOracleProgram] at hexec
  | succ fuel ih =>
      rw [show fuel + 1 + extraFuel = (fuel + extraFuel) + 1 by omega]
      simp only [runNPOracleProgram] at hexec ⊢
      cases hlookup : source[state.pc]? with
      | none => simp [hlookup] at hexec
      | some instruction =>
          have hwhole := hat state.pc instruction hlookup
          rw [hlookup] at hexec
          rw [relocateState_pc, hwhole]
          cases instruction with
          | halt outputRegister =>
              simp only [callableInstruction] at hexec ⊢
              rw [relocateState_below haccumulator,
                relocateState_register]
              rcases (by simpa using hexec) with ⟨_, houtput⟩
              subst output
              have hwrite :
                  (relocateState pcOffset registerOffset lowerRegisters
                    state).boundedWrite maximumBits accumulatorRegister
                      (Nat.pair (lowerRegisters accumulatorRegister)
                        (state.registers outputRegister)) =
                    some ((relocateState pcOffset registerOffset lowerRegisters
                      state).write accumulatorRegister
                        (Nat.pair (lowerRegisters accumulatorRegister)
                          (state.registers outputRegister))) := by
                simp [NPOracleState.boundedWrite, hpairBits]
              rw [hwrite]
              exact hreturn state fuel
          | set register value next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits register value with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec hpairBits hreturn
          | copy sourceRegister destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers sourceRegister) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite,
                    hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec hpairBits hreturn
          | increment register next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register + 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite,
                    hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec hpairBits hreturn
          | decrement register next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              rw [Nat.pred_eq_sub_one] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register - 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite,
                    hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec hpairBits hreturn
          | add left right destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left + state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_register,
                    relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec hpairBits hreturn
          | subtract left right destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left - state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_register,
                    relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec hpairBits hreturn
          | pair left right destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.pair (state.registers left) (state.registers right)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_register,
                    relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec hpairBits hreturn
          | unpairLeft sourceRegister destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers sourceRegister)).1 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite,
                    hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec hpairBits hreturn
          | unpairRight sourceRegister destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers sourceRegister)).2 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite,
                    hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec hpairBits hreturn
          | branchZero register zeroTarget nonzeroTarget =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              rw [relocateState_register]
              by_cases hzero : state.registers register = 0
              · simp only [if_pos hzero] at hexec ⊢
                rw [relocateState_jump]
                exact ih lowerRegisters hexec hpairBits hreturn
              · simp only [if_neg hzero] at hexec ⊢
                rw [relocateState_jump]
                exact ih lowerRegisters hexec hpairBits hreturn
          | encodeNat sourceRegister destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (CanonicalBinary.encodeNat
                    (state.registers sourceRegister)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite,
                    hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec hpairBits hreturn
          | shiftRight sourceRegister amount destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                rw [relocateState_register, relocateState_boundedWrite,
                  hwrite]
                simp only [Option.map]
                rw [relocateState_jump]
                exact ih lowerRegisters hexec hpairBits hreturn
          | shiftLeft sourceRegister amount destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                rw [relocateState_register, relocateState_boundedWrite,
                  hwrite]
                simp only [Option.map]
                rw [relocateState_jump]
                exact ih lowerRegisters hexec hpairBits hreturn
          | testBit sourceRegister indexRegister destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              rw [relocateState_register, relocateState_register]
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                rw [relocateState_boundedWrite, hwrite]
                simp only [Option.map]
                rw [relocateState_jump]
                exact ih lowerRegisters hexec hpairBits hreturn
          | sat query destination next =>
              simp only [callableInstruction, relocateInstruction] at hexec ⊢
              rw [relocateState_register]
              split at hexec
              · rename_i hquery
                rw [if_pos hquery]
                cases hwrite : state.boundedWrite maximumBits destination
                    (encodedSat (state.registers query)).toNat with
                | none => simp [hwrite] at hexec
                | some nextState =>
                    simp only [hwrite] at hexec
                    rw [relocateState_boundedWrite, hwrite]
                    simp only [Option.map]
                    rw [relocateState_jump]
                    exact ih lowerRegisters hexec hpairBits hreturn
              · simp at hexec

def StateAgreesBelow (span : ℕ) (left right : NPOracleState) : Prop :=
  left.pc = right.pc ∧
    ∀ register, register < span →
      left.registers register = right.registers register

theorem stateAgreesBelow_write {span : ℕ} {left right : NPOracleState}
    (hagrees : StateAgreesBelow span left right) (register value : ℕ) :
    StateAgreesBelow span (left.write register value)
      (right.write register value) := by
  refine ⟨hagrees.1, ?_⟩
  intro candidate _
  simp only [NPOracleState.write]
  split
  · rfl
  · exact hagrees.2 candidate (by assumption)

theorem stateAgreesBelow_jump {span : ℕ} {left right : NPOracleState}
    (hagrees : StateAgreesBelow span left right) (pc : ℕ) :
    StateAgreesBelow span (left.jump pc) (right.jump pc) := by
  exact ⟨rfl, hagrees.2⟩

theorem run_congr_of_stateAgreesBelow {program : NPOracleProgram}
    {span maximumBits fuel : ℕ} {left right : NPOracleState}
    (hspan : programRegisterSpan program ≤ span)
    (hagrees : StateAgreesBelow span left right) :
    runNPOracleProgram program maximumBits fuel left =
      runNPOracleProgram program maximumBits fuel right := by
  induction fuel generalizing left right with
  | zero => rfl
  | succ fuel ih =>
      simp only [runNPOracleProgram]
      cases hlookup : program[left.pc]? with
      | none =>
          have hright : program[right.pc]? = none := by
            rw [← hagrees.1]
            exact hlookup
          rw [hright]
      | some instruction =>
          have hright : program[right.pc]? = some instruction := by
            rw [← hagrees.1]
            exact hlookup
          have hmem : instruction ∈ program := List.mem_of_getElem? hlookup
          rw [hright]
          cases instruction with
          | halt output =>
              simp only
              have houtput : output < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 output houtput]
          | set register value next =>
              simp only
              by_cases hbits : natBitLength value ≤ maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits,
                  ]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees register value) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | copy source destination next =>
              simp only
              have hsource : source < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 source hsource]
              by_cases hbits :
                  natBitLength (right.registers source) ≤ maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits,
                  ]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees destination
                      (right.registers source)) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | increment register next =>
              simp only
              have hregister : register < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 register hregister]
              by_cases hbits :
                  natBitLength (right.registers register + 1) ≤ maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits,
                  ]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees register
                      (right.registers register + 1)) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | decrement register next =>
              simp only
              simp only [Nat.pred_eq_sub_one]
              have hregister : register < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 register hregister]
              by_cases hbits :
                  natBitLength (right.registers register - 1) ≤
                    maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees register
                      (right.registers register - 1)) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | add leftRegister rightRegister destination next =>
              simp only
              have hleft : leftRegister < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              have hrightRegister : rightRegister < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 leftRegister hleft,
                hagrees.2 rightRegister hrightRegister]
              by_cases hbits :
                  natBitLength (right.registers leftRegister +
                    right.registers rightRegister) ≤ maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees destination
                      (right.registers leftRegister +
                        right.registers rightRegister)) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | subtract leftRegister rightRegister destination next =>
              simp only
              have hleft : leftRegister < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              have hrightRegister : rightRegister < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 leftRegister hleft,
                hagrees.2 rightRegister hrightRegister]
              by_cases hbits :
                  natBitLength (right.registers leftRegister -
                    right.registers rightRegister) ≤ maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees destination
                      (right.registers leftRegister -
                        right.registers rightRegister)) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | pair leftRegister rightRegister destination next =>
              simp only
              have hleft : leftRegister < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              have hrightRegister : rightRegister < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 leftRegister hleft,
                hagrees.2 rightRegister hrightRegister]
              by_cases hbits :
                  natBitLength (Nat.pair (right.registers leftRegister)
                    (right.registers rightRegister)) ≤ maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits,
                  ]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees destination
                      (Nat.pair (right.registers leftRegister)
                        (right.registers rightRegister))) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | unpairLeft source destination next =>
              simp only
              have hsource : source < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 source hsource]
              by_cases hbits :
                  natBitLength (Nat.unpair (right.registers source)).1 ≤
                    maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits,
                  ]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees destination
                      (Nat.unpair (right.registers source)).1) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | unpairRight source destination next =>
              simp only
              have hsource : source < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 source hsource]
              by_cases hbits :
                  natBitLength (Nat.unpair (right.registers source)).2 ≤
                    maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits,
                  ]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees destination
                      (Nat.unpair (right.registers source)).2) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | branchZero register zeroTarget nonzeroTarget =>
              simp only
              have hregister : register < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 register hregister]
              exact ih (stateAgreesBelow_jump hagrees _)
          | encodeNat source destination next =>
              simp only
              have hsource : source < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 source hsource]
              by_cases hbits :
                  natBitLength
                      (CanonicalBinary.encodeNat (right.registers source)) ≤
                    maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees destination
                      (CanonicalBinary.encodeNat (right.registers source))) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | shiftRight source amount destination next =>
              simp only
              have hsource : source < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 source hsource]
              let shifted := Nat.shiftRight (right.registers source) amount
              change
                (match left.boundedWrite maximumBits destination shifted with
                | none => none
                | some nextState =>
                    runNPOracleProgram program maximumBits fuel
                      (nextState.jump next)) =
                (match right.boundedWrite maximumBits destination shifted with
                | none => none
                | some nextState =>
                    runNPOracleProgram program maximumBits fuel
                      (nextState.jump next))
              by_cases hbits : natBitLength shifted ≤ maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees destination shifted) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | shiftLeft source amount destination next =>
              simp only
              have hsource : source < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 source hsource]
              let shifted := Nat.shiftLeft (right.registers source) amount
              change
                (match left.boundedWrite maximumBits destination shifted with
                | none => none
                | some nextState =>
                    runNPOracleProgram program maximumBits fuel
                      (nextState.jump next)) =
                (match right.boundedWrite maximumBits destination shifted with
                | none => none
                | some nextState =>
                    runNPOracleProgram program maximumBits fuel
                      (nextState.jump next))
              by_cases hbits : natBitLength shifted ≤ maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees destination shifted) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | testBit source index destination next =>
              simp only
              have hsource : source < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              have hindex : index < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 source hsource, hagrees.2 index hindex]
              let bit :=
                ((right.registers source).testBit
                  (right.registers index)).toNat
              change
                (match left.boundedWrite maximumBits destination bit with
                | none => none
                | some nextState =>
                    runNPOracleProgram program maximumBits fuel
                      (nextState.jump next)) =
                (match right.boundedWrite maximumBits destination bit with
                | none => none
                | some nextState =>
                    runNPOracleProgram program maximumBits fuel
                      (nextState.jump next))
              by_cases hbits : natBitLength bit ≤ maximumBits
              · simp only [NPOracleState.boundedWrite, if_pos hbits]
                exact ih
                  (stateAgreesBelow_jump
                    (stateAgreesBelow_write hagrees destination bit) next)
              · simp [NPOracleState.boundedWrite, hbits]
          | sat query destination next =>
              simp only
              have hquery : query < span := lt_of_lt_of_le
                (register_lt_programRegisterSpan hmem (by
                  simp [instructionRegisters])) hspan
              rw [hagrees.2 query hquery]
              by_cases hqueryBits :
                  natBitLength (right.registers query) ≤ maximumBits
              · simp only [if_pos hqueryBits]
                by_cases hbits :
                    natBitLength (encodedSat (right.registers query)).toNat ≤
                      maximumBits
                · simp only [NPOracleState.boundedWrite, if_pos hbits,
                    ]
                  exact ih
                    (stateAgreesBelow_jump
                      (stateAgreesBelow_write hagrees destination
                        (encodedSat (right.registers query)).toNat) next)
                · simp [NPOracleState.boundedWrite, hbits]
              · simp only [if_neg hqueryBits]

def extendUpperRegisters (span registerOffset : ℕ)
    (background : ℕ → ℕ) (state : NPOracleState) : NPOracleState where
  pc := state.pc
  registers := fun register =>
    if register < span then state.registers register
    else background (registerOffset + register)

def relocateActiveState (pcOffset registerOffset span : ℕ)
    (background : ℕ → ℕ) (state : NPOracleState) : NPOracleState where
  pc := pcOffset + state.pc
  registers := fun candidate =>
    if registerOffset ≤ candidate ∧ candidate < registerOffset + span then
      state.registers (candidate - registerOffset)
    else background candidate

theorem state_ext (left right : NPOracleState)
    (hpc : left.pc = right.pc)
    (hregisters : left.registers = right.registers) :
    left = right := by
  cases left
  cases right
  simp_all

theorem stateAgreesBelow_extendUpperRegisters (span registerOffset : ℕ)
    (background : ℕ → ℕ) (state : NPOracleState) :
    StateAgreesBelow span state
      (extendUpperRegisters span registerOffset background state) := by
  refine ⟨rfl, ?_⟩
  intro register hregister
  simp [extendUpperRegisters, hregister]

theorem relocateState_extendUpperRegisters (pcOffset registerOffset span : ℕ)
    (background : ℕ → ℕ) (state : NPOracleState) :
    relocateState pcOffset registerOffset background
        (extendUpperRegisters span registerOffset background state) =
      relocateActiveState pcOffset registerOffset span background state := by
  apply state_ext
  · rfl
  · funext candidate
    by_cases hlower : registerOffset ≤ candidate
    · by_cases hupper : candidate < registerOffset + span
      · have hsub : candidate - registerOffset < span := by omega
        simp [relocateState, relocateActiveState, extendUpperRegisters,
          hlower, hupper, hsub]
      · have hsub : ¬candidate - registerOffset < span := by omega
        simp [relocateState, relocateActiveState, extendUpperRegisters,
          hlower, hupper, hsub]
    · simp [relocateState, relocateActiveState, hlower]

theorem run_callable_active {whole source : NPOracleProgram}
    {pcOffset registerOffset span accumulatorRegister returnPc maximumBits fuel
      output extraFuel finalOutput : ℕ}
    {state : NPOracleState} (background : ℕ → ℕ)
    (haccumulator : accumulatorRegister < registerOffset)
    (hspan : programRegisterSpan source ≤ span)
    (hat : ProgramCallableAt whole source pcOffset registerOffset
      accumulatorRegister returnPc)
    (hexec :
      runNPOracleProgram source maximumBits fuel state = some output)
    (hpairBits :
      natBitLength (Nat.pair (background accumulatorRegister) output) ≤
        maximumBits)
    (hreturn : ∀ (haltState : NPOracleState) (unused : ℕ),
      runNPOracleProgram whole maximumBits (unused + extraFuel)
        (((relocateState pcOffset registerOffset background haltState).write
          accumulatorRegister
            (Nat.pair (background accumulatorRegister) output)).jump
              returnPc) = some finalOutput) :
    runNPOracleProgram whole maximumBits (fuel + extraFuel)
      (relocateActiveState pcOffset registerOffset span background state) =
        some finalOutput := by
  let extended :=
    extendUpperRegisters span registerOffset background state
  have hextended :
      runNPOracleProgram source maximumBits fuel extended = some output := by
    rw [← hexec]
    exact (run_congr_of_stateAgreesBelow hspan
      (stateAgreesBelow_extendUpperRegisters span registerOffset background
        state)).symm
  rw [← relocateState_extendUpperRegisters pcOffset registerOffset span
    background state]
  apply run_callable background haccumulator hat hextended hpairBits
  exact hreturn

end NearCubicWires.CallableRelocation
