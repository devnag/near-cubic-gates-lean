import Proof.Foundations.ExecutableInterfaces

/-!
# Verified linker for the fixed NP-oracle register machine

Control-flow targets in `NPOracleProgram` are absolute, so concatenating lists
is unsound.  This module relocates targets, isolates stage registers, preserves
the public input length, and makes the inter-stage transfer explicit.
-/

namespace NearCubicWires.VerifiedLinker

open NearCubicWires
open NearCubicWires.ExecutableInterfaces

/-! ## Interpreter budget monotonicity -/

theorem boundedWrite_bits_mono
    {state nextState : NPOracleState} {oldBits newBits register value : ℕ}
    (hexec : state.boundedWrite oldBits register value = some nextState)
    (hbits : oldBits ≤ newBits) :
    state.boundedWrite newBits register value = some nextState := by
  simp only [NPOracleState.boundedWrite] at hexec ⊢
  split at hexec
  · rename_i hold
    simp only [Option.some.injEq] at hexec
    subst nextState
    simp [le_trans hold hbits]
  · simp at hexec

/-- Increasing the register-width budget cannot change a successful trace.
This belongs beside the interpreter linker because linked stages run at one
shared width, commonly the maximum of their independently proved widths. -/
theorem run_bits_mono
    {program : NPOracleProgram} {oldBits newBits fuel : ℕ}
    {state : NPOracleState} {output : ℕ}
    (hexec : runNPOracleProgram program oldBits fuel state = some output)
    (hbits : oldBits ≤ newBits) :
    runNPOracleProgram program newBits fuel state = some output := by
  induction fuel generalizing state with
  | zero =>
      simp [runNPOracleProgram] at hexec
  | succ fuel ih =>
      simp only [runNPOracleProgram] at hexec ⊢
      split at hexec
      · simp at hexec
      · split at hexec
        · rename_i hold
          simpa [le_trans hold hbits] using hexec
        · simp at hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · simp at hexec
        · rename_i nextState hwrite
          rw [boundedWrite_bits_mono hwrite hbits]
          exact ih hexec
      · split at hexec
        · rename_i hquery
          split at hexec
          · simp at hexec
          · rename_i nextState hwrite
            rw [if_pos (le_trans hquery hbits),
              boundedWrite_bits_mono hwrite hbits]
            exact ih hexec
        · simp at hexec

def instructionRegisters : NPOracleInstruction → List ℕ
  | .halt output => [output]
  | .set register _ _ => [register]
  | .copy source destination _ => [source, destination]
  | .increment register _ => [register]
  | .decrement register _ => [register]
  | .add left right destination _ => [left, right, destination]
  | .subtract left right destination _ => [left, right, destination]
  | .pair left right destination _ => [left, right, destination]
  | .unpairLeft source destination _ => [source, destination]
  | .unpairRight source destination _ => [source, destination]
  | .branchZero register _ _ => [register]
  | .encodeNat source destination _ => [source, destination]
  | .shiftRight source _ destination _ => [source, destination]
  | .shiftLeft source _ destination _ => [source, destination]
  | .testBit source index destination _ => [source, index, destination]
  | .sat query destination _ => [query, destination]

def instructionRegisterSpan (instruction : NPOracleInstruction) : ℕ :=
  (instructionRegisters instruction).foldr max 0 + 1

def programRegisterSpan : NPOracleProgram → ℕ
  | [] => 2
  | instruction :: rest =>
      max (instructionRegisterSpan instruction) (programRegisterSpan rest)

private theorem register_le_foldr_max {register : ℕ} {registers : List ℕ}
    (hmem : register ∈ registers) :
    register ≤ registers.foldr max 0 := by
  induction registers with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact le_max_left _ _
      · exact le_trans (ih hmem) (le_max_right _ _)

theorem instructionRegisterSpan_le_programRegisterSpan
    {instruction : NPOracleInstruction} {program : NPOracleProgram}
    (hmem : instruction ∈ program) :
    instructionRegisterSpan instruction ≤ programRegisterSpan program := by
  induction program with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [programRegisterSpan]
      rcases hmem with rfl | hmem
      · exact le_max_left _ _
      · exact le_trans (ih hmem) (le_max_right _ _)

theorem register_lt_programRegisterSpan
    {program : NPOracleProgram} {instruction : NPOracleInstruction}
    (hinstruction : instruction ∈ program) {register : ℕ}
    (hregister : register ∈ instructionRegisters instruction) :
    register < programRegisterSpan program := by
  exact lt_of_lt_of_le
    (Nat.lt_succ_of_le (register_le_foldr_max hregister))
    (instructionRegisterSpan_le_programRegisterSpan hinstruction)

def relocateInstruction (pcOffset registerOffset : ℕ) :
    NPOracleInstruction → NPOracleInstruction
  | .halt output => .halt (registerOffset + output)
  | .set register value next =>
      .set (registerOffset + register) value (pcOffset + next)
  | .copy source destination next =>
      .copy (registerOffset + source) (registerOffset + destination)
        (pcOffset + next)
  | .increment register next =>
      .increment (registerOffset + register) (pcOffset + next)
  | .decrement register next =>
      .decrement (registerOffset + register) (pcOffset + next)
  | .add left right destination next =>
      .add (registerOffset + left) (registerOffset + right)
        (registerOffset + destination) (pcOffset + next)
  | .subtract left right destination next =>
      .subtract (registerOffset + left) (registerOffset + right)
        (registerOffset + destination) (pcOffset + next)
  | .pair left right destination next =>
      .pair (registerOffset + left) (registerOffset + right)
        (registerOffset + destination) (pcOffset + next)
  | .unpairLeft source destination next =>
      .unpairLeft (registerOffset + source) (registerOffset + destination)
        (pcOffset + next)
  | .unpairRight source destination next =>
      .unpairRight (registerOffset + source) (registerOffset + destination)
        (pcOffset + next)
  | .branchZero register zeroTarget nonzeroTarget =>
      .branchZero (registerOffset + register)
        (pcOffset + zeroTarget) (pcOffset + nonzeroTarget)
  | .encodeNat source destination next =>
      .encodeNat (registerOffset + source) (registerOffset + destination)
        (pcOffset + next)
  | .shiftRight source amount destination next =>
      .shiftRight (registerOffset + source) amount
        (registerOffset + destination) (pcOffset + next)
  | .shiftLeft source amount destination next =>
      .shiftLeft (registerOffset + source) amount
        (registerOffset + destination) (pcOffset + next)
  | .testBit source index destination next =>
      .testBit (registerOffset + source) (registerOffset + index)
        (registerOffset + destination) (pcOffset + next)
  | .sat query destination next =>
      .sat (registerOffset + query) (registerOffset + destination)
        (pcOffset + next)

def continueInstruction (pcOffset transferRegister resetPc : ℕ) :
    NPOracleInstruction → NPOracleInstruction
  | .halt output => .copy output transferRegister resetPc
  | .set register value next => .set register value (pcOffset + next)
  | .copy source destination next =>
      .copy source destination (pcOffset + next)
  | .increment register next => .increment register (pcOffset + next)
  | .decrement register next => .decrement register (pcOffset + next)
  | .add left right destination next =>
      .add left right destination (pcOffset + next)
  | .subtract left right destination next =>
      .subtract left right destination (pcOffset + next)
  | .pair left right destination next =>
      .pair left right destination (pcOffset + next)
  | .unpairLeft source destination next =>
      .unpairLeft source destination (pcOffset + next)
  | .unpairRight source destination next =>
      .unpairRight source destination (pcOffset + next)
  | .branchZero register zeroTarget nonzeroTarget =>
      .branchZero register (pcOffset + zeroTarget) (pcOffset + nonzeroTarget)
  | .encodeNat source destination next =>
      .encodeNat source destination (pcOffset + next)
  | .shiftRight source amount destination next =>
      .shiftRight source amount destination (pcOffset + next)
  | .shiftLeft source amount destination next =>
      .shiftLeft source amount destination (pcOffset + next)
  | .testBit source index destination next =>
      .testBit source index destination (pcOffset + next)
  | .sat query destination next => .sat query destination (pcOffset + next)

def resetRegisters (firstRegister count startPc : ℕ) : NPOracleProgram :=
  (List.range count).map fun index =>
    .set (firstRegister + index) 0 (startPc + index + 1)

@[simp] theorem resetRegisters_length (firstRegister count startPc : ℕ) :
    (resetRegisters firstRegister count startPc).length = count := by
  simp [resetRegisters]

structure LinkLayout where
  firstSpan : ℕ
  secondSpan : ℕ
  firstBase : ℕ
  resetBase : ℕ
  secondBase : ℕ
  secondRegisterBase : ℕ
  savedLengthRegister : ℕ
  transferRegister : ℕ

theorem two_le_programRegisterSpan (program : NPOracleProgram) :
    2 ≤ programRegisterSpan program := by
  induction program with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [programRegisterSpan]
      exact le_trans ih (le_max_right _ _)

def linkLayout (first second : NPOracleProgram) : LinkLayout :=
  let firstSpan := programRegisterSpan first
  let secondSpan := programRegisterSpan second
  let firstBase := 1
  let resetBase := firstBase + first.length
  let secondBase := resetBase + secondSpan + 4
  { firstSpan
    secondSpan
    firstBase
    resetBase
    secondBase
    secondRegisterBase := firstSpan
    savedLengthRegister := firstSpan + secondSpan
    transferRegister := firstSpan + secondSpan + 1 }

/-- Both stages receive the same public input length.  The first output becomes
the second stage's register-zero request code. -/
def linkPrograms (first second : NPOracleProgram) : NPOracleProgram :=
  let layout := linkLayout first second
  [.copy 1 layout.savedLengthRegister layout.firstBase] ++
    first.map (continueInstruction layout.firstBase
      layout.transferRegister layout.resetBase) ++
    resetRegisters layout.secondRegisterBase layout.secondSpan layout.resetBase ++
    [.copy layout.transferRegister layout.secondRegisterBase
        (layout.resetBase + layout.secondSpan + 1),
      .copy layout.savedLengthRegister (layout.secondRegisterBase + 1)
        (layout.resetBase + layout.secondSpan + 2),
      .set layout.transferRegister 0
        (layout.resetBase + layout.secondSpan + 3),
      .set layout.savedLengthRegister 0 layout.secondBase] ++
    second.map (relocateInstruction layout.secondBase
      layout.secondRegisterBase)

def containsSAT (program : NPOracleProgram) : Bool :=
  program.any fun instruction => match instruction with
    | .sat _ _ _ => true
    | _ => false

@[simp] theorem containsSAT_relocateInstruction (pcOffset registerOffset : ℕ)
    (instruction : NPOracleInstruction) :
    (match relocateInstruction pcOffset registerOffset instruction with
      | .sat _ _ _ => true
      | _ => false) =
    (match instruction with
      | .sat _ _ _ => true
      | _ => false) := by
  cases instruction <;> rfl

@[simp] theorem containsSAT_continueInstruction
    (pcOffset transferRegister resetPc : ℕ)
    (instruction : NPOracleInstruction) :
    (match continueInstruction pcOffset transferRegister resetPc instruction with
      | .sat _ _ _ => true
      | _ => false) =
    (match instruction with
      | .sat _ _ _ => true
      | _ => false) := by
  cases instruction <;> rfl

private theorem any_const_false {α : Type} (values : List α) :
    values.any (fun _ => false) = false := by
  induction values with
  | nil => rfl
  | cons _ tail ih => simp [ih]

theorem containsSAT_linkPrograms (first second : NPOracleProgram) :
    containsSAT (linkPrograms first second) =
      (containsSAT first || containsSAT second) := by
  simp [containsSAT, linkPrograms, resetRegisters, List.any_append,
    Function.comp_def, any_const_false]

theorem oracleFree_iff_containsSAT_false (program : NPOracleProgram) :
    OracleFree program ↔ containsSAT program = false := by
  rw [OracleFree, List.all_eq_true, containsSAT, List.any_eq_false]
  constructor
  · intro hfree instruction hmem
    have h := hfree instruction hmem
    cases instruction <;> simp_all
  · intro hfree instruction hmem
    have h := hfree instruction hmem
    cases instruction <;> simp_all

theorem oracleFree_linkPrograms {first second : NPOracleProgram}
    (hfirst : OracleFree first) (hsecond : OracleFree second) :
    OracleFree (linkPrograms first second) := by
  rw [oracleFree_iff_containsSAT_false, containsSAT_linkPrograms,
    Bool.or_eq_false_iff]
  exact ⟨(oracleFree_iff_containsSAT_false first).mp hfirst,
    (oracleFree_iff_containsSAT_false second).mp hsecond⟩

def ProgramRelocatedAt (whole source : NPOracleProgram)
    (pcOffset registerOffset : ℕ) : Prop :=
  ∀ pc instruction, source[pc]? = some instruction →
    whole[pcOffset + pc]? =
      some (relocateInstruction pcOffset registerOffset instruction)

def ProgramContinuedAt (whole source : NPOracleProgram)
    (pcOffset transferRegister resetPc : ℕ) : Prop :=
  ∀ pc instruction, source[pc]? = some instruction →
    whole[pcOffset + pc]? =
      some (continueInstruction pcOffset transferRegister resetPc instruction)

def ResetProgramAt (whole : NPOracleProgram)
    (firstRegister count startPc : ℕ) : Prop :=
  ∀ index, index < count →
    whole[startPc + index]? =
      some (.set (firstRegister + index) 0 (startPc + index + 1))

theorem linkPrograms_firstAt (first second : NPOracleProgram) :
    ProgramContinuedAt (linkPrograms first second) first
      (linkLayout first second).firstBase
      (linkLayout first second).transferRegister
      (linkLayout first second).resetBase := by
  intro pc instruction hlookup
  have hpc : pc < first.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [linkPrograms, linkLayout]
  rw [show 1 + pc = pc + 1 by omega]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map, resetRegisters_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map, resetRegisters_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_cons, List.length_nil]
  rw [show pc + 1 - 1 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem linkPrograms_secondAt (first second : NPOracleProgram) :
    ProgramRelocatedAt (linkPrograms first second) second
      (linkLayout first second).secondBase
      (linkLayout first second).secondRegisterBase := by
  intro pc instruction hlookup
  have hpc : pc < second.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [linkPrograms, linkLayout]
  rw [show 1 + first.length + programRegisterSpan second + 4 + pc =
      (first.length + programRegisterSpan second + 4 + pc) + 1 by omega,
    List.getElem?_append_right (by
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_map, resetRegisters_length]
      omega)]
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_map, resetRegisters_length]
  rw [show first.length + programRegisterSpan second + 4 + pc + 1 -
      (1 + first.length + programRegisterSpan second + 4) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem linkPrograms_resetAt (first second : NPOracleProgram) :
    ResetProgramAt (linkPrograms first second)
      (linkLayout first second).secondRegisterBase
      (linkLayout first second).secondSpan
      (linkLayout first second).resetBase := by
  intro index hindex
  change index < programRegisterSpan second at hindex
  simp only [linkPrograms, linkLayout]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map, resetRegisters_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map, resetRegisters_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_map]
  rw [show 1 + first.length + index - (1 + first.length) = index by omega]
  simp only [resetRegisters, List.getElem?_map]
  rw [List.getElem?_range hindex]
  rfl

theorem linkPrograms_plumbingAt (first second : NPOracleProgram)
    (index : ℕ) (hindex : index < 4) :
    (linkPrograms first second)[
      (linkLayout first second).resetBase +
        (linkLayout first second).secondSpan + index]? =
      ([
        .copy (linkLayout first second).transferRegister
          (linkLayout first second).secondRegisterBase
          ((linkLayout first second).resetBase +
            (linkLayout first second).secondSpan + 1),
        .copy (linkLayout first second).savedLengthRegister
          ((linkLayout first second).secondRegisterBase + 1)
          ((linkLayout first second).resetBase +
            (linkLayout first second).secondSpan + 2),
        .set (linkLayout first second).transferRegister 0
          ((linkLayout first second).resetBase +
            (linkLayout first second).secondSpan + 3),
        .set (linkLayout first second).savedLengthRegister 0
          (linkLayout first second).secondBase
      ] : NPOracleProgram)[index]? := by
  simp only [linkPrograms, linkLayout]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map, resetRegisters_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map, resetRegisters_length]
    omega)]
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_map, resetRegisters_length]
  rw [show 1 + first.length + programRegisterSpan second + index -
      (1 + first.length + programRegisterSpan second) = index by omega]

def relocateState (pcOffset registerOffset : ℕ)
    (lowerRegisters : ℕ → ℕ) (state : NPOracleState) : NPOracleState where
  pc := pcOffset + state.pc
  registers := fun candidate =>
    if registerOffset ≤ candidate then
      state.registers (candidate - registerOffset)
    else lowerRegisters candidate

@[simp] theorem relocateState_pc (pcOffset registerOffset : ℕ)
    (lowerRegisters : ℕ → ℕ) (state : NPOracleState) :
    (relocateState pcOffset registerOffset lowerRegisters state).pc =
      pcOffset + state.pc := rfl

@[simp] theorem relocateState_register
    (pcOffset registerOffset register : ℕ)
    (lowerRegisters : ℕ → ℕ) (state : NPOracleState) :
    (relocateState pcOffset registerOffset lowerRegisters state).registers
      (registerOffset + register) = state.registers register := by
  simp [relocateState]

theorem relocateState_write (pcOffset registerOffset register value : ℕ)
    (lowerRegisters : ℕ → ℕ) (state : NPOracleState) :
    (relocateState pcOffset registerOffset lowerRegisters state).write
        (registerOffset + register) value =
      relocateState pcOffset registerOffset lowerRegisters
        (state.write register value) := by
  cases state with
  | mk statePc stateRegisters =>
    simp only [NPOracleState.write, relocateState]
    congr 1
    funext candidate
    by_cases hcandidate : registerOffset ≤ candidate
    · by_cases heq : candidate = registerOffset + register
      · subst candidate
        simp
      · have hsub : candidate - registerOffset ≠ register := by omega
        simp [hcandidate, heq, hsub]
    · have heq : candidate ≠ registerOffset + register := by omega
      simp [hcandidate, heq]

@[simp] theorem relocateState_jump (pcOffset registerOffset target : ℕ)
    (lowerRegisters : ℕ → ℕ) (state : NPOracleState) :
    (relocateState pcOffset registerOffset lowerRegisters state).jump
        (pcOffset + target) =
      relocateState pcOffset registerOffset lowerRegisters
        (state.jump target) := by
  rfl

theorem relocateState_boundedWrite (pcOffset registerOffset maximumBits
    register value : ℕ) (lowerRegisters : ℕ → ℕ)
    (state : NPOracleState) :
    (relocateState pcOffset registerOffset lowerRegisters state).boundedWrite
        maximumBits (registerOffset + register) value =
      Option.map (relocateState pcOffset registerOffset lowerRegisters)
        (state.boundedWrite maximumBits register value) := by
  simp only [NPOracleState.boundedWrite]
  split
  · simp [relocateState_write]
  · rfl

theorem run_relocated {whole source : NPOracleProgram}
    {pcOffset registerOffset maximumBits fuel output : ℕ}
    {state : NPOracleState} (lowerRegisters : ℕ → ℕ)
    (hat : ProgramRelocatedAt whole source pcOffset registerOffset)
    (hexec :
      runNPOracleProgram source maximumBits fuel state = some output) :
    runNPOracleProgram whole maximumBits fuel
      (relocateState pcOffset registerOffset lowerRegisters state) =
        some output := by
  induction fuel generalizing state lowerRegisters with
  | zero => simp [runNPOracleProgram] at hexec
  | succ fuel ih =>
      simp only [runNPOracleProgram] at hexec ⊢
      cases hlookup : source[state.pc]? with
      | none => simp [hlookup] at hexec
      | some instruction =>
          have hwhole := hat state.pc instruction hlookup
          rw [hlookup] at hexec
          rw [relocateState_pc, hwhole]
          cases instruction with
          | halt outputRegister =>
              simp only [relocateInstruction] at hexec ⊢
              simpa using hexec
          | set register value next =>
              simp only [relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits register value with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec
          | copy sourceRegister destination next =>
              simp only [relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers sourceRegister) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec
          | increment register next =>
              simp only [relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register + 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec
          | decrement register next =>
              simp only [relocateInstruction] at hexec ⊢
              rw [Nat.pred_eq_sub_one] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register - 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec
          | add left right destination next =>
              simp only [relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left + state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_register,
                    relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec
          | subtract left right destination next =>
              simp only [relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left - state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_register,
                    relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec
          | pair left right destination next =>
              simp only [relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.pair (state.registers left) (state.registers right)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_register,
                    relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec
          | unpairLeft sourceRegister destination next =>
              simp only [relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers sourceRegister)).1 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec
          | unpairRight sourceRegister destination next =>
              simp only [relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers sourceRegister)).2 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec
          | branchZero register zeroTarget nonzeroTarget =>
              simp only [relocateInstruction] at hexec ⊢
              rw [relocateState_register]
              by_cases hzero : state.registers register = 0
              · simp only [if_pos hzero] at hexec ⊢
                rw [relocateState_jump]
                exact ih lowerRegisters hexec
              · simp only [if_neg hzero] at hexec ⊢
                rw [relocateState_jump]
                exact ih lowerRegisters hexec
          | encodeNat sourceRegister destination next =>
              simp only [relocateInstruction] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits destination
                  (CanonicalBinary.encodeNat
                    (state.registers sourceRegister)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [relocateState_register, relocateState_boundedWrite, hwrite]
                  simp only [Option.map]
                  rw [relocateState_jump]
                  exact ih lowerRegisters hexec
          | shiftRight sourceRegister amount destination next =>
              simp only [relocateInstruction] at hexec ⊢
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                rw [relocateState_register, relocateState_boundedWrite, hwrite]
                simp only [Option.map]
                rw [relocateState_jump]
                exact ih lowerRegisters hexec
          | shiftLeft sourceRegister amount destination next =>
              simp only [relocateInstruction] at hexec ⊢
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                rw [relocateState_register, relocateState_boundedWrite, hwrite]
                simp only [Option.map]
                rw [relocateState_jump]
                exact ih lowerRegisters hexec
          | testBit sourceRegister indexRegister destination next =>
              simp only [relocateInstruction] at hexec ⊢
              rw [relocateState_register, relocateState_register]
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                rw [relocateState_boundedWrite, hwrite]
                simp only [Option.map]
                rw [relocateState_jump]
                exact ih lowerRegisters hexec
          | sat query destination next =>
              simp only [relocateInstruction] at hexec ⊢
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
                    exact ih lowerRegisters hexec
              · simp at hexec

def zeroRegisterRange : ℕ → ℕ → NPOracleState → NPOracleState
  | _, 0, state => state
  | firstRegister, count + 1, state =>
      zeroRegisterRange (firstRegister + 1) count
        (state.write firstRegister 0)

@[simp] theorem zeroRegisterRange_jump (firstRegister count pc : ℕ)
    (state : NPOracleState) :
    zeroRegisterRange firstRegister count (state.jump pc) =
      (zeroRegisterRange firstRegister count state).jump pc := by
  induction count generalizing firstRegister state with
  | zero => rfl
  | succ count ih =>
      simp only [zeroRegisterRange]
      rw [show (state.jump pc).write firstRegister 0 =
        (state.write firstRegister 0).jump pc by rfl]
      exact ih (firstRegister + 1) (state.write firstRegister 0)

theorem zeroRegisterRange_below {firstRegister count register : ℕ}
    (state : NPOracleState) (hregister : register < firstRegister) :
    (zeroRegisterRange firstRegister count state).registers register =
      state.registers register := by
  induction count generalizing firstRegister state with
  | zero => rfl
  | succ count ih =>
      simp only [zeroRegisterRange]
      rw [ih (state.write firstRegister 0) (by omega)]
      simp [NPOracleState.write]
      omega

theorem zeroRegisterRange_above {firstRegister count register : ℕ}
    (state : NPOracleState) (hregister : firstRegister + count ≤ register) :
    (zeroRegisterRange firstRegister count state).registers register =
      state.registers register := by
  induction count generalizing firstRegister state with
  | zero => rfl
  | succ count ih =>
      simp only [zeroRegisterRange]
      rw [ih (state.write firstRegister 0) (by omega)]
      simp [NPOracleState.write]
      omega

theorem zeroRegisterRange_inside {firstRegister count register : ℕ}
    (state : NPOracleState) (hlower : firstRegister ≤ register)
    (hupper : register < firstRegister + count) :
    (zeroRegisterRange firstRegister count state).registers register = 0 := by
  induction count generalizing firstRegister state with
  | zero => omega
  | succ count ih =>
      simp only [zeroRegisterRange]
      by_cases heq : register = firstRegister
      · subst register
        rw [zeroRegisterRange_below (state.write firstRegister 0) (by omega)]
        simp [NPOracleState.write]
      · exact ih (state.write firstRegister 0) (by omega) (by omega)

theorem resetProgramAt_tail {whole : NPOracleProgram}
    {firstRegister count startPc : ℕ}
    (hat : ResetProgramAt whole firstRegister (count + 1) startPc) :
    ResetProgramAt whole (firstRegister + 1) count (startPc + 1) := by
  intro index hindex
  have h := hat (index + 1) (by omega)
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

theorem run_resetProgramAt {whole : NPOracleProgram}
    {firstRegister count startPc maximumBits remaining output : ℕ}
    {state : NPOracleState}
    (hbits : 1 ≤ maximumBits)
    (hat : ResetProgramAt whole firstRegister count startPc)
    (hcontinuation :
      runNPOracleProgram whole maximumBits remaining
        ((zeroRegisterRange firstRegister count state).jump
          (startPc + count)) = some output) :
    runNPOracleProgram whole maximumBits (count + remaining)
      (state.jump startPc) = some output := by
  induction count generalizing firstRegister startPc state with
  | zero => simpa [zeroRegisterRange] using hcontinuation
  | succ count ih =>
      rw [show count + 1 + remaining = (count + remaining) + 1 by omega]
      simp only [runNPOracleProgram]
      have hlookup := hat 0 (by omega)
      simp only [Nat.add_zero] at hlookup
      rw [show (state.jump startPc).pc = startPc by rfl, hlookup]
      simp only
      have hwrite :
          (state.jump startPc).boundedWrite maximumBits firstRegister 0 =
            some ((state.write firstRegister 0).jump startPc) := by
        simp [NPOracleState.boundedWrite, natBitLength, hbits,
          NPOracleState.write, NPOracleState.jump]
      rw [hwrite]
      apply ih (resetProgramAt_tail hat)
      have hstates :
          (zeroRegisterRange (firstRegister + 1) count
              ((state.write firstRegister 0).jump startPc)).jump
                (startPc + 1 + count) =
            (zeroRegisterRange firstRegister (count + 1) state).jump
              (startPc + (count + 1)) := by
        rw [zeroRegisterRange_jump]
        simp only [zeroRegisterRange]
        rw [show startPc + 1 + count = startPc + (count + 1) by omega]
        rfl
      rw [hstates]
      exact hcontinuation

def firstStageState (layout : LinkLayout) (inputLength : ℕ)
    (state : NPOracleState) : NPOracleState where
  pc := layout.firstBase + state.pc
  registers := fun candidate =>
    if candidate < layout.firstSpan then state.registers candidate
    else if candidate = layout.savedLengthRegister then inputLength else 0

@[simp] theorem firstStageState_pc (layout : LinkLayout) (inputLength : ℕ)
    (state : NPOracleState) :
    (firstStageState layout inputLength state).pc =
      layout.firstBase + state.pc := rfl

theorem firstStageState_register (layout : LinkLayout) (inputLength : ℕ)
    (state : NPOracleState) {register : ℕ}
    (hregister : register < layout.firstSpan) :
    (firstStageState layout inputLength state).registers register =
      state.registers register := by
  simp [firstStageState, hregister]

theorem firstStageState_write (layout : LinkLayout) (inputLength : ℕ)
    (state : NPOracleState) {register value : ℕ}
    (hregister : register < layout.firstSpan) :
    (firstStageState layout inputLength state).write register value =
      firstStageState layout inputLength (state.write register value) := by
  cases state with
  | mk statePc stateRegisters =>
    simp only [firstStageState, NPOracleState.write]
    congr 1
    funext candidate
    by_cases heq : candidate = register
    · subst candidate
      simp [hregister]
    · by_cases hcandidate : candidate < layout.firstSpan
      · simp [heq, hcandidate]
      · simp [heq, hcandidate]

@[simp] theorem firstStageState_jump (layout : LinkLayout) (inputLength : ℕ)
    (state : NPOracleState) (target : ℕ) :
    (firstStageState layout inputLength state).jump
        (layout.firstBase + target) =
      firstStageState layout inputLength (state.jump target) := by
  rfl

theorem firstStageState_boundedWrite (layout : LinkLayout)
    (inputLength maximumBits : ℕ) (state : NPOracleState)
    {register value : ℕ} (hregister : register < layout.firstSpan) :
    (firstStageState layout inputLength state).boundedWrite
        maximumBits register value =
      Option.map (firstStageState layout inputLength)
        (state.boundedWrite maximumBits register value) := by
  simp only [NPOracleState.boundedWrite]
  split
  · simp [firstStageState_write layout inputLength state hregister]
  · rfl

theorem run_continued {whole source : NPOracleProgram}
    {layout : LinkLayout} {inputLength maximumBits fuel extraFuel
      intermediate finalOutput : ℕ} {state : NPOracleState}
    (hat : ProgramContinuedAt whole source layout.firstBase
      layout.transferRegister layout.resetBase)
    (hlayout : programRegisterSpan source ≤ layout.firstSpan)
    (hexec :
      runNPOracleProgram source maximumBits fuel state = some intermediate)
    (hhandoff : ∀ (haltState : NPOracleState) (unused : ℕ),
      runNPOracleProgram whole maximumBits (unused + extraFuel)
        (((firstStageState layout inputLength haltState).write
          layout.transferRegister intermediate).jump layout.resetBase) =
            some finalOutput) :
    runNPOracleProgram whole maximumBits (fuel + extraFuel)
      (firstStageState layout inputLength state) = some finalOutput := by
  induction fuel generalizing state with
  | zero => simp [runNPOracleProgram] at hexec
  | succ fuel ih =>
      rw [show fuel + 1 + extraFuel = (fuel + extraFuel) + 1 by omega]
      simp only [runNPOracleProgram] at hexec ⊢
      cases hlookup : source[state.pc]? with
      | none => simp [hlookup] at hexec
      | some instruction =>
          have hwhole := hat state.pc instruction hlookup
          have hmem : instruction ∈ source := List.mem_of_getElem? hlookup
          rw [hlookup] at hexec
          rw [firstStageState_pc, hwhole]
          cases instruction with
          | halt outputRegister =>
              simp only [continueInstruction] at hexec ⊢
              have houtputRegister : outputRegister < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              rw [firstStageState_register layout inputLength state
                houtputRegister]
              rcases (by simpa using hexec) with ⟨hbits, houtput⟩
              subst intermediate
              have hwrite :
                  (firstStageState layout inputLength state).boundedWrite
                      maximumBits layout.transferRegister
                        (state.registers outputRegister) =
                    some ((firstStageState layout inputLength state).write
                      layout.transferRegister
                        (state.registers outputRegister)) := by
                simp [NPOracleState.boundedWrite, hbits]
              rw [hwrite]
              exact hhandoff state fuel
          | set register value next =>
              simp only [continueInstruction] at hexec ⊢
              have hregister : register < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              cases hwrite :
                  state.boundedWrite maximumBits register value with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [firstStageState_boundedWrite layout inputLength
                    maximumBits state hregister, hwrite]
                  simp only [Option.map]
                  rw [firstStageState_jump]
                  exact ih hexec
          | copy sourceRegister destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hsource : sourceRegister < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers sourceRegister) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [firstStageState_register layout inputLength state hsource]
                  rw [firstStageState_boundedWrite layout inputLength
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageState_jump]
                  exact ih hexec
          | increment register next =>
              simp only [continueInstruction] at hexec ⊢
              have hregister : register < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register + 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [firstStageState_register layout inputLength state hregister]
                  rw [firstStageState_boundedWrite layout inputLength
                    maximumBits state hregister, hwrite]
                  simp only [Option.map]
                  rw [firstStageState_jump]
                  exact ih hexec
          | decrement register next =>
              simp only [continueInstruction] at hexec ⊢
              rw [Nat.pred_eq_sub_one] at hexec ⊢
              have hregister : register < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register - 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [firstStageState_register layout inputLength state hregister]
                  rw [firstStageState_boundedWrite layout inputLength
                    maximumBits state hregister, hwrite]
                  simp only [Option.map]
                  rw [firstStageState_jump]
                  exact ih hexec
          | add left right destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hleft : left < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hright : right < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left + state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [firstStageState_register layout inputLength state hleft,
                    firstStageState_register layout inputLength state hright]
                  rw [firstStageState_boundedWrite layout inputLength
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageState_jump]
                  exact ih hexec
          | subtract left right destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hleft : left < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hright : right < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left - state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [firstStageState_register layout inputLength state hleft,
                    firstStageState_register layout inputLength state hright]
                  rw [firstStageState_boundedWrite layout inputLength
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageState_jump]
                  exact ih hexec
          | pair left right destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hleft : left < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hright : right < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.pair (state.registers left) (state.registers right)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [firstStageState_register layout inputLength state hleft,
                    firstStageState_register layout inputLength state hright]
                  rw [firstStageState_boundedWrite layout inputLength
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageState_jump]
                  exact ih hexec
          | unpairLeft sourceRegister destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hsource : sourceRegister < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers sourceRegister)).1 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [firstStageState_register layout inputLength state hsource]
                  rw [firstStageState_boundedWrite layout inputLength
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageState_jump]
                  exact ih hexec
          | unpairRight sourceRegister destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hsource : sourceRegister < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers sourceRegister)).2 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [firstStageState_register layout inputLength state hsource]
                  rw [firstStageState_boundedWrite layout inputLength
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageState_jump]
                  exact ih hexec
          | branchZero register zeroTarget nonzeroTarget =>
              simp only [continueInstruction] at hexec ⊢
              have hregister : register < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              rw [firstStageState_register layout inputLength state hregister]
              by_cases hzero : state.registers register = 0
              · simp only [if_pos hzero] at hexec ⊢
                rw [firstStageState_jump]
                exact ih hexec
              · simp only [if_neg hzero] at hexec ⊢
                rw [firstStageState_jump]
                exact ih hexec
          | encodeNat sourceRegister destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hsource : sourceRegister < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              cases hwrite : state.boundedWrite maximumBits destination
                  (CanonicalBinary.encodeNat
                    (state.registers sourceRegister)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  rw [firstStageState_register layout inputLength state hsource]
                  rw [firstStageState_boundedWrite layout inputLength
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageState_jump]
                  exact ih hexec
          | shiftRight sourceRegister amount destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hsource : sourceRegister < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                rw [firstStageState_register layout inputLength state hsource]
                rw [firstStageState_boundedWrite layout inputLength
                  maximumBits state hdestination, hwrite]
                simp only [Option.map]
                rw [firstStageState_jump]
                exact ih hexec
          | shiftLeft sourceRegister amount destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hsource : sourceRegister < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                rw [firstStageState_register layout inputLength state hsource]
                rw [firstStageState_boundedWrite layout inputLength
                  maximumBits state hdestination, hwrite]
                simp only [Option.map]
                rw [firstStageState_jump]
                exact ih hexec
          | testBit sourceRegister indexRegister destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hsource : sourceRegister < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hindex : indexRegister < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              rw [firstStageState_register layout inputLength state hsource,
                firstStageState_register layout inputLength state hindex]
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                rw [firstStageState_boundedWrite layout inputLength
                  maximumBits state hdestination, hwrite]
                simp only [Option.map]
                rw [firstStageState_jump]
                exact ih hexec
          | sat query destination next =>
              simp only [continueInstruction] at hexec ⊢
              have hquery : query < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              have hdestination : destination < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              rw [firstStageState_register layout inputLength state hquery]
              split at hexec
              · rename_i hqueryBits
                rw [if_pos hqueryBits]
                cases hwrite : state.boundedWrite maximumBits destination
                    (encodedSat (state.registers query)).toNat with
                | none => simp [hwrite] at hexec
                | some nextState =>
                    simp only [hwrite] at hexec
                    rw [firstStageState_boundedWrite layout inputLength
                      maximumBits state hdestination, hwrite]
                    simp only [Option.map]
                    rw [firstStageState_jump]
                    exact ih hexec
              · simp at hexec

theorem run_fuel_add {program : NPOracleProgram} {maximumBits fuel : ℕ}
    {state : NPOracleState} {output : ℕ}
    (hexec :
      runNPOracleProgram program maximumBits fuel state = some output)
    (extra : ℕ) :
    runNPOracleProgram program maximumBits (fuel + extra) state = some output := by
  induction fuel generalizing state with
  | zero => simp [runNPOracleProgram] at hexec
  | succ fuel ih =>
      rw [Nat.succ_add]
      cases hlookup : program[state.pc]? with
      | none =>
          simp [runNPOracleProgram, hlookup] at hexec
      | some instruction =>
          simp only [runNPOracleProgram, hlookup] at hexec ⊢
          cases instruction with
          | halt _ =>
              exact hexec
          | set register value _ =>
              cases hwrite :
                  state.boundedWrite maximumBits register value with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | copy source destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers source) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | increment register _ =>
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register + 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | decrement register _ =>
              simp only at hexec ⊢
              rw [Nat.pred_eq_sub_one] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register - 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | add left right destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left + state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | subtract left right destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left - state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | pair left right destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.pair (state.registers left)
                    (state.registers right)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | unpairLeft source destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers source)).1 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | unpairRight source destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers source)).2 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | branchZero _ _ _ =>
              exact ih hexec
          | encodeNat source destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (CanonicalBinary.encodeNat
                    (state.registers source)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | shiftRight source amount destination _ =>
              simp only at hexec ⊢
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                exact ih hexec
          | shiftLeft source amount destination _ =>
              simp only at hexec ⊢
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                exact ih hexec
          | testBit source index destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (((state.registers source).testBit
                    (state.registers index)).toNat) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | sat query destination _ =>
              by_cases hquery :
                  natBitLength (state.registers query) ≤ maximumBits
              · simp only [if_pos hquery] at hexec ⊢
                cases hwrite : state.boundedWrite maximumBits destination
                    (encodedSat (state.registers query)).toNat with
                | none => simp [hwrite] at hexec
                | some nextState =>
                    simp only [hwrite] at hexec ⊢
                    exact ih hexec
              · simp [hquery] at hexec

theorem run_output_bounded {program : NPOracleProgram} {maximumBits fuel : ℕ}
    {state : NPOracleState} {output : ℕ}
    (hexec :
      runNPOracleProgram program maximumBits fuel state = some output) :
    natBitLength output ≤ maximumBits := by
  induction fuel generalizing state with
  | zero => simp [runNPOracleProgram] at hexec
  | succ fuel ih =>
      cases hlookup : program[state.pc]? with
      | none => simp [runNPOracleProgram, hlookup] at hexec
      | some instruction =>
          simp only [runNPOracleProgram, hlookup] at hexec
          cases instruction with
          | halt outputRegister =>
              rcases (by simpa using hexec) with ⟨hbits, houtput⟩
              subst output
              exact hbits
          | set register value next =>
              cases hwrite : state.boundedWrite maximumBits register value with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  exact ih hexec
          | copy source destination next =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers source) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  exact ih hexec
          | increment register next =>
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register + 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  exact ih hexec
          | decrement register next =>
              simp only at hexec
              rw [Nat.pred_eq_sub_one] at hexec
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register - 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  exact ih hexec
          | add left right destination next =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left + state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  exact ih hexec
          | subtract left right destination next =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left - state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  exact ih hexec
          | pair left right destination next =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.pair (state.registers left) (state.registers right)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  exact ih hexec
          | unpairLeft source destination next =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers source)).1 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  exact ih hexec
          | unpairRight source destination next =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers source)).2 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  exact ih hexec
          | branchZero register zeroTarget nonzeroTarget =>
              exact ih hexec
          | encodeNat source destination next =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (CanonicalBinary.encodeNat (state.registers source)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec
                  exact ih hexec
          | shiftRight source amount destination next =>
              simp only at hexec
              split at hexec
              · simp at hexec
              · exact ih hexec
          | shiftLeft source amount destination next =>
              simp only at hexec
              split at hexec
              · simp at hexec
              · exact ih hexec
          | testBit source index destination next =>
              simp only at hexec
              split at hexec
              · simp at hexec
              · exact ih hexec
          | sat query destination next =>
              by_cases hquery :
                  natBitLength (state.registers query) ≤ maximumBits
              · simp only [if_pos hquery] at hexec
                cases hwrite : state.boundedWrite maximumBits destination
                    (encodedSat (state.registers query)).toNat with
                | none => simp [hwrite] at hexec
                | some nextState =>
                    simp only [hwrite] at hexec
                    exact ih hexec
              · simp [hquery] at hexec

def firstStageHandoffState (layout : LinkLayout)
    (inputLength intermediate : ℕ) (haltState : NPOracleState) :
    NPOracleState :=
  (firstStageState layout inputLength haltState).write
    layout.transferRegister intermediate

def resetHandoffState (layout : LinkLayout)
    (inputLength intermediate : ℕ) (haltState : NPOracleState) :
    NPOracleState :=
  zeroRegisterRange layout.secondRegisterBase layout.secondSpan
    (firstStageHandoffState layout inputLength intermediate haltState)

def secondStageEntryState (layout : LinkLayout) (inputLength intermediate : ℕ)
    (haltState : NPOracleState) : NPOracleState :=
  (((((resetHandoffState layout inputLength intermediate haltState).write
      layout.secondRegisterBase intermediate).write
      (layout.secondRegisterBase + 1) inputLength).write
      layout.transferRegister 0).write
      layout.savedLengthRegister 0).jump layout.secondBase

private theorem npOracleState_ext (left right : NPOracleState)
    (hpc : left.pc = right.pc)
    (hregisters : left.registers = right.registers) :
    left = right := by
  cases left
  cases right
  simp_all

@[simp] private theorem stateWrite_pc (state : NPOracleState)
    (register value : ℕ) :
    (state.write register value).pc = state.pc := rfl

@[simp] private theorem stateWrite_registers (state : NPOracleState)
    (register value candidate : ℕ) :
    (state.write register value).registers candidate =
      if candidate = register then value else state.registers candidate := rfl

@[simp] private theorem stateJump_pc (state : NPOracleState) (pc : ℕ) :
    (state.jump pc).pc = pc := rfl

@[simp] private theorem stateJump_registers (state : NPOracleState)
    (pc candidate : ℕ) :
    (state.jump pc).registers candidate = state.registers candidate := rfl

theorem resetHandoffState_transfer (first second : NPOracleProgram)
    (inputLength intermediate : ℕ) (haltState : NPOracleState) :
    (resetHandoffState (linkLayout first second) inputLength intermediate
      haltState).registers (linkLayout first second).transferRegister =
        intermediate := by
  let layout := linkLayout first second
  change
    (resetHandoffState layout inputLength intermediate haltState).registers
        layout.transferRegister = intermediate
  rw [show resetHandoffState layout inputLength intermediate haltState =
    zeroRegisterRange layout.secondRegisterBase layout.secondSpan
      (firstStageHandoffState layout inputLength intermediate haltState) by
        rfl]
  rw [zeroRegisterRange_above _ (by
    simp only [layout, linkLayout]
    omega)]
  simp [firstStageHandoffState]

theorem resetHandoffState_savedLength (first second : NPOracleProgram)
    (inputLength intermediate : ℕ) (haltState : NPOracleState) :
    (resetHandoffState (linkLayout first second) inputLength intermediate
      haltState).registers (linkLayout first second).savedLengthRegister =
        inputLength := by
  let layout := linkLayout first second
  change
    (resetHandoffState layout inputLength intermediate haltState).registers
        layout.savedLengthRegister = inputLength
  rw [show resetHandoffState layout inputLength intermediate haltState =
    zeroRegisterRange layout.secondRegisterBase layout.secondSpan
      (firstStageHandoffState layout inputLength intermediate haltState) by
        rfl]
  rw [zeroRegisterRange_above _ (by
    simp only [layout, linkLayout]
    omega)]
  simp only [firstStageHandoffState, stateWrite_registers]
  rw [if_neg (by
    simp only [layout, linkLayout]
    omega)]
  simp only [firstStageState]
  rw [if_neg (by
    simp only [layout, linkLayout]
    omega), if_true]

theorem secondStageEntryState_eq_relocate (first second : NPOracleProgram)
    (inputLength intermediate : ℕ) (haltState : NPOracleState) :
    secondStageEntryState (linkLayout first second) inputLength intermediate
        haltState =
      relocateState (linkLayout first second).secondBase
        (linkLayout first second).secondRegisterBase haltState.registers
        (initialNPOracleState inputLength intermediate) := by
  let layout := linkLayout first second
  have hbase : layout.secondRegisterBase = layout.firstSpan := by
    simp [layout, linkLayout]
  have hsaved :
      layout.savedLengthRegister =
        layout.secondRegisterBase + layout.secondSpan := by
    simp [layout, linkLayout]
  have htransfer :
      layout.transferRegister =
        layout.secondRegisterBase + layout.secondSpan + 1 := by
    simp [layout, linkLayout]
  have hspan : 2 ≤ layout.secondSpan := by
    simpa [layout, linkLayout] using two_le_programRegisterSpan second
  apply npOracleState_ext
  · simp [secondStageEntryState, relocateState, initialNPOracleState]
  · funext candidate
    change
      (secondStageEntryState layout inputLength intermediate haltState).registers
          candidate =
        (relocateState layout.secondBase layout.secondRegisterBase
          haltState.registers
          (initialNPOracleState inputLength intermediate)).registers candidate
    by_cases hlow : candidate < layout.secondRegisterBase
    · simp only [secondStageEntryState, stateJump_registers,
        stateWrite_registers]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
      simp only [resetHandoffState]
      rw [zeroRegisterRange_below _ hlow]
      simp only [firstStageHandoffState, stateWrite_registers]
      rw [if_neg (by omega)]
      rw [firstStageState_register layout inputLength haltState (by
        simpa [hbase] using hlow)]
      simp [relocateState, hlow]
    · have hlower : layout.secondRegisterBase ≤ candidate := by omega
      by_cases hzero : candidate = layout.secondRegisterBase
      · subst candidate
        simp only [secondStageEntryState, stateJump_registers,
          stateWrite_registers]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_true]
        simp [relocateState, initialNPOracleState]
      · by_cases hone : candidate = layout.secondRegisterBase + 1
        · subst candidate
          simp only [secondStageEntryState, stateJump_registers,
            stateWrite_registers]
          rw [if_neg (by omega), if_neg (by omega), if_true]
          simp [relocateState, initialNPOracleState]
        · by_cases hinside :
            candidate < layout.secondRegisterBase + layout.secondSpan
          · simp only [secondStageEntryState, stateJump_registers,
              stateWrite_registers]
            rw [if_neg (by omega), if_neg (by omega), if_neg hone,
              if_neg hzero]
            simp only [resetHandoffState]
            rw [zeroRegisterRange_inside _ hlower hinside]
            have hsubZero :
                candidate - layout.secondRegisterBase ≠ 0 := by omega
            have hsubOne :
                candidate - layout.secondRegisterBase ≠ 1 := by omega
            simp [relocateState, initialNPOracleState, hlower, hsubZero,
              hsubOne]
          · have habove :
                layout.secondRegisterBase + layout.secondSpan ≤ candidate := by
              omega
            by_cases hsavedCandidate :
                candidate = layout.savedLengthRegister
            · subst candidate
              simp only [secondStageEntryState, stateJump_registers,
                stateWrite_registers]
              rw [if_true]
              simp [relocateState, initialNPOracleState, hsaved,
                show layout.secondSpan ≠ 0 by omega,
                show layout.secondSpan ≠ 1 by omega]
            · by_cases htransferCandidate :
                candidate = layout.transferRegister
              · subst candidate
                simp only [secondStageEntryState, stateJump_registers,
                  stateWrite_registers]
                rw [if_neg (by omega), if_true]
                simp only [relocateState]
                rw [if_pos hlower]
                simp only [initialNPOracleState]
                rw [show layout.transferRegister -
                    layout.secondRegisterBase = layout.secondSpan + 1 by omega]
                simp
                omega
              · have hfirst :
                (firstStageState layout inputLength haltState).registers
                        candidate = 0 := by
                  simp [firstStageState, hsavedCandidate]
                  omega
                simp only [secondStageEntryState, stateJump_registers,
                  stateWrite_registers]
                rw [if_neg hsavedCandidate, if_neg htransferCandidate,
                  if_neg hone, if_neg hzero]
                simp only [resetHandoffState]
                rw [zeroRegisterRange_above _ habove]
                simp only [firstStageHandoffState, stateWrite_registers]
                rw [if_neg htransferCandidate, hfirst]
                have hsubZero :
                    candidate - layout.secondRegisterBase ≠ 0 := by omega
                have hsubOne :
                    candidate - layout.secondRegisterBase ≠ 1 := by omega
                simp [relocateState, initialNPOracleState, hlower, hsubZero,
                  hsubOne]

theorem run_linkPrograms_handoff {first second : NPOracleProgram}
    {maximumBits firstInputLength intermediate secondFuel output unused : ℕ}
    {haltState : NPOracleState}
    (hbitsPositive : 1 ≤ maximumBits)
    (hinputLength : natBitLength firstInputLength ≤ maximumBits)
    (hintermediate : natBitLength intermediate ≤ maximumBits)
    (hsecond :
      runNPOracleProgram second maximumBits secondFuel
        (initialNPOracleState firstInputLength intermediate) = some output) :
    runNPOracleProgram (linkPrograms first second) maximumBits
        ((linkLayout first second).secondSpan + 4 + secondFuel + unused)
        ((firstStageHandoffState (linkLayout first second) firstInputLength
          intermediate haltState).jump
            (linkLayout first second).resetBase) =
      some output := by
  let layout := linkLayout first second
  change
    runNPOracleProgram (linkPrograms first second) maximumBits
        (layout.secondSpan + 4 + secondFuel + unused)
        ((firstStageHandoffState layout firstInputLength intermediate
          haltState).jump layout.resetBase) = some output
  rw [show layout.secondSpan + 4 + secondFuel + unused =
    layout.secondSpan + (4 + (secondFuel + unused)) by omega]
  apply run_resetProgramAt hbitsPositive (linkPrograms_resetAt first second)
  have hlookup0 :
      (linkPrograms first second)[layout.resetBase + layout.secondSpan]? =
        some (.copy layout.transferRegister layout.secondRegisterBase
          (layout.resetBase + layout.secondSpan + 1)) := by
    simpa [layout] using
      linkPrograms_plumbingAt first second 0 (by omega)
  have hlookup1 :
      (linkPrograms first second)[layout.resetBase + layout.secondSpan + 1]? =
        some (.copy layout.savedLengthRegister
          (layout.secondRegisterBase + 1)
          (layout.resetBase + layout.secondSpan + 2)) := by
    simpa [layout] using
      linkPrograms_plumbingAt first second 1 (by omega)
  have hlookup2 :
      (linkPrograms first second)[layout.resetBase + layout.secondSpan + 2]? =
        some (.set layout.transferRegister 0
          (layout.resetBase + layout.secondSpan + 3)) := by
    simpa [layout] using
      linkPrograms_plumbingAt first second 2 (by omega)
  have hlookup3 :
      (linkPrograms first second)[layout.resetBase + layout.secondSpan + 3]? =
        some (.set layout.savedLengthRegister 0 layout.secondBase) := by
    simpa [layout] using
      linkPrograms_plumbingAt first second 3 (by omega)
  let resetState :=
    resetHandoffState layout firstInputLength intermediate haltState
  let withOutput := resetState.write layout.secondRegisterBase intermediate
  let withInputLength :=
    withOutput.write (layout.secondRegisterBase + 1) firstInputLength
  let withoutTransfer := withInputLength.write layout.transferRegister 0
  let secondEntry := withoutTransfer.write layout.savedLengthRegister 0
  change
    runNPOracleProgram (linkPrograms first second) maximumBits
      (4 + (secondFuel + unused))
      (resetState.jump (layout.resetBase + layout.secondSpan)) = some output
  have htransferValue :
      resetState.registers layout.transferRegister = intermediate := by
    simpa [resetState, layout] using
      resetHandoffState_transfer first second firstInputLength intermediate
        haltState
  rw [show 4 + (secondFuel + unused) =
    (3 + (secondFuel + unused)) + 1 by omega]
  simp only [runNPOracleProgram]
  rw [stateJump_pc, hlookup0]
  simp only
  rw [stateJump_registers, htransferValue]
  have hwrite0 :
      (resetState.jump
          (layout.resetBase + layout.secondSpan)).boundedWrite maximumBits
            layout.secondRegisterBase intermediate =
        some ((resetState.jump
          (layout.resetBase + layout.secondSpan)).write
            layout.secondRegisterBase intermediate) := by
    simp [NPOracleState.boundedWrite, hintermediate]
  rw [hwrite0]
  change
    runNPOracleProgram (linkPrograms first second) maximumBits
      (3 + (secondFuel + unused))
      (withOutput.jump (layout.resetBase + layout.secondSpan + 1)) =
        some output
  rw [show 3 + (secondFuel + unused) =
    (2 + (secondFuel + unused)) + 1 by omega]
  simp only [runNPOracleProgram]
  rw [stateJump_pc, hlookup1]
  simp only
  have hsavedValue :
      resetState.registers layout.savedLengthRegister = firstInputLength := by
    simpa [resetState, layout] using
      resetHandoffState_savedLength first second firstInputLength intermediate
        haltState
  have hwithOutputSaved :
      withOutput.registers layout.savedLengthRegister = firstInputLength := by
    simp only [withOutput, stateWrite_registers]
    rw [if_neg (by
      have hspan2 := two_le_programRegisterSpan second
      simp only [layout, linkLayout]
      omega), hsavedValue]
  rw [stateJump_registers, hwithOutputSaved]
  have hwrite1 :
      (withOutput.jump
          (layout.resetBase + layout.secondSpan + 1)).boundedWrite maximumBits
            (layout.secondRegisterBase + 1) firstInputLength =
        some ((withOutput.jump
          (layout.resetBase + layout.secondSpan + 1)).write
            (layout.secondRegisterBase + 1) firstInputLength) := by
    simp [NPOracleState.boundedWrite, hinputLength]
  rw [hwrite1]
  change
    runNPOracleProgram (linkPrograms first second) maximumBits
      (2 + (secondFuel + unused))
      (withInputLength.jump (layout.resetBase + layout.secondSpan + 2)) =
        some output
  rw [show 2 + (secondFuel + unused) =
    (1 + (secondFuel + unused)) + 1 by omega]
  simp only [runNPOracleProgram]
  rw [stateJump_pc, hlookup2]
  simp only
  have hwrite2 :
      (withInputLength.jump
          (layout.resetBase + layout.secondSpan + 2)).boundedWrite maximumBits
            layout.transferRegister 0 =
        some ((withInputLength.jump
          (layout.resetBase + layout.secondSpan + 2)).write
            layout.transferRegister 0) := by
    simp [NPOracleState.boundedWrite, natBitLength, hbitsPositive]
  rw [hwrite2]
  change
    runNPOracleProgram (linkPrograms first second) maximumBits
      (1 + (secondFuel + unused))
      (withoutTransfer.jump (layout.resetBase + layout.secondSpan + 3)) =
        some output
  rw [show 1 + (secondFuel + unused) =
    (secondFuel + unused) + 1 by omega]
  simp only [runNPOracleProgram]
  rw [stateJump_pc, hlookup3]
  simp only
  have hwrite3 :
      (withoutTransfer.jump
          (layout.resetBase + layout.secondSpan + 3)).boundedWrite maximumBits
            layout.savedLengthRegister 0 =
        some ((withoutTransfer.jump
          (layout.resetBase + layout.secondSpan + 3)).write
            layout.savedLengthRegister 0) := by
    simp [NPOracleState.boundedWrite, natBitLength, hbitsPositive]
  rw [hwrite3]
  change
    runNPOracleProgram (linkPrograms first second) maximumBits
      (secondFuel + unused) (secondEntry.jump layout.secondBase) = some output
  have hrelocated :
      runNPOracleProgram (linkPrograms first second) maximumBits secondFuel
        (secondStageEntryState layout firstInputLength intermediate haltState) =
          some output := by
    rw [secondStageEntryState_eq_relocate first second]
    exact run_relocated haltState.registers
      (linkPrograms_secondAt first second) hsecond
  have hrelocatedExtra := run_fuel_add hrelocated unused
  have hentry :
      secondEntry.jump layout.secondBase =
        secondStageEntryState layout firstInputLength intermediate haltState := by
    rfl
  rw [hentry]
  exact hrelocatedExtra

theorem linkPrograms_prologue (first second : NPOracleProgram) :
    (linkPrograms first second)[0]? =
      some (.copy 1 (linkLayout first second).savedLengthRegister
        (linkLayout first second).firstBase) := by
  simp [linkPrograms]

def prologueState (layout : LinkLayout) (inputLength inputCode : ℕ) :
    NPOracleState :=
  ((initialNPOracleState inputLength inputCode).write
    layout.savedLengthRegister inputLength).jump layout.firstBase

theorem prologueState_eq_firstStageState (first second : NPOracleProgram)
    (inputLength inputCode : ℕ) :
    prologueState (linkLayout first second) inputLength inputCode =
      firstStageState (linkLayout first second) inputLength
        (initialNPOracleState inputLength inputCode) := by
  let layout := linkLayout first second
  have hfirstSpan : 2 ≤ layout.firstSpan := by
    simpa [layout, linkLayout] using two_le_programRegisterSpan first
  have hsaved :
      layout.savedLengthRegister =
        layout.firstSpan + layout.secondSpan := by
    simp [layout, linkLayout]
  change
    prologueState layout inputLength inputCode =
      firstStageState layout inputLength
        (initialNPOracleState inputLength inputCode)
  apply npOracleState_ext
  · rfl
  · funext candidate
    simp only [prologueState, stateJump_registers, stateWrite_registers]
    by_cases hbelow : candidate < layout.firstSpan
    · rw [if_neg (by omega)]
      simp [firstStageState, hbelow]
    · by_cases hsavedCandidate : candidate = layout.savedLengthRegister
      · subst candidate
        simp [firstStageState, hsaved]
      · rw [if_neg hsavedCandidate]
        have hzero : candidate ≠ 0 := by omega
        have hone : candidate ≠ 1 := by omega
        simp [firstStageState, hbelow, hsavedCandidate,
          initialNPOracleState, hzero, hone]

def linkFuel (second : NPOracleProgram) (firstFuel secondFuel : ℕ) : ℕ :=
  1 + firstFuel + (programRegisterSpan second + 4 + secondFuel)

/-- Executable sequential composition: the output of `first` is the request in
register zero for `second`; both programs see the same public length in
register one.  The theorem accounts for every prologue, reset, and plumbing
instruction executed by the linked program. -/
theorem run_linkPrograms {first second : NPOracleProgram}
    {maximumBits inputLength inputCode firstFuel intermediate secondFuel
      output : ℕ}
    (hbitsPositive : 1 ≤ maximumBits)
    (hinputLength : natBitLength inputLength ≤ maximumBits)
    (hfirst :
      runNPOracleProgram first maximumBits firstFuel
        (initialNPOracleState inputLength inputCode) = some intermediate)
    (hsecond :
      runNPOracleProgram second maximumBits secondFuel
        (initialNPOracleState inputLength intermediate) = some output) :
    runNPOracleProgram (linkPrograms first second) maximumBits
        (linkFuel second firstFuel secondFuel)
        (initialNPOracleState inputLength inputCode) = some output := by
  let layout := linkLayout first second
  let extraFuel := layout.secondSpan + 4 + secondFuel
  have hintermediate : natBitLength intermediate ≤ maximumBits :=
    run_output_bounded hfirst
  change
    runNPOracleProgram (linkPrograms first second) maximumBits
        (1 + firstFuel + (programRegisterSpan second + 4 + secondFuel))
        (initialNPOracleState inputLength inputCode) = some output
  rw [show 1 + firstFuel + (programRegisterSpan second + 4 + secondFuel) =
    (firstFuel + extraFuel) + 1 by
      simp only [extraFuel, layout, linkLayout]
      omega]
  simp only [runNPOracleProgram]
  rw [show (initialNPOracleState inputLength inputCode).pc = 0 by rfl,
    linkPrograms_prologue first second]
  simp only
  rw [show (initialNPOracleState inputLength inputCode).registers 1 =
    inputLength by simp [initialNPOracleState]]
  have hprologueWrite :
      (initialNPOracleState inputLength inputCode).boundedWrite maximumBits
          (linkLayout first second).savedLengthRegister inputLength =
        some ((initialNPOracleState inputLength inputCode).write
          (linkLayout first second).savedLengthRegister inputLength) := by
    simp [NPOracleState.boundedWrite, hinputLength]
  rw [hprologueWrite]
  simp only
  rw [show
    ((initialNPOracleState inputLength inputCode).write
      (linkLayout first second).savedLengthRegister inputLength).jump
        (linkLayout first second).firstBase =
      firstStageState layout inputLength
        (initialNPOracleState inputLength inputCode) by
          simpa [prologueState, layout] using
            prologueState_eq_firstStageState first second inputLength inputCode]
  apply run_continued (linkPrograms_firstAt first second)
    (le_refl (programRegisterSpan first)) hfirst
  intro haltState unused
  change
    runNPOracleProgram (linkPrograms first second) maximumBits
      (unused + extraFuel)
      ((firstStageHandoffState layout inputLength intermediate
        haltState).jump layout.resetBase) = some output
  rw [show unused + extraFuel =
    layout.secondSpan + 4 + secondFuel + unused by
      simp only [extraFuel]
      omega]
  exact run_linkPrograms_handoff hbitsPositive hinputLength hintermediate
    hsecond

theorem linkFuel_exact (second : NPOracleProgram)
    (firstFuel secondFuel : ℕ) :
    linkFuel second firstFuel secondFuel =
      firstFuel + secondFuel + programRegisterSpan second + 5 := by
  simp [linkFuel]
  omega

theorem linkPrograms_length (first second : NPOracleProgram) :
    (linkPrograms first second).length =
      first.length + second.length + programRegisterSpan second + 5 := by
  simp [linkPrograms, linkLayout, resetRegisters_length]
  omega

theorem linkScratchRegisterCount (first second : NPOracleProgram) :
    (linkLayout first second).transferRegister + 1 =
      programRegisterSpan first + programRegisterSpan second + 2 := by
  simp [linkLayout]

end NearCubicWires.VerifiedLinker
