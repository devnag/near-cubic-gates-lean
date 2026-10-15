import Proof.Circuits.CallableRelocation

namespace NearCubicWires.AmbientLinkEntry

open NearCubicWires
open NearCubicWires.CallableRelocation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

private theorem stateExt {left right : NPOracleState} (hpc : left.pc = right.pc)
    (hregisters : left.registers = right.registers) : left = right := by
  cases left
  cases right
  simp_all

/-! ## 1. The linked program's register span -/

private theorem programRegisterSpan_le_of_forall {program : NPOracleProgram}
    {bound : ℕ} (hbound : 2 ≤ bound)
    (hinstruction : ∀ instruction ∈ program,
      instructionRegisterSpan instruction ≤ bound) :
    programRegisterSpan program ≤ bound := by
  induction program with
  | nil => exact hbound
  | cons head tail ih =>
      simp only [programRegisterSpan]
      refine max_le (hinstruction head (by simp)) (ih ?_)
      intro instruction hmem
      exact hinstruction instruction (by simp [hmem])

private theorem instructionRegisterSpan_continueInstruction
    (pcOffset transferRegister resetPc : ℕ)
    (instruction : NPOracleInstruction) :
    instructionRegisterSpan
        (continueInstruction pcOffset transferRegister resetPc instruction) ≤
      max (instructionRegisterSpan instruction) (transferRegister + 1) := by
  cases instruction <;>
    simp [continueInstruction, instructionRegisterSpan,
      instructionRegisters] <;>
    omega

private theorem instructionRegisterSpan_relocateInstruction
    (pcOffset registerOffset : ℕ) (instruction : NPOracleInstruction) :
    instructionRegisterSpan
        (relocateInstruction pcOffset registerOffset instruction) ≤
      registerOffset + instructionRegisterSpan instruction := by
  cases instruction <;>
    simp [relocateInstruction, instructionRegisterSpan, instructionRegisters]

theorem programRegisterSpan_linkPrograms_le (first second : NPOracleProgram) :
    programRegisterSpan (linkPrograms first second) ≤
      (linkLayout first second).transferRegister + 1 := by
  have hfirstSpan : 2 ≤ programRegisterSpan first :=
    two_le_programRegisterSpan first
  have hsecondSpan : 2 ≤ programRegisterSpan second :=
    two_le_programRegisterSpan second
  refine programRegisterSpan_le_of_forall (by simp [linkLayout]) ?_
  intro instruction hmem
  simp only [linkPrograms, linkLayout, resetRegisters, List.mem_append,
    List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with ((hmem | hmem) | hmem) | hmem
  · rcases hmem with hmem | ⟨source, hsource, hmem⟩
    · subst hmem
      simp [instructionRegisterSpan, instructionRegisters, linkLayout]
    · subst hmem
      refine (instructionRegisterSpan_continueInstruction _ _ _ source).trans ?_
      have := instructionRegisterSpan_le_programRegisterSpan hsource
      simp only [linkLayout]
      omega
  · obtain ⟨index, hindex, hmem⟩ := hmem
    subst hmem
    simp [instructionRegisterSpan, instructionRegisters, linkLayout]
    omega
  · rcases hmem with hmem | hmem | hmem | hmem <;> subst hmem <;>
      simp [instructionRegisterSpan, instructionRegisters, linkLayout] <;> omega
  · obtain ⟨source, hsource, hmem⟩ := hmem
    subst hmem
    refine (instructionRegisterSpan_relocateInstruction _ _ source).trans ?_
    have := instructionRegisterSpan_le_programRegisterSpan hsource
    simp only [linkLayout]
    omega

/-! ## 2. The first stage at an ambient register background -/

def firstStageStateAt (layout : LinkLayout) (ambient : ℕ → ℕ)
    (state : NPOracleState) : NPOracleState where
  pc := layout.firstBase + state.pc
  registers := fun candidate =>
    if candidate < layout.firstSpan then state.registers candidate
    else ambient candidate

@[simp] theorem firstStageStateAt_pc (layout : LinkLayout) (ambient : ℕ → ℕ)
    (state : NPOracleState) :
    (firstStageStateAt layout ambient state).pc =
      layout.firstBase + state.pc := rfl

theorem firstStageStateAt_register (layout : LinkLayout) (ambient : ℕ → ℕ)
    (state : NPOracleState) {register : ℕ}
    (hregister : register < layout.firstSpan) :
    (firstStageStateAt layout ambient state).registers register =
      state.registers register := by
  simp [firstStageStateAt, hregister]

theorem firstStageStateAt_write (layout : LinkLayout) (ambient : ℕ → ℕ)
    (state : NPOracleState) {register value : ℕ}
    (hregister : register < layout.firstSpan) :
    (firstStageStateAt layout ambient state).write register value =
      firstStageStateAt layout ambient (state.write register value) := by
  cases state with
  | mk statePc stateRegisters =>
    simp only [firstStageStateAt, NPOracleState.write]
    congr 1
    funext candidate
    by_cases heq : candidate = register
    · subst candidate
      simp [hregister]
    · by_cases hcandidate : candidate < layout.firstSpan
      · simp [heq, hcandidate]
      · simp [heq, hcandidate]

@[simp] theorem firstStageStateAt_jump (layout : LinkLayout) (ambient : ℕ → ℕ)
    (state : NPOracleState) (target : ℕ) :
    (firstStageStateAt layout ambient state).jump
        (layout.firstBase + target) =
      firstStageStateAt layout ambient (state.jump target) := by
  rfl

theorem firstStageStateAt_boundedWrite (layout : LinkLayout)
    (ambient : ℕ → ℕ) (maximumBits : ℕ) (state : NPOracleState)
    {register value : ℕ} (hregister : register < layout.firstSpan) :
    (firstStageStateAt layout ambient state).boundedWrite
        maximumBits register value =
      Option.map (firstStageStateAt layout ambient)
        (state.boundedWrite maximumBits register value) := by
  simp only [NPOracleState.boundedWrite]
  split
  · simp [firstStageStateAt_write layout ambient state hregister]
  · rfl

theorem run_continuedAt {whole source : NPOracleProgram}
    {layout : LinkLayout} {ambient : ℕ → ℕ}
    {maximumBits fuel extraFuel
      intermediate finalOutput : ℕ} {state : NPOracleState}
    (hat : ProgramContinuedAt whole source layout.firstBase
      layout.transferRegister layout.resetBase)
    (hlayout : programRegisterSpan source ≤ layout.firstSpan)
    (hexec :
      runNPOracleProgram source maximumBits fuel state = some intermediate)
    (hhandoff : ∀ (haltState : NPOracleState) (unused : ℕ),
      runNPOracleProgram whole maximumBits (unused + extraFuel)
        (((firstStageStateAt layout ambient haltState).write
          layout.transferRegister intermediate).jump layout.resetBase) =
            some finalOutput) :
    runNPOracleProgram whole maximumBits (fuel + extraFuel)
      (firstStageStateAt layout ambient state) = some finalOutput := by
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
          rw [firstStageStateAt_pc, hwhole]
          cases instruction with
          | halt outputRegister =>
              simp only [continueInstruction] at hexec ⊢
              have houtputRegister : outputRegister < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              rw [firstStageStateAt_register layout ambient state
                houtputRegister]
              rcases (by simpa using hexec) with ⟨hbits, houtput⟩
              subst intermediate
              have hwrite :
                  (firstStageStateAt layout ambient state).boundedWrite
                      maximumBits layout.transferRegister
                        (state.registers outputRegister) =
                    some ((firstStageStateAt layout ambient state).write
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
                  rw [firstStageStateAt_boundedWrite layout ambient
                    maximumBits state hregister, hwrite]
                  simp only [Option.map]
                  rw [firstStageStateAt_jump]
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
                  rw [firstStageStateAt_register layout ambient state hsource]
                  rw [firstStageStateAt_boundedWrite layout ambient
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageStateAt_jump]
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
                  rw [firstStageStateAt_register layout ambient state hregister]
                  rw [firstStageStateAt_boundedWrite layout ambient
                    maximumBits state hregister, hwrite]
                  simp only [Option.map]
                  rw [firstStageStateAt_jump]
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
                  rw [firstStageStateAt_register layout ambient state hregister]
                  rw [firstStageStateAt_boundedWrite layout ambient
                    maximumBits state hregister, hwrite]
                  simp only [Option.map]
                  rw [firstStageStateAt_jump]
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
                  rw [firstStageStateAt_register layout ambient state hleft,
                    firstStageStateAt_register layout ambient state hright]
                  rw [firstStageStateAt_boundedWrite layout ambient
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageStateAt_jump]
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
                  rw [firstStageStateAt_register layout ambient state hleft,
                    firstStageStateAt_register layout ambient state hright]
                  rw [firstStageStateAt_boundedWrite layout ambient
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageStateAt_jump]
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
                  rw [firstStageStateAt_register layout ambient state hleft,
                    firstStageStateAt_register layout ambient state hright]
                  rw [firstStageStateAt_boundedWrite layout ambient
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageStateAt_jump]
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
                  rw [firstStageStateAt_register layout ambient state hsource]
                  rw [firstStageStateAt_boundedWrite layout ambient
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageStateAt_jump]
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
                  rw [firstStageStateAt_register layout ambient state hsource]
                  rw [firstStageStateAt_boundedWrite layout ambient
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageStateAt_jump]
                  exact ih hexec
          | branchZero register zeroTarget nonzeroTarget =>
              simp only [continueInstruction] at hexec ⊢
              have hregister : register < layout.firstSpan := by
                exact lt_of_lt_of_le
                  (register_lt_programRegisterSpan hmem (by
                    simp [instructionRegisters])) hlayout
              rw [firstStageStateAt_register layout ambient state hregister]
              by_cases hzero : state.registers register = 0
              · simp only [if_pos hzero] at hexec ⊢
                rw [firstStageStateAt_jump]
                exact ih hexec
              · simp only [if_neg hzero] at hexec ⊢
                rw [firstStageStateAt_jump]
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
                  rw [firstStageStateAt_register layout ambient state hsource]
                  rw [firstStageStateAt_boundedWrite layout ambient
                    maximumBits state hdestination, hwrite]
                  simp only [Option.map]
                  rw [firstStageStateAt_jump]
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
                rw [firstStageStateAt_register layout ambient state hsource]
                rw [firstStageStateAt_boundedWrite layout ambient
                  maximumBits state hdestination, hwrite]
                simp only [Option.map]
                rw [firstStageStateAt_jump]
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
                rw [firstStageStateAt_register layout ambient state hsource]
                rw [firstStageStateAt_boundedWrite layout ambient
                  maximumBits state hdestination, hwrite]
                simp only [Option.map]
                rw [firstStageStateAt_jump]
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
              rw [firstStageStateAt_register layout ambient state hsource,
                firstStageStateAt_register layout ambient state hindex]
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                rw [firstStageStateAt_boundedWrite layout ambient
                  maximumBits state hdestination, hwrite]
                simp only [Option.map]
                rw [firstStageStateAt_jump]
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
              rw [firstStageStateAt_register layout ambient state hquery]
              split at hexec
              · rename_i hqueryBits
                rw [if_pos hqueryBits]
                cases hwrite : state.boundedWrite maximumBits destination
                    (encodedSat (state.registers query)).toNat with
                | none => simp [hwrite] at hexec
                | some nextState =>
                    simp only [hwrite] at hexec
                    rw [firstStageStateAt_boundedWrite layout ambient
                      maximumBits state hdestination, hwrite]
                    simp only [Option.map]
                    rw [firstStageStateAt_jump]
                    exact ih hexec
              · simp at hexec

/-! ## 3. The reset block as an equation -/

theorem run_resetProgramAt_eq {whole : NPOracleProgram}
    {firstRegister count startPc maximumBits remaining : ℕ}
    {state : NPOracleState} (hbits : 1 ≤ maximumBits)
    (hat : ResetProgramAt whole firstRegister count startPc) :
    runNPOracleProgram whole maximumBits (count + remaining)
        (state.jump startPc) =
      runNPOracleProgram whole maximumBits remaining
        ((zeroRegisterRange firstRegister count state).jump
          (startPc + count)) := by
  induction count generalizing firstRegister startPc state with
  | zero => simp [zeroRegisterRange]
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
      simp only
      rw [ih (resetProgramAt_tail hat)]
      congr 1
      rw [zeroRegisterRange_jump]
      simp only [zeroRegisterRange]
      rw [show startPc + 1 + count = startPc + (count + 1) by omega]
      rfl

private theorem zeroRegisterRange_pc (firstRegister count : ℕ)
    (state : NPOracleState) :
    (zeroRegisterRange firstRegister count state).pc = state.pc := by
  induction count generalizing firstRegister state with
  | zero => rfl
  | succ count ih =>
      simp only [zeroRegisterRange]
      exact ih (firstRegister + 1) (state.write firstRegister 0)

/-! ## 4. The linked program at an arbitrary entry state -/

set_option maxHeartbeats 1600000 in
-- The statement quantifies the first stage over every entry, so its
-- instantiation inside the prologue elaborates a large term.

theorem run_linkPrograms_anyEntry {first second : NPOracleProgram}
    {maximumBits inputCode firstFuel intermediate secondFuel output : ℕ}
    (hbitsPositive : 1 ≤ maximumBits) (entry : NPOracleState)
    (hentryPc : entry.pc = 0) (hentryInput : entry.registers 0 = inputCode)
    (hlengthBits : natBitLength (entry.registers 1) ≤ maximumBits)
    (hfirst : ∀ state : NPOracleState, state.pc = 0 →
      state.registers 0 = inputCode →
      state.registers 1 = entry.registers 1 →
      runNPOracleProgram first maximumBits firstFuel state = some intermediate)
    (hsecond :
      runNPOracleProgram second maximumBits secondFuel
        (initialNPOracleState (entry.registers 1) intermediate) = some output) :
    runNPOracleProgram (linkPrograms first second) maximumBits
        (linkFuel second firstFuel secondFuel) entry = some output := by
  have hfirstSpan : 2 ≤ programRegisterSpan first :=
    two_le_programRegisterSpan first
  have hsecondSpan : 2 ≤ programRegisterSpan second :=
    two_le_programRegisterSpan second
  obtain ⟨entry0, hentry0Pc, hentry0Registers⟩ :
      ∃ state : NPOracleState, state.pc = 0 ∧ ∀ candidate,
        state.registers candidate =
          if candidate < (linkLayout first second).transferRegister + 1 then
            entry.registers candidate else 0 :=
    ⟨{ pc := 0
       registers := fun candidate =>
         if candidate < (linkLayout first second).transferRegister + 1 then
           entry.registers candidate else 0 }, rfl, fun _ => rfl⟩
  obtain ⟨firstEntry, hfirstEntryPc, hfirstEntryRegisters⟩ :
      ∃ state : NPOracleState, state.pc = 0 ∧ ∀ candidate,
        state.registers candidate = entry0.registers candidate :=
    ⟨{ pc := 0, registers := entry0.registers }, rfl, fun _ => rfl⟩
  have hbelow : ∀ candidate,
      candidate < (linkLayout first second).transferRegister + 1 →
      entry0.registers candidate = entry.registers candidate := by
    intro candidate hcandidate
    rw [hentry0Registers, if_pos hcandidate]
  have habove : ∀ candidate,
      (linkLayout first second).transferRegister + 1 ≤ candidate →
      entry0.registers candidate = 0 := by
    intro candidate hcandidate
    rw [hentry0Registers, if_neg (by omega)]
  have hzeroBelow : (0 : ℕ) < (linkLayout first second).transferRegister + 1 := by
    simp [linkLayout]
  have honeBelow : (1 : ℕ) < (linkLayout first second).transferRegister + 1 := by
    simp [linkLayout]
  have hentry0Input : entry0.registers 0 = inputCode := by
    rw [hbelow 0 hzeroBelow, hentryInput]
  have hentry0Length : entry0.registers 1 = entry.registers 1 :=
    hbelow 1 honeBelow
  have hexec :
      runNPOracleProgram first maximumBits firstFuel firstEntry =
        some intermediate := by
    refine hfirst firstEntry hfirstEntryPc ?_ ?_
    · rw [hfirstEntryRegisters, hentry0Input]
    · rw [hfirstEntryRegisters, hentry0Length]
  have hintermediateBits : natBitLength intermediate ≤ maximumBits :=
    run_output_bounded hexec
  rw [run_congr_of_stateAgreesBelow
    (programRegisterSpan_linkPrograms_le first second)
    (show StateAgreesBelow ((linkLayout first second).transferRegister + 1)
        entry entry0 from
      ⟨by rw [hentryPc, hentry0Pc], fun candidate hcandidate =>
        (hbelow candidate hcandidate).symm⟩)]
  rw [show linkFuel second firstFuel secondFuel =
    (firstFuel +
      ((linkLayout first second).secondSpan + 4 + secondFuel)) + 1 by
      simp only [linkFuel, linkLayout]
      omega]
  simp only [runNPOracleProgram]
  rw [hentry0Pc, linkPrograms_prologue first second]
  simp only
  rw [hentry0Length]
  rw [show entry0.boundedWrite maximumBits
      (linkLayout first second).savedLengthRegister (entry.registers 1) =
      some (entry0.write (linkLayout first second).savedLengthRegister
        (entry.registers 1)) by
    simp [NPOracleState.boundedWrite, hlengthBits]]
  simp only
  rw [show (entry0.write (linkLayout first second).savedLengthRegister
        (entry.registers 1)).jump (linkLayout first second).firstBase =
      firstStageStateAt (linkLayout first second)
        (fun candidate =>
          if candidate = (linkLayout first second).savedLengthRegister then
            entry.registers 1 else entry0.registers candidate)
        firstEntry by
    refine stateExt ?_ ?_
    · simp [firstStageStateAt, NPOracleState.jump, hfirstEntryPc]
    · funext candidate
      by_cases hcandidate : candidate < (linkLayout first second).firstSpan
      · have hne : candidate ≠ (linkLayout first second).savedLengthRegister := by
          simp only [linkLayout] at hcandidate ⊢
          omega
        simp [firstStageStateAt, NPOracleState.jump, NPOracleState.write,
          hcandidate, hne, hfirstEntryRegisters]
      · simp [firstStageStateAt, NPOracleState.jump, NPOracleState.write,
          hcandidate]]
  refine run_continuedAt (linkPrograms_firstAt first second) (le_refl _) hexec ?_
  intro haltState unused
  have hhandoff :=
    run_linkPrograms_handoff (first := first) (second := second)
      (maximumBits := maximumBits) (firstInputLength := entry.registers 1)
      (intermediate := intermediate) (secondFuel := secondFuel)
      (output := output) (unused := unused) (haltState := haltState)
      hbitsPositive hlengthBits hintermediateBits hsecond
  rw [show unused + ((linkLayout first second).secondSpan + 4 + secondFuel) =
    (linkLayout first second).secondSpan + (4 + secondFuel + unused) by omega]
  rw [run_resetProgramAt_eq hbitsPositive (linkPrograms_resetAt first second)]
  rw [show zeroRegisterRange (linkLayout first second).secondRegisterBase
        (linkLayout first second).secondSpan
        ((firstStageStateAt (linkLayout first second)
          (fun candidate =>
            if candidate = (linkLayout first second).savedLengthRegister then
              entry.registers 1 else entry0.registers candidate)
          haltState).write (linkLayout first second).transferRegister
            intermediate) =
      zeroRegisterRange (linkLayout first second).secondRegisterBase
        (linkLayout first second).secondSpan
        (firstStageHandoffState (linkLayout first second) (entry.registers 1)
          intermediate haltState) by
    refine stateExt ?_ ?_
    · rw [zeroRegisterRange_pc, zeroRegisterRange_pc]
      rfl
    · funext candidate
      by_cases hlow :
          candidate < (linkLayout first second).secondRegisterBase
      · rw [zeroRegisterRange_below _ hlow, zeroRegisterRange_below _ hlow]
        have hne : candidate ≠ (linkLayout first second).transferRegister := by
          simp only [linkLayout] at hlow ⊢
          omega
        have hfirstLow : candidate < (linkLayout first second).firstSpan := by
          simp only [linkLayout] at hlow ⊢
          omega
        simp [firstStageStateAt, firstStageHandoffState, firstStageState,
          NPOracleState.write, hne, hfirstLow]
      · by_cases hmid :
            candidate <
              (linkLayout first second).secondRegisterBase +
                (linkLayout first second).secondSpan
        · rw [zeroRegisterRange_inside _ (by omega) hmid,
            zeroRegisterRange_inside _ (by omega) hmid]
        · rw [zeroRegisterRange_above _ (by omega),
            zeroRegisterRange_above _ (by omega)]
          have hfirstHigh :
              ¬candidate < (linkLayout first second).firstSpan := by
            simp only [linkLayout] at hlow hmid ⊢
            omega
          by_cases htransfer :
              candidate = (linkLayout first second).transferRegister
          · subst candidate
            simp [firstStageStateAt, firstStageHandoffState, firstStageState,
              NPOracleState.write]
          · by_cases hsaved :
                candidate = (linkLayout first second).savedLengthRegister
            · subst candidate
              simp [firstStageStateAt, firstStageHandoffState, firstStageState,
                NPOracleState.write, htransfer, hfirstHigh]
            · have hhigh :
                  (linkLayout first second).transferRegister + 1 ≤ candidate := by
                simp only [linkLayout] at hlow hmid hsaved htransfer ⊢
                omega
              simp [firstStageStateAt, firstStageHandoffState, firstStageState,
                NPOracleState.write, htransfer, hsaved, hfirstHigh,
                habove candidate hhigh]]
  rw [← run_resetProgramAt_eq hbitsPositive (linkPrograms_resetAt first second)]
  rw [show (linkLayout first second).secondSpan + (4 + secondFuel + unused) =
    (linkLayout first second).secondSpan + 4 + secondFuel + unused by omega]
  exact hhandoff

end NearCubicWires.AmbientLinkEntry
