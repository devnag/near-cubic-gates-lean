import Proof.Circuits.CallableRelocation
import Proof.Circuits.CanonicalBalancedTraversal

namespace NearCubicWires.CanonicalRoundCall

open NearCubicWires
open NearCubicWires.CallableRelocation
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## §1 The pure round fold -/

/-- Result of `rounds` rounds of `step`, with the counter descending from
`rounds` to `1`. -/
def roundFold (step : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | carried, 0 => carried
  | carried, count + 1 => roundFold step (step carried (count + 1)) count

@[simp] theorem roundFold_zero (step : ℕ → ℕ → ℕ) (carried : ℕ) :
    roundFold step carried 0 = carried :=
  rfl

theorem roundFold_succ (step : ℕ → ℕ → ℕ) (carried count : ℕ) :
    roundFold step carried (count + 1) =
      roundFold step (step carried (count + 1)) count :=
  rfl

/-! ## §2 Layout and program -/

/-- First program counter of the two frame-install instructions. -/
def roundDecodeBase (callee : NPOracleProgram) : ℕ :=
  4 + programRegisterSpan callee

/-- Entry program counter of the relocated callee. -/
def roundCalleeBase (callee : NPOracleProgram) : ℕ :=
  roundDecodeBase callee + 2

/-- Program counter the callee's halt returns to. -/
def roundReturnPc (callee : NPOracleProgram) : ℕ :=
  roundCalleeBase callee + callee.length

/-- Program counter of the counter decrement. -/
def roundAdvancePc (callee : NPOracleProgram) : ℕ :=
  roundReturnPc callee + 1

/-- Program counter of the controller's halt. -/
def roundDonePc (callee : NPOracleProgram) : ℕ :=
  roundReturnPc callee + 2

def roundCallProgram (callee : NPOracleProgram) : NPOracleProgram :=
  ((([ .unpairLeft 0 3 1
     , .unpairRight 0 2 2
     , .branchZero 3 (roundDonePc callee) 3
     , .pair 2 3 4 4
     ] ++
     resetRegisters 5 (programRegisterSpan callee) 4) ++
     [ .copy 2 6 (roundDecodeBase callee + 1)
     , .copy 4 5 (roundCalleeBase callee)
     ]) ++
     callee.map
       (callableInstruction (roundCalleeBase callee) 5 4
         (roundReturnPc callee))) ++
     [ .unpairRight 4 2 (roundAdvancePc callee)
     , .decrement 3 2
     , .halt 2
     ]

private theorem oracleFree_append
    {first second : NPOracleProgram}
    (hfirst : OracleFree first) (hsecond : OracleFree second) :
    OracleFree (first ++ second) := by
  unfold OracleFree at hfirst hsecond ⊢
  simp [hfirst, hsecond]

private theorem oracleFree_resetRegisters (firstRegister count startPc : ℕ) :
    OracleFree (resetRegisters firstRegister count startPc) := by
  unfold OracleFree
  simp [resetRegisters, List.all_map]

private theorem oracleFree_callableMap
    {callee : NPOracleProgram} (hcallee : OracleFree callee)
    (pcOffset registerOffset accumulatorRegister returnPc : ℕ) :
    OracleFree
      (callee.map (callableInstruction pcOffset registerOffset
        accumulatorRegister returnPc)) := by
  rw [oracleFree_iff_containsSAT_false] at hcallee ⊢
  unfold containsSAT at hcallee ⊢
  rw [List.any_map]
  change callee.any (fun instruction =>
    match callableInstruction pcOffset registerOffset accumulatorRegister
        returnPc instruction with
    | .sat _ _ _ => true
    | _ => false) = false
  exact (any_callableInstruction callee pcOffset registerOffset
    accumulatorRegister returnPc).trans hcallee

theorem roundCallProgram_oracleFree
    {callee : NPOracleProgram} (hcallee : OracleFree callee) :
    OracleFree (roundCallProgram callee) := by
  have hprologue : OracleFree
      [ NPOracleInstruction.unpairLeft 0 3 1
      , .unpairRight 0 2 2
      , .branchZero 3 (roundDonePc callee) 3
      , .pair 2 3 4 4
      ] := by rfl
  have hreset := oracleFree_resetRegisters 5 (programRegisterSpan callee) 4
  have hdecode : OracleFree
      [ NPOracleInstruction.copy 2 6 (roundDecodeBase callee + 1)
      , .copy 4 5 (roundCalleeBase callee)
      ] := by rfl
  have hcallable :=
    oracleFree_callableMap hcallee (roundCalleeBase callee) 5 4
      (roundReturnPc callee)
  have htail : OracleFree
      [ NPOracleInstruction.unpairRight 4 2 (roundAdvancePc callee)
      , .decrement 3 2
      , .halt 2
      ] := by rfl
  simpa [roundCallProgram] using
    oracleFree_append
      (oracleFree_append
        (oracleFree_append
          (oracleFree_append hprologue hreset) hdecode)
        hcallable)
      htail

/-! ## §3 Instruction positions -/

private theorem roundCallProgram_prologue (callee : NPOracleProgram)
    (index : ℕ) (hindex : index < 4) :
    (roundCallProgram callee)[index]? =
      ([ .unpairLeft 0 3 1
       , .unpairRight 0 2 2
       , .branchZero 3 (roundDonePc callee) 3
       , .pair 2 3 4 4
       ] : NPOracleProgram)[index]? := by
  simp only [roundCallProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil, List.length_map]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_cons, List.length_nil]
    omega)]

theorem roundCallProgram_decodeRounds (callee : NPOracleProgram) :
    (roundCallProgram callee)[0]? = some (.unpairLeft 0 3 1) := by
  simpa using roundCallProgram_prologue callee 0 (by omega)

theorem roundCallProgram_decodeState (callee : NPOracleProgram) :
    (roundCallProgram callee)[1]? = some (.unpairRight 0 2 2) := by
  simpa using roundCallProgram_prologue callee 1 (by omega)

theorem roundCallProgram_loop (callee : NPOracleProgram) :
    (roundCallProgram callee)[2]? =
      some (.branchZero 3 (roundDonePc callee) 3) := by
  simpa using roundCallProgram_prologue callee 2 (by omega)

theorem roundCallProgram_request (callee : NPOracleProgram) :
    (roundCallProgram callee)[3]? = some (.pair 2 3 4 4) := by
  simpa using roundCallProgram_prologue callee 3 (by omega)

theorem roundCallProgram_resetAt (callee : NPOracleProgram) :
    ResetProgramAt (roundCallProgram callee) 5 (programRegisterSpan callee) 4 := by
  intro index hindex
  simp only [roundCallProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil, List.length_map]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  simp only [List.length_cons, List.length_nil]
  rw [show 4 + index - 4 = index by omega]
  simp only [resetRegisters, List.getElem?_map]
  rw [List.getElem?_range hindex]
  rfl

private theorem roundCallProgram_decodeAt (callee : NPOracleProgram)
    (index : ℕ) (hindex : index < 2) :
    (roundCallProgram callee)[roundDecodeBase callee + index]? =
      ([ .copy 2 6 (roundDecodeBase callee + 1)
       , .copy 4 5 (roundCalleeBase callee)
       ] : NPOracleProgram)[index]? := by
  simp only [roundCallProgram, roundDecodeBase]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil, List.length_map]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil]
    omega)]
  simp only [List.length_append, resetRegisters_length, List.length_cons,
    List.length_nil]
  rw [show 4 + programRegisterSpan callee + index -
      (4 + programRegisterSpan callee) = index by omega]

theorem roundCallProgram_installLength (callee : NPOracleProgram) :
    (roundCallProgram callee)[roundDecodeBase callee]? =
      some (.copy 2 6 (roundDecodeBase callee + 1)) := by
  simpa using roundCallProgram_decodeAt callee 0 (by omega)

theorem roundCallProgram_installRequest (callee : NPOracleProgram) :
    (roundCallProgram callee)[roundDecodeBase callee + 1]? =
      some (.copy 4 5 (roundCalleeBase callee)) := by
  simpa using roundCallProgram_decodeAt callee 1 (by omega)

theorem roundCallProgram_callableAt (callee : NPOracleProgram) :
    ProgramCallableAt (roundCallProgram callee) callee
      (roundCalleeBase callee) 5 4 (roundReturnPc callee) := by
  intro pc instruction hlookup
  have hpc : pc < callee.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [roundCallProgram, roundCalleeBase, roundDecodeBase]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil, List.length_map]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil]
    omega)]
  simp only [List.length_append, resetRegisters_length, List.length_cons,
    List.length_nil]
  rw [show 4 + programRegisterSpan callee + 2 + pc -
      (4 + programRegisterSpan callee + 2) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem roundCallProgram_return (callee : NPOracleProgram) :
    (roundCallProgram callee)[roundReturnPc callee]? =
      some (.unpairRight 4 2 (roundAdvancePc callee)) := by
  simp only [roundCallProgram, roundReturnPc, roundCalleeBase, roundDecodeBase]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil, List.length_map]
    omega)]
  simp only [List.length_append, resetRegisters_length, List.length_cons,
    List.length_nil, List.length_map]
  rw [show 4 + programRegisterSpan callee + 2 + callee.length -
      (4 + programRegisterSpan callee + 2 + callee.length) = 0 by omega]
  rfl

theorem roundCallProgram_advance (callee : NPOracleProgram) :
    (roundCallProgram callee)[roundAdvancePc callee]? =
      some (.decrement 3 2) := by
  simp only [roundCallProgram, roundAdvancePc, roundReturnPc, roundCalleeBase,
    roundDecodeBase]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil, List.length_map]
    omega)]
  simp only [List.length_append, resetRegisters_length, List.length_cons,
    List.length_nil, List.length_map]
  rw [show 4 + programRegisterSpan callee + 2 + callee.length + 1 -
      (4 + programRegisterSpan callee + 2 + callee.length) = 1 by omega]
  rfl

theorem roundCallProgram_halt (callee : NPOracleProgram) :
    (roundCallProgram callee)[roundDonePc callee]? = some (.halt 2) := by
  simp only [roundCallProgram, roundDonePc, roundReturnPc, roundCalleeBase,
    roundDecodeBase]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, resetRegisters_length, List.length_cons,
      List.length_nil, List.length_map]
    omega)]
  simp only [List.length_append, resetRegisters_length, List.length_cons,
    List.length_nil, List.length_map]
  rw [show 4 + programRegisterSpan callee + 2 + callee.length + 2 -
      (4 + programRegisterSpan callee + 2 + callee.length) = 2 by omega]
  rfl

/-! ## §4 One round's callee frame -/

def roundCallFrame (callee : NPOracleProgram)
    (context request : ℕ) (state : NPOracleState) : NPOracleState :=
  (((zeroRegisterRange 5 (programRegisterSpan callee) state).write 6
      context).write 5 request).jump (roundCalleeBase callee)

theorem roundCallFrame_registers_low (callee : NPOracleProgram)
    (context request : ℕ) (state : NPOracleState)
    {candidate : ℕ} (hcandidate : candidate < 5) :
    (roundCallFrame callee context request state).registers candidate =
      state.registers candidate := by
  have hbelow :=
    zeroRegisterRange_below (firstRegister := 5)
      (count := programRegisterSpan callee) state hcandidate
  have hfive : candidate ≠ 5 := by omega
  have hsix : candidate ≠ 6 := by omega
  simpa [roundCallFrame, NPOracleState.write, NPOracleState.jump, hfive,
    hsix] using hbelow

/-- The installed frame is exactly the relocated image of the callee's own
canonical initial state. -/
theorem roundCallFrame_eq_active (callee : NPOracleProgram)
    (context request : ℕ) (state : NPOracleState) :
    roundCallFrame callee context request state =
      relocateActiveState (roundCalleeBase callee) 5
        (programRegisterSpan callee)
        (roundCallFrame callee context request state).registers
        (initialNPOracleState context request) := by
  apply state_ext
  · simp [roundCallFrame, relocateActiveState, initialNPOracleState,
      NPOracleState.jump]
  · funext candidate
    by_cases hinside :
        5 ≤ candidate ∧ candidate < 5 + programRegisterSpan callee
    · obtain ⟨hlower, hupper⟩ := hinside
      by_cases hfive : candidate = 5
      · subst candidate
        simp [roundCallFrame, relocateActiveState, initialNPOracleState,
          NPOracleState.write, NPOracleState.jump]
      · by_cases hsix : candidate = 6
        · subst candidate
          simp [roundCallFrame, relocateActiveState, initialNPOracleState,
            NPOracleState.write, NPOracleState.jump]
        · have hreset :
              (zeroRegisterRange 5 (programRegisterSpan callee)
                state).registers candidate = 0 :=
            zeroRegisterRange_inside state hlower hupper
          have hsubZero : candidate - 5 ≠ 0 := by omega
          have hsubOne : candidate - 5 ≠ 1 := by omega
          simp [roundCallFrame, relocateActiveState, initialNPOracleState,
            NPOracleState.write, NPOracleState.jump, hfive, hsix, hsubZero,
            hsubOne, hreset, hlower, hupper]
    · simp [relocateActiveState, hinside]

private theorem write_jump_registers_of_ne (state : NPOracleState)
    (register value pc candidate : ℕ) (hne : candidate ≠ register) :
    ((state.write register value).jump pc).registers candidate =
      state.registers candidate := by
  simp [NPOracleState.write, NPOracleState.jump, hne]

private theorem returnState_registers_low
    (pcOffset returnPc accumulatorValue : ℕ) (background : ℕ → ℕ)
    (haltState : NPOracleState) (candidate : ℕ)
    (hcandidate : candidate < 5) (haccumulator : candidate ≠ 4) :
    (((relocateState pcOffset 5 background haltState).write 4
        accumulatorValue).jump returnPc).registers candidate =
      background candidate := by
  simp only [NPOracleState.jump, NPOracleState.write]
  rw [if_neg haccumulator]
  exact relocateState_below hcandidate

private theorem returnState_registers_accumulator
    (pcOffset returnPc accumulatorValue : ℕ) (background : ℕ → ℕ)
    (haltState : NPOracleState) :
    (((relocateState pcOffset 5 background haltState).write 4
        accumulatorValue).jump returnPc).registers 4 = accumulatorValue := by
  simp [NPOracleState.jump, NPOracleState.write]

/-! ## §5 The counted loop, executed -/

def roundCallLoopFuel (callee : NPOracleProgram)
    (calleeFuel step : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | _carried, 0 => 1
  | carried, count + 1 =>
      programRegisterSpan callee + calleeFuel carried (count + 1) + 6 +
        roundCallLoopFuel callee calleeFuel step
          (step carried (count + 1)) count

theorem roundCallLoopFuel_succ (callee : NPOracleProgram)
    (calleeFuel step : ℕ → ℕ → ℕ) (carried count : ℕ) :
    roundCallLoopFuel callee calleeFuel step carried (count + 1) =
      programRegisterSpan callee + calleeFuel carried (count + 1) + 6 +
        roundCallLoopFuel callee calleeFuel step
          (step carried (count + 1)) count :=
  rfl

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

private theorem reachable_roundFold {step : ℕ → ℕ → ℕ}
    {reachable : ℕ → ℕ → Prop}
    (hadvance : ∀ carried counter, reachable carried (counter + 1) →
      reachable (step carried (counter + 1)) counter) :
    ∀ (remaining carried : ℕ), reachable carried remaining →
      reachable (roundFold step carried remaining) 0 := by
  intro remaining
  induction remaining with
  | zero => exact fun _ hreachable => hreachable
  | succ count inductionHypothesis =>
      exact fun carried hreachable =>
        inductionHypothesis _ (hadvance carried count hreachable)

set_option maxHeartbeats 1000000 in
-- One round is a branch, a request pairing, the bank reset, the two frame
-- installs, the relocated callee, and the two-instruction return; the induction
-- carries only the carried state and the counter.
private theorem run_roundCallLoop
    {callee : NPOracleProgram} {maximumBits : ℕ}
    {calleeFuel step : ℕ → ℕ → ℕ} {reachable : ℕ → ℕ → Prop}
    (hpositive : 1 ≤ maximumBits)
    (hcarriedBits : ∀ carried counter, reachable carried counter →
      natBitLength (Nat.pair carried counter) ≤ maximumBits)
    (hreturnBits : ∀ carried counter, reachable carried (counter + 1) →
      natBitLength
          (Nat.pair (Nat.pair carried (counter + 1))
            (step carried (counter + 1))) ≤ maximumBits)
    (hadvance : ∀ carried counter, reachable carried (counter + 1) →
      reachable (step carried (counter + 1)) counter)
    (hexec : ∀ carried counter, reachable carried (counter + 1) →
      runNPOracleProgram callee maximumBits (calleeFuel carried (counter + 1))
          (initialNPOracleState carried
            (Nat.pair carried (counter + 1))) =
        some (step carried (counter + 1))) :
    ∀ (remaining carried : ℕ) (loopState : NPOracleState),
      reachable carried remaining →
      loopState.pc = 2 →
      loopState.registers 2 = carried →
      loopState.registers 3 = remaining →
      RunsWithin (roundCallProgram callee) maximumBits
        (roundCallLoopFuel callee calleeFuel step carried remaining) loopState
        (fun finish =>
          finish.pc = roundDonePc callee ∧
          finish.registers 2 = roundFold step carried remaining) := by
  intro remaining
  induction remaining with
  | zero =>
      intro carried loopState _hreachable hpc hcarried hcounter
      have hbranch :=
        runsTo_branchZero (program := roundCallProgram callee)
          (maximumBits := maximumBits) (roundCallProgram_loop callee) hpc
      rw [hcounter, if_pos rfl] at hbranch
      refine hbranch.toRunsWithin.mono ?_
      intro finish hfinish
      subst finish
      exact ⟨rfl, by simpa [NPOracleState.jump] using hcarried⟩
  | succ count inductionHypothesis =>
      intro carried loopState hreachable hpc hcarried hcounter
      obtain ⟨requestState, hrequestState⟩ :
          ∃ frameSource : NPOracleState,
            frameSource =
              (loopState.jump 3).write 4 (Nat.pair carried (count + 1)) :=
        ⟨_, rfl⟩
      have hrequestTwo : requestState.registers 2 = carried := by
        rw [hrequestState]
        simpa [NPOracleState.write, NPOracleState.jump] using hcarried
      have hrequestThree : requestState.registers 3 = count + 1 := by
        rw [hrequestState]
        simpa [NPOracleState.write, NPOracleState.jump] using hcounter
      have hrequestFour :
          requestState.registers 4 = Nat.pair carried (count + 1) := by
        rw [hrequestState]
        simp [NPOracleState.write, NPOracleState.jump]
      have hrequestBits :
          natBitLength (Nat.pair carried (count + 1)) ≤ maximumBits :=
        hcarriedBits carried (count + 1) hreachable
      have hcarriedValueBits : natBitLength carried ≤ maximumBits :=
        bits_of_le (Nat.left_le_pair _ _) hrequestBits
      have hframeBits := hreturnBits carried count hreachable
      have houtputBits :
          natBitLength (step carried (count + 1)) ≤ maximumBits :=
        bits_of_le (Nat.right_le_pair _ _) hframeBits
      have hnextBits :
          natBitLength (Nat.pair (step carried (count + 1)) count) ≤
            maximumBits :=
        hcarriedBits _ count (hadvance carried count hreachable)
      have hcountBits : natBitLength count ≤ maximumBits :=
        bits_of_le (Nat.right_le_pair _ _) hnextBits
      have hbranch :=
        runsTo_branchZero (program := roundCallProgram callee)
          (maximumBits := maximumBits) (roundCallProgram_loop callee) hpc
      rw [hcounter, if_neg (by omega : count + 1 ≠ 0)] at hbranch
      have hpair :
          RunsToIn (roundCallProgram callee) maximumBits 1 (loopState.jump 3)
            (requestState.jump 4) := by
        rw [hrequestState]
        exact runsTo_pair (roundCallProgram_request callee) rfl
          (by simp [NPOracleState.jump, hcarried, hcounter]) hrequestBits
      have hprologue :
          RunsToIn (roundCallProgram callee) maximumBits 2 loopState
            (requestState.jump 4) :=
        hbranch.trans hpair
      have hresetWithin :
          RunsWithin (roundCallProgram callee) maximumBits
            (programRegisterSpan callee) (requestState.jump 4)
            (· =
              (zeroRegisterRange 5 (programRegisterSpan callee)
                requestState).jump (roundDecodeBase callee)) := by
        intro extra finalOutput hcontinuation
        have hafter :
            runNPOracleProgram (roundCallProgram callee) maximumBits extra
                ((zeroRegisterRange 5 (programRegisterSpan callee)
                  requestState).jump (roundDecodeBase callee)) =
              some finalOutput := by
          simpa using hcontinuation _ 0 rfl
        exact run_resetProgramAt hpositive
          (roundCallProgram_resetAt callee) hafter
      have hresetTwo :
          (zeroRegisterRange 5 (programRegisterSpan callee)
            requestState).registers 2 = carried := by
        rw [zeroRegisterRange_below _ (by omega)]
        exact hrequestTwo
      have hresetFour :
          (zeroRegisterRange 5 (programRegisterSpan callee)
            requestState).registers 4 = Nat.pair carried (count + 1) := by
        rw [zeroRegisterRange_below _ (by omega)]
        exact hrequestFour
      have hinstallContext :
          RunsToIn (roundCallProgram callee) maximumBits 1
            ((zeroRegisterRange 5 (programRegisterSpan callee)
              requestState).jump (roundDecodeBase callee))
            ((((zeroRegisterRange 5 (programRegisterSpan callee)
              requestState).jump (roundDecodeBase callee)).write 6
                carried).jump (roundDecodeBase callee + 1)) :=
        runsTo_copy (roundCallProgram_installLength callee) rfl hresetTwo
          hcarriedValueBits
      have hinstallRequestValue :
          ((((zeroRegisterRange 5 (programRegisterSpan callee)
            requestState).jump (roundDecodeBase callee)).write 6
              carried).jump (roundDecodeBase callee + 1)).registers 4 =
            Nat.pair carried (count + 1) := by
        rw [write_jump_registers_of_ne _ 6 carried
          (roundDecodeBase callee + 1) 4 (by omega)]
        exact hresetFour
      have hinstallRequest :
          RunsToIn (roundCallProgram callee) maximumBits 1
            ((((zeroRegisterRange 5 (programRegisterSpan callee)
              requestState).jump (roundDecodeBase callee)).write 6
                carried).jump (roundDecodeBase callee + 1))
            (roundCallFrame callee carried (Nat.pair carried (count + 1))
              requestState) :=
        runsTo_copy (roundCallProgram_installRequest callee) rfl
          hinstallRequestValue hrequestBits
      have hframeThree :
          (roundCallFrame callee carried (Nat.pair carried (count + 1))
            requestState).registers 3 = count + 1 := by
        rw [roundCallFrame_registers_low callee carried
          (Nat.pair carried (count + 1)) requestState (by omega : (3 : ℕ) < 5)]
        exact hrequestThree
      have hframeFour :
          (roundCallFrame callee carried (Nat.pair carried (count + 1))
            requestState).registers 4 = Nat.pair carried (count + 1) := by
        rw [roundCallFrame_registers_low callee carried
          (Nat.pair carried (count + 1)) requestState (by omega : (4 : ℕ) < 5)]
        exact hrequestFour
      have hcalleeWithin :
          RunsWithin (roundCallProgram callee) maximumBits
            (calleeFuel carried (count + 1) + 2)
            (roundCallFrame callee carried (Nat.pair carried (count + 1))
              requestState)
            (fun finish =>
              finish.pc = 2 ∧
              finish.registers 2 = step carried (count + 1) ∧
              finish.registers 3 = count) := by
        intro extra finalOutput hcontinuation
        rw [show calleeFuel carried (count + 1) + 2 + extra =
            calleeFuel carried (count + 1) + (2 + extra) by omega]
        rw [roundCallFrame_eq_active callee carried
          (Nat.pair carried (count + 1)) requestState]
        refine run_callable_active
          (background :=
            (roundCallFrame callee carried (Nat.pair carried (count + 1))
              requestState).registers)
          (by omega) (le_refl _) (roundCallProgram_callableAt callee)
          (hexec carried count hreachable) ?_ ?_
        · rw [hframeFour]
          exact hframeBits
        · intro haltState unused
          rw [hframeFour]
          rw [show unused + (2 + extra) = unused + extra + 1 + 1 by omega]
          rw [run_unpairRight_instruction (value := step carried (count + 1))
            (roundCallProgram_return callee) rfl
            (by
              rw [returnState_registers_accumulator]
              simp)
            houtputBits]
          rw [run_decrement_instruction (value := count)
            (roundCallProgram_advance callee) rfl
            (by
              rw [write_jump_registers_of_ne _ 2 (step carried (count + 1))
                (roundAdvancePc callee) 3 (by omega)]
              rw [returnState_registers_low _ _ _ _ _ 3 (by omega) (by omega)]
              rw [hframeThree]
              simp)
            hcountBits]
          apply hcontinuation _ unused
          refine ⟨rfl, ?_, ?_⟩
          · rw [write_jump_registers_of_ne _ 3 count 2 2 (by omega)]
            simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
      have hthroughReset :
          RunsWithin (roundCallProgram callee) maximumBits
            (2 + programRegisterSpan callee) loopState
            (· =
              (zeroRegisterRange 5 (programRegisterSpan callee)
                requestState).jump (roundDecodeBase callee)) :=
        RunsWithin.trans hprologue.toRunsWithin
          (fun middle hmiddle => by
            subst hmiddle
            exact hresetWithin)
      have hthroughDecode :
          RunsWithin (roundCallProgram callee) maximumBits
            (2 + programRegisterSpan callee + 2) loopState
            (· =
              roundCallFrame callee carried
                (Nat.pair carried (count + 1)) requestState) :=
        RunsWithin.trans hthroughReset
          (fun middle hmiddle => by
            subst hmiddle
            exact (hinstallContext.trans hinstallRequest).toRunsWithin)
      have hthroughCall :
          RunsWithin (roundCallProgram callee) maximumBits
            (2 + programRegisterSpan callee + 2 +
              (calleeFuel carried (count + 1) + 2)) loopState
            (fun finish =>
              finish.pc = 2 ∧
              finish.registers 2 = step carried (count + 1) ∧
              finish.registers 3 = count) :=
        RunsWithin.trans hthroughDecode
          (fun middle hmiddle => by
            subst hmiddle
            exact hcalleeWithin)
      have htotal :
          RunsWithin (roundCallProgram callee) maximumBits
            (2 + programRegisterSpan callee + 2 +
              (calleeFuel carried (count + 1) + 2) +
              roundCallLoopFuel callee calleeFuel step
                (step carried (count + 1)) count)
            loopState
            (fun finish =>
              finish.pc = roundDonePc callee ∧
              finish.registers 2 =
                roundFold step (step carried (count + 1)) count) :=
        RunsWithin.trans hthroughCall
          (fun middle hmiddle =>
            inductionHypothesis (step carried (count + 1)) middle
              (hadvance carried count hreachable) hmiddle.1 hmiddle.2.1
              hmiddle.2.2)
      rw [roundCallLoopFuel_succ]
      rw [show programRegisterSpan callee + calleeFuel carried (count + 1) + 6 +
          roundCallLoopFuel callee calleeFuel step
            (step carried (count + 1)) count =
          2 + programRegisterSpan callee + 2 +
            (calleeFuel carried (count + 1) + 2) +
            roundCallLoopFuel callee calleeFuel step
              (step carried (count + 1)) count by omega]
      exact htotal

/-! ## §6 The public round-call theorem -/

/-- Public request ABI: `pair rounds initialState`. -/
def roundCallInput (rounds initialState : ℕ) : ℕ :=
  Nat.pair rounds initialState

def roundCallFuel (callee : NPOracleProgram) (calleeFuel step : ℕ → ℕ → ℕ)
    (initialState rounds : ℕ) : ℕ :=
  roundCallLoopFuel callee calleeFuel step initialState rounds + 3

theorem run_roundCallProgram
    {callee : NPOracleProgram} {maximumBits : ℕ}
    (inputLength rounds initialState : ℕ)
    (calleeFuel step : ℕ → ℕ → ℕ) (reachable : ℕ → ℕ → Prop)
    (hpositive : 1 ≤ maximumBits)
    (hinputBits :
      natBitLength (roundCallInput rounds initialState) ≤ maximumBits)
    (hstart : reachable initialState rounds)
    (hcarriedBits : ∀ carried counter, reachable carried counter →
      natBitLength (Nat.pair carried counter) ≤ maximumBits)
    (hreturnBits : ∀ carried counter, reachable carried (counter + 1) →
      natBitLength
          (Nat.pair (Nat.pair carried (counter + 1))
            (step carried (counter + 1))) ≤ maximumBits)
    (hadvance : ∀ carried counter, reachable carried (counter + 1) →
      reachable (step carried (counter + 1)) counter)
    (hexec : ∀ carried counter, reachable carried (counter + 1) →
      runNPOracleProgram callee maximumBits (calleeFuel carried (counter + 1))
          (initialNPOracleState carried
            (Nat.pair carried (counter + 1))) =
        some (step carried (counter + 1))) :
    runNPOracleProgram (roundCallProgram callee) maximumBits
        (roundCallFuel callee calleeFuel step initialState rounds)
        (initialNPOracleState inputLength
          (roundCallInput rounds initialState)) =
      some (roundFold step initialState rounds) := by
  have hroundsBits : natBitLength rounds ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hinitialBits : natBitLength initialState ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hfinalBits :
      natBitLength (roundFold step initialState rounds) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _)
      (hcarriedBits _ 0
        (reachable_roundFold hadvance rounds initialState hstart))
  have hloop :=
    run_roundCallLoop (callee := callee) (maximumBits := maximumBits)
      (calleeFuel := calleeFuel) (step := step)
      (reachable := reachable) hpositive hcarriedBits hreturnBits
      hadvance hexec rounds initialState
      (((((initialNPOracleState inputLength
        (roundCallInput rounds initialState)).write 3 rounds).jump 1).write 2
          initialState).jump 2)
      hstart rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump])
  rw [show roundCallFuel callee calleeFuel step initialState rounds =
      roundCallLoopFuel callee calleeFuel step initialState rounds + 1 + 1 +
        1 by
    unfold roundCallFuel
    omega]
  rw [run_unpairLeft_instruction (value := rounds)
    (roundCallProgram_decodeRounds callee) rfl
    (by simp [initialNPOracleState, roundCallInput]) hroundsBits]
  rw [run_unpairRight_instruction (value := initialState)
    (roundCallProgram_decodeState callee) rfl
    (by
      simp [initialNPOracleState, roundCallInput, NPOracleState.write,
        NPOracleState.jump])
    hinitialBits]
  refine hloop 1 (roundFold step initialState rounds) ?_
  intro finish unused hfinish
  exact run_halt_instruction (fuel := unused) (roundCallProgram_halt callee)
    hfinish.1 hfinish.2 hfinalBits

end NearCubicWires.CanonicalRoundCall
